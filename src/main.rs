use rustsat::{
    types::{Lit, Clause, Assignment, TernaryVal},
    instances::SatInstance,
    solvers::Solve,
    encodings::CollectClauses,
    clause
};

use rustsat_glucose::core::Glucose;

mod logic;
use logic::*;

const N_GATES: usize = 5;
const N_INPUTS: usize = 3;
const N_OUTPUTS: usize = 2;

// AND, OR, XOR, NAND, NOR, XNOR
const ALLOWED_GATES: [&str; 6] = ["AND", "OR", "XOR", "NAND", "NOR", "XNOR"];

const OUTPUTS: [[bool; N_OUTPUTS]; 1 << N_INPUTS] = [
    [false, false],
    [true, false],
    [true, false],
    [false, true],
    [true, false],
    [false, true],
    [false, true],
    [true, true],
];

trait Generator<T> {
    fn make(instance: &mut SatInstance) -> Self;
    fn read_into(self, assignment: &Assignment) -> T;
}

trait GetBool {
    fn get_bool(&self, lit: Lit) -> bool;
}

impl GetBool for Assignment {
    fn get_bool(&self, lit: Lit) -> bool {
        match self.lit_value(lit) {
            TernaryVal::True => true,
            TernaryVal::False => false,
            TernaryVal::DontCare => panic!("Bad lit")
        }
    }
}

fn get_location(assignment: &Assignment, arr: &[Lit]) -> Option<usize> {
    arr.iter().position(|&l| assignment.get_bool(l))
}

#[derive(Clone, Copy, Debug)]
struct GateIO {
    num: usize,
    gate: usize,
}

#[derive(Clone, Copy, Debug)]
struct GateIOLit {
    num: [Lit; N_INPUTS],
    gate: [Lit; N_GATES],
}

impl Generator<GateIO> for GateIOLit {
    fn make(instance: &mut SatInstance) -> Self {
        GateIOLit {
            num: std::array::from_fn(|_| instance.new_lit()),
            gate: std::array::from_fn(|_| instance.new_lit()),
        }
    }

    fn read_into(self, assignment: &Assignment) -> GateIO {
        GateIO {
            num: get_location(assignment, &self.num).map_or(0, |v| v + 1),
            gate: get_location(assignment, &self.gate).map_or(0, |v| v + 1),
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct Gate {
    ty: usize,
    inputs: [GateIO; 2],
}

#[derive(Clone, Copy, Debug)]
struct GateLit {
    ty: [Lit; ALLOWED_GATES.len()],
    inputs: [GateIOLit; 2],
}

impl Generator<Gate> for GateLit {
    fn make(instance: &mut SatInstance) -> Self {
        GateLit {
            ty: std::array::from_fn(|_| instance.new_lit()),
            inputs: std::array::from_fn(|_| GateIOLit::make(instance)),
        }
    }

    fn read_into(self, assignment: &Assignment) -> Gate {
        Gate {
           ty: get_location(assignment, &self.ty).unwrap(),
           inputs: self.inputs.map(|input| input.read_into(assignment)),
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct CircuitLit {
    gates: [GateLit; N_GATES],
    outputs: [[Lit; N_GATES]; N_OUTPUTS],
}

#[derive(Clone, Copy, Debug)]
struct Circuit {
    gates: [Gate; N_GATES],
    outputs: [usize; N_OUTPUTS],
}

impl Generator<Circuit> for CircuitLit {
    fn make(instance: &mut SatInstance) -> Self {
        CircuitLit {
            gates: std::array::from_fn(|_| GateLit::make(instance)),
            outputs: std::array::from_fn(
                |_| std::array::from_fn(|_| instance.new_lit()))
        }
    }

    fn read_into(self, assignment: &Assignment) -> Circuit {
        Circuit {
            gates: self.gates.map(|gate| gate.read_into(assignment)),
            outputs: self.outputs.map(
                |outp| get_location(assignment, &outp).unwrap() + 1) 
        }
    }
}


fn and(v: Lit, a: Lit, b: Lit, out: Lit) -> Vec<Clause> {
    vec![
        clause![!v, a, !out],
        clause![!v, b, !out],
        clause![!v, !a, !b, out]
    ]
}

fn or(v: Lit, a: Lit, b: Lit, out: Lit) -> Vec<Clause> {
    vec![
        clause![!v, !a, out],
        clause![!v, !b, out],
        clause![!v, a, b, !out]
    ]
}

fn xor(v: Lit, a: Lit, b: Lit, out: Lit) -> Vec<Clause> {
    vec![
        clause![!v, !a, !b, !out],
        clause![!v, !a, b, out],
        clause![!v, a, !b, out],
        clause![!v, a, b, !out]
    ]
}

fn not(mut clauses: Vec<Clause>) -> Vec<Clause> {
    for clause in &mut clauses {
        let last = clause.iter_mut().last().unwrap();
        *last = !*last; 
    }

    clauses
}

fn main() {
    let mut instance = SatInstance::new();
    let tt = instance.new_lit();
    instance.add_unit(tt);

    let circuit = CircuitLit::make(&mut instance);

    for gate in &circuit.gates {
        instance.extend_clauses(quadratic_one(gate.ty)).unwrap();

        instance.extend_clauses(quadratic_one(gate.inputs[0].num.into_iter()
                .chain(gate.inputs[0].gate))).unwrap();
        instance.extend_clauses(quadratic_one(gate.inputs[1].num.into_iter()
                .chain(gate.inputs[1].gate))).unwrap();
    }

    for output in &circuit.outputs {
        instance.extend_clauses(quadratic_one(output)).unwrap(); 
    }

    for v in 0..1 << N_INPUTS {
        let outps: [Lit; N_OUTPUTS] = std::array::from_fn(
            |i| if OUTPUTS[v][i] { tt } else { !tt });
        
        let inpts: [Lit; N_INPUTS] = std::array::from_fn(
            |i| if (v >> i) & 1 == 1 { tt } else { !tt });

        let gate_outs: [Lit; N_GATES] = std::array::from_fn(
            |_| instance.new_lit());
    
        for (i, gate) in circuit.gates.into_iter().enumerate() {
            let is = [instance.new_lit(), instance.new_lit()];
            let out = gate_outs[i];

            let mut ty = 0;
            for allowed_gate in ALLOWED_GATES {
                let clauses = match allowed_gate {
                    "AND"  => and(gate.ty[ty], is[0], is[1], out),
                    "OR"   => or(gate.ty[ty], is[0], is[1], out),
                    "XOR"  => xor(gate.ty[ty], is[0], is[1], out),
                    "NAND" => not(and(gate.ty[ty], is[0], is[1], out)),
                    "NOR"  => not(or(gate.ty[ty], is[0], is[1], out)),
                    "XNOR" => not(xor(gate.ty[ty], is[0], is[1], out)),
                    _ => panic!()
                };

                ty += 1;
                
                instance.extend_clauses(clauses).unwrap();
            }

            for (input, inv) in gate.inputs.into_iter().zip(is) {
                for inpt in 0..N_INPUTS {
                    instance.extend_clauses([
                        clause![!input.num[inpt], !inpts[inpt], inv],
                        clause![!input.num[inpt], inpts[inpt], !inv]
                    ]).unwrap();
                }
                
                for gate in 0..N_GATES {
                    instance.extend_clauses([
                        clause![!input.gate[gate], !gate_outs[gate], inv],
                        clause![!input.gate[gate], gate_outs[gate], !inv]
                    ]).unwrap();
                }
            }
    
            for outp in 0..N_OUTPUTS {
                instance.extend_clauses([
                    clause![!circuit.outputs[outp][i], !outps[outp], out],
                    clause![!circuit.outputs[outp][i], outps[outp], !out]
                ]).unwrap();
            }
        } 
    }
    
    // Gates 
    for g in 0..N_GATES {
        // Every logic gate must be used
        let mut is_used = Clause::new();

        for g2 in g..N_GATES {
            // Gates cant read from future gates
            instance.add_unit(!circuit.gates[g].inputs[0].gate[g2]);
            instance.add_unit(!circuit.gates[g].inputs[1].gate[g2]);   
            
            is_used.add(circuit.gates[g2].inputs[0].gate[g]);
            is_used.add(circuit.gates[g2].inputs[1].gate[g]);
        }

        for o in circuit.outputs {
            is_used.add(o[g]);
        }

        instance.add_clause(is_used);
    } 

    instance.write_dimacs_path("cnf.txt").unwrap();
    let (cnf, _) = instance.into_cnf();

    let mut glucose = Glucose::default();
    glucose.add_cnf(cnf).unwrap();

    glucose.solve().unwrap();
    let assignment = glucose.full_solution().expect("No solution");
    // println!("{:?}", assignment);

    let circuit = circuit.read_into(&assignment);
    
    print(circuit);
    //print_gviz(circuit);
}

fn print(circuit: Circuit) {
    let input_strs = ('A'..'Z')
        .take(N_INPUTS)
        .map(|c| c.to_string())
        .collect::<Vec<String>>();

    println!("Inputs: {}", input_strs.join(", "));

    for (i, gate) in circuit.gates.into_iter().enumerate() {
        let gate_string = ALLOWED_GATES[gate.ty].to_string();

        let inputs = gate.inputs.map(
            |input| if input.num > 0 { input_strs[input.num - 1].clone() } 
                else { format!("X{}", input.gate) }); 
        
        println!("X{} = {} {} {}", i + 1, inputs[0], gate_string, inputs[1]);
    }

    println!("Outputs: {}", 
        circuit.outputs.map(|outp| format!("X{outp}")).join(", "));
}

#[allow(dead_code)]
fn print_gviz(circuit: Circuit) {
    let input_strs = ('A'..'Z')
        .take(N_INPUTS)
        .map(|c| c.to_string())
        .collect::<Vec<String>>();

    for (i, gate) in circuit.gates.into_iter().enumerate() {
        let gate_string = ALLOWED_GATES[gate.ty].to_string();

        let inputs = gate.inputs.map(
            |input| if input.num > 0 { input_strs[input.num - 1].clone() } 
                else { format!("X{}", input.gate) }); 
        
        println!("{{{} {}}} -> X{}", inputs[0], inputs[1], i + 1);
        println!("X{} [label=\"{}\"]", i + 1, gate_string);
    }
    
}
