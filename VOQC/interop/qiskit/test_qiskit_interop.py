
def assert_equality(before, after, list_opt=None):
    pm = PassManager()
    pm.append(VOQC())
    pm.append(VOQC([list_opt]))
    new_circ = pm.run(before)
    assert (new_circ == after)
def test_AT():
    before = format_from_qasm()
    after = QuantumCircuit.from_qasm_file("optim_tof_10.qasm")
def test_PF():
    before = format_from_qasm()
    after = QuantumCircuit.from_qasm_file("optim_pf2_50.qasm")
def test_QFT():
    before = format_from_qasm()
    
    after = QuantumCircuit.from_qasm_file("optim_Adder8.qasm")       
