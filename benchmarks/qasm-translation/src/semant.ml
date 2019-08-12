open OQAST

module StringMap = Map.Make(String)

let qelib1 = [
  ("u3",  TGate(3,1));
  ("u2",  TGate(2,1));
  ("u1",  TGate(1,1));
  ("cx",  TGate(0,2));
  ("id",  TGate(0,1));
  ("x",   TGate(0,1));
  ("y",   TGate(0,1));
  ("z",   TGate(0,1));
  ("h",   TGate(0,1));
  ("s",   TGate(0,1));
  ("sdg", TGate(0,1));
  ("t",   TGate(0,1));
  ("tdg", TGate(0,1));
  ("rx",  TGate(1,1));
  ("ry",  TGate(1,1));
  ("rz",  TGate(1,1));
  ("cz",  TGate(0,2));
  ("cy",  TGate(0,2));
  ("ch",  TGate(0,2));
  ("ccx", TGate(0,3));
  ("crz", TGate(1,2));
  ("cu1", TGate(1,2));
  ("cu3", TGate(3,2))
]

let check_stmt symTab stmt =
  match stmt with
  | Include "qelib1.inc" -> List.fold_left
                              (fun map (gate, typ) -> StringMap.add gate typ map)
                              symTab qelib1
  | Include _ -> raise (Failure "Unsupported include")
  | Decl (QReg (id, size)) -> StringMap.add id (TQReg size) symTab
  | Decl (CReg (id, size)) -> StringMap.add id (TCReg size) symTab
  | GateDecl ((id, params, qargs), _) ->
    StringMap.add id (TGate (List.length params, List.length qargs)) symTab
  | OpaqueDecl (id, params, qargs) ->
    StringMap.add id (TGate (List.length params, List.length qargs)) symTab
  | _ -> symTab

let check program = List.fold_left check_stmt StringMap.empty program
