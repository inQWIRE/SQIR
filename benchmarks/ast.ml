type id = int

type typ =
  | H
  | X
  | Z

type controls = id list list

type op = typ * id * controls

type program = op list
