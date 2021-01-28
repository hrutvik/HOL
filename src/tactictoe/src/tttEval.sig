signature tttEval =
sig

  include Abbrev

  type tnn = mlTreeNeuralNetwork.tnn
  type nnfiles = string option * string option * string option

  val export_pb_flag : bool ref
  val cheat_flag : bool ref

  val prepare_global_data : (string * int) -> unit
  val ttt_eval : string -> (string * int) -> 
    mlThmData.thmdata * mlTacticData.tacdata ->
    tnn option * tnn option * tnn option ->
    goal -> unit

  val write_evalscript : string -> string -> nnfiles -> string -> unit
  val run_evalscript : string -> string -> nnfiles -> string -> unit
  val run_evalscript_thyl : string -> string -> bool * int ->
    nnfiles -> string list -> unit

  (* statistics *)
  val compile_info : string -> string
  val cumul_graph : real -> string -> unit
  val compare_stats : string list -> string -> unit

  (* reinforcement learning for the value *)
  val rlval : string -> string list -> int -> unit
  val rlval_loop: string -> string list -> int * int -> unit

end
