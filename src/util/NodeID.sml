structure NodeID :>
sig
  type t

  (** Generate a fresh node ID, guaranteed distinct from all previous ones. *)
  val fresh: unit -> t

  val compare: t * t -> order
  val toString: t -> string
end =
struct
  type t = int

  val counter = ref 0

  fun fresh () =
    let val id = !counter
    in counter := id + 1; id
    end

  val compare = Int.compare
  val toString = Int.toString
end
