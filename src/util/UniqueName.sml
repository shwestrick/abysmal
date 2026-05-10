structure UniqueName :>
sig
  val fresh: string -> string
end =
struct
  val counter = ref 0
  fun fresh base =
    let val n = !counter
    in counter := n + 1; base ^ Int.toString n
    end
end
