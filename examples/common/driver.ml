include Driver

let s_int = obliv_int_s

let private_s_int = Conceal.obliv_int_s

let unsafe_r_int = Reveal.obliv_int_r
let unsafe_r_bool = Reveal.obliv_bool_r

let unsafe_if s m n = if Reveal.obliv_bool_r s then m else n

let private_obliv_array_new = Conceal.obliv_array_conceal_with Plaintext.obliv_array_new

let obliv_array_new_from = Conceal.obliv_array_new_for