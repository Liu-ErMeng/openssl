-- Numerical certificate source: https://github.com/pyca/verified-garbage/blob/de587df854d6a33e9174b98bb63f4db6261a5f10/lean/VerifiedGarbage/Proof/P384/Prime.lean
-- Rechecked by Lean 4.19.0; no upstream proof code is imported.
import P384.Pratt

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2048

namespace P384
namespace Certificate

theorem prime_2 : Nat.Prime 2 := by norm_num
theorem prime_3 : Nat.Prime 3 := by norm_num
theorem prime_5 : Nat.Prime 5 := by norm_num
theorem prime_7 : Nat.Prime 7 := by norm_num
theorem prime_11 : Nat.Prime 11 := by norm_num
theorem prime_13 : Nat.Prime 13 := by norm_num
theorem prime_17 : Nat.Prime 17 := by norm_num
theorem prime_19 : Nat.Prime 19 := by norm_num
theorem prime_41 : Nat.Prime 41 := by norm_num
theorem prime_47 : Nat.Prime 47 := by norm_num
theorem prime_59 : Nat.Prime 59 := by norm_num
theorem prime_61 : Nat.Prime 61 := by norm_num
theorem prime_67 : Nat.Prime 67 := by norm_num
theorem prime_97 : Nat.Prime 97 := by norm_num
theorem prime_157 : Nat.Prime 157 := by norm_num
theorem prime_181 : Nat.Prime 181 := by norm_num
theorem prime_211 : Nat.Prime 211 := by norm_num
theorem prime_263 : Nat.Prime 263 := by norm_num
theorem prime_599 : Nat.Prime 599 := by norm_num
theorem prime_661 : Nat.Prime 661 := by norm_num
theorem prime_881 : Nat.Prime 881 := by norm_num
theorem prime_937 : Nat.Prime 937 := by norm_num
theorem prime_1033 : Nat.Prime 1033 := by norm_num
theorem prime_1373 : Nat.Prime 1373 := by norm_num
theorem prime_2213 : Nat.Prime 2213 := by norm_num
theorem prime_3253 : Nat.Prime 3253 := by norm_num
theorem prime_3517 : Nat.Prime 3517 := by norm_num
theorem prime_6317 : Nat.Prime 6317 := by norm_num
theorem prime_8389 : Nat.Prime 8389 := by norm_num
theorem prime_21407 : Nat.Prime 21407 := by norm_num
theorem prime_38557 : Nat.Prime 38557 := by norm_num

theorem prime_2862218959 : Nat.Prime 2862218959 := by
  refine Pratt.prime_of_certificate 2862218959 3 32 [2, 3, 157, 1373, 2213]
    (by decide) (by decide) ?_ (by decide) (by decide)
    (by unfold List.Forall; decide)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact prime_2
  · exact prime_3
  · exact prime_157
  · exact prime_1373
  · exact prime_2213

theorem prime_807145746439 : Nat.Prime 807145746439 := by
  refine Pratt.prime_of_certificate 807145746439 3 40 [2, 3, 47, 2862218959]
    (by decide) (by decide) ?_ (by decide) (by decide)
    (by unfold List.Forall; decide)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact prime_2
  · exact prime_3
  · exact prime_47
  · exact prime_2862218959

theorem prime_312289 : Nat.Prime 312289 := by
  refine Pratt.prime_of_certificate 312289 14 19 [2, 2, 2, 2, 2, 3, 3253]
    (by decide) (by decide) ?_ (by decide) (by decide)
    (by unfold List.Forall; decide)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_2
  · exact prime_2
  · exact prime_2
  · exact prime_2
  · exact prime_2
  · exact prime_3
  · exact prime_3253

theorem prime_513928823 : Nat.Prime 513928823 := by
  refine Pratt.prime_of_certificate 513928823 5 29 [2, 11, 59, 599, 661]
    (by decide) (by decide) ?_ (by decide) (by decide)
    (by unfold List.Forall; decide)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact prime_2
  · exact prime_11
  · exact prime_59
  · exact prime_599
  · exact prime_661

theorem prime_53448597593 : Nat.Prime 53448597593 := by
  refine Pratt.prime_of_certificate 53448597593 3 36 [2, 2, 2, 13, 513928823]
    (by decide) (by decide) ?_ (by decide) (by decide)
    (by unfold List.Forall; decide)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact prime_2
  · exact prime_2
  · exact prime_2
  · exact prime_13
  · exact prime_513928823

theorem prime_1357291859799823621 : Nat.Prime 1357291859799823621 := by
  refine Pratt.prime_of_certificate 1357291859799823621 2 61 [2, 2, 3, 5, 67, 6317, 53448597593]
    (by decide) (by decide) ?_ (by decide) (by decide)
    (by unfold List.Forall; decide)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_2
  · exact prime_2
  · exact prime_3
  · exact prime_5
  · exact prime_67
  · exact prime_6317
  · exact prime_53448597593

theorem prime_105957871 : Nat.Prime 105957871 := by
  refine Pratt.prime_of_certificate 105957871 3 27 [2, 3, 5, 19, 211, 881]
    (by decide) (by decide) ?_ (by decide) (by decide)
    (by unfold List.Forall; decide)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_2
  · exact prime_3
  · exact prime_5
  · exact prime_19
  · exact prime_211
  · exact prime_881

theorem prime_246608641 : Nat.Prime 246608641 := by
  refine Pratt.prime_of_certificate 246608641 19 28 [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 21407]
    (by decide) (by decide) ?_ (by decide) (by decide)
    (by unfold List.Forall; decide)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_2
  · exact prime_2
  · exact prime_2
  · exact prime_2
  · exact prime_2
  · exact prime_2
  · exact prime_2
  · exact prime_2
  · exact prime_3
  · exact prime_3
  · exact prime_5
  · exact prime_21407

theorem prime_529709925838459440593 : Nat.Prime 529709925838459440593 := by
  refine Pratt.prime_of_certificate 529709925838459440593 3 69 [2, 2, 2, 2, 7, 181, 105957871, 246608641]
    (by decide) (by decide) ?_ (by decide) (by decide)
    (by unfold List.Forall; decide)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_2
  · exact prime_2
  · exact prime_2
  · exact prime_2
  · exact prime_7
  · exact prime_181
  · exact prime_105957871
  · exact prime_246608641

theorem prime_6051631 : Nat.Prime 6051631 := by
  refine Pratt.prime_of_certificate 6051631 6 23 [2, 3, 5, 13, 59, 263]
    (by decide) (by decide) ?_ (by decide) (by decide)
    (by unfold List.Forall; decide)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_2
  · exact prime_3
  · exact prime_5
  · exact prime_13
  · exact prime_59
  · exact prime_263

theorem prime_336757 : Nat.Prime 336757 := by
  refine Pratt.prime_of_certificate 336757 2 19 [2, 2, 3, 7, 19, 211]
    (by decide) (by decide) ?_ (by decide) (by decide)
    (by unfold List.Forall; decide)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_2
  · exact prime_2
  · exact prime_3
  · exact prime_7
  · exact prime_19
  · exact prime_211

theorem prime_568151 : Nat.Prime 568151 := by
  refine Pratt.prime_of_certificate 568151 17 20 [2, 5, 5, 11, 1033]
    (by decide) (by decide) ?_ (by decide) (by decide)
    (by unfold List.Forall; decide)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact prime_2
  · exact prime_5
  · exact prime_5
  · exact prime_11
  · exact prime_1033

theorem prime_363557 : Nat.Prime 363557 := by
  refine Pratt.prime_of_certificate 363557 2 19 [2, 2, 97, 937]
    (by decide) (by decide) ?_ (by decide) (by decide)
    (by unfold List.Forall; decide)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact prime_2
  · exact prime_2
  · exact prime_97
  · exact prime_937

theorem prime_532247449 : Nat.Prime 532247449 := by
  refine Pratt.prime_of_certificate 532247449 7 29 [2, 2, 2, 3, 61, 363557]
    (by decide) (by decide) ?_ (by decide) (by decide)
    (by unfold List.Forall; decide)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_2
  · exact prime_2
  · exact prime_2
  · exact prime_3
  · exact prime_61
  · exact prime_363557

theorem prime_44925942675193 : Nat.Prime 44925942675193 := by
  refine Pratt.prime_of_certificate 44925942675193 5 46 [2, 2, 2, 3, 3517, 532247449]
    (by decide) (by decide) ?_ (by decide) (by decide)
    (by unfold List.Forall; decide)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_2
  · exact prime_2
  · exact prime_2
  · exact prime_3
  · exact prime_3517
  · exact prime_532247449

theorem prime_35581458644053887931343 : Nat.Prime 35581458644053887931343 := by
  refine Pratt.prime_of_certificate 35581458644053887931343 5 75 [2, 17, 41, 568151, 44925942675193]
    (by decide) (by decide) ?_ (by decide) (by decide)
    (by unfold List.Forall; decide)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact prime_2
  · exact prime_17
  · exact prime_41
  · exact prime_568151
  · exact prime_44925942675193

theorem prime_23964610537191310276190549303 : Nat.Prime 23964610537191310276190549303 := by
  refine Pratt.prime_of_certificate 23964610537191310276190549303 5 95 [2, 336757, 35581458644053887931343]
    (by decide) (by decide) ?_ (by decide) (by decide)
    (by unfold List.Forall; decide)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact prime_2
  · exact prime_336757
  · exact prime_35581458644053887931343

theorem prime_862725979338887169942859774909 : Nat.Prime 862725979338887169942859774909 := by
  refine Pratt.prime_of_certificate 862725979338887169942859774909 2 100 [2, 2, 3, 3, 23964610537191310276190549303]
    (by decide) (by decide) ?_ (by decide) (by decide)
    (by unfold List.Forall; decide)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact prime_2
  · exact prime_2
  · exact prime_3
  · exact prime_3
  · exact prime_23964610537191310276190549303

theorem prime_20705423504133292078628634597817 : Nat.Prime 20705423504133292078628634597817 := by
  refine Pratt.prime_of_certificate 20705423504133292078628634597817 5 105 [2, 2, 2, 3, 862725979338887169942859774909]
    (by decide) (by decide) ?_ (by decide) (by decide)
    (by unfold List.Forall; decide)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact prime_2
  · exact prime_2
  · exact prime_2
  · exact prime_3
  · exact prime_862725979338887169942859774909

theorem prime_413244619895455989650825325680172591660047 : Nat.Prime 413244619895455989650825325680172591660047 := by
  refine Pratt.prime_of_certificate 413244619895455989650825325680172591660047 5 139 [2, 17, 97, 6051631, 20705423504133292078628634597817]
    (by decide) (by decide) ?_ (by decide) (by decide)
    (by unfold List.Forall; decide)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact prime_2
  · exact prime_17
  · exact prime_97
  · exact prime_6051631
  · exact prime_20705423504133292078628634597817

theorem prime_12397338596863679689524759770405177749801411 : Nat.Prime 12397338596863679689524759770405177749801411 := by
  refine Pratt.prime_of_certificate 12397338596863679689524759770405177749801411 2 144 [2, 3, 5, 413244619895455989650825325680172591660047]
    (by decide) (by decide) ?_ (by decide) (by decide)
    (by unfold List.Forall; decide)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact prime_2
  · exact prime_3
  · exact prime_5
  · exact prime_413244619895455989650825325680172591660047

theorem prime_19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097 : Nat.Prime 19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097 := by
  refine Pratt.prime_of_certificate 19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097 3 334 [2, 2, 2, 2, 11, 11, 11, 8389, 38557, 312289, 1357291859799823621, 529709925838459440593, 12397338596863679689524759770405177749801411]
    (by decide) (by decide) ?_ (by decide) (by decide)
    (by unfold List.Forall; decide)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_2
  · exact prime_2
  · exact prime_2
  · exact prime_2
  · exact prime_11
  · exact prime_11
  · exact prime_11
  · exact prime_8389
  · exact prime_38557
  · exact prime_312289
  · exact prime_1357291859799823621
  · exact prime_529709925838459440593
  · exact prime_12397338596863679689524759770405177749801411

theorem prime_39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319 : Nat.Prime 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319 := by
  refine Pratt.prime_of_certificate 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319 19 384 [2, 19, 67, 807145746439, 19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097]
    (by decide) (by decide) ?_ (by decide) (by decide)
    (by unfold List.Forall; decide)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact prime_2
  · exact prime_19
  · exact prime_67
  · exact prime_807145746439
  · exact prime_19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097

end Certificate

theorem p_prime : p.Prime := by
  have hp : p = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319 := by decide
  rw [hp]
  exact Certificate.prime_39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319

end P384
