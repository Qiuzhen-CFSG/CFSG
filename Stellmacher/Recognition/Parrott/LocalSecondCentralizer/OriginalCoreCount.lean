module

public import Stellmacher.Recognition.Parrott.SecondCentralizerOriginalCoreCount
public import Stellmacher.Recognition.Parrott.LocalNormalizer.Fusion
public import Stellmacher.Recognition.Parrott.LocalSecondCentralizer.OuterSelection


/-!
# The selected inverter's original-core centralizer

The intrinsic order-five commutator pairing shows that any element of J
commuting with an element outside J′ lies in one of the two derived cosets
represented by 1 and that element. For the supplied involution a this puts
the entire core centralizer in F=⟨a⟩C_{J′}(a), giving C_J(a)=F.

The existing outside-omega transport provides compatible elementary data
with a=w. Its fixed join has order 32, so |C_J(w)|=32. In particular,
further intersection with C_G(v) has order at most 32.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674, p.678 (C_J(a)=F), and §4, p.682.
-/

/-! These variants use `ParrottLocalInputs`: the derived-core normalizer
identity and solvability of the actual second elementary normalizers.
No solvability of the full second involution centralizer is assumed. -/

open Subgroup
open scoped IsMulCommutative

namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- An outside-omega involution has an original-core centralizer of order 32. -/
public theorem outside_omega_original_core_centralizer_card_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let P := (d.sylow : Subgroup G) ⊓ centralizer ({v} : Set G)
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let Y := J.map H.subtype
    ∀ w : G, w ∈ P → orderOf w = 2 → w ∉ W →
      Nat.card (Y ⊓ centralizer ({w} : Set G) : Subgroup G) = 32 := by
  intro N K W P H J Y w hw hw2 hwW
  obtain ⟨e, hew, _, _, _, _⟩ :=
    d.normalizer_fixed_outside_omega_fixed_join_of_local_inputs h hlocal hproper Q v hv hfix w hw hw2 hwW
  have he := e.original_core_centralizer_eq_fixed_join h
  change Y ⊓ centralizer ({(e.a : G)} : Set G) = e.F at he
  rw [hew] at he
  rw [he, e.card]

end Stellmacher.Recognition.ParrottSecondElementaryData
