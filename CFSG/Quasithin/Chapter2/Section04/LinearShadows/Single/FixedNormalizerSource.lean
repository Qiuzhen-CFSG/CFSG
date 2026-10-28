module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CyclicSource
public import Theory.GroupTheory.InvolutionClosureNormalizer
public import Theory.GroupTheory.RelativeSylowNormalizer

/-!
# Promoting the original fixed-core Sylow subgroup

Strong involution closure and generation of the fixed core by its
involutions make every normalizer of C_T(s) normalize C_R(s). The local
normalizer bound then promotes the specified Sylow subgroup to C_G(s),
without replacing its ambient image by a conjugate.

The remaining generation and local normalizer premises are the marked
fixed-group rows of 2.4.12–18. The source consumer here removes the separate
normalizer-stability and Sylow-promotion premises in 2.4.23(4).
Source: Aschbacher–Smith, printed p.537.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

omit [Finite G] in
/-- Original strong involution closure controls the normalizer of the
literal fixed Thompson subgroup, once its local involution generation is known. -/
theorem source_fixed_core_normalizer
    (d : MinimalBlockSetup M) (T : Sylow 2 G) (s : G)
    (hclosed : ∀ r t : T, orderOf r = 2 →
      (r : G) ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) →
      IsConj (r : G) (t : G) →
      (t : G) ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
    (hgen : let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
      let Ts := (T : Subgroup G) ⊓ centralizer ({s} : Set G)
      closure {r : G | r ∈ R ⊓ Ts ∧ orderOf r = 2} = R ⊓ Ts) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Ts := (T : Subgroup G) ⊓ centralizer ({s} : Set G)
    normalizer (Ts : Set G) ≤ normalizer (R ⊓ Ts : Set G) := by
  apply normalizer_le_normalizer_inf_of_involution_closure _ _ _ inf_le_left ?_ hgen
  intro r t hr hrR hrT htT hrt
  exact hclosed ⟨r,hrT⟩ ⟨t,htT⟩ ((orderOf_injective (T : Subgroup G).subtype (T : Subgroup G).subtype_injective ⟨r,hrT⟩).symm.trans hr) hrR hrt

/-- The fixed-core normalizer bound promotes the literal local Sylow in
2.4.23(4) to the full involution centralizer. -/
theorem source_sylow_centralizer_of_fixed_core_normalizer
    (d : MinimalBlockSetup M) (T : Sylow 2 G) (s : G)
    (hclosed : ∀ r t : T, orderOf r = 2 →
      (r : G) ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) →
      IsConj (r : G) (t : G) →
      (t : G) ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
    (hgen : let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
      let Ts := (T : Subgroup G) ⊓ centralizer ({s} : Set G)
      closure {r : G | r ∈ R ⊓ Ts ∧ orderOf r = 2} = R ⊓ Ts)
    (W : Subgroup G) (hW : W ≤ centralizer ({s} : Set G))
    (hlocal : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({s} : Set G)) W)
    (hN : centralizer ({s} : Set G) ⊓ normalizer
      (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
        ((T : Subgroup G) ⊓ centralizer ({s} : Set G)) : Set G) ≤ W) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({s} : Set G))
      (centralizer ({s} : Set G)) := by
  exact exists_sylow_eq_of_relative_normalizer_le hlocal hW
    ((inf_le_inf_left _ (source_fixed_core_normalizer d T s hclosed hgen)).trans hN)
end CFSG.Quasithin.Chapter2.LinearShadows.Single
