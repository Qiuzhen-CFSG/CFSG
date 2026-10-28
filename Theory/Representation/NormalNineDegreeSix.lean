module
public import Theory.GroupAction.OddInvariantWeight
public import Theory.Representation.ElementaryNineFixedDecomposition
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.Representation.BinaryOddDisplacement.PrimeDivisibility
public import Theory.Representation.NormalInvariants
import Mathlib.Tactic

/-!
# A normal cubic from an elementary nine-group in degree six

The four cubic fixed spaces decompose the module and have even dimensions.
Their half-dimensions sum to three. A Sylow two-subgroup therefore fixes a
cubic line by the odd invariant-weight argument. The four-point action then
has a globally fixed cubic line, giving an ambient-normal cubic subgroup.

This avoids recognizing the full linear normalizer in the elementary-nine
branch of Aschbacher--Smith G.9.4, printed p.355.
-/

public section
open Subgroup Module Representation Representation.BinaryOffender
open scoped BigOperators
namespace Representation.NormalNineDegreeSix
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

@[instance_reducible] private def cubicAction (P : Subgroup G) [P.Normal]
    (S : Subgroup G) : MulAction S {L : Subgroup P // Nat.card L = 3} where
  smul g L := ⟨L.val.map ((MulAut.conjNormal (g : G) : MulAut P)).toMonoidHom,
    (card_map_of_injective (MulAut.conjNormal (g : G) : MulAut P).injective).trans L.property⟩
  one_smul L := by
    apply Subtype.ext
    change L.val.map ((MulAut.conjNormal (1 : G) : MulAut P)).toMonoidHom = L.val
    rw [show (MulAut.conjNormal (1 : G) : MulAut P).toMonoidHom = MonoidHom.id P from
      MonoidHom.ext (fun x => by simp),map_id]
  mul_smul d e L := by
    apply Subtype.ext
    change L.val.map ((MulAut.conjNormal ((d : G) * (e : G)) : MulAut P)).toMonoidHom =
      (L.val.map ((MulAut.conjNormal (e : G) : MulAut P)).toMonoidHom).map
        ((MulAut.conjNormal (d : G) : MulAut P)).toMonoidHom
    rw [map_map]
    congr 1
    ext x
    simp [map_mul,MulAut.mul_apply]

/-- A fixed-point-free normal elementary nine-group in binary degree six
contains an ambient-normal cubic subgroup. -/
theorem exists_normal_cubic (ρ : Representation (ZMod 2) G V)
    (P : Subgroup G) [P.Normal] [IsElementaryAbelian 3 P]
    (hP : Nat.card P = 9) (hd : finrank (ZMod 2) V = 6)
    (hfixed : fixedSpace ρ P = ⊥) :
    ∃ C : Subgroup G, C ≤ P ∧ C.Normal ∧ Nat.card C = 3 := by
  classical
  let σ := ρ.comp P.subtype
  let I := {L : Subgroup P // Nat.card L = 3}
  let : Fintype I := Fintype.ofFinite I
  let S : Sylow 2 G := Classical.choice inferInstance
  let := cubicAction P (S : Subgroup G)
  let d : I → ℕ := fun L => finrank (ZMod 2) (fixedSpace σ L.val)
  let w : I → ℕ := fun L => d L / 2
  have h2 (L : I) : 2 ∣ d L := by
    have hp : IsPGroup 3 L.val := IsPGroup.of_card (n := 1) (by simpa using L.property)
    have hc := orderOf_two_dvd_fixedCodim_of_isPGroup σ Nat.prime_three (by decide) L.val hp
    have he := fixedCodim_add_finrank σ L.val
    have ho : orderOf (2 : ZMod 3) = 2 := orderOf_eq_prime (by decide) (by decide)
    rw [ho] at hc
    change fixedCodim σ L.val + d L = _ at he
    rw [hd] at he
    omega
  have hsum : ∑ L : I, d L = 6 := by
    have hf : fixedSpace σ ⊤ = ⊥ := by
      rw [fixedSpace_comp_map, ← MonoidHom.range_eq_map, P.range_subtype]
      exact hfixed
    exact (ElementaryNineFixedDecomposition.sum_fixed_finrank_eq σ hP hf).trans hd
  have hsumw : ∑ L : I, w L = 3 := by
    have he : 2 * (∑ L : I, w L) = 6 := by
      rw [Finset.mul_sum, ←hsum]
      apply Finset.sum_congr rfl
      intro L _
      exact Nat.mul_div_cancel' (h2 L)
    omega
  have hw : ∀ (g : S) (L : I), w (g • L) = w L := by
    intro g L
    have hm : (L.val.map ((MulAut.conjNormal (g : G) : MulAut P)).toMonoidHom).map P.subtype =
        (L.val.map P.subtype).map (MulAut.conj (g : G)).toMonoidHom := by
      rw [map_map,map_map]
      congr 1
    have he := (fixedSpaceConjEquiv ρ (L.val.map P.subtype) (g : G)).finrank_eq
    have hde : d (g • L) = d L := by
      change finrank (ZMod 2) (fixedSpace σ
        (L.val.map ((MulAut.conjNormal (g : G) : MulAut P)).toMonoidHom)) = _
      rw [fixedSpace_comp_map,hm]
      change _ = finrank (ZMod 2) (fixedSpace σ L.val)
      rw [fixedSpace_comp_map]
      exact he.symm
    exact congrArg (fun n => n / 2) hde
  obtain ⟨L,hL⟩ := MulAction.exists_fixed_of_odd_weight S.isPGroup' w hw
    (by rw [hsumw]; decide)
  let B := L.val.map P.subtype
  have hB : Nat.card B = 3 :=
    (card_map_of_injective P.subtype_injective).trans L.property
  have hSB : (S : Subgroup G) ≤ normalizer (B : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    have he := congrArg (fun L : I => L.val.map P.subtype) (hL ⟨g,hg⟩)
    change (L.val.map ((MulAut.conjNormal g : MulAut P)).toMonoidHom).map P.subtype = _ at he
    have hm : P.subtype.comp (MulAut.conjNormal g : MulAut P).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp P.subtype := by ext x; rfl
    rw [map_map,hm,←map_map] at he
    exact he
  exact exists_normal_cubic_le_of_sylow_invariant P (Or.inr hP) S B
    (map_subtype_le _) hB hSB

/-- In a faithful irreducible action the common fixed space is automatically zero. -/
theorem exists_normal_cubic_of_irreducible
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    [Representation.IsIrreducible ρ]
    (P : Subgroup G) [P.Normal] [IsElementaryAbelian 3 P]
    (hP : Nat.card P = 9) (hd : finrank (ZMod 2) V = 6) :
    ∃ C : Subgroup G, C ≤ P ∧ C.Normal ∧ Nat.card C = 3 := by
  apply exists_normal_cubic ρ P hP hd
  by_contra hn
  have hk := le_ker_of_normal_invariants_ne_bot ρ P hn
  have hb : P = ⊥ := bot_unique (hk.trans_eq ((MonoidHom.ker_eq_bot_iff ρ).mpr hf))
  simp [hb] at hP

end Representation.NormalNineDegreeSix
