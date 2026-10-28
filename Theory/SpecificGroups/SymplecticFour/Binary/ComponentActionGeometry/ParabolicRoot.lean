module

public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.SymplecticFour.RootSubgroup
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
public import Theory.SpecificGroups.AlternatingSix.OuterInvolutionExtension.NaturalCoordinates

/-!
# A literal root action fixing a binary maximal parabolic

Let D = Sp₄(2)′. An order-two subgroup of Aut(D) induced by the full
matrix group and fixing a maximal Sylow-two overgroup pointwise is conjugate,
by an automorphism of D, to the action of one of the eight matrix root groups.

The polar equivalence identifies D with the actual six-point A₆. Its maximal
Sylow overgroups have order 24, whereas an inner involution fixes a subgroup
of order eight. The acting involution is therefore a natural outer involution.
The exceptional A₆ automorphism and permutation conjugacy take either such
class to (3 5). The duad-vector table proves that the polar image of this
transposition is exactly root 0 at parameter 1. Over the binary field that element
generates the entire root subgroup. All finite identities use kernel reduction.

Conjugating matrices stay in full Sp₄(2); the carrier acted on throughout is
its commutator subgroup. No classification assumptions enter the argument.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, E.6.8(2b), printed pp.247–248; the polar model from
I.5, printed pp.419–422.
-/

public section

open Subgroup Matrix GLS3.Chapter5 AlternatingSix.ShadowLocal
open Theory.SpecificGroups.SymmetricSix hiding A6
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.Binary
open Representation.OneCohomology.SymplecticFour

namespace Theory.SpecificGroups.SymplecticFour.Binary.ComponentActionGeometry

set_option maxRecDepth 10000

private def rootDuad (d : Duad) : Duad :=
  ![0, 1, 4, 3, 2, 5, 8, 7, 6, 11, 10, 9, 14, 13, 12] d

private theorem rootDuad_smul (d : Duad) :
    (Equiv.swap (3 : Fin 6) 5) • d = rootDuad d := by
  apply duadSet_injective
  rw [duadSet_smul]
  revert d
  decide +kernel

/-- The long root is the transposition (3 5) in the given polar table. -/
private theorem root_zero_polar : polarRepresentation (Equiv.swap (3 : Fin 6) 5) =
    rootElement (K := ZMod 2) 0 1 := by
  apply Subtype.ext
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  by_cases hv : v = 0
  · simp [hv]
  obtain ⟨d, hd⟩ := polarVector_bijective.2 ⟨v, hv⟩
  have he : (polarVector d).val = v := congrArg Subtype.val hd
  rw [← he, polarRepresentation_equivariant, rootDuad_smul]
  change (polarVector (rootDuad d)).val = rootMatrix (K := ZMod 2) 0 1 *ᵥ (polarVector d).val
  clear hd he hv v
  revert d
  decide +kernel

/-- Restrict the actual polar equivalence to the commutator carrier. -/
private noncomputable def derivedPolarEquiv : commutator (Sp (ZMod 2)) ≃* A6 := by
  refine (symmetricSixEquiv.symm.subgroupMap _).trans (MulEquiv.subgroupCongr ?_)
  rw [map_commutator_eq,
    MonoidHom.range_eq_top.mpr symmetricSixEquiv.symm.surjective]
  exact alternatingGroup.commutator_perm_eq (by norm_num)

private theorem derivedPolarEquiv_coe (x : commutator (Sp (ZMod 2))) :
    (derivedPolarEquiv x : Equiv.Perm (Fin 6)) = symmetricSixEquiv.symm x := rfl

private theorem polar_conjugation (g : Sp (ZMod 2)) :
    MulAut.congr derivedPolarEquiv (MulAut.conjNormal g) =
      permutationAction (symmetricSixEquiv.symm g) := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change (derivedPolarEquiv (MulAut.conjNormal g (derivedPolarEquiv.symm x)) :
    Equiv.Perm (Fin 6)) = _
  rw [derivedPolarEquiv_coe, MulAut.conjNormal_apply, map_mul, map_mul, map_inv]
  rw [← derivedPolarEquiv_coe, derivedPolarEquiv.apply_symm_apply]
  rfl

private theorem parabolic_card (P : Subgroup A6) (hc : IsCoatom P) (S : Sylow 2 A6)
    (hSP : (S : Subgroup A6) ≤ P) : Nat.card P = 24 := by
  obtain ⟨g, _, hg⟩ := a6_coatoms_over_sylow S
  rcases (hg P).mp ⟨hc, hSP⟩ with h | h
  · rw [h]
    change Nat.card (a6DuadStabilizer.map (MulAut.conj g).toMonoidHom) = 24
    rw [card_map_of_injective (MulAut.conj g).injective, a6DuadStabilizer_order]
  · rw [h]
    change Nat.card (a6SynthemeStabilizer.map (MulAut.conj g).toMonoidHom) = 24
    rw [card_map_of_injective (MulAut.conj g).injective, a6SynthemeStabilizer_order]

/-- Order 24 excludes the inner fixed subgroup of order eight. The
exceptional A₆ automorphism then handles either odd involution class. -/
private theorem natural_coatom_coordinates (β : AutA6)
    (hβ : β ^ 2 = 1) (hne : β ≠ 1) (hn : β ∈ natural)
    (P : Subgroup A6) (hP : IsCoatom P) (S : Sylow 2 A6)
    (hSP : (S : Subgroup A6) ≤ P)
    (hfix : ∀ x ∈ P, β x = x) :
    ∃ k : MulAut A6, MulAut.congr k β = permutationAction (Equiv.swap 3 5) := by
  have hout : β ∉ AlternatingSix.ShadowLocal.inner := by
    rintro ⟨a, ha⟩
    have ho : orderOf a = 2 := by
      have hh := orderOf_eq_prime hβ hne
      rw [← ha, orderOf_injective _ inner_injective] at hh
      exact hh
    have hd := card_dvd_of_le (show P ≤ automorphismFixedSubgroup β from hfix)
    rw [parabolic_card P hP S hSP, ← ha, inner_involution_fixed_card a ho] at hd
    norm_num at hd
  obtain ⟨c, s, hs, hcs⟩ :=
    AlternatingSix.OuterInvolutionExtension.natural_involution_transposition_coordinates
      β hβ hn hout
  have hc : IsConj s (Equiv.swap (3 : Fin 6) 5) :=
    Equiv.Perm.isConj_of_cycleType_eq ((Equiv.Perm.isSwap_iff_cycleType.mp hs).trans
      (show (Equiv.swap (3 : Fin 6) 5).cycleType = {2} by decide +kernel).symm)
  obtain ⟨p, hp⟩ := isConj_iff.mp hc
  refine ⟨c.trans (permutationAction p), ?_⟩
  change MulAut.congr (permutationAction p) (MulAut.congr c β) = _
  rw [hcs]
  change permutationAction p * permutationAction s * (permutationAction p)⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul, hp]

private theorem two_generator {X : Type*} [Group X] (J : Subgroup X)
    (hJ : Nat.card J = 2) :
    ∃ a : X, a ∈ J ∧ a ≠ 1 ∧ a ^ 2 = 1 ∧ J = zpowers a := by
  obtain ⟨a, ha, hu⟩ := (Nat.card_eq_two_iff' (1 : J)).mp hJ
  have han : (a : X) ≠ 1 := by
    intro he
    exact ha (Subtype.ext he)
  refine ⟨a, a.property, han, ?_, ?_⟩
  · have hp : a ^ 2 = 1 := hJ ▸ pow_card_eq_one'
    exact congrArg Subtype.val hp
  · apply le_antisymm
    · intro x hx
      by_cases hx1 : x = 1
      · rw [hx1]
        exact one_mem _
      · have he : (⟨x, hx⟩ : J) = a := hu _ (fun h => hx1 (congrArg Subtype.val h))
        rw [show x = a.val from congrArg Subtype.val he]
        exact mem_zpowers _
    · exact zpowers_le.mpr a.property

private theorem root_group_zpowers (r : Fin 8) :
    closure (Set.range (rootElement (K := ZMod 2) r)) =
      zpowers (rootElement r 1) := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨t, rfl⟩
    have ht : t = 0 ∨ t = 1 :=
      (show ∀ u : ZMod 2, u = 0 ∨ u = 1 by decide +kernel) t
    rcases ht with rfl | rfl
    · rw [RootSubgroup.element_zero]
      exact one_mem _
    · exact mem_zpowers _
  · exact zpowers_le.mpr (subset_closure ⟨1, rfl⟩)

local notation "D" => commutator (Sp (ZMod 2))

/-- An order-two action induced by full Sp₄(2), fixing a maximal Sylow
overgroup pointwise, is conjugate to an actual matrix root action on Sp₄(2)′. -/
theorem parabolic_action_is_root (J : Subgroup (MulAut D)) (hJ : Nat.card J = 2)
    (hn : J ≤ (MulAut.conjNormal (H := D)).range)
    (P : Subgroup D) (hP : IsCoatom P)
    (S : Sylow 2 D) (hSP : (S : Subgroup D) ≤ P)
    (hfix : ∀ a ∈ J, ∀ x ∈ P, a x = x) :
    ∃ f : MulAut D, ∃ r : Fin 8,
      J.map (MulAut.congr f).toMonoidHom =
        (closure (Set.range (rootElement (K := ZMod 2) r))).map
          (MulAut.conjNormal (H := D)) := by
  obtain ⟨a, ha, hane, ha2, hgen⟩ := two_generator J hJ
  let β := MulAut.congr derivedPolarEquiv a
  let Q := P.map derivedPolarEquiv.toMonoidHom
  let T := S.mapSurjective (f := derivedPolarEquiv.toMonoidHom) derivedPolarEquiv.surjective
  have hβ : β ^ 2 = 1 := by rw [← map_pow, ha2, map_one]
  have hβne : β ≠ 1 := by
    intro hh
    exact hane ((MulAut.congr derivedPolarEquiv).injective (hh.trans (map_one _).symm))
  have hβn : β ∈ natural := by
    obtain ⟨g, hg⟩ := hn ha
    refine ⟨symmetricSixEquiv.symm g, ?_⟩
    exact (polar_conjugation g).symm.trans (congrArg (MulAut.congr derivedPolarEquiv) hg)
  have hQ : IsCoatom Q := (derivedPolarEquiv.mapSubgroup.isCoatom_iff P).mpr hP
  have hTQ : (T : Subgroup A6) ≤ Q := map_mono hSP
  have hfixQ : ∀ x ∈ Q, β x = x := by
    rintro _ ⟨x, hx, rfl⟩
    change derivedPolarEquiv (a (derivedPolarEquiv.symm (derivedPolarEquiv x))) =
      derivedPolarEquiv x
    rw [derivedPolarEquiv.symm_apply_apply, hfix a ha x hx]
  obtain ⟨k, hk⟩ := natural_coatom_coordinates β hβ hβne hβn Q hQ T hTQ hfixQ
  let f := (MulAut.congr derivedPolarEquiv).symm k
  have hfa : MulAut.congr f a = MulAut.conjNormal (rootElement (K := ZMod 2) 0 1) := by
    apply (MulAut.congr derivedPolarEquiv).injective
    rw [polar_conjugation, ← root_zero_polar, ← symmetricSixEquiv_apply,
      symmetricSixEquiv.symm_apply_apply]
    change MulAut.congr derivedPolarEquiv (f * a * f⁻¹) = _
    rw [map_mul, map_mul, map_inv]
    have hf : MulAut.congr derivedPolarEquiv f = k :=
      (MulAut.congr derivedPolarEquiv).apply_symm_apply k
    rw [hf]
    exact hk
  refine ⟨f, 0, ?_⟩
  rw [hgen, MonoidHom.map_zpowers, root_group_zpowers, MonoidHom.map_zpowers]
  exact congrArg zpowers hfa

end Theory.SpecificGroups.SymplecticFour.Binary.ComponentActionGeometry
