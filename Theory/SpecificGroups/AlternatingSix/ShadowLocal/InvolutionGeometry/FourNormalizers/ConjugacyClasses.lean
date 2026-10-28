module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.FourNormalizers.Automorphisms

/-!
# The two inner conjugacy classes of four-groups in A₆

Every four-group is inner-conjugate to standardFour or secondFour. The two
representatives are not inner-conjugate. An automorphism preserves the first
class exactly when it belongs to the natural S₆ subgroup of Aut(A₆).

The proof adjusts an odd relabelling by the transposition (56), which fixes
the standard four-group. The existing exceptional class swap and the
index-two theorem then classify all four-groups. This distinguishes the
natural outer automorphisms from the exceptional outer class swaps, and is
the concrete class criterion used in the rank-two local geometry.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.567–570; compare the diagram-action branch of 13.8.21(2), p.956.
Identification of a particular source parabolic with either normalizer is
an additional local-group calculation, not an assumption in these theorems.
-/

@[expose] public section

open Subgroup GLS3.Chapter5
namespace AlternatingSix.ShadowLocal.FourNormalizers

private theorem even_adjust (σ : Equiv.Perm (Fin 6)) :
    ∃ g : A6, σ = g.val ∨ σ = g.val * tailSwap := by
  have he : σ ∈ alternatingGroup (Fin 6) ∨ σ * tailSwap ∈ alternatingGroup (Fin 6) := by
    simp only [Equiv.Perm.mem_alternatingGroup]
    revert σ
    decide +kernel
  rcases he with h | h
  · exact ⟨⟨σ, h⟩, Or.inl rfl⟩
  · refine ⟨⟨σ * tailSwap, h⟩, Or.inr ?_⟩
    change σ = (σ * tailSwap) * tailSwap
    rw [mul_assoc, show tailSwap * tailSwap = 1 by decide, mul_one]

theorem natural_iff_standard_conjugate (β : AutA6) :
    β ∈ natural ↔ ∃ g : A6,
      standardFour.map β.toMonoidHom = standardFour.map (MulAut.conj g).toMonoidHom := by
  constructor
  · rintro ⟨σ, hσ⟩
    change permutationAction σ = β at hσ
    subst β
    obtain ⟨g, h | h⟩ := even_adjust σ
    · exact ⟨g, by rw [h, permutationAction_coe]⟩
    · refine ⟨g, ?_⟩
      rw [h, map_mul, permutationAction_coe]
      change standardFour.map ((MulAut.conj g).toMonoidHom.comp
        (permutationAction tailSwap).toMonoidHom) = _
      rw [← map_map, (natural_stabilizes_standard_iff tailSwap).mpr rfl]
  · rintro ⟨g, hg⟩
    have hs : standardFour.map ((MulAut.conj g)⁻¹ * β).toMonoidHom = standardFour := by
      change standardFour.map ((MulAut.conj g).symm.toMonoidHom.comp β.toMonoidHom) = _
      rw [← map_map, hg, map_map]
      simp
    have hn := standard_stabilizer_le_natural _ hs
    have hi : MulAut.conj g ∈ natural := inner_le_natural ⟨g, rfl⟩
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using natural.mul_mem hi hn

theorem second_not_standard_conjugate :
    ¬ ∃ g : A6, secondFour = standardFour.map (MulAut.conj g).toMonoidHom := by
  intro h
  apply classSwap_not_natural
  exact (natural_iff_standard_conjugate classSwap).mpr
    (by simpa only [classSwap_standardFour] using h)

theorem natural_conjugation_iff (α β : AutA6) :
    α * β * α⁻¹ ∈ natural ↔ β ∈ natural := by
  let : natural.Normal := normal_of_index_eq_two naturalAlternatingAutomorphismSubgroup_index
  constructor
  · intro h
    have hc := Subgroup.Normal.conj_mem (inferInstance : natural.Normal) _ h α⁻¹
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_inv, inv_mul_cancel, mul_one] using hc
  · intro h
    exact Subgroup.Normal.conj_mem inferInstance _ h _

theorem four_has_two_classes (F : Subgroup A6) [IsKleinFour F] :
    (∃ g : A6, F = standardFour.map (MulAut.conj g).toMonoidHom) ∨
    (∃ g : A6, F = secondFour.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨α, rfl⟩ := exists_map_standardFour F
  by_cases ha : α ∈ natural
  · exact Or.inl ((natural_iff_standard_conjugate α).mp ha)
  · have hn : classSwap⁻¹ * α ∈ natural := by
      rw [Subgroup.mul_mem_iff_of_index_two naturalAlternatingAutomorphismSubgroup_index]
      simp only [inv_mem_iff, classSwap_not_natural, ha]
    obtain ⟨g, hg⟩ := (natural_iff_standard_conjugate (classSwap⁻¹ * α)).mp hn
    have he := congrArg (fun P : Subgroup A6 => P.map classSwap.toMonoidHom) hg
    have hid : classSwap.toMonoidHom.comp (classSwap⁻¹ * α).toMonoidHom = α.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      exact classSwap.apply_symm_apply _
    rw [map_map, hid] at he
    refine Or.inr ⟨classSwap g, he.trans ?_⟩
    rw [← classSwap_standardFour, map_map, map_map]
    apply congrArg (fun f : A6 →* A6 => standardFour.map f)
    apply MonoidHom.ext
    intro x
    change classSwap (g * x * g⁻¹) = classSwap g * classSwap x * (classSwap g)⁻¹
    simp only [map_mul, map_inv]

end AlternatingSix.ShadowLocal.FourNormalizers
