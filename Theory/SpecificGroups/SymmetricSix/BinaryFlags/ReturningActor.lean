module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.SylowGeometry
public import Theory.GroupTheory.SubgroupConjugation
/-!
# Returning transpositions in a six-letter point stabilizer

A Sylow two-subgroup of the point stabilizer contains a transposition
whose commutator with its actual alternating-four residual has order
three. Conjugate the standard Sylow inside the point stabilizer and carry
both elements through the same inner automorphism. Every transposition
can be moved to this actor by an even permutation: adjust an odd
conjugator by the starting transposition itself.

The source application uses this even conjugator to select an element
of the original component L, retaining its given Sylow subgroup and
literal first residual. No subgroup enumeration is required.
Source: Aschbacher–Smith, final proof of 13.4.1, printed p.915,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.ReturningActor
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
abbrev S := Equiv.Perm (Fin 6)

private theorem canonical_actor (P : Sylow 2 S) (hP : (P : Subgroup S) ≤ H1) :
    ∃ t ∈ (P : Subgroup S), t.IsSwap ∧ ∃ r ∈ K, orderOf ⁅r,t⁆ = 3 := by
  let P₀ := canonicalSylow.subtype (show (canonicalSylow : Subgroup S) ≤ H1 by
    rw [canonicalSylow_coe]; exact inf_le_left)
  let P₁ := P.subtype hP
  obtain ⟨b,hb⟩ := MulAction.exists_smul_eq H1 P₀ P₁
  have he : (P₀ : Subgroup H1).map (MulAut.conj b).toMonoidHom = P₁ :=
    congrArg (fun Q : Sylow 2 H1 => (Q : Subgroup H1)) hb
  have ht0 : swap01 ∈ (canonicalSylow : Subgroup S) := by
    rw [canonicalSylow_coe]
    exact ⟨D_le_H1 swap01_mem_D,D_le_H2 swap01_mem_D⟩
  let t : S := MulAut.conj b.val swap01
  have ht : t ∈ (P : Subgroup S) := by
    have ht' : (⟨swap01,D_le_H1 swap01_mem_D⟩ : H1) ∈ P₀ := ht0
    have hh := he ▸ mem_map_of_mem (MulAut.conj b).toMonoidHom ht'
    exact hh
  have hswap : t.IsSwap := by
    change (b.val * Equiv.swap 0 1 * b.val⁻¹).IsSwap
    rw [←Equiv.swap_apply_apply]
    exact ⟨_,_,b.val.injective.ne (by decide),rfl⟩
  have hKN : H1 ≤ normalizer (K : Set S) := by
    rw [←residual_H1]
    exact H1.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H1 (pResidual 2 H1))
  have hr : MulAut.conj b.val (cycle012 ^ 2) ∈ K :=
    le_normalizer_iff.mp hKN b.val b.property _ (K.pow_mem (by decide) 2)
  refine ⟨t,ht,hswap,_,hr,?_⟩
  change orderOf ⁅MulAut.conj b.val (cycle012 ^ 2),MulAut.conj b.val swap01⁆ = 3
  rw [←map_commutatorElement,(MulAut.conj b.val).orderOf_eq]
  have hc : ⁅cycle012 ^ 2,swap01⁆ = cycle012 := by decide
  rw [hc]
  exact orderOf_eq_prime (by decide : cycle012 ^ 3 = 1) (by decide)

/-- In a Sylow subgroup of a six-letter point stabilizer, an actual
transposition has a commutator of order three with its A4 residual. -/
theorem conjugate_point_actor (P : Sylow 2 S) (a : S)
    (hP : (P : Subgroup S) ≤ H1.conjBy a) :
    ∃ t ∈ (P : Subgroup S), t.IsSwap ∧
      ∃ r ∈ K.conjBy a, orderOf ⁅r,t⁆ = 3 := by
  let f := (MulAut.conj a⁻¹).toMonoidHom
  let Q := P.mapSurjective (f := f) (MulAut.conj a⁻¹).surjective
  have hQ : (Q : Subgroup S) ≤ H1 := by
    have hh := map_mono (f := f) hP
    change (Q : Subgroup S) ≤ (H1.conjBy a).conjBy a⁻¹ at hh
    rwa [conjBy_inv] at hh
  obtain ⟨t,ht,hts,r,hr,ho⟩ := canonical_actor Q hQ
  refine ⟨MulAut.conj a t,?_,?_,MulAut.conj a r,mem_map_of_mem _ hr,?_⟩
  · have hh := mem_map_of_mem (MulAut.conj a).toMonoidHom ht
    change MulAut.conj a t ∈ ((P : Subgroup S).conjBy a⁻¹).conjBy a at hh
    rwa [conjBy_inv'] at hh
  · obtain ⟨i,j,hij,rfl⟩ := hts
    change (a * Equiv.swap i j * a⁻¹).IsSwap
    rw [←Equiv.swap_apply_apply]
    exact ⟨_,_,a.injective.ne hij,rfl⟩
  · rw [←map_commutatorElement,(MulAut.conj a).orderOf_eq]
    exact ho

/-- The actor can be reached from any given transposition by an even
permutation, retaining the prescribed Sylow subgroup and point residual. -/
theorem even_conjugate_point_actor (P : Sylow 2 S) (a t₀ : S)
    (hP : (P : Subgroup S) ≤ H1.conjBy a) (ht₀ : t₀.IsSwap) :
    ∃ b : alternatingGroup (Fin 6),
      MulAut.conj b.val t₀ ∈ (P : Subgroup S) ∧
      ∃ r ∈ K.conjBy a, orderOf ⁅r,MulAut.conj b.val t₀⁆ = 3 := by
  obtain ⟨t,ht,hts,r,hr,ho⟩ := conjugate_point_actor P a hP
  have hc : IsConj t₀ t := Equiv.Perm.isConj_of_cycleType_eq
    ((Equiv.Perm.isSwap_iff_cycleType.mp ht₀).trans
      (Equiv.Perm.isSwap_iff_cycleType.mp hts).symm)
  obtain ⟨c,hc⟩ := isConj_iff.mp hc
  have hb : ∃ b : alternatingGroup (Fin 6), MulAut.conj b.val t₀ = t := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign c) with he | he
    · exact ⟨⟨c,he⟩,hc⟩
    · have heven : c * t₀ ∈ alternatingGroup (Fin 6) := by
        rw [Equiv.Perm.mem_alternatingGroup,map_mul,he,ht₀.sign_eq]
        decide
      refine ⟨⟨c*t₀,heven⟩,?_⟩
      change (c*t₀)*t₀*(c*t₀)⁻¹=t
      rw [←hc]
      group
  obtain ⟨b,hb⟩ := hb
  exact ⟨b,hb.symm ▸ ht,r,hr,hb.symm ▸ ho⟩
end Theory.SpecificGroups.SymmetricSix.BinaryFlags.ReturningActor
