module
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.SixPoint.Normalizer.Quotient
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.SixPoint.Normalizer.SextetSeed
public import Theory.GroupTheory.SylowKernelCore

/-!
# Transport of sextet complements by native Mathieu conjugation

Translation of every tetrad by an element of native M24 preserves all sextet
axioms, including the literal octad unions. Stabilizers, intrinsic two-cores,
and normalizers then transport by the same conjugation homomorphism.

Consequently a standard-sextet complement for any native cubic fixing six
points gives a sextet complement for the designated representative. The
existing cubic-conjugacy theorem supplies the actual native conjugator.

Source: Aschbacher–Smith H.15.7(1), printed pp.401–402. This is the geometric
transport step; its complement hypotheses are discharged by the affine
calculation and the separately owned native two-core comparison.
-/

@[expose] public section
namespace MathieuCode.SixPoint.SextetComplement
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise
noncomputable section

/-- Translate all the tetrads of a genuine sextet by a native Mathieu permutation. -/
def translateSextet (g : M24) (S : Sextet) : Sextet where
  parts := g • S.parts
  card := by rw [Finset.card_smul_finset, S.card]
  tetrad A hA := by
    obtain ⟨B,hB,rfl⟩ := Finset.mem_smul_finset.mp hA
    rw [Finset.card_smul_finset, S.tetrad B hB]
  disjoint A hA B hB hne := by
    obtain ⟨C,hC,rfl⟩ := Finset.mem_smul_finset.mp hA
    obtain ⟨D,hD,rfl⟩ := Finset.mem_smul_finset.mp hB
    have hd := S.disjoint C hC D hD (fun h => hne (congrArg (g • ·) h))
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Finset.disjoint_left.mp hd
      ((Finset.inv_smul_mem_iff).mpr hx) ((Finset.inv_smul_mem_iff).mpr hy)
  cover := by
    apply Finset.eq_univ_of_forall
    intro x
    have hx : g⁻¹ • x ∈ S.parts.biUnion id := by rw [S.cover]; exact Finset.mem_univ _
    obtain ⟨A,hA,hx⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨g • A, Finset.smul_mem_smul_finset hA,
      Finset.inv_smul_mem_iff.mp hx⟩
  octad A hA B hB hne := by
    obtain ⟨C,hC,rfl⟩ := Finset.mem_smul_finset.mp hA
    obtain ⟨D,hD,rfl⟩ := Finset.mem_smul_finset.mp hB
    rw [← Finset.smul_finset_union]
    have h := S.octad C hC D hD (fun h => hne (congrArg (g • ·) h))
    change g.val • (C ∪ D) ∈ (m24Blocks : Set (Finset (Fin 24)))
    rw [← (mem_M24_iff _).mp g.property]
    exact Set.smul_mem_smul_set h

theorem translateSextet_stabilizer (g : M24) (S : Sextet) :
    sextetStabilizer (translateSextet g S) =
      (sextetStabilizer S).map (MulAut.conj g).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj g S.parts

/-- Transport a proved standard-sextet complement to the designated cubic representative. -/
theorem representative_complement_of_standard (D : Subgroup M24)
    (hD : Nat.card D = 3) (hfix : Nat.card (FixedPoint D) = 6)
    (hN : Subgroup.normalizer (D : Set M24) ≤ sextetStabilizer standardSextet)
    (hinf : (sextetStabilizer standardSextet).pCoreIn 2 ⊓
      Subgroup.normalizer (D : Set M24) = ⊥)
    (hsup : (sextetStabilizer standardSextet).pCoreIn 2 ⊔
      Subgroup.normalizer (D : Set M24) = sextetStabilizer standardSextet) :
    ∃ S : Sextet,
      let N := Subgroup.normalizer (cubicSubgroup : Set M24)
      let H := sextetStabilizer S
      let K := (pCore 2 H).map H.subtype
      N ≤ H ∧ K ⊓ N = ⊥ ∧ K ⊔ N = H ∧
        ∃ g : M24, g.val • S.parts = standardSextet.parts := by
  obtain ⟨g, hg⟩ := cubicSubgroup_conjugacy D hD hfix
  refine ⟨translateSextet g standardSextet, ?_⟩
  dsimp only
  have hn := D.map_equiv_normalizer_eq (MulAut.conj g)
  rw [hg] at hn
  have hk := Subgroup.map_pCoreIn_of_injective 2
    (sextetStabilizer standardSextet) (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  rw [← translateSextet_stabilizer] at hk
  change _ ≤ _ ∧ (sextetStabilizer _).pCoreIn 2 ⊓ _ = ⊥ ∧
    (sextetStabilizer _).pCoreIn 2 ⊔ _ = _ ∧ _
  rw [← hk, ← hn, ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    hinf, Subgroup.map_bot, ← Subgroup.map_sup, hsup, translateSextet_stabilizer]
  refine ⟨Subgroup.map_mono hN, rfl, rfl, g⁻¹, ?_⟩
  change g⁻¹ • (g • standardSextet.parts) = standardSextet.parts
  exact inv_smul_smul g _

end
end MathieuCode.SixPoint.SextetComplement
