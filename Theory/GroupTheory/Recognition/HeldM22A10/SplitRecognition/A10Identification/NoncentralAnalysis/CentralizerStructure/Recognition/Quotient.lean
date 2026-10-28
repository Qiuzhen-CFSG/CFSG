module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Core
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Section
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.Lift

/-!
# The dihedral quotient after splitting the lifted core

Let A be the image in C of the derived subgroup of the inverse image of M.
If the actual map A → M is bijective, A has index eight in C and avoids mu.
The local involutions mu' and lambda define a homomorphism D8 → C whose
central involution maps to mu. Every nontrivial normal subgroup of D8
contains that involution. Consequently D8 embeds into C/A; the index
calculation makes this an isomorphism.

This argument uses the fixed concrete local coordinates. It does not require
the source's later lambda/xi normalizations or generator-action clauses.
The final section lemma is conditional on both the splitting and an actual
A6 equivalence. Neither of those outstanding recognition inputs is asserted
here. In particular C/<mu> remains distinct from C/A throughout.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, proof of Lemma 4.2, pp.234--235.
-/

open Subgroup
noncomputable section
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
universe u

private def localDihedral : DihedralGroup 4 →* NoncentralAnalysis.Coordinates.H where
  toFun d := match d with
    | .r i => (NoncentralAnalysis.Coordinates.lam * NoncentralAnalysis.Coordinates.mup) ^ i.val
    | .sr i => NoncentralAnalysis.Coordinates.mup *
        (NoncentralAnalysis.Coordinates.lam * NoncentralAnalysis.Coordinates.mup) ^ i.val
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

private theorem localDihedral_centralizes : ∀ d,
    localDihedral d * NoncentralAnalysis.Coordinates.mu =
      NoncentralAnalysis.Coordinates.mu * localDihedral d := by
  decide +kernel

private theorem localDihedral_central : localDihedral (.r 2) =
    NoncentralAnalysis.Coordinates.mu := by decide +kernel

private theorem dihedral_four_injective {B : Type*} [Group B]
    (f : DihedralGroup 4 →* B) (h : f (.r 2) ≠ 1) : Function.Injective f := by
  have hcases : ∀ d : DihedralGroup 4, d = 1 ∨ d = .r 2 ∨
      d * d = .r 2 ∨ (.r 1 * d * (.r 1)⁻¹) * d⁻¹ = .r 2 := by decide +kernel
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply eq_bot_iff.mpr
  intro d hd
  have hfd : f d = 1 := hd
  rcases hcases d with h1 | h2 | hsq | hcomm
  · exact h1
  · exact (h (h2 ▸ hfd)).elim
  · apply False.elim
    apply h
    rw [← hsq, map_mul, hfd, one_mul]
  · apply False.elim
    apply h
    rw [← hcomm, map_mul, map_mul, map_mul, map_inv, map_inv, hfd]
    simp

variable {G : Type u} [Group G] {D : LocalData G}
  {e : D.centralizer ≃* CentralizerModels.a10Centralizer}

private def ambientDihedral (D : LocalData G)
    (e : D.centralizer ≃* CentralizerModels.a10Centralizer) :
    DihedralGroup 4 →* C D e where
  toFun d := ⟨D.a10ModelEmbedding e (localDihedral d),
    mem_centralizer_singleton_iff.mpr (by
      simpa only [map_mul, LocalData.a10NoncentralInvolution,
        NoncentralAnalysis.Coordinates.mu] using
        congrArg (D.a10ModelEmbedding e) (localDihedral_centralizes d))⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

private theorem ambientDihedral_central : ambientDihedral D e (.r 2) = mu D e := by
  apply Subtype.ext
  change D.a10ModelEmbedding e (localDihedral (.r 2)) = D.a10NoncentralInvolution e
  rw [localDihedral_central]
  rfl

namespace QuotientCore
variable (c : QuotientCore D e)

public theorem mu_not_mem_derivedLift
    (hinj : Function.Injective c.derivedMap) : mu D e ∉ c.derivedLift := by
  intro hmu
  have hbot : mu D e ∈ (⊥ : Subgroup (C D e)) := by
    rw [← c.Z_inf_derivedLift_eq_bot_of_injective hinj]
    exact ⟨mem_zpowers _, hmu⟩
  have horder := mu_order D e
  rw [show mu D e = 1 from hbot, orderOf_one] at horder
  contradiction

/-- Splitting the lifted core determines the actual final quotient. -/
public theorem quotient_dihedral [Finite G]
    (hbij : Function.Bijective c.derivedMap) :
    Nonempty ((C D e ⧸ c.derivedLift) ≃* DihedralGroup 4) := by
  let f := (QuotientGroup.mk' c.derivedLift).comp (ambientDihedral D e)
  have hf : Function.Injective f := by
    apply dihedral_four_injective
    change QuotientGroup.mk' c.derivedLift (ambientDihedral D e (.r 2)) ≠ 1
    rw [ambientDihedral_central]
    exact fun h => c.mu_not_mem_derivedLift hbij.1 ((QuotientGroup.eq_one_iff _).mp h)
  have hcard : Nat.card (C D e ⧸ c.derivedLift) = 8 := c.derivedLift_index hbij
  have hbijf : Function.Bijective f := hf.bijective_of_nat_card_le (by
    rw [hcard, DihedralGroup.nat_card])
  exact ⟨(MulEquiv.ofBijective f hbijf).symm⟩

/-- Conditional assembly; recognition and splitting remain separate obligations. -/
public theorem alternatingSixSection_of_derivedMap [Finite G]
    (hbij : Function.Bijective c.derivedMap)
    (hA : Nonempty (c.derivedLift ≃* alternatingGroup (Fin 6))) :
    Nonempty (AlternatingSixSection (C D e)) := by
  obtain ⟨eA⟩ := hA
  obtain ⟨eQ⟩ := c.quotient_dihedral hbij
  exact ⟨⟨c.derivedLift, c.derivedLift_normal, eA, eQ⟩⟩

end QuotientCore
end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
