module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Core
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Section
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.Lift
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.NoEight
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.Quotient
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.Kernel
/-!
# The proper faithful extension in Held's PSL2(7) exclusion

The fixed local involution mu' is outside the canonical derived lift A:
its commutator with lambda is mu, whereas injectivity of the derived map
excludes mu from A. Thus X = A<mu'> is a proper extension. Its elements
inherit the absence of order eight from C. The imported kernel argument
proves that X acts faithfully on A once the normalized actors are supplied.
The A6 alternative transports directly through the bijective derived map.

The construction of the actors and the PSL2(7) automorphism obstruction
remain separate obligations. This module does not yet assert the requested
unconditional A6 identification from the two core premises.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 4.2, pp.234--235.
-/

open Subgroup
noncomputable section
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
namespace FaithfulExclusion
universe u
variable {G : Type u} [Group G] {D : LocalData G}
  {e : D.centralizer ≃* CentralizerModels.a10Centralizer}
  (c : QuotientCore D e)

public theorem muPrime_not_mem_derivedLift
    (hinj : Function.Injective c.derivedMap) : muPrime D e ∉ c.derivedLift := by
  intro hm
  let f := D.a10ModelEmbedding e
  let l : C D e := ⟨f NoncentralAnalysis.Coordinates.lam,
    mem_centralizer_singleton_iff.mpr (by
      change f NoncentralAnalysis.Coordinates.lam * f NoncentralAnalysis.Coordinates.mu =
        f NoncentralAnalysis.Coordinates.mu * f NoncentralAnalysis.Coordinates.lam
      rw [← map_mul, ← map_mul]
      congr 1
      decide +kernel)⟩
  have hcomm := c.derivedLift.mul_mem
    (c.derivedLift_normal.conj_mem _ hm l) (c.derivedLift.inv_mem hm)
  have he : l * muPrime D e * l⁻¹ * (muPrime D e)⁻¹ = mu D e := by
    apply Subtype.ext
    change f NoncentralAnalysis.Coordinates.lam * f NoncentralAnalysis.Coordinates.mup *
      (f NoncentralAnalysis.Coordinates.lam)⁻¹ * (f NoncentralAnalysis.Coordinates.mup)⁻¹ =
      f NoncentralAnalysis.Coordinates.mu
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    decide +kernel
  exact c.mu_not_mem_derivedLift hinj (he ▸ hcomm)

public theorem extensionCore_ne_top
    (hinj : Function.Injective c.derivedMap) : extensionCore c ≠ ⊤ := by
  intro htop
  have hm : muPrime D e ∈ extension c := mem_sup_right (mem_zpowers _)
  have hmem : (⟨muPrime D e, hm⟩ : extension c) ∈ extensionCore c := by
    rw [htop]
    trivial
  exact muPrime_not_mem_derivedLift c hinj hmem

public theorem extension_no_order_eight [Finite G]
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e)) (x : extension c) :
    orderOf x ≠ 8 := by
  rw [Subgroup.orderOf_mk]
  exact no_order_eight D e hfusion x.1

/-- The alternating branch of the supplied quotient-core alternatives. -/
public theorem derivedLift_alternating_of_subgroup_alternating
    (hbij : Function.Bijective c.derivedMap)
    (hA : Nonempty (c.subgroup ≃* alternatingGroup (Fin 6))) :
    Nonempty (c.derivedLift ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨eA⟩ := hA
  exact ⟨(MulEquiv.ofBijective c.derivedMap hbij).trans eA⟩

end FaithfulExclusion
end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
