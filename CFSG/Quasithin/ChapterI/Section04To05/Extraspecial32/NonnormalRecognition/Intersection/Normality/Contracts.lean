module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Intersection.Normality.Centralizer

/-!+# The remaining actor in the nonnormal-quaternion intersection argument

Source 2.4 arranges the fusion witness by H-conjugacy so that an involution
in the second core inverts the chosen Sylow three-subgroup. In the
nonnormal-quaternion case this involution interchanges the two intrinsic
quaternion factors. The structure below records that construction, including
the actual ambient membership and the generation of H. Its existence is a
remaining theorem, not part of the original hypotheses.

For any such actor, the checked intersection lemmas prove that it normalizes
the arranged eight, and ambient self-centralization proves that its action
there is nontrivial. The remaining intrinsic quaternion argument must show
that this eight is invariant under the cubic subgroup as well.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), Lemmas 2.2–2.4 and 2.6(1), pp.33–35.
-/

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition

open Subgroup

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The genuine arranged inverter needed by source 2.6. This records no
normality conclusion for the intersection. -/
public structure ArrangedSwapWitness (h : Hypotheses z) (g : G) where
  a : Centralizer z
  u : Centralizer z
  factors : QuaternionCentralProductData (Core z)
  square : u ^ 2 = 1
  outside : (u : G) ∉ coreInG z
  in_conjugate_core : (u : G) ∈
    (coreInG z).map (MulAut.conj ((a : G) * g)).toMonoidHom
  inverts : ∀ x ∈ (h.X : Subgroup (Centralizer z)), u * x * u⁻¹ = x⁻¹
  swaps : factors.left.map (MulAut.conjNormal u).toMonoidHom = factors.right
  generates : Core z ⊔ (h.X : Subgroup (Centralizer z)) ⊔ zpowers u = ⊤

/-- H-conjugacy preserves the fusion conditions with the stated left-conjugation convention. -/
public theorem arranged_fusion_conditions (h : Hypotheses z) (g : G)
    (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z)
    (a : Centralizer z) :
    ((a : G) * g) * z * ((a : G) * g)⁻¹ ∈ coreInG z ∧
      ((a : G) * g) * z * ((a : G) * g)⁻¹ ≠ z := by
  have haN : (a : G) ∈ normalizer (coreInG z : Set G) :=
    h.normalizer_core.symm ▸ a.property
  have hconj : ((a : G) * g) * z * ((a : G) * g)⁻¹ =
      (MulAut.conj (a : G)) (g * z * g⁻¹) := by
    simp only [MulAut.conj_apply, mul_inv_rev, mul_assoc]
  have haz : (MulAut.conj (a : G)) z = z :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp a.property)
  rw [hconj]
  exact ⟨(haN _).mp hgQ, fun he => hg ((MulAut.conj (a : G)).injective (he.trans haz.symm))⟩

/-- The actual arranged actor normalizes the eight and acts nontrivially on it.
The second assertion applies the proved source 2.5(1), not an action premise. -/
public theorem ArrangedSwapWitness.intersection_action (h : Hypotheses z) (g : G)
    (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z)
    (w : ArrangedSwapWitness h g) :
    (w.u : G) ∈ normalizer (coreIntersection z ((w.a : G) * g) : Set G) ∧
      (w.u : G) ∉ centralizer (coreIntersection z ((w.a : G) * g) : Set G) := by
  obtain ⟨haQ, ha⟩ := arranged_fusion_conditions h g hgQ hg w.a
  refine ⟨conjugate_core_normalizes_intersection h _ haQ ha w.in_conjugate_core, ?_⟩
  rw [coreIntersection_self_centralizing h _ haQ ha]
  exact fun hu => w.outside hu.1

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition
