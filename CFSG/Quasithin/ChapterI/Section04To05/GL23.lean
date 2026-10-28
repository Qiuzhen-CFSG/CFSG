module
public import CFSG.Quasithin.ChapterI.Section04To05.GL23.Simplicity
public import ABG.Recognition.ThreeGlobalDegreeIdentities
public import ABG.Recognition.ThreeLinearRecognition
public import ABG.Recognition.ThreeMathieuRecognition

/-!
# Aschbacher–Smith I.4.2: GL₂(3) involution centralizers

A finite group with one conjugacy class of involutions and an involution
centralizer isomorphic to GL₂(3) is isomorphic to PSL₃(3) or M₁₁.
The local hypotheses give simplicity and semidihedral Sylow two-subgroups
of order sixteen. Wong's character identities then give orders 5616 and
7920, and the two recognition theorems identify the concrete models.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.4.2,
printed p.416; W. J. Wong, *On finite groups whose 2-Sylow subgroups have
cyclic subgroups of index 2* (1964), Theorem 6, pp.106–111.
-/

namespace CFSG.Quasithin

/-- Aschbacher–Smith I.4.2, with actual isomorphisms and no simplicity,
Sylow, or group-order hypothesis. -/
public theorem GL23InvolutionCentralizerHypotheses.recognition
    {G : Type*} [Group G] [Finite G] (h : GL23InvolutionCentralizerHypotheses G) :
    Nonempty (G ≃* ABG.PSL3 3 1) ∨ Nonempty (G ≃* Sporadic.Mathieu.M11) := by
  classical
  let : IsSimpleGroup G := h.isSimpleGroup
  let S : Sylow 2 G := Classical.choice inferInstance
  obtain ⟨hS, hcard⟩ := h.sylow_structure S
  let hC : ∀ t : G, orderOf t = 2 →
      Subgroup.centralizer ({t} : Set G) ≃* ABG.GL2 3 1 :=
    fun t ht => (h.centralizer_equiv_of_involution t ht).some
  obtain ⟨c⟩ := ABG.exists_threeGlobalDegreeData S hS hcard hC
  rcases c.degree_alternatives with ⟨_, hG⟩ | ⟨_, hG⟩
  · exact Or.inr (ABG.nonempty_mulEquiv_M11_of_card_eq_7920 S hS hcard hC hG)
  · exact Or.inl (ABG.nonempty_mulEquiv_PSL3_of_card_eq_5616 S hS hcard hC hG)

namespace ChapterI
/-- The unbundled exact source statement of I.4.2. -/
public theorem lemma_I_4_2 {G : Type*} [Group G] [Finite G]
    (z : G) (hz : orderOf z = 2)
    (hclass : ∀ u : G, orderOf u = 2 → ∃ g : G, g * u * g⁻¹ = z)
    (hC : Nonempty (Subgroup.centralizer ({z} : Set G) ≃* ABG.GL2 3 1)) :
    Nonempty (G ≃* ABG.PSL3 3 1) ∨ Nonempty (G ≃* Sporadic.Mathieu.M11) :=
  GL23InvolutionCentralizerHypotheses.recognition ⟨z, hz, hclass, hC⟩
end ChapterI
end CFSG.Quasithin
