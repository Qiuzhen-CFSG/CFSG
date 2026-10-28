module

public import Stellmacher.SectionFiveToSeven.Result7_8.LocalInputs
public import Stellmacher.SectionFiveToSeven.Result7_8.QuotientModel
public import Stellmacher.SectionThree.GeneratedDihedralAction

/-!
# The proved quotient-action configuration of Stellmacher (7.8)

Under the exact actor and edge hypotheses of (7.8), this module assembles
the index-two actor coatom, a self-containing conjugator whose square lies
in the local core, the actual quotient dihedral product, generation with
the edge stabilizer, and generation by every actor outside the coatom.
Any two conjugates of the neighboring center are interchanged by an element
whose image in the local quotient is an involution.

LocalInputs supplies the Section 3 hypotheses using the neighboring core
as the normal subgroup for extraction. The reflection-conjugator, actor-core,
generation, image, and orbit lemmas provide the individual assertions.
The residual commutator assertion is stated for that fixed neighboring core.

Source: Stellmacher (7.8), Journal of Algebra 190 (1997), p. 36. This is an
explicit partial assembly: it neither claims the disputed actual-involution
lifting in (c), nor the simultaneous Baumann assertion (e). The original
numbered statement is left unchanged.
-/

namespace Stellmacher.SectionsFiveToSeven

open CosetGraphContext Stellmacher.SectionThree

/-- The proved (7.8)(a,b,d), quotient-action version of (c), and the residual
commutator with the fixed neighboring core used in the extraction. -/
public theorem sevenEight_quotient_configuration
    {G : Type*} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2)
    (d l : Gamma.Vertex) (hl : l ∈ neighborhood Gamma d)
    (A : Subgroup G) (hA : A ≤ q Gamma l)
    (hAnot : ¬ A ≤ q Gamma d)
    (hPhi : frattiniAmbient A ≤ q Gamma d) :
    ∃ x : G, ∃ A₀ L : Subgroup G, ∃ hLP : L ≤ stabilizer Gamma d,
      x ∈ stabilizer Gamma d ∧ A₀ ≤ A ∧
      L = A ⊔ conjugateBy A x ∧
      Nat.card A = 2 * Nat.card A₀ ∧
      x ∈ L ∧ x ^ 2 ∈ q Gamma d ∧
      A₀ = A ⊓ twoCoreIn L ∧
      L ⊔ (stabilizer Gamma l ⊓ stabilizer Gamma d) = stabilizer Gamma d ∧
      Nonempty (QuotientDihedralProduct L (q Gamma d) A₀) ∧
      (∀ Z₁ Z₂ : Subgroup G,
        Z₁ ∈ conjugateSubgroupOrbit (z Gamma l) L →
        Z₂ ∈ conjugateSubgroupOrbit (z Gamma l) L →
        ∃ t : L, _root_.IsInvolution
          (QuotientGroup.mk' (pCore 2 (stabilizer Gamma d))
            ⟨(t : G), hLP t.property⟩) ∧
          Z₁.conjBy (t : G) = Z₂ ∧ Z₂.conjBy (t : G) = Z₁) ∧
      (∀ b : G, b ∈ A → b ∉ A₀ →
        L = Subgroup.closure ({b} : Set G) ⊔ conjugateBy A x) ∧
      twoResidualIn L ≤ ⁅twoResidualIn L, q Gamma l⁆ := by
  classical
  let P := stabilizer Gamma d
  let T : Sylow 2 ↥(stabilizer Gamma d ⊓ stabilizer Gamma l) := default
  let W := sylowTwoAmbient (stabilizer Gamma d ⊓ stabilizer Gamma l) T
  have hi := sevenEight_local_inputs h Gamma d l hl A hA hAnot hPhi T
  obtain ⟨a, haA, haCore⟩ := hi.outside_actor
  have hWP : W ≤ P := sylow_le_of_mem_PSet hi.first_mem
  let hAP : A ≤ P := hi.actor_le.trans hWP
  have hTnot : ¬ q Gamma l ≤ twoCoreAmbient P := by
    intro hT
    exact haCore (hT (hA haA))
  let e := solvablePrimitive_dihedralExtraction W hi.sectionThree P hi.first_mem
    (q Gamma l) hi.neighbor_core_normal A hi.actor_le a haA haCore
    hi.frattini_le_core hi.solvable hTnot
  let AP := A.subgroupOf P
  let LP := AP ⊔ AP.conjBy e.x
  let L := LP.map P.subtype
  let qP := QuotientGroup.mk' (pCore 2 P)
  let R := (e.F₀.subgroupOf P).map qP
  let J := (L.subgroupOf P).map qP
  have hLgen : L = A ⊔ A.conjBy (e.x : G) :=
    (generated_inside_and_quotient_image P A hAP e.x).1
  have hLP : L ≤ P := Subgroup.map_subtype_le LP
  have hAL : A ≤ L := by rw [hLgen]; exact le_sup_left
  have hF : e.F₀ = twoResidualAmbient L := by
    rw [hLgen]
    exact e.residual_generated
  have hAelem := elementary_actor_image P A hAP
    (IsPGroup.to_le hi.sectionThree.nontrivial_two_subgroup.2 hi.actor_le)
    hi.frattini_le_core
  obtain ⟨y, hyL, hySq, hyConj⟩ :=
    extracted_self_containing_reflection_conjugator P (q Gamma l) A hAP a haA e
  have hLgenY : L = A ⊔ conjugateBy A (y : G) := by
    change L = A ⊔ A.conjBy (y : G)
    rw [hyConj]
    exact hLgen
  have hcore : q Gamma d = twoCoreAmbient P := by
    rw [q, Gamma.twoCoreAt_def]
    rfl
  have hA₀core : e.A₀ = A ⊓ twoCoreIn L := by
    change e.A₀ = A ⊓ twoCoreAmbient L
    rw [hLgen]
    exact extracted_actor_eq_core_intersection P (q Gamma l) A hAP a haA e hAelem
  have hLS : L ⊔ W = P := by
    rw [hLgen]
    exact extracted_sup_sylow_eq W hi.sectionThree P hi.first_mem hi.solvable
      (q Gamma l) A hAP a haA e
  have hWedge₀ : W ≤ stabilizer Gamma d ⊓ stabilizer Gamma l := by
    exact Subgroup.map_subtype_le (T : Subgroup ↥(stabilizer Gamma d ⊓ stabilizer Gamma l))
  have hWedge : W ≤ stabilizer Gamma l ⊓ P :=
    le_inf (hWedge₀.trans inf_le_right) (hWedge₀.trans inf_le_left)
  have hLedge : L ⊔ (stabilizer Gamma l ⊓ P) = P := by
    apply le_antisymm (sup_le hLP inf_le_right)
    calc
      P = L ⊔ W := hLS.symm
      _ ≤ L ⊔ (stabilizer Gamma l ⊓ P) := sup_le_sup_left hWedge L
  obtain ⟨E, hE, hproduct⟩ :=
    extracted_generated_image_product P (q Gamma l) A hAP a haA e hAelem
  have hmodel : Nonempty (QuotientDihedralProduct L (q Gamma d) e.A₀) := by
    rw [hcore]
    exact quotientDihedralProduct_of_internal_image P L e.A₀ hLP
      (e.A₀_le.trans hAL) e.p e.n e.prime_p e.odd_p E hE hproduct
  have hJ : J = R ⊔ (A.subgroupOf P).map qP := by
    change (L.subgroupOf P).map qP = _
    rw [subgroupOf_map_subtype_eq]
    exact extracted_generated_quotient_image P (q Gamma l) A hAP a haA e hAelem
  have hRdata : R ≤ J ∧ (R.subgroupOf J).Normal := by
    simpa only [R, hF] using residual_image_normal P L hLP
  have hRcyclic : IsCyclic R := by
    rw [show R = Subgroup.zpowers (qP e.x) from e.rotation_eq]
    infer_instance
  have hCoreW : twoCoreAmbient P ≤ W := by
    obtain ⟨U, hU⟩ := hi.first_mem.1.2.1
    change (U : Subgroup P).map P.subtype = W at hU
    rw [← hU]
    exact Subgroup.map_mono ((pCore_isPGroup (p := 2)).le_sylow_of_normal U)
  have horbit := generated_subgroup_orbit_quotient_reflection P L W (z Gamma l) A
    hLP hAL hi.actor_le hi.neighbor_center_normal.1 hi.neighbor_center_normal.2
    hCoreW R hRdata.1 hRdata.2 hRcyclic (IsPGroup.of_card e.rotation_card)
    e.odd_p hJ a haA e.reflection_involution e.reflected
  refine ⟨(y : G), e.A₀, L, hLP, y.property, e.A₀_le, hLgenY,
    e.A₀_index_two, ?_, ?_, hA₀core, hLedge, hmodel, horbit, ?_, ?_⟩
  · rw [hLgenY]
    exact hyL
  · exact hcore ▸ hySq
  · intro b hb hb₀
    change L = Subgroup.closure ({b} : Set G) ⊔ A.conjBy (y : G)
    rw [hLgen, hyConj, ← Subgroup.zpowers_eq_closure]
    exact extracted_generated_by_outside_actor P (q Gamma l) A hAP a haA e hAelem b hb hb₀
  · change twoResidualAmbient L ≤ ⁅twoResidualAmbient L, q Gamma l⁆
    rw [← hF]
    exact e.residual_commutator

end Stellmacher.SectionsFiveToSeven
