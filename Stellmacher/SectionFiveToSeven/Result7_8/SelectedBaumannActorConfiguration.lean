module

public import Stellmacher.SectionFiveToSeven.Result7_8.LocalInputs
public import Stellmacher.SectionFiveToSeven.Result7_8.QuotientModel
public import Stellmacher.SectionThree.GeneratedDihedralAction
public import Stellmacher.BaumannNormalizer

/-!
# Selected Baumann extraction with a prescribed actor

Fix an edge Sylow whose Baumann subgroup is not contained in the first
vertex core. Under the actor and Frattini hypotheses of (7.8), retain a
prescribed element of the actor subgroup outside that core. One primitive
dihedral extraction provides the quotient configuration, with this element
outside its index-two actor subgroup, and controls the residual of the same
extracted subgroup by its commutator with the selected Baumann subgroup.

The selected Baumann subgroup is normal in the edge Sylow and supplies the
normal-subgroup parameter of primitive extraction. Apply that extraction to
the prescribed actor. Its factorization of the actor subgroup shows that the
prescribed element cannot lie in the index-two subgroup. The existing
reflection, generation, quotient-model and neighboring-center orbit lemmas
then assemble the remaining assertions while retaining the same witnesses.

Source: Stellmacher (3.6), (7.8), Journal of Algebra 190 (1997), pp.22–23, 36,
and the second extraction in (9.3), p.49, assertion (3), where retaining an
actor in the chosen vertex center ensures the later geometric alignment.
This is the selected-Sylow quotient-action configuration: no simultaneous
Baumann control, whole-edge residual normalization, or actual involution
lift is claimed. The numbered (7.8) statement is unchanged.
-/

namespace Stellmacher.SectionsFiveToSeven

open CosetGraphContext Stellmacher.SectionThree

open scoped Pointwise

/-- The selected edge-Sylow quotient configuration of (7.8), retaining the
prescribed actor outside the coatom of the same witnesses. -/
public theorem sevenEight_quotient_configuration_for_edge_sylow_with_actor
    {G : Type*} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2)
    (d l : Gamma.Vertex) (hl : l ∈ neighborhood Gamma d)
    (A : Subgroup G) (hA : A ≤ q Gamma l)
    (hAnot : ¬ A ≤ q Gamma d)
    (hPhi : frattiniAmbient A ≤ q Gamma d)
    (T : Sylow 2 ↥(stabilizer Gamma d ⊓ stabilizer Gamma l))
    (hBaumann : ¬ baumannIn
      (sylowTwoAmbient (stabilizer Gamma d ⊓ stabilizer Gamma l) T) ≤ q Gamma d)
    (actor : G) (hactorA : actor ∈ A) (hactorCore : actor ∉ q Gamma d) :
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
      twoResidualIn L ≤ ⁅twoResidualIn L, baumannIn
        (sylowTwoAmbient (stabilizer Gamma d ⊓ stabilizer Gamma l) T)⁆ ∧ actor ∉ A₀ := by
  classical
  let P := stabilizer Gamma d
  let W := sylowTwoAmbient (stabilizer Gamma d ⊓ stabilizer Gamma l) T
  have hi := sevenEight_local_inputs h Gamma d l hl A hA hAnot hPhi T
  let a := actor
  have haA : a ∈ A := hactorA
  have hWP : W ≤ P := sylow_le_of_mem_PSet hi.first_mem
  let hAP : A ≤ P := hi.actor_le.trans hWP
  have hnormal : NormalIn (baumannIn W) W := by
    refine ⟨inf_le_left, ?_⟩
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer
      (show baumannIn W ≤ W from inf_le_left)).mpr
    exact W.le_normalizer.trans (normalizer_le_normalizer_baumann W)
  have hcore : q Gamma d = twoCoreAmbient P := by
    rw [q, Gamma.twoCoreAt_def]
    rfl
  have haCore : a ∉ twoCoreAmbient P := hcore ▸ hactorCore
  let e := solvablePrimitive_dihedralExtraction W hi.sectionThree P hi.first_mem
    (baumannIn W) hnormal A hi.actor_le a haA haCore
    hi.frattini_le_core hi.solvable (hcore ▸ hBaumann)
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
    extracted_self_containing_reflection_conjugator P (baumannIn W) A hAP a haA e
  have hLgenY : L = A ⊔ conjugateBy A (y : G) := by
    change L = A ⊔ A.conjBy (y : G)
    rw [hyConj]
    exact hLgen
  have hA₀core : e.A₀ = A ⊓ twoCoreIn L := by
    change e.A₀ = A ⊓ twoCoreAmbient L
    rw [hLgen]
    exact extracted_actor_eq_core_intersection P (baumannIn W) A hAP a haA e hAelem
  have hLS : L ⊔ W = P := by
    rw [hLgen]
    exact extracted_sup_sylow_eq W hi.sectionThree P hi.first_mem hi.solvable
      (baumannIn W) A hAP a haA e
  have hWedge₀ : W ≤ stabilizer Gamma d ⊓ stabilizer Gamma l := by
    exact Subgroup.map_subtype_le _
  have hWedge : W ≤ stabilizer Gamma l ⊓ P := by
    simpa only [P, inf_comm] using hWedge₀
  have hLedge : L ⊔ (stabilizer Gamma l ⊓ P) = P :=
    le_antisymm (sup_le hLP inf_le_right) (hLS ▸ sup_le_sup_left hWedge L)
  obtain ⟨E, hE, hproduct⟩ :=
    extracted_generated_image_product P (baumannIn W) A hAP a haA e hAelem
  have hmodel : Nonempty (QuotientDihedralProduct L (q Gamma d) e.A₀) := by
    rw [hcore]
    exact quotientDihedralProduct_of_internal_image P L e.A₀ hLP
      (e.A₀_le.trans hAL) e.p e.n e.prime_p e.odd_p E hE hproduct
  have hJ : J = R ⊔ (A.subgroupOf P).map qP := by
    change (L.subgroupOf P).map qP = _
    rw [subgroupOf_map_subtype_eq]
    exact extracted_generated_quotient_image P (baumannIn W) A hAP a haA e hAelem
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
  have hactorCoatom : actor ∉ e.A₀ := by
    intro hactor
    have hAA₀ : A ≤ e.A₀ := by
      intro element helement
      have hprod : element ∈ (Subgroup.zpowers a : Set G) * (e.A₀ : Set G) :=
        e.A_factor ▸ helement
      obtain ⟨power, hpower, coatom, hcoatom, rfl⟩ := hprod
      exact e.A₀.mul_mem ((Subgroup.zpowers_le.mpr hactor) hpower) hcoatom
    have heq : A = e.A₀ := le_antisymm hAA₀ e.A₀_le
    have hindex := e.A₀_index_two
    have hcard : Nat.card A = Nat.card e.A₀ := congrArg (fun subgroup : Subgroup G =>
      Nat.card subgroup) heq
    have hpos : 0 < Nat.card e.A₀ := Nat.card_pos
    omega
  refine ⟨(y : G), e.A₀, L, hLP, y.property, e.A₀_le, hLgenY,
    e.A₀_index_two, ?_, ?_, hA₀core, hLedge, hmodel, horbit, ?_, ?_, hactorCoatom⟩
  · rw [hLgenY]
    exact hyL
  · exact hcore ▸ hySq
  · intro b hb hb₀
    change L = Subgroup.closure ({b} : Set G) ⊔ A.conjBy (y : G)
    rw [hLgen, hyConj, ← Subgroup.zpowers_eq_closure]
    exact extracted_generated_by_outside_actor P (baumannIn W) A hAP a haA e hAelem b hb hb₀
  · change twoResidualAmbient L ≤ ⁅twoResidualAmbient L, baumannIn W⁆
    rw [← hF]
    exact e.residual_commutator

end Stellmacher.SectionsFiveToSeven
