module

public import Stellmacher.SectionFiveToSeven.Result7_8.LocalInputs
public import Stellmacher.SectionFiveToSeven.Result7_8.QuotientModel
public import Stellmacher.SectionThree.GeneratedDihedralAction


/-!
# The actual-involution configuration for exponent-two actors

Under the edge and actor hypotheses of Stellmacher (7.8), suppose in
addition that every element of A has square one. Then the extracted local
dihedral configuration has actual involutions interchanging any two
members of the neighboring-center subgroup orbit. The index-two actor
coatom, self-containing conjugator, quotient model, and generation
assertions all refer to the same extracted subgroup L.

Use the neighboring two-core as the normal actor in primitive extraction.
The self-containing reflection-conjugator, actor-core, quotient-image and
local-generation lemmas give the configuration. The subgroup-orbit proof
selects swapping elements that are conjugates of an outside element of A.
That element is nonidentity, and the explicit square-one hypothesis makes
it and all those conjugates actual involutions. This is the valid lifting
argument for elementary-actor applications; it does not infer involutions
merely from an involution in a quotient.

The residual commutator is asserted with the fixed neighboring core used
in this extraction. The separate simultaneous Baumann assertion of (7.8)(e)
is not part of this specialization, and the original numbered theorem is
unchanged. Source: Stellmacher (7.8), Journal of Algebra 190 (1997), p36,
refs/latex/stellmacher-n-group.tex, with the explicit actor-exponent-two
hypothesis supplying the actual-involution step.
-/

namespace Stellmacher.SectionsFiveToSeven

open CosetGraphContext Stellmacher.SectionThree

/-- The local configuration has actual swapping involutions for an exponent-two actor. -/
public theorem sevenEight_involution_configuration_of_actor_exponent_two
    {G : Type*} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2)
    (d l : Gamma.Vertex) (hl : l ∈ neighborhood Gamma d)
    (A : Subgroup G) (hA : A ≤ q Gamma l)
    (hAnot : ¬ A ≤ q Gamma d)
    (hPhi : frattiniAmbient A ≤ q Gamma d)
    (hAexp : ∀ a : G, a ∈ A → a ^ 2 = 1) :
    ∃ x : G, ∃ A₀ L : Subgroup G, L ≤ stabilizer Gamma d ∧
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
        ∃ t : L, _root_.IsInvolution (t : G) ∧
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
  have hconj := generated_subgroup_orbit_conjugate_reflection P L W (z Gamma l) A
    hLP hAL hi.actor_le hi.neighbor_center_normal.1 hi.neighbor_center_normal.2
    hCoreW R hRdata.1 hRdata.2 hRcyclic (IsPGroup.of_card e.rotation_card)
    e.odd_p hJ a haA e.reflected
  have ha : a ≠ 1 := by
    intro ha
    exact haCore (ha ▸ (twoCoreAmbient P).one_mem)
  have horbit :
      ∀ Z₁ Z₂ : Subgroup G,
        Z₁ ∈ conjugateSubgroupOrbit (z Gamma l) L →
        Z₂ ∈ conjugateSubgroupOrbit (z Gamma l) L →
        ∃ t : L, _root_.IsInvolution (t : G) ∧
          Z₁.conjBy (t : G) = Z₂ ∧ Z₂.conjBy (t : G) = Z₁ := by
    intro Z₁ Z₂ hZ₁ hZ₂
    obtain ⟨c, hswap₁, hswap₂⟩ := hconj Z₁ Z₂ hZ₁ hZ₂
    let t : L := c * ⟨a, hAL haA⟩ * c⁻¹
    refine ⟨t, ⟨?_, ?_⟩, hswap₁, hswap₂⟩
    · change (c : G) * a * (c : G)⁻¹ ≠ 1
      intro heq
      apply ha
      calc
        a = (c : G)⁻¹ * ((c : G) * a * (c : G)⁻¹) * c := by group
        _ = 1 := by rw [heq]; simp
    · change ((c : G) * a * (c : G)⁻¹) ^ 2 = 1
      calc
        ((c : G) * a * (c : G)⁻¹) ^ 2 = (c : G) * a ^ 2 * (c : G)⁻¹ := by
          simp [pow_two, mul_assoc]
        _ = 1 := by rw [hAexp a haA]; simp
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
