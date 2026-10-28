module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.FullCatalogue
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels.DefiningFields.Linear.Marking
public import Theory.SpecificGroups.PSL2.SymmetricThreePairs
public import Theory.SpecificGroups.PSL3.SymmetricThreePairs
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.BinaryThree
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels.ResidualThree

/-!
# The linear defining fields in the original 13.5.21 quotient

Sylow centrality puts the marked involution in the actual component. Its
conjugate pairs force the defining field of either linear family to have
order two. The orthogonal row supplies PSL₂ over the field of twice the
parameter degree, so that row is impossible. All comparisons pass through
L/Z(L); centerlessness of the covering SL₃ is never an input.

The original B.4.2 action equivalences and the B.4.5 orthogonal actor are
retained. Binary coordinates and the actual marked generator are exported
for the natural-row and residual-three consumers.

Source: Aschbacher–Smith, B.4.2/B.4.5, printed pp.86–87, and 13.5.21,
printed p.924 (PDF p.941), the deductions from conditions (i) and (iv).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels.DefiningFields
open Configuration
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {K : Subgroup G}
  (s : Selected D K) (h : D.Hypothesis) [(componentCentralizer s h).Normal]

/-- The literal central-quotient comparison with the matrix row. -/
def chiefLinearQuotientEquiv {E : Type*} [Group E] (L : Subgroup E)
    (comparison : Khat s h ≃* (L ⧸ center L))
    {F : Type*} [Field F] {d : ℕ}
    (e : L ≃* Matrix.SpecialLinearGroup (Fin d) F) :
    Khat s h ≃* Matrix.ProjectiveSpecialLinearGroup (Fin d) F :=
  comparison.trans (QuotientGroup.congr _ _ e (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (centerCongr e ⟨x, hx⟩).property
    · intro hy
      exact ⟨e.symm y, (centerCongr e.symm ⟨y, hy⟩).property, e.apply_symm_apply y⟩))

/-- The comparison uses the original quotient maps on actual representatives. -/
theorem chiefLinearQuotientEquiv_mk {E : Type*} [Group E] (L : Subgroup E)
    (comparison : Khat s h ≃* (L ⧸ center L))
    {F : Type*} [Field F] {d : ℕ}
    (e : L ≃* Matrix.SpecialLinearGroup (Fin d) F) (l : L) :
    chiefLinearQuotientEquiv s h L comparison e
      (comparison.symm (QuotientGroup.mk' (center L) l)) =
      QuotientGroup.mk' (center (Matrix.SpecialLinearGroup (Fin d) F)) (e l) := by
  simp [chiefLinearQuotientEquiv, QuotientGroup.congr_mk]

/-- Condition (iv) restricts to the original marked generator in K̂. -/
theorem ComponentMarking.pairs (m : ComponentMarking s h) (hiv : PairCondition s h) :
    SymmetricThreePairs m.generator := by
  apply SymmetricThreePairs.of_injective (Khat s h).subtype Subtype.coe_injective
  intro x hn
  have he : (zpowers (m.generator : Xhat s h) ⊔
      zpowers (MulAut.conj x (m.generator : Xhat s h)) : Subgroup (Xhat s h)) =
      markedPair s h x := by
    rw [markedPair, ← m.generates, MonoidHom.map_zpowers]
    rfl
  obtain ⟨e⟩ := hiv x (fun hp => hn (he.symm ▸ hp))
  exact ⟨(MulEquiv.subgroupCongr he).trans e⟩

private theorem degree_one_of_card {F : Type*} [Finite F] {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (hb : Nat.card F ≤ 2) : n = 1 := by
  have hh : 2 ^ n ≤ 2 ^ 1 := by simpa only [pow_one, ← hF] using hb
  have hn1 : n ≤ 1 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh
  omega

/-- B.4.2(1) has binary defining field, with the actual component marking. -/
theorem source_linearTwo_degree_one
    (Y : Subgroup G) (p : Prefix s h Y) (hiv : PairCondition s h)
    {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) (L : Subgroup E)
    (comparison : Khat s h ≃* (L ⧸ center L)) (F : BinaryField)
    (action : ActionEquiv (ρ.comp L.subtype) (linearNatural F 2)) :
    F.degree = 1 ∧ Nonempty (ComponentMarking s h) := by
  let e := chiefLinearQuotientEquiv s h L comparison action.groupEquiv
  obtain ⟨m⟩ := source_linearTwo_marking s h Y p F.Carrier e
  have hc := Theory.PSL2.field_card_le_two_of_involution_pairs (e m.generator)
    ((e.orderOf_eq m.generator).trans m.order) ((m.pairs s h hiv).map_equiv e)
  exact ⟨degree_one_of_card F.degree_pos F.card_eq hc, ⟨m⟩⟩

/-- B.4.2(2) has binary defining field. The comparison is with SL₃/Z(SL₃). -/
theorem source_linearThree_degree_one
    (Y : Subgroup G) (p : Prefix s h Y) (hiv : PairCondition s h)
    {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) (L : Subgroup E)
    (comparison : Khat s h ≃* (L ⧸ center L)) (F : BinaryField)
    (action : ActionEquiv (ρ.comp L.subtype) (linearNatural F 3)) :
    F.degree = 1 ∧ Nonempty (ComponentMarking s h) := by
  let e := chiefLinearQuotientEquiv s h L comparison action.groupEquiv
  obtain ⟨m⟩ := source_linearThree_marking s h Y p F.Carrier F.degree_pos F.card_eq e
  have hc := Theory.PSL3.field_card_le_two_of_involution_pairs F.Carrier F.degree_pos
    F.card_eq (e m.generator) ((e.orderOf_eq m.generator).trans m.order)
    ((m.pairs s h hiv).map_equiv e)
  exact ⟨degree_one_of_card F.degree_pos F.card_eq hc, ⟨m⟩⟩


/-- Table B.4.5's orthogonal actor uses the larger field F. Its degree is
positive and even, contradicting the binary field forced by the pairs. -/
theorem source_not_orthogonal_component
    (Y : Subgroup G) (p : Prefix s h Y) (hiv : PairCondition s h)
    {E : Type*} [Group E] (L : Subgroup E)
    (comparison : Khat s h ≃* (L ⧸ center L))
    (Kfield F : Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.BinaryField)
    (degree : F.degree = 2 * Kfield.degree) :
    ¬ Nonempty (L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F.Carrier) := by
  rintro ⟨actor⟩
  let sl := MulEquiv.ofBijective (BenderSuzuki.Converse.pi F.Carrier)
    ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩
  let e := chiefLinearQuotientEquiv s h L comparison (actor.trans sl.symm)
  obtain ⟨m⟩ := source_linearTwo_marking s h Y p F.Carrier e
  have hc := Theory.PSL2.field_card_le_two_of_involution_pairs (e m.generator)
    ((e.orderOf_eq m.generator).trans m.order) ((m.pairs s h hiv).map_equiv e)
  have hn := degree_one_of_card F.degree_pos F.card_eq hc
  have hk := Kfield.degree_pos
  omega

/-- The original intertwiner is composed with the canonical degree-one
field coordinates. This retains the actual row action. -/
def binaryLinearAction {E W : Type*} [Group E]
    [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) E W} {F : BinaryField} {d : ℕ}
    (action : ActionEquiv ρ (linearNatural F d)) (degree : F.degree = 1) :
    ActionEquiv ρ (linearNatural BinaryField.two d) :=
  let e := ExtensionConsequences.degreeOneNaturalEquiv F degree d
  ⟨action.groupEquiv.trans e.groupEquiv, action.linearEquiv.trans e.linearEquiv,
    fun g v => (congrArg e.linearEquiv (action.intertwines g v)).trans
      (e.intertwines (action.groupEquiv g) (action.linearEquiv v))⟩

/-- The complete binary linear-two output, from the original configuration
and the actual B.4.2 action, with component membership and Sylow marking. -/
theorem source_binary_linearTwo
    (Y : Subgroup G) (hY : Y ≤ D.L₁) (c : SourceConfiguration s h Y hY)
    {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) (L : Subgroup E)
    (comparison : Khat s h ≃* (L ⧸ center L)) (F : BinaryField)
    (action : ActionEquiv (ρ.comp L.subtype) (linearNatural F 2)) :
    F.degree = 1 ∧ Nonempty (ComponentMarking s h) ∧
      Nonempty (ActionEquiv (ρ.comp L.subtype) (linearNatural BinaryField.two 2)) := by
  obtain ⟨hf, hm⟩ := source_linearTwo_degree_one s h Y c.proved_prefix c.condition_iv
    ρ L comparison F action
  exact ⟨hf, hm, ⟨binaryLinearAction action hf⟩⟩

/-- The complete binary linear-three output retains the original action,
its central quotient and the marked involution. -/
theorem source_binary_linearThree
    (Y : Subgroup G) (hY : Y ≤ D.L₁) (c : SourceConfiguration s h Y hY)
    {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) (L : Subgroup E)
    (comparison : Khat s h ≃* (L ⧸ center L)) (F : BinaryField)
    (action : ActionEquiv (ρ.comp L.subtype) (linearNatural F 3)) :
    F.degree = 1 ∧ Nonempty (ComponentMarking s h) ∧
      Nonempty (ActionEquiv (ρ.comp L.subtype) (linearNatural BinaryField.two 3)) := by
  obtain ⟨hf, hm⟩ := source_linearThree_degree_one s h Y c.proved_prefix c.condition_iv
    ρ L comparison F action
  exact ⟨hf, hm, ⟨binaryLinearAction action hf⟩⟩

/-- Literal application of the orthogonal exclusion to the original
configuration, keeping the table's two distinct field parameters. -/
theorem source_not_orthogonal_of_configuration
    (Y : Subgroup G) (hY : Y ≤ D.L₁) (c : SourceConfiguration s h Y hY)
    {E : Type*} [Group E] (L : Subgroup E)
    (comparison : Khat s h ≃* (L ⧸ center L))
    (Kfield F : Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.BinaryField)
    (degree : F.degree = 2 * Kfield.degree) :
    ¬ Nonempty (L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F.Carrier) :=
  source_not_orthogonal_component s h Y c.proved_prefix c.condition_iv L comparison Kfield F degree

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels.DefiningFields
