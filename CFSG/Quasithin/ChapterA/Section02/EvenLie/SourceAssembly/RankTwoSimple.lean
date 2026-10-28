module

public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.ClassicalSimple
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.SimpleCase

/-!
# The remaining rank-two simple source branches

The actual binary G2, triality and Ree groups, the Suzuki groups and the
three literal small derived endpoints belong to the precise C catalogue,
hence also B. The source minimal counterexample is therefore impossible in
each branch. These inclusions retain the actual fixed-field conventions and
derived carriers; the ternary small Ree comparison is a separate model fact.
Source: Aschbacher--Smith A.2.4 and the last paragraph of A.2.18, printed p.40.
-/

public section
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie
universe u
variable {G : Type u} [Group G]

/-- The literal g2 model belongs to both source lists. -/
theorem caseI_g2 {a : ℕ} (ha : 2 ≤ a)
    (iso : ClassificationModels.IsG2At G (2 ^ a)) :
    IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) := by
  have hc : IsTheoremCModel G := .rank_two a (.g2 ha iso)
  exact ⟨hc.toTheoremBModel, fun _ => hc⟩

/-- The literal triality model belongs to both source lists. -/
theorem caseI_triality {a : ℕ} (ha : 0 < a)
    (iso : Triality.Standard.IsTrialityGroupAt (2 ^ a) G) :
    IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) := by
  have hc : IsTheoremCModel G := .rank_two a (.triality ha iso)
  exact ⟨hc.toTheoremBModel, fun _ => hc⟩

/-- The literal suzuki model belongs to both source lists. -/
theorem caseI_suzuki {m : ℕ} (hm : 1 ≤ m)
    (iso : Nonempty (G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) := by
  have hc : IsTheoremCModel G := .bender (.suzuki m hm iso)
  exact ⟨hc.toTheoremBModel, fun _ => hc⟩

/-- The literal reeF4 model belongs to both source lists. -/
theorem caseI_reeF4 {m : ℕ} (hm : 1 ≤ m)
    (iso : Nonempty (G ≃* ReeF4.Model m)) :
    IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) := by
  have hc : IsTheoremCModel G := .rank_two (2 * m + 1) (.ree_f4 m hm rfl iso)
  exact ⟨hc.toTheoremBModel, fun _ => hc⟩

/-- The literal symplectic derived model belongs to both source lists. -/
theorem caseI_symplectic_derived
    (iso : Nonempty (G ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) :
    IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) := by
  have hc : IsTheoremCModel G := .rank_two 1 (.symplectic_derived rfl iso)
  exact ⟨hc.toTheoremBModel, fun _ => hc⟩

/-- The literal g2 derived model belongs to both source lists. -/
theorem caseI_g2_derived
    (iso : Nonempty (G ≃* commutator (Atlas.G2.Model (ZMod 2)))) :
    IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) := by
  have hc : IsTheoremCModel G := .rank_two 1 (.g2_derived rfl iso)
  exact ⟨hc.toTheoremBModel, fun _ => hc⟩

/-- The literal tits model belongs to both source lists. -/
theorem caseI_tits
    (iso : Nonempty (G ≃* Tits.ParrottGroup)) :
    IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) := by
  have hc : IsTheoremCModel G := .rank_two 1 (.tits rfl iso)
  exact ⟨hc.toTheoremBModel, fun _ => hc⟩

variable [Finite G] [IsSimpleGroup G] {K : GroupClass.{u}}

/-- The actual g2 branch contradicts the simultaneous source minimum. -/
theorem not_minimalCounterexample_g2
    (h : MinimalCounterexample K G) {a : ℕ} (ha : 2 ≤ a)
    (iso : ClassificationModels.IsG2At G (2 ^ a)) : False := by
  obtain ⟨_, _, _, hfails⟩ := h.simple_case inferInstance
  obtain ⟨hb, hc⟩ := caseI_g2 ha iso
  rcases hfails with hn | ⟨hstrong, hn⟩
  · exact hn hb
  · exact hn (hc hstrong)

/-- The actual triality branch contradicts the simultaneous source minimum. -/
theorem not_minimalCounterexample_triality
    (h : MinimalCounterexample K G) {a : ℕ} (ha : 0 < a)
    (iso : Triality.Standard.IsTrialityGroupAt (2 ^ a) G) : False := by
  obtain ⟨_, _, _, hfails⟩ := h.simple_case inferInstance
  obtain ⟨hb, hc⟩ := caseI_triality ha iso
  rcases hfails with hn | ⟨hstrong, hn⟩
  · exact hn hb
  · exact hn (hc hstrong)

/-- The actual suzuki branch contradicts the simultaneous source minimum. -/
theorem not_minimalCounterexample_suzuki
    (h : MinimalCounterexample K G) {m : ℕ} (hm : 1 ≤ m)
    (iso : Nonempty (G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) : False := by
  obtain ⟨_, _, _, hfails⟩ := h.simple_case inferInstance
  obtain ⟨hb, hc⟩ := caseI_suzuki hm iso
  rcases hfails with hn | ⟨hstrong, hn⟩
  · exact hn hb
  · exact hn (hc hstrong)

/-- The actual reeF4 branch contradicts the simultaneous source minimum. -/
theorem not_minimalCounterexample_reeF4
    (h : MinimalCounterexample K G) {m : ℕ} (hm : 1 ≤ m)
    (iso : Nonempty (G ≃* ReeF4.Model m)) : False := by
  obtain ⟨_, _, _, hfails⟩ := h.simple_case inferInstance
  obtain ⟨hb, hc⟩ := caseI_reeF4 hm iso
  rcases hfails with hn | ⟨hstrong, hn⟩
  · exact hn hb
  · exact hn (hc hstrong)

/-- The actual symplectic derived branch contradicts the simultaneous source minimum. -/
theorem not_minimalCounterexample_symplectic_derived
    (h : MinimalCounterexample K G)
    (iso : Nonempty (G ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) : False := by
  obtain ⟨_, _, _, hfails⟩ := h.simple_case inferInstance
  obtain ⟨hb, hc⟩ := caseI_symplectic_derived iso
  rcases hfails with hn | ⟨hstrong, hn⟩
  · exact hn hb
  · exact hn (hc hstrong)

/-- The actual g2 derived branch contradicts the simultaneous source minimum. -/
theorem not_minimalCounterexample_g2_derived
    (h : MinimalCounterexample K G)
    (iso : Nonempty (G ≃* commutator (Atlas.G2.Model (ZMod 2)))) : False := by
  obtain ⟨_, _, _, hfails⟩ := h.simple_case inferInstance
  obtain ⟨hb, hc⟩ := caseI_g2_derived iso
  rcases hfails with hn | ⟨hstrong, hn⟩
  · exact hn hb
  · exact hn (hc hstrong)

/-- The actual tits branch contradicts the simultaneous source minimum. -/
theorem not_minimalCounterexample_tits
    (h : MinimalCounterexample K G)
    (iso : Nonempty (G ≃* Tits.ParrottGroup)) : False := by
  obtain ⟨_, _, _, hfails⟩ := h.simple_case inferInstance
  obtain ⟨hb, hc⟩ := caseI_tits iso
  rcases hfails with hn | ⟨hstrong, hn⟩
  · exact hn hb
  · exact hn (hc hstrong)

end CFSG.Quasithin.ChapterA.Section02.EvenLie
