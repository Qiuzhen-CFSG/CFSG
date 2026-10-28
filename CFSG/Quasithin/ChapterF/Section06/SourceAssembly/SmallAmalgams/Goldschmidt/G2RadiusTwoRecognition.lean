module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.G2RadiusTwoFirstGroups
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.G2RadiusTwoSecondRecognition
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.G2RadiusTwoCoreBounds
public import Theory.GroupTheory.WreathedThirtyTwoVertex.Recognition
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalRigidity.G2

/-!
# Compatible recognition of the original radius-two source amalgam

The actual second parabolic identifies the common Sylow subgroup with the
concrete wreathed group. The first endpoint has order ninety-six and a
nonabelian self-centralizing two-core, so existing vertex recognition
identifies it with the first derived G₂ parabolic. Sylow normalization and
the proved G₂ overlap rigidity retain both original inclusion maps. This
discharges the literal RadiusTwoMarkedInput used by the source-cut assembly.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.9),
printed pp.400–401.
-/

@[expose] public section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry GreenBook
namespace RadiusTwoRecognition

private theorem swap_primitive {G : Type*} [Group G] {A B : Subgroup G}
    (h : PrimitiveCubic (inclusionAmalgam A B)) :
    PrimitiveCubic (inclusionAmalgam B A) := by
  have hs : SylowEmbedded 2
      (ofSubgroups B (A ⊓ B) A inf_le_right inf_le_left) :=
    ⟨h.sylow.right_injective, h.sylow.left_injective,
      h.sylow.right_sylow, h.sylow.left_sylow⟩
  have hf : Faithful (ofSubgroups B (A ⊓ B) A inf_le_right inf_le_left) :=
    fun N hB hA => h.faithful N hA hB
  have hp : PrimitiveCubic (ofSubgroups B (A ⊓ B) A inf_le_right inf_le_left) :=
    ⟨hs, hf, h.right_index, h.left_index⟩
  have transport (D : Subgroup G) (hD : D = A ⊓ B)
      (h₁ : D ≤ B) (h₂ : D ≤ A) : PrimitiveCubic (ofSubgroups B D A h₁ h₂) := by
    subst D
    exact hp
  exact transport (B ⊓ A) (inf_comm B A) inf_le_left inf_le_right

/-- The actual second endpoint supplies the common wreathed Sylow group;
order and intrinsic core then recognize the first endpoint and both markings. -/
theorem marked_of_second_equiv {G : Type*} [Group G] {A B : Subgroup G}
    (h : PrimitiveCubic (inclusionAmalgam A B)) (hA : Nat.card A = 96)
    (hc : centralizer (pCore 2 A : Set A) ≤ pCore 2 A)
    (hna : ¬ IsMulCommutative (pCore 2 A))
    (eB : B ≃* Atlas.G2.BinaryParabolicPair.derivedSecond) :
    ExceptionalModels.G2.IsDerivedAmalgam (inclusionAmalgam A B) := by
  let : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; decide)
  have hm : SylowEmbedded 2 ExceptionalModels.G2.simpleAmalgam :=
    sylowEmbedded_ofSubgroups ExceptionalModels.G2.derivedS _ _ _ _ _ rfl
  obtain ⟨Si, hSi⟩ := h.sylow.right_sylow
  obtain ⟨Sj, hSj⟩ := hm.right_sylow
  obtain ⟨_, eD, _⟩ := exists_normalized_endpoint
    (inclusionAmalgam A B).right ExceptionalModels.G2.simpleAmalgam.right
    h.sylow.right_injective hm.right_injective Si hSi Sj hSj eB
  obtain ⟨S, hS⟩ := h.sylow.left_sylow
  let eS : S ≃* (A ⊓ B : Subgroup G) :=
    (MulEquiv.subgroupCongr hS).trans (MonoidHom.ofInjective h.sylow.left_injective).symm
  obtain ⟨w⟩ :=
    Atlas.G2.BinaryParabolicPair.derivedSylow_isWreathedOfHeight.nonempty_mulEquiv_regularWreath
  obtain ⟨eA⟩ := WreathedVertex.equiv_derivedFirst_of_card96 hA hc hna S
    (eS.trans (eD.trans w))
  exact ExceptionalRigidity.G2.simple_iso_of_parabolicEquiv h.sylow h.faithful ⟨eA,eD,eB⟩

end RadiusTwoRecognition

/-- Goldschmidt (6.9) for the original radius-two source action, with its
literal endpoint groups, common overlap and both overlap maps. -/
theorem LargeTreeSource.radiusTwo_marked {G : Type*} [Group G]
    {F : Bool → Subgroup G} {s : ℕ} (h : LargeTreeSource F s)
    (c : CanonicalLabelSetup F s) (hr : c.radius = 2) : DerivedMarkedBase F := by
  have hs : 4 ≤ s := by have := h.five_le; omega
  let a := RankTwo.base F c.side
  let β := RankTwo.base F (!c.side)
  have hadj : (RankTwo.graph F).Adj a β :=
    ⟨by change c.side ≠ !c.side; cases c.side <;> decide, incident_base F _ _⟩
  have ha : a.type = c.side := rfl
  have hβ : β.type ≠ c.side := by change (!c.side) ≠ c.side; cases c.side <;> decide
  obtain ⟨hfirst,hsecond⟩ := c.radiusTwo_source_groups_eq_stabilizers hr hs h.action ha hadj
  have hsecond' : c.radiusTwoSecondGroup β = F (!c.side) :=
    hsecond.trans (stabilizer_base F (!c.side))
  obtain ⟨f⟩ := h.action.toCubicTreeAction.exists_branchFrame β
  let r := RadiusTwoSixLabels.frame h.action.toCubicTreeAction f
  obtain ⟨e⟩ := r.second_equiv_derivedSecond c hr hs h.action.toCubicTreeAction hβ
  let eB : F (!c.side) ≃* Atlas.G2.BinaryParabolicPair.derivedSecond :=
    (MulEquiv.subgroupCongr hsecond').symm.trans e
  have hA : Nat.card (F c.side) = 96 := by
    rw [← show RankTwo.stabilizer F a = F c.side from stabilizer_base F c.side,
      ← hfirst, ← RadiusTwoFirstArms.group_eq_first c h.action.toCubicTreeAction hadj]
    exact RadiusTwoFirstArms.group_card c hr hs h.action.toCubicTreeAction a ha
  have hc : centralizer (pCore 2 (F c.side) : Set (F c.side)) ≤ pCore 2 (F c.side) := by
    have he := h.action.toCubicTreeAction.stabilizer_centralizer_twoCore_le_of_large_residual
      h.not_cubic h.not_alternating a
    rwa [show RankTwo.stabilizer F a = F c.side from stabilizer_base F c.side] at he
  have hn : ¬ IsMulCommutative (pCore 2 (F c.side)) := by
    have he := (c.radiusTwo_stabilizer_twoCore_structure hr hs h.action.toCubicTreeAction ha).2
    rwa [show RankTwo.stabilizer F a = F c.side from stabilizer_base F c.side] at he
  have oriented (i : Bool) (hAi : Nat.card (F i) = 96)
      (hci : centralizer (pCore 2 (F i) : Set (F i)) ≤ pCore 2 (F i))
      (hni : ¬ IsMulCommutative (pCore 2 (F i)))
      (eBi : F (!i) ≃* Atlas.G2.BinaryParabolicPair.derivedSecond) : DerivedMarkedBase F := by
    cases i
    · exact Or.inl (RadiusTwoRecognition.marked_of_second_equiv h.action.primitive hAi hci hni eBi)
    · exact Or.inr (RadiusTwoRecognition.marked_of_second_equiv
        (RadiusTwoRecognition.swap_primitive h.action.primitive) hAi hci hni eBi)
  exact oriented c.side hA hc hn eB

universe u

/-- The literal radius-two premise of the source-cut classification is discharged. -/
theorem radiusTwoMarkedInput : RadiusTwoMarkedInput.{u} := by
  intro G _ F s h c hr
  exact h.radiusTwo_marked c hr

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
