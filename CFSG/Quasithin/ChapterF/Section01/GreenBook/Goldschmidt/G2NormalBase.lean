module

public import Theory.GroupTheory.Amalgam.NormalBaseRecognition
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.Goldschmidt.G2NormalBase.RecognitionData

/-!
# Reconstruction of the binary G₂ normal-base extensions

When the genuine two-perfect residual of a cubic tree action is the marked
G₂(2)′ amalgam, the original overlap embeds in the full G₂(2) Borel and
contains its derived Borel. The latter has index two. Normal-supplement
gluing therefore identifies the original inclusion amalgam with the
derived or full marked model. An overlap of order at least 64 excludes
the derived model, whose overlap has order 32.

This is the extension step of Goldschmidt (1980), §3.7, used in the binary
G₂ alternatives of Aschbacher--Smith F.1.12. The marked residual model is
the earlier-source input; the finite-triple consumers take this residual
in the universal completion and return the original inclusion maps.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.Goldschmidt.G2NormalBase
open Subgroup Theory.GroupTheory RankTwoAmalgam
open SourceAssembly.Goldschmidt ExceptionalModels.G2
open Atlas.G2.BinaryParabolicPair
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

private theorem innerB_le_innerP0 : Model.innerB ≤ Model.innerP0 :=
  Subgroup.map_mono derivedSylow_le_first

private theorem innerB_le_innerP1 : Model.innerB ≤ Model.innerP1 :=
  Subgroup.map_mono derivedSylow_le_second

private def innerAmalgam : RankTwoAmalgam Model.innerP0 Model.innerB Model.innerP1 :=
  ofSubgroups _ _ _ innerB_le_innerP0 innerB_le_innerP1

private def innerModelIso : Iso simpleAmalgam innerAmalgam where
  left := derivedL₁.equivMapOfInjective Derived.subtype Derived.subtype_injective
  middle := derivedB.equivMapOfInjective Derived.subtype Derived.subtype_injective
  right := derivedL₂.equivMapOfInjective Derived.subtype Derived.subtype_injective
  left_commutes _ := rfl
  right_commutes _ := rfl

private def generatedAmalgam (e : Iso (baseAmalgam F) simpleAmalgam) :=
  ofSubgroups (Model.innerP0 ⊔ (ambientOverlapHom e).range)
    (ambientOverlapHom e).range (Model.innerP1 ⊔ (ambientOverlapHom e).range)
    le_sup_right le_sup_right

private theorem exists_generated_iso (h : CubicTreeAction F)
    (e : Iso (baseAmalgam F) simpleAmalgam) :
    Nonempty (Iso (inclusionAmalgam (F false) (F true)) (generatedAmalgam e)) := by
  obtain ⟨E, _⟩ := NormalBaseRecognition.exists_iso (pResidual 2 G) (F false) (F true)
    Model.innerP0 Model.innerP1 (leftCoreEquiv e) (rightCoreEquiv e)
    (ambientOverlapHom e) (ambientOverlapHom_injective h e) h.residual_source.2.2
    (ambientOverlapHom_mem_inner_iff h e Model.innerP0 Model.innerP0_inf_fullB)
    (ambientOverlapHom_mem_inner_iff h e Model.innerP1 Model.innerP1_inf_fullB)
    (ambientOverlapHom_base_left e) (ambientOverlapHom_base_right e)
    (leftCoreEquiv_conj e) (rightCoreEquiv_conj e)
  exact ⟨E⟩

private def generatedIsoInner (e : Iso (baseAmalgam F) simpleAmalgam)
    (hr : (ambientOverlapHom e).range = Model.innerB) :
    Iso (generatedAmalgam e) innerAmalgam where
  left := MulEquiv.subgroupCongr (by rw [hr, sup_eq_left.mpr innerB_le_innerP0])
  middle := MulEquiv.subgroupCongr hr
  right := MulEquiv.subgroupCongr (by rw [hr, sup_eq_left.mpr innerB_le_innerP1])
  left_commutes _ := rfl
  right_commutes _ := rfl

private def generatedIsoFull (e : Iso (baseAmalgam F) simpleAmalgam)
    (hr : (ambientOverlapHom e).range = fullB) :
    Iso (generatedAmalgam e) fullAmalgam where
  left := MulEquiv.subgroupCongr (by rw [hr, ← Model.fullL₁_eq_innerP0_sup_fullB])
  middle := MulEquiv.subgroupCongr hr
  right := MulEquiv.subgroupCongr (by rw [hr, ← Model.fullL₂_eq_innerP1_sup_fullB])
  left_commutes _ := rfl
  right_commutes _ := rfl

/-- Both marked binary G₂ extensions of the classified residual amalgam. -/
theorem classification_of_residual_iso (h : CubicTreeAction F)
    (e : Iso (baseAmalgam F) simpleAmalgam) :
    Nonempty (Iso (inclusionAmalgam (F false) (F true)) simpleAmalgam) ∨
      Nonempty (Iso (inclusionAmalgam (F false) (F true)) fullAmalgam) := by
  obtain ⟨E⟩ := exists_generated_iso h e
  rcases ambient_overlap_range_cases e with hi | hf
  · exact Or.inl ⟨(E.trans (generatedIsoInner e hi)).trans innerModelIso.symm⟩
  · exact Or.inr ⟨E.trans (generatedIsoFull e hf)⟩

/-- The large-overlap hypothesis selects the full G₂(2) extension. -/
theorem full_of_residual_iso_of_large_overlap (h : CubicTreeAction F)
    (e : Iso (baseAmalgam F) simpleAmalgam)
    (hlarge : 64 ≤ Nat.card ↥(F false ⊓ F true)) :
    Nonempty (Iso (inclusionAmalgam (F false) (F true)) fullAmalgam) := by
  rcases classification_of_residual_iso h e with he | he
  · obtain ⟨E⟩ := he
    have hc : Nat.card ↥(F false ⊓ F true) = 32 :=
      (Nat.card_congr E.middle.toEquiv).trans Model.card_derivedB
    omega
  · exact he

/-- Reconstruct the original finite triple from the genuine residual in its
universal completion, retaining both original overlap inclusions. -/
theorem classification_of_goldschmidt_residual_iso [Finite G] {A B : Subgroup G}
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    (e : Iso (baseAmalgam (Universal.cosetFamily (inclusionAmalgam A B))) simpleAmalgam) :
    Nonempty (Iso (inclusionAmalgam A B) simpleAmalgam) ∨
      Nonempty (Iso (inclusionAmalgam A B) fullAmalgam) := by
  let u := Universal.markedIso (inclusionAmalgam A B)
    (Subgroup.inclusion_injective inf_le_left) (Subgroup.inclusion_injective inf_le_right)
  rcases classification_of_residual_iso
      (universalCubicTreeAction_of_goldschmidt h hcore) e with he | he
  · obtain ⟨E⟩ := he
    exact Or.inl ⟨u.trans E⟩
  · obtain ⟨E⟩ := he
    exact Or.inr ⟨u.trans E⟩

/-- The actual large-overlap finite-triple consumer for F.1.12's full binary
G₂ branch. Its residual input is a marked model in the universal completion. -/
theorem full_of_goldschmidt_residual_iso_of_large_overlap [Finite G] {A B : Subgroup G}
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    (e : Iso (baseAmalgam (Universal.cosetFamily (inclusionAmalgam A B))) simpleAmalgam)
    (hlarge : 64 ≤ Nat.card ↥(A ⊓ B)) :
    Nonempty (Iso (inclusionAmalgam A B) fullAmalgam) := by
  rcases classification_of_goldschmidt_residual_iso h hcore e with he | he
  · obtain ⟨E⟩ := he
    have hc : Nat.card ↥(A ⊓ B) = 32 :=
      (Nat.card_congr E.middle.toEquiv).trans Model.card_derivedB
    omega
  · exact he

end CFSG.Quasithin.ChapterF.GreenBook.Goldschmidt.G2NormalBase
