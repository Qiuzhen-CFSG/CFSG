module

public import Theory.GroupTheory.Amalgam.NormalBaseRecognition
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.Goldschmidt.MathieuNormalBase.RecognitionData

/-!
# Reconstruction of the two Mathieu normal-base extensions

Suppose the genuine two-perfect residual of a cubic tree action is marked
isomorphic to the M₁₂ amalgam. Its original overlap embeds into the actual
Aut(M₁₂) Borel. The inner overlap has index two, so that image is either
the inner Borel or the full Borel. Normal-supplement gluing reconstructs
both original endpoint groups, with the same overlap map on each side.
The resulting compatible isomorphism identifies the original amalgam with
the marked M₁₂ or Aut(M₁₂) source model.

This proves the extension step of Goldschmidt (1980), §3.8, consumed by
Aschbacher--Smith F.1.12(12)--(13). The earlier classification of the
two-perfect residual remains the explicit marked-isomorphism hypothesis.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.Goldschmidt.MathieuNormalBase
open Subgroup Theory.GroupTheory RankTwoAmalgam Sporadic.Mathieu
open SourceAssembly.Goldschmidt ModelProducts
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

private theorem innerB_le_innerP (i : Fin 2) : innerB ≤ innerP i :=
  Subgroup.map_mono (show MathieuTwelve.B ≤ MathieuTwelve.P i from le_sup_right)

private def innerAmalgam : RankTwoAmalgam (innerP 0) innerB (innerP 1) :=
  ofSubgroups _ _ _ (innerB_le_innerP 0) (innerB_le_innerP 1)

/-- Inner conjugation identifies the entire original marked source amalgam
with its image inside the actual full automorphism group. -/
private def innerModelIso : Iso MathieuTwelve.amalgam innerAmalgam where
  left := (MathieuTwelve.P 0).equivMapOfInjective MulAut.conj conj_injective
  middle := MathieuTwelve.B.equivMapOfInjective MulAut.conj conj_injective
  right := (MathieuTwelve.P 1).equivMapOfInjective MulAut.conj conj_injective
  left_commutes _ := rfl
  right_commutes _ := rfl

private def generatedAmalgam (e : Iso (baseAmalgam F) MathieuTwelve.amalgam) :=
  ofSubgroups (innerP 0 ⊔ (ambientOverlapHom e).range)
    (ambientOverlapHom e).range (innerP 1 ⊔ (ambientOverlapHom e).range)
    le_sup_right le_sup_right

private theorem exists_generated_iso (h : CubicTreeAction F)
    (e : Iso (baseAmalgam F) MathieuTwelve.amalgam) :
    Nonempty (Iso (inclusionAmalgam (F false) (F true)) (generatedAmalgam e)) := by
  obtain ⟨E, _⟩ := NormalBaseRecognition.exists_iso (pResidual 2 G) (F false) (F true)
    (innerP 0) (innerP 1) (leftCoreEquiv e) (rightCoreEquiv e)
    (ambientOverlapHom e) (ambientOverlapHom_injective h e) h.residual_source.2.2
    (ambientOverlapHom_mem_innerP_iff h e 0) (ambientOverlapHom_mem_innerP_iff h e 1)
    (ambientOverlapHom_base_left e) (ambientOverlapHom_base_right e)
    (leftCoreEquiv_conj e) (rightCoreEquiv_conj e)
  exact ⟨E⟩

private def generatedIsoInner (e : Iso (baseAmalgam F) MathieuTwelve.amalgam)
    (hr : (ambientOverlapHom e).range = innerB) : Iso (generatedAmalgam e) innerAmalgam where
  left := MulEquiv.subgroupCongr (by rw [hr, sup_eq_left.mpr (innerB_le_innerP 0)])
  middle := MulEquiv.subgroupCongr hr
  right := MulEquiv.subgroupCongr (by rw [hr, sup_eq_left.mpr (innerB_le_innerP 1)])
  left_commutes _ := rfl
  right_commutes _ := rfl

private def generatedIsoOuter (e : Iso (baseAmalgam F) MathieuTwelve.amalgam)
    (hr : (ambientOverlapHom e).range = AutMathieuTwelve.autB) :
    Iso (generatedAmalgam e) AutMathieuTwelve.autAmalgam where
  left := MulEquiv.subgroupCongr (by rw [hr, ← autP_eq_innerP_sup_autB 0])
  middle := MulEquiv.subgroupCongr hr
  right := MulEquiv.subgroupCongr (by rw [hr, ← autP_eq_innerP_sup_autB 1])
  left_commutes _ := rfl
  right_commutes _ := rfl

/-- The full Mathieu extension classification, with both original inclusion
maps retained. The only earlier-source input is the marked residual model. -/
theorem classification_of_residual_iso (h : CubicTreeAction F)
    (e : Iso (baseAmalgam F) MathieuTwelve.amalgam) :
    Nonempty (Iso (inclusionAmalgam (F false) (F true)) MathieuTwelve.amalgam) ∨
      Nonempty (Iso (inclusionAmalgam (F false) (F true)) AutMathieuTwelve.autAmalgam) := by
  obtain ⟨E⟩ := exists_generated_iso h e
  rcases ambient_overlap_range_cases e with hi | ho
  · exact Or.inl ⟨(E.trans (generatedIsoInner e hi)).trans innerModelIso.symm⟩
  · exact Or.inr ⟨E.trans (generatedIsoOuter e ho)⟩

/-- Apply the normal-base extension step to the original finite Goldschmidt
triple, using the residual of its universal completion and the original marks. -/
theorem classification_of_goldschmidt_residual_iso [Finite G] {A B : Subgroup G}
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    (e : Iso (baseAmalgam (Universal.cosetFamily (inclusionAmalgam A B)))
      MathieuTwelve.amalgam) :
    Nonempty (Iso (inclusionAmalgam A B) MathieuTwelve.amalgam) ∨
      Nonempty (Iso (inclusionAmalgam A B) AutMathieuTwelve.autAmalgam) := by
  let u := Universal.markedIso (inclusionAmalgam A B)
    (Subgroup.inclusion_injective inf_le_left) (Subgroup.inclusion_injective inf_le_right)
  rcases classification_of_residual_iso
      (universalCubicTreeAction_of_goldschmidt h hcore) e with he | he
  · obtain ⟨E⟩ := he
    exact Or.inl ⟨u.trans E⟩
  · obtain ⟨E⟩ := he
    exact Or.inr ⟨u.trans E⟩

end CFSG.Quasithin.ChapterF.GreenBook.Goldschmidt.MathieuNormalBase
