module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeFour.ShortAmbient
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeFour.ShortAmbient.Automizer
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.CartanTransport
public import Theory.SpecificGroups.ReeF4.SourceCompletion.ShortCentralizerGeometry.Invariance
public import Theory.SpecificGroups.ReeF4.SourceCompletion.ShortCentralizerGeometry.Action

/-!
# The long-root plane in the actual extension short centralizer

Every full left-endpoint automorphism preserves the native plane. Transport
that plane through the supplied equivalence with the entire extension
centralizer; it is nontrivial, elementary and relatively normal. Its actual
native PSL₂ subgroup acts faithfully. Unique fixed cosets therefore force
the local subgroup to be the entire ambient short centralizer by I.8.5.
The fixed-coset premise is supplied by the commuting-class comparison at
the literal Chapter6 consumer. No ambient centralizer order is assumed.

Source: Aschbacher--Smith F.4.42, printed p.295 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeFour.ShortAmbient
open ReeF4 Parabolics EvenInvolutionGeometry ElementaryTwoBound
open ReeF4.SourceCompletion.ShortCentralizerGeometry
variable {m : ℕ} (E : GeneralReeExtension.SourceExtension m)

theorem extension_left_preserves_plane (hm : 0 < m)
    (a : MulAut (Model m)) (ha : a ∈ E.left) :
    (Replacement.V m).map a.toMonoidHom = Replacement.V m := by
  have hi := ReeF4.SmallCompletion.conj_injective m hm
  apply automorphism_preserves_plane hm
  obtain ⟨g,hg,b,hb,rfl⟩ := E.left_factor hi a ha
  have hbP : (parabolic m .linear).map b.toMonoidHom = parabolic m .linear := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (E.middle_preserves_left hi ⟨b,hb⟩ x).mpr hx
    · intro x hx
      exact ⟨b.symm x,(E.middle_preserves_left hi ⟨b,hb⟩ (b.symm x)).mp
        (by simpa using hx),b.apply_symm_apply x⟩
  rw [show (MulAut.conj g * b).toMonoidHom =
    (MulAut.conj g).toMonoidHom.comp b.toMonoidHom from rfl, ←map_map,hbP]
  exact mem_normalizer_iff_map_conj_eq.mp ((parabolic m .linear).le_normalizer hg)

/-- Transport the literal native plane, its full-endpoint invariance and its
faithful PSL₂ action through the entire local short-centralizer comparison.
The remaining fixed-coset premise is discharged by commuting-class counting. -/
theorem eq_top_of_extension_plane
    {M : Type*} [Group M] [Finite M] (hm : 0 < m)
    {t : Model m} (ht : IsShortRootInvolution t) (htR : t ∈ radical m .linear)
    (hC : centralizer ({E.baseHom t} : Set E.carrier) ≤ E.left.subgroupOf E.carrier)
    (X : Subgroup M) (e : X ≃* centralizer ({E.baseHom t} : Set E.carrier))
    (hfix : ∀ a : X, (∃ w : Replacement.V m, w ≠ 1 ∧ (e a).val = E.baseHom w.val) →
      ∃! q : M ⧸ X, a.val • q = q) : X = ⊤ := by
  have hi := ReeF4.SmallCompletion.conj_injective m hm
  have hbase := E.baseHom_injective hi
  have hCn : centralizer ({t} : Set (Model m)) ≤ parabolic m .linear := by
    intro x hx
    apply (E.baseHom_mem_family_iff hi false x).mp
    exact hC (mem_centralizer_singleton_iff.mpr
      ((show Commute x t from mem_centralizer_singleton_iff.mp hx).map E.baseHom).eq)
  have hV := plane_le_short_centralizer htR
  let b : centralizer ({t} : Set (Model m)) →*
      centralizer ({E.baseHom t} : Set E.carrier) :=
    (E.baseHom.comp (centralizer ({t} : Set (Model m))).subtype).codRestrict _
      (fun x => mem_centralizer_singleton_iff.mpr
        ((show Commute x.val t from mem_centralizer_singleton_iff.mp x.property).map E.baseHom).eq)
  let j : Replacement.V m →* X := e.symm.toMonoidHom.comp
    (b.comp ((Replacement.V m).subtype.codRestrict _ (fun w => hV w.property)))
  have hjv (w : Replacement.V m) : (e (j w)).val = E.baseHom w.val := by
    change (e (e.symm _)).val = _
    rw [e.apply_symm_apply]
    rfl
  have hj : Function.Injective j := by
    intro w u h
    apply Subtype.ext
    apply hbase
    rw [←hjv,←hjv,h]
  let : j.range.Normal := by
    refine ⟨?_⟩
    rintro _ ⟨w,rfl⟩ a
    let aE : E.carrier := (e a).val
    have haE : aE.val ∈ E.left := hC (e a).property
    have haV := extension_left_preserves_plane E hm aE.val haE
    let w' : Replacement.V m := ⟨aE.val w.val,by
      have hw := mem_map_of_mem aE.val.toMonoidHom w.property
      rw [haV] at hw
      exact hw⟩
    refine ⟨w',?_⟩
    apply e.injective
    apply Subtype.ext
    simp only [map_mul,map_inv,Subgroup.coe_mul,Subgroup.coe_inv,hjv]
    exact baseHom_conjugation E aE w.val
  obtain ⟨f,hf,hfa⟩ := short_plane_faithful_psl hm ht hCn
  let fX := e.symm.toMonoidHom.comp (b.comp f)
  have hfv (k : LargeLocalSeeds.LinearQuotient m) :
      (e (fX k)).val = E.baseHom (f k).val := by
    change (e (e.symm _)).val = _
    rw [e.apply_symm_apply]
    rfl
  let := LargeLocalSeeds.linearQuotient_simple m hm
  let := LargeLocalSeeds.linearQuotient_perfect m hm
  let : IsElementaryAbelian 2 (Replacement.V m) := Replacement.CentralizerGeometry.elementary_V m
  let : Nontrivial (Replacement.V m) := (Subgroup.nontrivial_iff_ne_bot _).mpr (plane_ne_bot m)
  apply eq_top_of_unique_fixed_nonsolvable_action X j hj fX _
    (Group.IsPerfect.not_isSolvable (LargeLocalSeeds.LinearQuotient m)) _
  · intro k hk
    apply hfa
    rw [map_one]
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    change (shortPlaneAction hm hCn (f k) w : Model m) = w.val
    rw [shortPlaneAction_apply]
    have hc := mem_centralizer_iff.mp hk (j w) ⟨w,rfl⟩
    have heq := congrArg (fun a : X => (e a).val) hc
    simp only [map_mul,Subgroup.coe_mul,hjv,hfv] at heq
    have hn : w.val * (f k).val = (f k).val * w.val :=
      hbase (by simpa only [map_mul] using heq)
    rw [←hn,mul_inv_cancel_right]
  · intro w hw
    exact hfix (j w) ⟨w,hw,hjv w⟩

end CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeFour.ShortAmbient
