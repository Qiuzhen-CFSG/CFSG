module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.NativeRestoration
public import CFSG.Quasithin.Chapter5.Section03UnitaryFullNormalizer.Endpoint

/-!
# Restoring original endpoints from a native flag action

Native lifts preserve the reduced completion kernel and hence give a faithful
action of the whole original Borel. If an inner automorphism preserving both
native endpoints comes from their overlap, its original actor belongs to the
reduced Borel. The existing normal-supplement gluing theorem then constructs
both original endpoint maps and their full intersection. Only simultaneous
flag preservation is needed; separate endpoint normalizer results are not.

Source: DGS, *Groups and Graphs* (1985), (15.2), pp.226–228. The native lift
and flag assertions are model inputs, with a literal U₅ application supplied
in `UnitaryFiveNative`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.SpecificGroups.ClassicalUnitary
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open SuzukiContainment SourceCompletion.UnitaryNonbinary

private theorem inner_iff_of_faithful_flag
    {G X : Type*} [Group G] [Group X]
    (C D : Subgroup G) (hCD : C ≤ D) (P Q B : Subgroup X)
    (e : C ≃* B) (σ : D →* NativeAmalgamActions.flagAutomorphisms P Q)
    (hσ : Function.Injective σ)
    (hflag : ∀ x : X, P.map (MulAut.conj x).toMonoidHom = P →
      Q.map (MulAut.conj x).toMonoidHom = Q → x ∈ B)
    (ha : ∀ c : C, (σ (inclusion hCD c)).val = MulAut.conj (e c : X))
    (d : D) :
    (σ d).val ∈ SourceCompletion.UnitaryNonbinary.inner X ↔ (d : G) ∈ C := by
  constructor
  · rintro ⟨x,hx⟩
    have hxB : x ∈ B := hflag x (hx.symm ▸ (σ d).property.1) (hx.symm ▸ (σ d).property.2)
    let c := e.symm ⟨x,hxB⟩
    have he : σ (inclusion hCD c) = σ d := by
      apply Subtype.ext
      rw [ha]
      simpa only [c,e.apply_symm_apply] using hx
    exact (congrArg Subtype.val (hσ he)) ▸ c.property
  · intro hd
    exact ⟨e ⟨d,hd⟩, (ha ⟨d,hd⟩).symm⟩

namespace NativeFlag
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} (h : HypothesisF11 L S)
  (P Q B : Subgroup X) (hBP : B ≤ P) (hBQ : B ≤ Q)
  (hgen : P ⊔ Q = ⊤)
  (hlift : ∀ a : Iso (ofSubgroups P B Q hBP hBQ) (ofSubgroups P B Q hBP hBQ),
    ∃ f : X →* X,
      (∀ x : P, f (x : X) = (a.left x : X)) ∧
      (∀ x : Q, f (x : X) = (a.right x : X)))
  (e : Iso (reducedAmalgam L S) (ofSubgroups P B Q hBP hBQ))

private def completion : FaithfulCompletion (reducedAmalgam L S) (G := X) :=
  (FaithfulCompletion.ofSubgroups P B Q hBP hBQ hgen).comapIso e

include hlift in
private theorem preserved : PreservesCompletionKernel h (completion P Q B hBP hBQ hgen e) :=
  NativeRestoration.preserves_of_native_lifts (reducedOverlapAction h) e
    (FaithfulCompletion.ofSubgroups P B Q hBP hBQ hgen) hlift

private def actor : commonBorel L S →* MulAut X :=
  completionAction h (completion P Q B hBP hBQ hgen e)
    (preserved h P Q B hBP hBQ hgen hlift e)

private theorem actor_injective : Function.Injective (actor h P Q B hBP hBQ hgen hlift e) :=
  completionAction_injective h (completion P Q B hBP hBQ hgen e)
    (preserved h P Q B hBP hBQ hgen hlift e)

private theorem actor_flag (b : commonBorel L S) :
    P.map (actor h P Q B hBP hBQ hgen hlift e b).toMonoidHom = P ∧
      Q.map (actor h P Q B hBP hBQ hgen hlift e b).toMonoidHom = Q := by
  have hl := completionAction_endpoint_range h (completion P Q B hBP hBQ hgen e)
    (preserved h P Q B hBP hBQ hgen hlift e) 0 b
  have hr := completionAction_endpoint_range h (completion P Q B hBP hBQ hgen e)
    (preserved h P Q B hBP hBQ hgen hlift e) 1 b
  change (completion P Q B hBP hBQ hgen e).left.range.map
    (actor h P Q B hBP hBQ hgen hlift e b).toMonoidHom =
      (completion P Q B hBP hBQ hgen e).left.range at hl
  change (completion P Q B hBP hBQ hgen e).right.range.map
    (actor h P Q B hBP hBQ hgen hlift e b).toMonoidHom =
      (completion P Q B hBP hBQ hgen e).right.range at hr
  simp only [completion, FaithfulCompletion.comapIso_left_range,
    FaithfulCompletion.ofSubgroups_left_range] at hl
  simp only [completion, FaithfulCompletion.comapIso_right_range,
    FaithfulCompletion.ofSubgroups_right_range] at hr
  exact ⟨hl,hr⟩

private def action : commonBorel L S →* NativeAmalgamActions.flagAutomorphisms P Q :=
  (actor h P Q B hBP hBQ hgen hlift e).codRestrict _
    (actor_flag h P Q B hBP hBQ hgen hlift e)

private theorem action_injective : Function.Injective (action h P Q B hBP hBQ hgen hlift e) := by
  intro a b hab
  exact actor_injective h P Q B hBP hBQ hgen hlift e (congrArg Subtype.val hab)

private theorem action_reduced (b : commonBorel L (reducedSylow L S)) :
    (action h P Q B hBP hBQ hgen hlift e (inclusion (reduced_commonBorel_le h) b)).val =
      MulAut.conj (e.middle b : X) := by
  have hm : (completion P Q B hBP hBQ hgen e).middle b = (e.middle b : X) :=
    congrArg Subtype.val (e.left_commutes b)
  exact (completionAction_reduced h (completion P Q B hBP hBQ hgen e)
    (preserved h P Q B hBP hBQ hgen hlift e) b).trans (congrArg MulAut.conj hm)

private theorem action_inner
    (hflag : ∀ x : X,
      P.map (MulAut.conj x).toMonoidHom = P →
      Q.map (MulAut.conj x).toMonoidHom = Q → x ∈ B)
    (b : commonBorel L S) :
    (action h P Q B hBP hBQ hgen hlift e b).val ∈ SourceCompletion.UnitaryNonbinary.inner X ↔
      (b : G) ∈ commonBorel L (reducedSylow L S) :=
  inner_iff_of_faithful_flag _ _ (reduced_commonBorel_le h) P Q B e.middle
    (action h P Q B hBP hBQ hgen hlift e)
    (action_injective h P Q B hBP hBQ hgen hlift e) hflag
    (action_reduced h P Q B hBP hBQ hgen hlift e) b

private theorem action_left (b : commonBorel L S) (x : parabolic L (reducedSylow L S) 0) :
    ∃ hx : b.val*x.val*b.val⁻¹ ∈ parabolic L (reducedSylow L S) 0,
      (e.left ⟨b.val*x.val*b.val⁻¹,hx⟩).val =
        (action h P Q B hBP hBQ hgen hlift e b).val (e.left x).val :=
  ⟨(reducedEndpointAction h 0 b x).property,
    (completionAction_left h (completion P Q B hBP hBQ hgen e)
      (preserved h P Q B hBP hBQ hgen hlift e) b x).symm⟩

private theorem action_right (b : commonBorel L S) (x : parabolic L (reducedSylow L S) 1) :
    ∃ hx : b.val*x.val*b.val⁻¹ ∈ parabolic L (reducedSylow L S) 1,
      (e.right ⟨b.val*x.val*b.val⁻¹,hx⟩).val =
        (action h P Q B hBP hBQ hgen hlift e b).val (e.right x).val :=
  ⟨(reducedEndpointAction h 1 b x).property,
    (completionAction_right h (completion P Q B hBP hBQ hgen e)
      (preserved h P Q B hBP hBQ hgen hlift e) b x).symm⟩

include h in
private theorem original_product (i : Fin 2) (x : G) (hx : x ∈ parabolic L S i) :
    ∃ p ∈ parabolic L (reducedSylow L S) i, ∃ b ∈ commonBorel L S, x = p*b := by
  rw [← reduced_parabolic_supplement h i] at hx
  have hm : x ∈ (parabolic L (reducedSylow L S) i : Set G) * (commonBorel L S : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _
      ((commonBorel_le_parabolic i).trans (parabolic_normalizes_reduced h i))]
    exact hx
  obtain ⟨p,hp,b,hb,he⟩ := hm
  exact ⟨p,hp,b,hb,he.symm⟩

end NativeFlag

/-- The native flag action restores the original full inclusion diagram,
with both reduced restrictions and the entire original Borel retained. -/
theorem exists_original_extension_of_native_flag
    {G X : Type*} [Group G] [Group X]
    {L : Fin 2 → Subgroup G} {S : Subgroup G} (h : HypothesisF11 L S)
    (P Q B : Subgroup X) (hBP : B ≤ P) (hBQ : B ≤ Q)
    (hPQ : P ⊓ Q = B) (hgen : P ⊔ Q = ⊤)
    (hconj : Function.Injective (MulAut.conj : X →* MulAut X))
    (hflag : ∀ x : X,
      P.map (MulAut.conj x).toMonoidHom = P →
      Q.map (MulAut.conj x).toMonoidHom = Q → x ∈ B)
    (hlift : ∀ a : Iso (ofSubgroups P B Q hBP hBQ) (ofSubgroups P B Q hBP hBQ),
      ∃ f : X →* X,
        (∀ x : P, f (x : X) = (a.left x : X)) ∧
        (∀ x : Q, f (x : X) = (a.right x : X)))
    (e : Iso (reducedAmalgam L S) (ofSubgroups P B Q hBP hBQ)) :
    ∃ E : SourceExtension P Q, ∃ F : Iso (originalAmalgam L S) E.amalgam,
      (∀ x : parabolic L (reducedSylow L S) 0,
        (F.left (inclusion (reduced_parabolic_le h 0) x) : MulAut X) =
          MulAut.conj (e.left x : X)) ∧
      (∀ x : parabolic L (reducedSylow L S) 1,
        (F.right (inclusion (reduced_parabolic_le h 1) x) : MulAut X) =
          MulAut.conj (e.right x : X)) ∧
      (∀ b : commonBorel L (reducedSylow L S),
        (F.middle (inclusion (reduced_commonBorel_le h) b) : MulAut X) =
          MulAut.conj (e.middle b : X)) := by
  obtain ⟨E,F,hl,hr,hb,_⟩ := Chapter5.Section03UnitaryFullNormalizer.extension_of_native_lift
    P Q B hPQ hgen hconj
    (parabolic L (reducedSylow L S) 0) (parabolic L (reducedSylow L S) 1)
    (parabolic L S 0) (parabolic L S 1) (commonBorel L S) (commonBorel L (reducedSylow L S))
    (reduced_parabolic_le h 0) (reduced_parabolic_le h 1)
    (commonBorel_le_parabolic 0) (commonBorel_le_parabolic 1)
    (reduced_commonBorel_le h) (reduced_parabolic_inf_borel h 0) (reduced_parabolic_inf_borel h 1)
    (NativeFlag.original_product h 0) (NativeFlag.original_product h 1) e.left e.right e.middle
    (fun b => congrArg Subtype.val (e.left_commutes b))
    (fun b => congrArg Subtype.val (e.right_commutes b))
    (NativeFlag.action h P Q B hBP hBQ hgen hlift e)
    (NativeFlag.action_injective h P Q B hBP hBQ hgen hlift e)
    (NativeFlag.action_inner h P Q B hBP hBQ hgen hlift e hflag)
    (NativeFlag.action_reduced h P Q B hBP hBQ hgen hlift e)
    (NativeFlag.action_left h P Q B hBP hBQ hgen hlift e)
    (NativeFlag.action_right h P Q B hBP hBQ hgen hlift e)
  exact ⟨E,F,hl,hr,fun b => (hb _).trans (NativeFlag.action_reduced h P Q B hBP hBQ hgen hlift e b)⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
