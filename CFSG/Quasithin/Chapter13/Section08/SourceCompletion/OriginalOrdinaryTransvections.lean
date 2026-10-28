module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OriginalTransvection

/-!
# The original ordinary transvection actor has order 720

The source recognition theorem gives the whole actor on the literal quotient.
An ordinary local A₆ quotient excludes the covered alternative by its center.
Both remaining full module models have the same symmetric six-point actor.
Consequently a larger original quotient actor has no rank-one displacement.
This supplies the strict critical case without a universal local-input family.
Source: Aschbacher--Smith 13.8.5 and its uses in 13.8.24--25,
printed pp.947--948,958--960.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension

private theorem rank_one_transvection
    {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) A E) (g : A)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) = 1) :
    IsTransvection ρ g := by
  let t := LinearEquiv.ofBijective (ρ g) (ρ.apply_bijective g)
  obtain ⟨f,v,he⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr
    (show Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) ≤ 1 from hr.le)
  have hact (w : E) : ρ g w = w + f w • v := LinearMap.congr_fun he w
  have hne : ρ g ≠ LinearMap.id := by
    intro h
    rw [h,sub_self,LinearMap.range_zero,finrank_bot] at hr
    contradiction
  have hf : f ≠ 0 := by
    intro h
    apply hne
    ext w
    simpa [h] using hact w
  have hv : v ≠ 0 := by
    intro h
    apply hne
    ext w
    simpa [h] using hact w
  have hfv : f v = 0 := by
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (f v) with h | h
    · exact h
    · have htv : t v = 0 := by
        change ρ g v = 0
        rw [hact,h,one_smul,ZModModule.add_self]
      exact (hv (t.map_eq_zero_iff.mp htv)).elim
  exact ⟨f,v,hf,hv,hfv,hact⟩


universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- A transvection at the original ordinary source forces the whole actor
H/O₂(H) to have order 720. -/
theorem original_transvection_star_card
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9all : ∀ J ∈ Source.Hz (sourceOne L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M) :
    let := d.uh_elementary hH
    ∀ (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁))),
      IsConjugation H V₃ V₁ ρ → (∃ t, IsTransvection ρ t) →
      Nat.card (Source.Hstar H) = 720 := by
  let := d.uh_elementary hH
  dsimp only
  intro ρ hρ ht
  have full := (original_transvection_recognition_of_plane_noncentral
    d eL hmax hF9all hm hH ρ hρ ht).2
  rcases full with ⟨hmodel,_,_⟩ | ⟨_,⟨eHex⟩⟩
  · rcases hmodel with ⟨eA,_⟩ | ⟨⟨eA,_⟩,_⟩ <;>
      rw [Nat.card_congr eA.toEquiv] <;>
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  · have hc := Nat.card_congr (centerCongr (eHex.symm.trans eL)).toEquiv
    rw [Representation.Hexacode.even_center_card,
      alternatingGroup.center_eq_bot (by simp), card_bot] at hc
    omega

/-- A larger actual quotient actor cannot have rank-one displacement on
its literal original U_H/V₁. -/
theorem original_no_rank_one_of_star_card_gt720
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9all : ∀ J ∈ Source.Hz (sourceOne L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hcard : 720 < Nat.card (Source.Hstar H)) :
    let := d.uh_elementary hH
    ∀ (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁))),
      IsConjugation H V₃ V₁ ρ → ∀ g,
      Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) ≠ 1 := by
  let := d.uh_elementary hH
  dsimp only
  intro ρ hρ g hg
  have hc := original_transvection_star_card d eL hmax hF9all hm hH ρ hρ
    ⟨g,rank_one_transvection ρ g hg⟩
  omega

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
