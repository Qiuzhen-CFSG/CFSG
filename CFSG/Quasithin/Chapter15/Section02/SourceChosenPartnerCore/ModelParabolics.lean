module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.ParabolicTransport
public import Theory.Representation.SmallDisplacementParabolics.Construction
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Applying the complete model calculation in the original partner quotient

The residual--Sylow supplement places H in the actual L = KcT. Restricting
L → L/O₂(L) to H has two-group kernel, so the image X has the same two-core
quotient as H. This proves the required S₃ wreath quotient without identifying
X itself with that quotient. The model theorem then constructs the moving
parabolic, and the existing literal quotient transport yields the contradiction.

The faithful chief model and its nonzero H-fixed projection of the source plane
remain explicit inputs. Their construction and the final 15.2.27(2) assembly
belong to qt-e-152-critical-pair. No parabolic existence or movement is assumed.

Source: Aschbacher--Smith, original 15.2.27(2), printed p.1119 (PDF p.1136).
-/

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChosenGeometry
open Representation.SmallDisplacementParabolics
variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The source H lies in the residual span joined with the original Sylow. -/
theorem source_chosen_local_le_partner_join {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (hg : ChosenPlaneGeometry h H ZS) :
    H ≤ partnerSpan H Mc ⊔ (T : Subgroup G) := by
  have hTH : (T : Subgroup G) ≤ H := hg.outside.1.1.2
  have he := congrArg (Subgroup.map H.subtype)
    (pResidual_sup_sylow_eq_top (T.subtype hTH))
  have ht : Subgroup.map H.subtype (T.subtype hTH : Subgroup H) =
      (T : Subgroup G) := by
    change ((T : Subgroup G).subgroupOf H).map H.subtype = (T : Subgroup G)
    exact map_subgroupOf_eq_of_le hTH
  calc
    H = ChosenGeometry.residual H ⊔ (T : Subgroup G) := by
      simpa only [Subgroup.map_sup, ht, ChosenGeometry.residual, ← MonoidHom.range_eq_map,
        H.range_subtype] using he.symm
    _ ≤ partnerSpan H Mc ⊔ (T : Subgroup G) :=
      sup_le_sup (le_conjugateSpanBy (ChosenGeometry.residual H) Mc) le_rfl

private theorem core_quotient_equiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    Nonempty ((A ⧸ pCore 2 A) ≃* (B ⧸ pCore 2 B)) := by
  let q := (QuotientGroup.mk' (pCore 2 B)).comp f
  have hq : q.ker = pCore 2 A := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact f.comap_pCore_of_ker_isPGroup hf hk
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hq.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q
      ((QuotientGroup.mk'_surjective _).comp hf))⟩

/-- The actual H-image has the source wreath quotient by its own two-core. -/
theorem source_chosen_partner_image_quotient {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (hg : ChosenPlaneGeometry h H ZS) :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    let X := (H.subgroupOf L).map (QuotientGroup.mk' (pCore 2 L))
    Nonempty ((X ⧸ pCore 2 X) ≃* RegularWreathProduct (Equiv.Perm (Fin 3)) PairIndex) := by
  dsimp only
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 L)
  let H₀ := H.subgroupOf L
  let X := H₀.map q
  let f := q.subgroupMap H₀
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 (q.subgroupMap H₀).ker
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  obtain ⟨eX⟩ := core_quotient_equiv f (q.subgroupMap_surjective H₀) hk
  let eH : H₀ ≃* H := subgroupOfEquivOfLe (source_chosen_local_le_partner_join hg)
  let eQ := QuotientGroup.congr (pCore 2 H₀) (pCore 2 H) eH (pCore_map_iso 2 eH)
  obtain ⟨e⟩ := hg.quotient
  exact ⟨eX.symm.trans (eQ.trans e)⟩

/-- The recognized chief action supplies the source contradiction, with the
literal H-image quotient and moving parabolic both constructed here. -/
theorem source_chosen_false_of_partner_actionModel
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hplane : ∀ J ∈ Chapter3.HStar (T : Subgroup G) M,
      residual J ≤ centralizer (ZS : Set G)) :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 L)
    let X := (H.subgroupOf L).map q
    ∀ (ρ : Representation (ZMod 2) (L ⧸ pCore 2 L) W) (w : W), w ≠ 0 →
      ActionModel ρ →
      (∀ g : L, (g : G) ∈ centralizer (ZS : Set G) → ρ (q g) w = w) →
      (∀ g ∈ X, ρ g w = w) → False := by
  dsimp only
  intro ρ w hw hmodel hfix hXfix
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 L)
  let S := (T.subtype (show (T : Subgroup G) ≤ L from le_sup_right)).mapSurjective
    (QuotientGroup.mk'_surjective (pCore 2 L))
  let X := (H.subgroupOf L).map q
  have hSX : (S : Subgroup (L ⧸ pCore 2 L)) ≤ X :=
    map_mono (comap_mono hg.outside.1.1.2)
  obtain ⟨d⟩ := exists_of_actionModel ρ hmodel S X hSX
    (source_chosen_partner_image_quotient hg) w hw hXfix
  exact source_chosen_false_of_partner_core_quotient h hg hMc hplane ρ w hfix d

end CFSG.Quasithin.Chapter15.Section02
