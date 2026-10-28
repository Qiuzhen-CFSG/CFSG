module
public import Theory.SpecificGroups.Triality.ShortRootCentralizer.Faithful
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityShortCentralizer.Action

/-!
# The faithful plane action in the original prepared triality row

The native PSL₂(q) action transports along the original central endpoint
into the actual characteristic plane in O₂(L). The resulting faithful
homomorphism has a pointwise ambient conjugation equation; no abstract
representation or action premise is assumed. The prepared context supplies
m=n>1, including q=4.

Source: the nonunitary triality case of Aschbacher--Smith F.4.42,
printed p.295, applied in 5.3.3, p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open _root_.Triality.Standard.ShortRootCentralizer
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem faithful_image (m : ℕ) (hm : 0 < m) (hm2 : 1 < m)
    (f : parabolic (binaryParameters m hm) .central →* G) (hf : Function.Injective f) :
    let P := binaryParameters m hm
    ∃ k : plane P ≃* TrialityShortAction.plane f,
      ∃ ρ : PSL(2,GaloisField P.prime P.exponent) →* MulAut (TrialityShortAction.plane f),
        Function.Injective ρ ∧
        (∀ v, (k v).val = f ⟨v.val,
          radical_le_parabolic P .central (plane_le_radical P v.property)⟩) ∧
        (∀ a : levi P .central, ∀ v : plane P,
          (ρ (leviCentralEquivPSL2 P rfl a) (k v)).val =
            f ⟨a.val,levi_le_parabolic P .central a.property⟩ * (k v).val *
              (f ⟨a.val,levi_le_parabolic P .central a.property⟩)⁻¹) := by
  let P := binaryParameters m hm
  have hP : plane P ≤ parabolic P .central :=
    (plane_le_radical P).trans (radical_le_parabolic P .central)
  let k : plane P ≃* TrialityShortAction.plane f :=
    (subgroupOfEquivOfLe hP).symm.trans
      (((plane P).subgroupOf (parabolic P .central)).equivMapOfInjective f hf)
  obtain ⟨r,hr,he⟩ := plane_faithful_psl2 m hm hm2
  let ρ := (MulAut.congr k).toMonoidHom.comp r
  refine ⟨k,ρ,(MulAut.congr k).injective.comp hr,fun _ => rfl,?_⟩
  intro a v
  change (k (r (leviCentralEquivPSL2 P rfl a) (k.symm (k v)))).val = _
  rw [k.symm_apply_apply]
  change f ⟨(r (leviCentralEquivPSL2 P rfl a) v).val,_⟩ =
    f ⟨a.val,levi_le_parabolic P .central a.property⟩ *
      f ⟨v.val,hP v.property⟩ *
        (f ⟨a.val,levi_le_parabolic P .central a.property⟩)⁻¹
  rw [←map_inv,←map_mul,←map_mul]
  exact congrArg f (Subtype.ext (he a v))

/-- The original characteristic plane carries the faithful central PSL₂(q)
action, with its actual ambient conjugation equation. -/
theorem Preparation.triality_short_plane_faithful_psl2
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse) :
    let P := binaryParameters m hm
    let f := (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0).subtype.comp
      e.left.symm.toMonoidHom
    TrialityShortAction.plane f = (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype ∧
    ∃ k : plane P ≃* TrialityShortAction.plane f,
      ∃ ρ : PSL(2,GaloisField P.prime P.exponent) →* MulAut (TrialityShortAction.plane f),
        Function.Injective ρ ∧
        (∀ v, (k v).val = f ⟨v.val,
          radical_le_parabolic P .central (plane_le_radical P v.property)⟩) ∧
        (∀ a : levi P .central, ∀ v : plane P,
          (ρ (leviCentralEquivPSL2 P rfl a) (k v)).val =
            f ⟨a.val,levi_le_parabolic P .central a.property⟩ * (k v).val *
              (f ⟨a.val,levi_le_parabolic P .central a.property⟩)⁻¹) := by
  have hp2 := (d.triality_local_structure h hH.1.1.2 hp m hm e).2.1
  have hplane := (d.triality_short_centralizer_of_long_unique_fixed h hH hp m hm e).2.2.1
  exact ⟨hplane,faithful_image m hm hp2 _
    ((ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0).subtype_injective.comp
      e.left.symm.injective)⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
