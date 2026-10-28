module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityShortCentralizer.ActionModel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityShortCentralizer.Sylow

/-!
# The long-root plane in the original prepared triality row

The original left endpoint identifies the central radical with O₂(L).
Consequently its center is the characteristic long-root plane constructed
in the native short-root centralizer. The whole Borel identifies both
pinned roots with their original right-endpoint markings. The perfect
central Levi action and I.8.5 reduce ambient containment to the pinned
long root's unique fixed coset in the actual C_G(t)/C_{N_G(L)}(t).

This is a conditional intermediate step of Aschbacher–Smith F.4.42,
printed p.295, used in 5.3.3, p.659 (`refs/quasithin.pdf`). The unique
fixed coset is not proved here; the original F.4.42 goal remains separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.RadicalCoordinates Triality.Standard.RadicalCoordinates.LeviCommutators
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

private theorem triality_long_eq_highest (P : Parameters) (hp : P.prime = 2) (a : fixedField P) :
    long P hp 2 a = RadicalCoordinates.Centers.highestHom P hp (Multiplicative.ofAdd a) := by
  apply congrArg (toCarrier P)
  apply Subtype.ext
  apply Subtype.ext
  exact longElementary_val P hp 2 a

/-- The actual central radical yields the characteristic long-root plane.
I.8.5 reduces full ambient short-root containment to the pinned long root's
unique fixed coset, with all action hypotheses proved. -/
theorem Preparation.triality_short_centralizer_of_long_unique_fixed
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
    let v : G := f (TrialityShortAction.short P rfl)
    v = (e.right.symm (TrialityCompletionFusion.shortElement P rfl)).val ∧
      (TrialityShortAction.longMark rfl f).val =
        (e.right.symm (TrialityCompletionFusion.longElement P rfl)).val ∧
      TrialityShortAction.plane f = (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype ∧
      ((∃! q : centralizer ({v} : Set G) ⧸ (normalizer (L : Set G)).subgroupOf
          (centralizer ({v} : Set G)), TrialityShortAction.longMark rfl f • q=q) →
      centralizer ({v} : Set G) ≤ normalizer (L : Set G)) := by
  let P := binaryParameters m hm
  let X := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let f := X.subtype.comp e.left.symm.toMonoidHom
  have hf : Function.Injective f := X.subtype_injective.comp e.left.symm.injective
  have hm2 := (d.triality_local_structure h hH.1.1.2 hp m hm e).2.1
  have hq : 2 < P.q := Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) hm2
  let J := (localFactor P .central).subgroupOf (parabolic P .central)
  have hJ : J = solvableResidual (parabolic P .central) := by
    apply map_injective (parabolic P .central).subtype_injective
    rw [map_subgroupOf_eq_of_le (localFactor_le_parabolic P .central),
      parabolic_solvableResidual_map P rfl hq .central]
  have hJf : J.map f = L := by
    rw [hJ,show f=X.subtype.comp e.left.symm.toMonoidHom from rfl,
      ←map_map,map_solvableResidual_eq e.left.symm.toMonoidHom e.left.symm.surjective]
    exact d.parabolic_residuals h hH.1.1.2 hp 0
  have hQ : ((radical P .central).subgroupOf (parabolic P .central)).map f=L.pCoreIn 2 := by
    have hh := map_pCoreIn_of_injective 2 J f hf
    rw [hJf,pCoreIn_subgroupOf 2 (localFactor P .central) (parabolic P .central)
      (localFactor_le_parabolic P .central)] at hh
    change (((pCore 2 (localFactor P .central)).map (localFactor P .central).subtype).subgroupOf
      (parabolic P .central)).map f=L.pCoreIn 2 at hh
    rw [localFactor_twoCore_map P rfl .central] at hh
    exact hh
  have hplane : TrialityShortAction.plane f=(center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype := by
    rw [TrialityShortAction.plane_center f hf,hQ]
  have hN : f.range ≤ normalizer (L : Set G) := by
    rintro _ ⟨x,rfl⟩
    exact (d.triality_normalizer_local_data h hH hp m hm e).left_le (e.left.symm x).property
  have hn : normalizer (L : Set G) ≤
      normalizer (((radical P .central).subgroupOf (parabolic P .central)).map f : Set G) := by
    rw [hQ]
    exact normalizer_le_normalizer_characteristic_image L (pCore 2 L)
  have hv : f (TrialityShortAction.short P rfl) =
      (e.right.symm (TrialityCompletionFusion.shortElement P rfl)).val := by
    let b : borel P := ⟨short P rfl 2 1,unipotent_le_borel P (by
      apply descendSubgroup_mono P (rootSubgroup_le_positiveSubgroup P rfl .central)
      exact short_mem P rfl .central 2 trivial 1)⟩
    exact (congrArg Subtype.val (e.symm.left_commutes b)).trans
      (congrArg Subtype.val (e.symm.right_commutes b)).symm
  have hz : (TrialityShortAction.longMark rfl f).val =
      (e.right.symm (TrialityCompletionFusion.longElement P rfl)).val := by
    let b : borel P := ⟨long P rfl 2 1,unipotent_le_borel P (by
      apply descendSubgroup_mono P (rootSubgroup_le_positiveSubgroup P rfl .arms)
      exact long_mem P rfl .arms 2 trivial 1)⟩
    have he : (e.left.symm (TrialityShortAction.long P rfl)).val =
        (e.right.symm ⟨long P rfl 2 1,borel_le_parabolic P .arms b.property⟩).val :=
      (congrArg Subtype.val (e.symm.left_commutes b)).trans
        (congrArg Subtype.val (e.symm.right_commutes b)).symm
    exact he.trans (congrArg (fun a => (e.right.symm a).val)
      (Subtype.ext (triality_long_eq_highest P rfl 1)))
  exact ⟨hv,hz,hplane,
    TrialityShortAction.centralizer_le_of_long_unique_fixed m hm hm2 f hf
      (normalizer (L : Set G)) hN hn⟩
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
