module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.TitsSourceLocals
public import Stellmacher.Recognition.Parrott.LocalGeneratorConstruction.SylowNormalization
public import Stellmacher.Recognition.Parrott.LocalNormalizer.Fusion
public import Stellmacher.Recognition.Parrott.SylowPresentation
public import Theory.SpecificGroups.Tits.FirstParabolicCoordinates

/-!
# Sylow coordinates conditional on the intrinsic centralizer input

Parrott's local construction gives a normalized frame and the eight-word
calculation gives its Sylow coordinates. Conjugacy inside C_G(z) puts them
in the prescribed Sylow subgroup, preserving the literal central element z.
The original empty faithful family discharges the local solvability inputs.

The source reconstruction of the intrinsic centralizer hypotheses remains
open: core order 512, class at least three, the faithful C5:C4 quotient,
and the five-centralizer condition. No parabolic equivalence is an input to
this reduction, and it does not claim to establish those missing facts.

Source: Aschbacher--Smith14.2.20--21, pp.988--989, and Parrott (1972),
pp.672 and678--684.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
open Tits.FirstParabolicCoordinates
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private def transport {A B : Type*} [Group A] [Group B]
    {S : Subgroup A} {R : Subgroup B} (d : SylowCoordinates S) (f : S ≃* R) :
    SylowCoordinates R where
  s := fun i => f (d.s i)
  relations := d.relations.map f.toMonoidHom
  generates := by
    have h := congrArg (Subgroup.map f.toMonoidHom) d.generates
    rw [MonoidHom.map_closure, ← Set.range_comp, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr f.surjective] at h
    exact h

/-- Construct all eight generators in the prescribed Sylow from the intrinsic
centralizer conditions. Conjugation stays inside C_G(z), so r5 remains z. -/
theorem source_sylow_coordinates_of_parrott
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (z : G) (hz : z ∈ centralInvolutions T)
    (hp : Recognition.ParrottCentralizerHypotheses z) :
    ∃ d : SylowCoordinates (T.subtype hTH : Subgroup H),
      r5 (fun i => ((d.s i : H) : G)) = z := by
  let : IsSimpleGroup G := hG.simple
  have hns : ¬ Group.IsSolvable G := fun hs =>
    hG.nonabelian (isMulCommutative_iff.mpr (IsSimpleGroup.comm_iff_isSolvable.mpr hs))
  have hsol := sylow_local_solvable_of_empty_faithful_of_solvable_centralizer
    hG T hempty z hz (hp.card_and_solvable z).2
  let hlocal : Recognition.ParrottLocalInputs z := {
    derived_normalizer := parrott_derived_normalizer_of_sylow_local_solvability z hp hsol
    second_normalizer_solvable := fun d =>
      parrott_second_normalizer_solvable_of_sylow_local_solvability z d hsol }
  obtain ⟨d, ⟨n⟩⟩ := Recognition.parrott_normalizer_fusion_exists_of_local_inputs hns hp hlocal
  obtain ⟨f⟩ := n.exists_sylow_generators_of_local_inputs hns hlocal hp
  let C := centralizer ({z} : Set G)
  have hTC : (T : Subgroup G) ≤ C := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr
      (((mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp hz).2.2 t ht)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C d.localSylow (T.subtype hTC)
  have hg' : (d.localSylow : Subgroup C).map (MulAut.conj g).toMonoidHom =
      (T.subtype hTC : Subgroup C) := congrArg (fun S : Sylow 2 C => (S : Subgroup C)) hg
  have hcomp : C.subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (g : G)).toMonoidHom.comp C.subtype := by ext; rfl
  have hmap : (d.sylow : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom =
      (T : Subgroup G) := by
    rw [d.sylow_map, map_map, ← hcomp, ← map_map, hg', Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTC]
  let q : (d.sylow : Subgroup G) ≃* (T : Subgroup G) :=
    (equivMapOfInjective _ (MulAut.conj (g : G)).toMonoidHom
      (MulAut.conj (g : G)).injective).trans (MulEquiv.subgroupCongr hmap)
  let qH : (d.sylow : Subgroup G) ≃* (T.subtype hTH : Subgroup H) :=
    q.trans (subgroupOfEquivOfLe hTH).symm
  refine ⟨transport f.sylowCoordinates qH, ?_⟩
  change r5 (fun i => (MulAut.conj (g : G)) (f.sylowWords i)) = z
  rw [show r5 (fun i => (MulAut.conj (g : G)) (f.sylowWords i)) =
    (MulAut.conj (g : G)) (r5 f.sylowWords) by simp only [r5, map_mul, map_pow]]
  rw [f.sylowWords_r5]
  change (g : G) * z * (g : G)⁻¹ = z
  rw [mem_centralizer_singleton_iff.mp g.property, mul_inv_cancel_right]

/-- The literal HStar consumer leaves only the intrinsic centralizer input.
The final source theorem must construct that input before this task is complete. -/
theorem source_sylow_coordinates_of_intrinsic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (H : Subgroup G)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hintrinsic : ∃ z : G, zpowers z = centralInvolutions T ∧
      Recognition.ParrottCentralizerHypotheses z) :
    Nonempty (SylowCoordinates (T.subtype hH.1.1.2 : Subgroup H)) := by
  obtain ⟨z, hz, hp⟩ := hintrinsic
  obtain ⟨d, _⟩ := source_sylow_coordinates_of_parrott hG T hempty H hH.1.1.2 z
    (hz ▸ mem_zpowers z) hp
  exact ⟨d⟩

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic
