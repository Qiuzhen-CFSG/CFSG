module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.ResidualBenderCenter
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentModels.OriginalImage
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedBender.Placement
public import Theory.GroupTheory.GeneralizedFitting.SylowCentralizerSchreier

/-!
# Residual-fixed center points for any Bender component

A central element of the source maximal subgroup normalizes an even simple
component because it fixes its Sylow subgroup. The literal Borel intersection
and pointwise Borel rigidity then make it centralize that component. It also
centralizes the chosen Sylow; together they generate the whole group, whose
solvable radical is trivial. Thus no nontrivial central point survives.

The original-source consumer applies this to the actual image in H/J and
excludes both normal and exchanged Bender components from residual centralization.
Source: Aschbacher--Smith E.2.17, printed p.230, using E.2.2 and E.2.7.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Witnesses.PairedBender
variable {H : Type*} [Group H] [Finite H]

theorem component_bender_center_point_eq_one
    (hH : IsStronglyQuasithin H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hrad : solvableRadical H = ⊥)
    (K : Subgroup H) (hK : IsComponent H K) [IsSimpleGroup K]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : ClassificationModels.IsBenderModel K)
    (z : H)
    (hzM : z ∈ (center (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype) : z = 1 := by
  let M := ChapterB.minimalParabolicMax T hP
  have hTM : (T : Subgroup H) ≤ M := (ChapterB.minimalParabolicMax_spec T hP).2
  obtain ⟨zz,hzz,hzzG⟩ := hzM
  have hfix : ∀ x ∈ M, x*z=z*x := by
    intro x hx
    have hh := congrArg Subtype.val (mem_center_iff.mp hzz (⟨x,hx⟩ : M))
    change x*(zz:H)=(zz:H)*x at hh
    change (zz:H)=z at hzzG
    rwa [hzzG] at hh
  let := hK.2
  have heven : 2 ∣ Nat.card K := by
    by_contra hn
    have hodd : Odd (Nat.card K) := Nat.not_even_iff_odd.mp (by
      simpa only [even_iff_two_dvd] using hn)
    exact Group.IsPerfect.not_isSolvable K (odd_order_theorem K hodd)
  have hKz : center K = ⊥ := center_eq_bot_of_isSubnormal_of_solvableRadical_eq_bot hrad hK.1
  obtain ⟨S,hS⟩ := T.exists_subgroupOf_eq_of_subnormal K hK.1
  have hdiv : 2 ∣ Nat.card (K ⧸ center K) := by
    rw [hKz,Nat.card_congr QuotientGroup.quotientBot.toEquiv]
    exact heven
  have hzN : z ∈ normalizer (K : Set H) := hK.centralizer_sylow_le_normalizer S hdiv (by
    rintro x ⟨s,hs,rfl⟩
    have hsT : (s:H) ∈ T := show s ∈ (T : Subgroup H).subgroupOf K from hS ▸ hs
    exact hfix s (hTM hsT))
  have hmodel : ChapterF.Source.IsRankOneModel K := by
    cases hm with
    | linear n hn h => exact .linear n (by omega) h
    | unitary n hn h => exact .projective_unitary n (by omega) h
    | suzuki m _ h => exact .suzuki m h
  have hB := component_borel_intersection T hP K hK heven
    (Structure.generating_component_orbit_eq_residual hH T hK hgen) hmodel
  have hα : K.normalizerMonoidHom ⟨z,hzN⟩ = 1 := by
    apply Structure.bender_pointwise_borel_eq_one hm S
    intro d hd
    have hdM : (d:H) ∈ M := by
      change d ∈ M.subgroupOf K
      rw [hB,←hS]
      exact hd
    apply Subtype.ext
    change z * (d:H) * z⁻¹ = d
    rw [←hfix d hdM,mul_inv_cancel_right]
  have hzC : z ∈ centralizer (K : Set H) := by
    have hh : (⟨z,hzN⟩ : normalizer (K:Set H)) ∈ K.normalizerMonoidHom.ker := hα
    rw [normalizerMonoidHom_ker] at hh
    exact hh
  have hzall : (⊤ : Subgroup H) ≤ centralizer ({z} : Set H) := by
    rw [←hgen]
    apply sup_le
    · intro x hx
      exact mem_centralizer_singleton_iff.mpr (hzC x hx)
    · intro x hx
      exact mem_centralizer_singleton_iff.mpr (hfix x (hTM hx))
  have hzcenter : z ∈ center H := by
    exact mem_center_iff.mpr (fun x => mem_centralizer_singleton_iff.mp (hzall (mem_top x)))
  have hcenter : center H ≤ solvableRadical H := le_solvableRadical (center H)
    inferInstance (Group.isSolvable_of_comm (fun a b => Subtype.ext
      (Subgroup.mem_center_iff.mp a.property b).symm))
  exact mem_bot.mp (hrad ▸ hcenter hzcenter)


theorem source_original_component_bender_residual_exclusion
    {κ : GroupClass} (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : ClassificationModels.IsBenderModel
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))))
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hout : ¬V ≤ ChapterB.minimalParabolicCore T hP)
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H)) : False := by
  let J := ChapterB.minimalParabolicCore T hP
  let M := ChapterB.minimalParabolicMax T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let D := K.map q
  let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable T hP
  have hsX : ¬ Group.IsSolvable (H ⧸ J) := fun hx =>
    hs ((Group.isSolvable_iff_subgroup_quotient J).mpr ⟨inferInstance,hx⟩)
  have hi := Structure.source_component_simple_image T hP hs K hK hgen
  let : IsSimpleGroup D := hi.1
  have hmin := (Structure.source_star_minimal_core_free T hP).1
  have hcore : ChapterB.minimalParabolicCore S hmin = ⊥ :=
    (Structure.source_star_minimal_core_free T hP).2
  have hrad : solvableRadical (H ⧸ J) = ⊥ :=
    (ChapterB.minimalParabolic_nonsolvable_core_eq_radical S hmin hsX).symm.trans hcore
  have hmax : ChapterB.minimalParabolicMax S hmin = M.map q :=
    (ChapterB.minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'])).symm
  obtain ⟨v,_,hv,hvc⟩ := source_star_maximal_center_point T hP V hVT hvn hout hres
  apply hv
  apply component_bender_center_point_eq_one (Structure.source_star_sqtk hA hH T hP hs).stronglyQuasithin
    S hmin hrad D hi.2.1 hi.2.2.2 hm v
  rwa [hmax]

end CFSG.Quasithin.ChapterE.Witnesses.PairedBender
