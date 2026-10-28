module
public import CFSG.Quasithin.ChapterC.Section06.Original.Definitions
public import Theory.GroupTheory.SubgroupEnumerationBinary
public import Mathlib.Order.Atoms.Finite

/-!
# Original C.6 normalizer control gives the C.5 configuration

Choose an index-two overgroup of the actual Sylow intersection in Λ.
The source normalizer condition excludes every nontrivial subgroup normal
in both this overgroup and H; the two-residual supplements the Sylow
subgroup. This constructs every C.5.1 field except its unique-maximal
property, which is supplied separately by the quotient models.

Source: Aschbacher--Smith C.6.1, printed pp.164--165.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section06.Original
variable {G : Type*} [Group G] [Finite G] {H Λ : Subgroup G}

theorem Input.exists_index_two_overgroup (d : Input H Λ) :
    ∃ M : Subgroup G, Λ ⊓ H ≤ M ∧ M ≤ Λ ∧ (Λ ⊓ H).relIndex M = 2 := by
  have hR : (Λ ⊓ H).subgroupOf Λ < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    exact fun he => d.proper.not_ge (subgroupOf_eq_top.mp he)
  obtain ⟨X,hX,_⟩ := exists_covBy_le_of_lt hR
  have hi := SubgroupEnumeration.relIndex_two_of_covBy d.two hX
  refine ⟨X.map Λ.subtype,?_,map_subtype_le _,?_⟩
  · rw [←map_subgroupOf_eq_of_le (inf_le_left : Λ ⊓ H ≤ Λ)]
    exact map_mono hX.le
  · have he := relIndex_map_map_of_injective ((Λ ⊓ H).subgroupOf Λ) X Λ.subtype_injective
    rw [map_subgroupOf_eq_of_le (inf_le_left : Λ ⊓ H ≤ Λ)] at he
    exact he.trans hi

theorem Input.original_hypotheses (d : Input H Λ)
    (hu : Order.HasUniqueMaximalOver (d.sylow : Subgroup H) ⊤)
    (M : Subgroup G) (hRM : Λ ⊓ H ≤ M) (hMΛ : M ≤ Λ)
    (hi : (Λ ⊓ H).relIndex M = 2) :
    Nonempty (Section05.BlockAnalysis.OriginalHypotheses H M
      ((pResidual 2 H).map H.subtype) (Λ ⊓ H) (Λ ⊓ H)) := by
  let R := Λ ⊓ H
  let K := (pResidual 2 H).map H.subtype
  have hn : (R.subgroupOf M).Normal := normal_of_index_eq_two hi
  have hMR : M ≤ normalizer (R : Set G) := (normal_subgroupOf_iff_le_normalizer hRM).mp hn
  have hRH : R ⊔ K = H := by
    have hh := congrArg (Subgroup.map H.subtype) (pResidual_sup_sylow_eq_top d.sylow)
    simpa only [Subgroup.map_sup,d.intersection,←MonoidHom.range_eq_map,range_subtype,sup_comm] using hh
  have hS : ∃ S : Sylow 2 (R ⊔ K : Subgroup G),
      (S : Subgroup (R ⊔ K : Subgroup G)).map (R ⊔ K).subtype = R := by
    rw [hRH]
    exact ⟨d.sylow,d.intersection⟩
  obtain ⟨S,hS⟩ := hS
  refine ⟨{ fitting := d.fitting
            sylow := d.sylow
            sylow_image := d.intersection
            unique := hu
            residual := rfl
            R_le := le_rfl
            T_le := hRM
            R_normal := hMR
            residual_sylow := S
            residual_sylow_image := hS
            no_common_normal := ?_ }⟩
  intro W hWR hWnormal
  by_contra hW
  have hw : M ⊔ H ≤ normalizer (W : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (hWR.trans (hRM.trans le_sup_left))).mp hWnormal
  have hc := d.control W hW hWR (le_sup_right.trans hw)
  have he : M ≤ R := (le_inf hMΛ (le_sup_left.trans hw)).trans hc.le
  have hh : R.relIndex M = 1 := relIndex_eq_one.mpr he
  change R.relIndex M = 2 at hi
  omega

theorem Input.exists_c5_configuration (d : Input H Λ)
    (hu : Order.HasUniqueMaximalOver (d.sylow : Subgroup H) ⊤) :
    ∃ M : Subgroup G, Λ ⊓ H ≤ M ∧ M ≤ Λ ∧ (Λ ⊓ H).relIndex M = 2 ∧
      Nonempty (Section05.BlockAnalysis.OriginalHypotheses H M
        ((pResidual 2 H).map H.subtype) (Λ ⊓ H) (Λ ⊓ H)) := by
  obtain ⟨M,hRM,hMΛ,hi⟩ := d.exists_index_two_overgroup
  exact ⟨M,hRM,hMΛ,hi,d.original_hypotheses hu M hRM hMΛ hi⟩
end CFSG.Quasithin.ChapterC.Section06.Original
