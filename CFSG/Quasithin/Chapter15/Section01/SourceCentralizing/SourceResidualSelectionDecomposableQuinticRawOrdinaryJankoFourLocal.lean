module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawNormalizerQuotient
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.MathieuTwentyFour

/-! A literal characteristic-two local-family member with M24 core quotient
lies in the marked local. Its original seed action supplies B.5; simplicity
makes the central core comparison faithful, contradicting the model list. -/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G]

/-- The raw local M24 member is contained in the original marked subgroup.
Escape from M is derived from perfection and the original local module. -/
theorem PreparedChosenModule.raw_local_mathieuTwentyFour_le_marked
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 K : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hK : K ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hf : generalizedFitting K = pCore 2 K)
    (e : (K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24) :
    K ≤ centralizer (Z1 : Set G) ⊓ Mc := by
  by_contra hout
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  have houtM : ¬K ≤ M := by
    intro hKM
    let : Group.IsPerfect (K.subgroupOf (K ⊔ S)) := hK.2.1.perfect
    let i : K.subgroupOf (K ⊔ S) ≃* K := subgroupOfEquivOfLe le_sup_left
    let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := i.toMonoidHom) i.surjective
    exact hout (le_inf hK.1
      ((perfect_subgroup_centralizes_localModule hG T hempty hM hKM).trans
        (localModule_centralizer_le_partner T M hu)))
  let H := K ⊔ (S ⊓ normalizer (K : Set G))
  let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
  let C := centralizer (W : Set H)
  let q := QuotientGroup.mk' C
  let I := (K.subgroupOf H).map q
  obtain ⟨hr,_,_,hquasi,_,hIJ,⟨c⟩⟩ :=
    h.raw_component_normalizer_source hG T hM hJ hu hZ hZne hK hq hf hout houtM
  let := hr.elementary
  have hm : StarModels.Model I :=
    StarModels.model_of_source _ (subgroupOfEquivOfLe hIJ).symm c
  obtain ⟨_,f,_,_,_,hfs,_,_⟩ :=
    h.raw_component_normalizer_quotient hG T hM hJ hu hZ hZne hK hq hf hout houtM
  let := Sporadic.Mathieu.m24_isSimpleGroup
  let : IsSimpleGroup (K ⧸ pCore 2 K) := e.isSimpleGroup
  let : IsQuasisimple I := hquasi
  let : IsSimpleGroup (I ⧸ center I) := IsQuasisimple.simple
  let : Nontrivial I := (QuotientGroup.mk'_surjective (center I)).nontrivial
  have hi : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    rcases f.normal_ker.eq_bot_or_eq_top with hb | ht
    · exact hb
    · have he := f.ker_eq_top_iff.mp ht
      obtain ⟨x,hx⟩ := exists_ne (1 : I)
      obtain ⟨y,rfl⟩ := hfs x
      exact (hx (by rw [he]; rfl)).elim
  exact StarModels.not_mathieuTwentyFour hm
    ((MulEquiv.ofBijective f ⟨hi,hfs⟩).symm.trans e)

end CFSG.Quasithin.Chapter15.Section01
