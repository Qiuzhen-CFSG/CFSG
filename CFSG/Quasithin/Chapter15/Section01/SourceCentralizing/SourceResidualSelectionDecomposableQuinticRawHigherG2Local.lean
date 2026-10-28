module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawRankOneImage
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.HigherFieldApplications

/-! Nonshort local rank-one core quotients lie in the actual marked local.
The centerless core identifies the original normalizer image, whose genuine
seed reconstruction would otherwise make the same local member short. -/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- The original local-family member with a nonshort binary SL2 core
quotient lies in the marked subgroup; no placement premise is supplied. -/
theorem PreparedChosenModule.raw_nonshort_slTwo_le_marked
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 K : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hK : K ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hf : generalizedFitting K = pCore 2 K)
    (hnot : ¬IsShort K)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
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
  obtain ⟨_,f,_,_,_,hfs,hfc,_⟩ :=
    h.raw_component_normalizer_quotient hG T hM hJ hu hZ hZne hK hq hf hout houtM
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [Theory.GroupTheory.FixedElementary.map_center,
      Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot,Subgroup.map_bot]
  have hi : Function.Injective f := (MonoidHom.ker_eq_bot_iff _).mp
    (bot_unique (hfc.trans hz.le))
  let ei := MulEquiv.ofBijective f ⟨hi,hfs⟩
  rcases h.raw_rankOne_image_block hG T hM hJ hu hZ hZne hK hq hf hout houtM F
      (ei.symm.trans e) with ⟨n,hb⟩ | hb
  · exact hnot hb.2.1
  · exact hnot hb.2.1

/-- The native PSL2 formulation for the actual higher-field residuals. -/
theorem PreparedChosenModule.raw_nonshort_pslTwo_le_marked
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 K : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hK : K ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hf : generalizedFitting K = pCore 2 K) (hnot : ¬IsShort K)
    (n : ℕ) (hn : 1 < n) (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^n)) :
    K ≤ centralizer (Z1 : Set G) ⊓ Mc := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hfour : 3 < Nat.card F := by
    rw [hF]
    have hh : 2^2 ≤ 2^n := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
    omega
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) :=
    { toIsPerfect := GorensteinWalter.sl2_isPerfect_of_card_gt_three F hfour
      simple := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega) }
  let e0 := e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm
  have hq : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv e0.symm
  exact h.raw_nonshort_slTwo_le_marked hG T hempty hM hJ hu hZ hZne hK hq hf hnot F e0

end CFSG.Quasithin.Chapter15.Section01
