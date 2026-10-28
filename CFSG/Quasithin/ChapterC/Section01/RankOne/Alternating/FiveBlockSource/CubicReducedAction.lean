module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.CubicModule
public import Theory.GroupTheory.SylowIndexThreeQuotient
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure
public import Theory.GroupTheory.ReducedNormal.MovedCentralizer
/-!
# The canonical reduced action of an index-three Sylow local

Thompson movement excludes a normal Sylow. The three-coset action gives
G/O₂(G)=S₃. Reducedness and movement force the literal centralizer quotient
to have order six and C_G(U)=O₂(G). The actual solvable FF support then gives
Baumann Sylow and alpha, including the bound on the original moved module.
Source: Aschbacher–Smith C.1.21(4), C.1.23(1), printed pp.129–130.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
variable {G : Type*} [Group G] [Finite G]

/-- A moving reduced module at Sylow index three has the actual faithful
six-element action; neither the action order nor its kernel is assumed. -/
theorem reduced_index_three_action (T : Sylow 2 G)
    (hi : (T : Subgroup G).index = 3)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    Nat.card (G ⧸ centralizer (U : Set G)) = 6 ∧
      centralizer (U : Set G) = pCore 2 G ∧ Group.IsSolvable G := by
  let C := centralizer (U : Set G)
  let Q := pCore 2 G
  have hQC : Q ≤ C := le_centralizer_iff.mp hU.le_centralizer_pCore
  have hproper : Q < (T : Subgroup G) := by
    apply lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal T)
    intro he
    apply hJ
    have hjT : elementaryAbelianMaxJ (T : Subgroup G) ≤ T := sSup_le fun _ h => h.1
    exact hjT.trans (he ▸ hQC)
  obtain ⟨e⟩ := sylow_index_three_core_quotient T hi hproper
  have hsix : Nat.card (G ⧸ Q) = 6 := by
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  let q := QuotientGroup.mk' C
  let f := QuotientGroup.lift Q q (hQC.trans_eq (QuotientGroup.ker_mk' C).symm)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective C y
    exact ⟨QuotientGroup.mk' Q g,rfl⟩
  have hd : Nat.card (G ⧸ C) ∣ 6 := hsix ▸ card_dvd_of_surjective f hf
  let I := (elementaryAbelianMaxJ (T : Subgroup G)).map q
  have hIP : IsPGroup 2 I := (T.isPGroup'.to_le
    (sSup_le fun _ h => h.1 : elementaryAbelianMaxJ (T : Subgroup G) ≤ T)).map q
  have hnI : I ≠ ⊥ := by
    intro he
    apply hJ
    exact ((Subgroup.map_eq_bot_iff _).mp he).trans_eq (QuotientGroup.ker_mk' C)
  have htwo : 2 ∣ Nat.card (G ⧸ C) := by
    rcases hIP.card_eq_or_dvd with h1 | h2
    · have hh : 1 < Nat.card I := (one_lt_card_iff_ne_bot I).mpr hnI
      omega
    · exact h2.trans (card_subgroup_dvd_card I)
  have hc : Nat.card (G ⧸ C) = 6 := by
    have hle := Nat.le_of_dvd (by decide : 0 < 6) hd
    have hne2 : Nat.card (G ⧸ C) ≠ 2 := by
      intro he
      have hp : IsPGroup 2 (G ⧸ C) := IsPGroup.of_card (n:=1) (by simpa using he)
      have ht : (⊤ : Subgroup (G ⧸ C)) ≤ pCore 2 (G ⧸ C) :=
        le_sSup ⟨inferInstance,hp.to_subgroup ⊤⟩
      rw [hU.quotient_pCore_eq_bot] at ht
      have hh := congrArg (fun K : Subgroup (G ⧸ C) => Nat.card K) (le_antisymm ht bot_le)
      simp only [card_top,card_bot,he] at hh
      omega
    interval_cases hh : Nat.card (G ⧸ C) <;> simp_all
  have hfinj : Function.Injective f :=
    ((Nat.bijective_iff_surjective_and_card f).mpr ⟨hf,hsix.trans hc.symm⟩).1
  have hCQ : C ≤ Q := by
    intro c hc'
    apply (QuotientGroup.eq_one_iff c).mp
    apply hfinj
    exact (QuotientGroup.eq_one_iff c).mpr hc'
  exact ⟨hc,le_antisymm hCQ hQC,SymmetricThreeTwoCore.solvable e⟩
/-- At index three the original Sylow is the unique maximal overgroup;
movement excludes its normality. -/
theorem reduced_index_three_minimal (T : Sylow 2 G)
    (hi : (T : Subgroup G).index = 3)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    ChapterB.IsMinimalParabolicOver T ⊤ := by
  have ht : IsCoatom (T : Subgroup G) := by
    refine ⟨fun he => by simp [he] at hi,fun M hTM => ?_⟩
    have hd := index_dvd_of_le hTM.le
    rw [hi] at hd
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact index_eq_one.mp h1
    · have hh := index_strictAnti hTM
      omega
  apply ChapterB.isMinimalParabolicOver_top_iff T |>.mpr
  refine ⟨⟨T,⟨ht,le_rfl⟩,fun M hM => ?_⟩,?_⟩
  · exact (ht.le_iff_eq hM.1.1).mp hM.2
  · intro hn
    have hTQ : (T : Subgroup G) ≤ pCore 2 G := le_sSup ⟨hn,T.isPGroup'⟩
    apply hJ
    exact (sSup_le fun _ h => h.1).trans
      (hTQ.trans (le_centralizer_iff.mp hU.le_centralizer_pCore))

/-- The order, faithful quotient and natural module required in the cubic
Baumann argument follow from the original index-three reduced module. -/
theorem reduced_index_three_baumann (T : Sylow 2 G)
    (hi : (T : Subgroup G).index = 3)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    Chapter1.IsSylowIn 2 (ChapterB.baumann (T : Subgroup G))
      (pResidual 2 G ⊔ ChapterB.baumann (T : Subgroup G)) ∧
      ChapterB.thompsonAlpha (T : Subgroup G) =
        (ChapterB.thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) ⊔
          (U ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ∧
      Nat.card (⁅U,pResidual 2 G⁆ : Subgroup G) = 4 := by
  obtain ⟨hc,_,hs⟩ := reduced_index_three_action T hi U hU hJ
  let : Group.IsSolvable G := hs
  let q := QuotientGroup.mk' (centralizer (U : Set G))
  have hq := QuotientGroup.mk'_surjective (centralizer (U : Set G))
  have hk := QuotientGroup.ker_mk' (centralizer (U : Set G))
  have hP := reduced_index_three_minimal T hi U hU hJ
  obtain ⟨hb,ha⟩ := cubic_baumann_sylow_and_alpha T hP U hU hJ q hq hk
    inferInstance hU.quotient_pCore_eq_bot hc
  exact ⟨hb,ha,cubic_thompson_moved_card U q hq hk T hJ
    inferInstance hU.quotient_pCore_eq_bot hc⟩

/-- Applying Baumann to the actual moved reduced module supplies the alpha
bound required by the literal localV construction. -/
theorem reduced_index_three_moved_baumann (T : Sylow 2 G)
    (hi : (T : Subgroup G).index = 3)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    Chapter1.IsSylowIn 2 (ChapterB.baumann (T : Subgroup G))
      (pResidual 2 G ⊔ ChapterB.baumann (T : Subgroup G)) ∧
      ChapterB.thompsonAlpha (T : Subgroup G) ≤ ⁅U,pResidual 2 G⁆ ⊔
        (ChapterB.thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) := by
  let W := ⁅U,pResidual 2 G⁆
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left U _)
  have hW := hU.moved U
  have hJW : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G) := by
    rwa [hU.centralizer_moved_eq U]
  obtain ⟨hb,ha,_⟩ := reduced_index_three_baumann T hi W hW hJW
  exact ⟨hb,ha.le.trans (sup_le le_sup_right (inf_le_left.trans le_sup_left))⟩

end CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
