module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticMiddleCoreProduct

/-!
# Reciprocal intersections in the original quintic configuration

An actual escaping conjugate gives two distinct Sylows at the cubic endpoint.
Their three full cores generate that endpoint. Its trivial center forces the
two original central lines to be disjoint. The reciprocal span--core
intersections commute because their commutator lies in both lines.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
open ChapterF.Source ChapterF.Source.DGS85
variable {G : Type*} [Group G] [Finite G]

/-- The same escaping conjugator retains the full three-core generation and
forces the reciprocal intersections to commute. -/
theorem source_quintic_reciprocal_core_geometry
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (g : G) (hg : g ∈ sourceResidual M Mc ⊔ (T : Subgroup G))
    (hescape : ¬ (conjugateSpanBy (localModule T M) H).map
      (MulAut.conj g).toMonoidHom ≤ H.pCoreIn 2) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let U := conjugateSpanBy (localModule T M) H
    let QH := H.pCoreIn 2
    let Qstar := QH.map (MulAut.conj g).toMonoidHom
    let Ustar := U.map (MulAut.conj g).toMonoidHom
    let Z := centralInvolutions T
    X = (QH ⊔ Qstar) ⊔ X.pCoreIn 2 ∧
      Z ⊓ Z.map (MulAut.conj g).toMonoidHom = ⊥ ∧
      ⁅U ⊓ Qstar,Ustar ⊓ QH⁆ = ⊥ := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let V := localModule T M
  let U := conjugateSpanBy V H
  let Q := X.pCoreIn 2
  let QH := H.pCoreIn 2
  let Z := centralInvolutions T
  let c := (MulAut.conj g).toMonoidHom
  let Y := QH.map c
  let D := U.map c
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hQHT : QH ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow H (T.subtype hTH)).trans_eq (map_subgroupOf_eq_of_le hTH)
  have hUQH : U ≤ QH := by
    obtain ⟨he,F,hp,_,_,hloc⟩ := Section02.source_lemma_14_2_6
      hG T hempty hM hu hmany hcard e
    let := he
    obtain ⟨_,hl,_,_,_,_⟩ := hloc H hH.1
    have hh := hl.U_le_core
    change conjugateSpanBy (rankTwoSeed T M) H ≤ H.pCoreIn 2 at hh
    simpa only [Section02.rankTwoSeed_eq_localModule] using hh
  have hHU : H ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy _ _
  have hQN : X ≤ normalizer (Q : Set G) := X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hmapQ : Q.map c = Q := mem_normalizer_iff_map_conj_eq.mp (hQN hg)
  obtain ⟨hF,_,_,hNX,_,_,hHZ⟩ :=
    Section02.SolvableAmalgam.source_small_index_hypothesis_F_1_1
      hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2 (Or.inr hi)
  have hgen : X = (QH ⊔ Y) ⊔ Q := by
    have hT : QH ⊔ Q = (T : Subgroup G) :=
      (source_quintic_dgs_common_sylow hG T hempty hM hu hmany hcard e H hH hi).1
    have hgT : g ∉ (T : Subgroup G) := by
      intro ht
      have hm : U.map c = U := mem_normalizer_iff_map_conj_eq.mp (hHU (hTH ht))
      exact hescape (hm.le.trans hUQH)
    let S := T.subtype hTX
    let gx : X := ⟨g,hg⟩
    have hS : (S : Subgroup X).map X.subtype = (T : Subgroup G) := map_subgroupOf_eq_of_le hTX
    have hR : ((gx • S : Sylow 2 X) : Subgroup X).map X.subtype =
        (T : Subgroup G).map c := by
      change ((S : Subgroup X).map (MulAut.conj gx).toMonoidHom).map X.subtype = _
      rw [←hS,Subgroup.map_map,Subgroup.map_map]
      rfl
    have hne : S ≠ gx • S := by
      intro he
      have hm := congrArg (fun R : Sylow 2 X => (R : Subgroup X).map X.subtype) he
      rw [hS,hR] at hm
      have hn : g ∈ normalizer (T : Set G) := mem_normalizer_iff_map_conj_eq.mpr hm.symm
      exact hgT (hNX ▸ (show g ∈ X ⊓ normalizer (T : Set G) from ⟨hg,hn⟩))
    have hh := CommutingThreeProfile.rankOne_sylow_pair_generates X (hF.quotient 1) S (gx • S) hne
    rw [hS,hR,←hT,Subgroup.map_sup,hmapQ] at hh
    rw [sup_sup_sup_comm,sup_idem] at hh
    exact hh.symm
  have hZV : Z ≤ V := le_conjugateSpanBy _ _
  have hXV : X ≤ normalizer (V : Set G) := by
    rw [←InitialSource.UniformControl.source_local_eq_normalizer hG T hM.1]
    exact sup_le (sourceResidual_le M Mc) hM.1.2
  have hmapV : V.map c = V := mem_normalizer_iff_map_conj_eq.mp (hXV hg)
  have hZgV : Z.map c ≤ V := (map_mono hZV).trans hmapV.le
  have hQcV : Q ≤ centralizer (V : Set G) :=
    (Section02.source_residualSylow_quotient hG T hempty hM hu hmany hcard e).1.le.trans inf_le_right
  have hZQH : Z ≤ centralizer (QH : Set G) :=
    (le_centralizer_iff.mp hHZ).trans (centralizer_le (pCoreIn_le 2 H))
  have hZgY : Z.map c ≤ centralizer (Y : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [←map_commutator,commutator_eq_bot_iff_le_centralizer.mpr hZQH,Subgroup.map_bot]
  have hZX : center X = ⊥ :=
    (source_quintic_cubic_natural_center hG T hempty hM hu hmany hcard e H hH hi).1
  have hdisj : Z ⊓ Z.map c = ⊥ := by
    apply bot_unique
    intro z hz
    have hzX : z ∈ X :=
      ((hZV.trans (le_conjugateSpanBy _ _)).trans (hUQH.trans (hQHT.trans hTX))) hz.1
    have hzC : z ∈ centralizer (X : Set G) := by
      have hh : X ≤ centralizer ({z} : Set G) := by
        rw [hgen]
        exact sup_le (sup_le
          (fun t ht => mem_centralizer_singleton_iff.mpr ((hZQH hz.1) t ht))
          (fun t ht => mem_centralizer_singleton_iff.mpr ((hZgY hz.2) t ht)))
          (fun t ht => mem_centralizer_singleton_iff.mpr
            (((le_centralizer_iff.mp hQcV) (hZV hz.1)) t ht))
      exact fun t ht => mem_centralizer_singleton_iff.mp (hh ht)
    have hzc : (⟨z,hzX⟩ : X) ∈ center X :=
      mem_center_iff.mpr (fun t => Subtype.ext (hzC t t.property))
    have hone := mem_bot.mp (hZX ▸ hzc)
    exact mem_bot.mpr (congrArg Subtype.val hone)
  have hcomm : ⁅U,QH⁆ = Z :=
    (source_quintic_core_commutators hG T hempty hM hu hmany hcard e H hH hi).2
  have hcommg : ⁅D,Y⁆ = Z.map c := by rw [←map_commutator,hcomm]
  have hcross : ⁅U ⊓ Y,D ⊓ QH⁆ = ⊥ := by
    apply bot_unique
    rw [←hdisj]
    apply le_inf
    · exact (commutator_mono inf_le_left inf_le_right).trans hcomm.le
    · rw [commutator_comm]
      exact (commutator_mono inf_le_left inf_le_right).trans hcommg.le
  exact ⟨hgen,hdisj,hcross⟩

end CFSG.Quasithin.Chapter14.Section06
