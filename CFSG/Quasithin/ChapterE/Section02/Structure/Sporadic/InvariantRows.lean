module
public import CFSG.Quasithin.ChapterE.Section02.Structure.Sporadic.Reduction
public import Theory.Mathieu.M24.LocalGeometry.Stabilizers
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.LocalGeneration
public import Theory.SpecificGroups.Held.AutomorphismLocalPair
public import Theory.SpecificGroups.Rudvalis.Model.SylowInvariantPair
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.Rudvalis.LocalCover.Generation
/-!
# Automorphism-invariant sporadic Sylow pairs

The actual M24, Held, Higman–Sims and Rudvalis locals contain the marked
Sylow subgroup and are fixed by every automorphism preserving it. Their
known generation identities therefore lift through any normal supplement.
Self-centralizing two-cores, and the incompatible Rudvalis local orders,
prove properness without additional geometry premises.

Source: Aschbacher–Smith E.2.2, printed pp.215–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure.Sporadic
variable {G : Type*} [Group G] [Finite G]

theorem no_m24 (T : Sylow 2 G) (L : Subgroup G) [L.Normal] [IsSimpleGroup L]
    (ha : ¬ IsMulCommutative L) (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (e : L ≃* Sporadic.Mathieu.M24) : ¬ ChapterB.IsMinimalParabolicOver T ⊤ := by
  let : IsSimpleGroup Sporadic.Mathieu.M24 := e.symm.isSimpleGroup
  have hc := core_eq_bot_of_simple (noncomm_of_equiv L ha e)
  let S : Sylow 2 Sporadic.Mathieu.M24 := default
  obtain ⟨P,Q,_,_,hp,hq,hcp,hcq,hjoin⟩ :=
    Sporadic.Mathieu.M24LocalGeometry.Stabilizers.exists_pair_over_sylow S
  exact ChapterB.not_minimalParabolic_of_intrinsic_parabolics T L e hgen S P Q hjoin
    (proper_of_core_centralizer hc P hcp) (proper_of_core_centralizer hc Q hcq) hp hq
    (fun a h => ⟨Sporadic.Mathieu.M24LocalGeometry.Stabilizers.automorphism_preserves_overgroup S P hp a h,
      Sporadic.Mathieu.M24LocalGeometry.Stabilizers.automorphism_preserves_overgroup S Q hq a h⟩)

theorem no_held (T : Sylow 2 G) (L : Subgroup G) [L.Normal] [IsSimpleGroup L]
    (ha : ¬ IsMulCommutative L) (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (e : L ≃* Held.He) : ¬ ChapterB.IsMinimalParabolicOver T ⊤ := by
  let : IsSimpleGroup Held.He := e.symm.isSimpleGroup
  have hc := core_eq_bot_of_simple (noncomm_of_equiv L ha e)
  let S : Sylow 2 Held.He := default
  exact ChapterB.not_minimalParabolic_of_intrinsic_parabolics T L e hgen S
    (Held.AutomorphismLocalPair.centerLocal S) (Held.AutomorphismLocalPair.largeLocal S)
    (Held.AutomorphismLocalPair.locals_generate S)
    (proper_of_core_centralizer hc _ (Held.AutomorphismLocalPair.centerLocal_selfCentralizingCore S))
    (proper_of_core_centralizer hc _ (Held.AutomorphismLocalPair.largeLocal_selfCentralizingCore_of_sylow S))
    (Held.AutomorphismLocalPair.le_centerLocal S) (Held.AutomorphismLocalPair.le_largeLocal S)
    (Held.AutomorphismLocalPair.locals_invariant S)

open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.LocalGeneration
  Sporadic.LeechRelated.HS.BlockNormalizer
  Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralInvolutionCore in
theorem no_higmanSims (T : Sylow 2 G) (L : Subgroup G) [L.Normal] [IsSimpleGroup L]
    (ha : ¬ IsMulCommutative L) (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (e : L ≃* Sporadic.LeechRelated.HS.Carrier) : ¬ ChapterB.IsMinimalParabolicOver T ⊤ := by
  let : IsSimpleGroup Carrier := e.symm.isSimpleGroup
  have hc := core_eq_bot_of_simple (noncomm_of_equiv L ha e)
  have hfirst : centralizer (pCore 2 (member 0) : Set (member 0)) ≤ pCore 2 (member 0) := by
    change centralizer (pCore 2 (EvenLocalCandidates.localGroup 0) : Set (EvenLocalCandidates.localGroup 0)) ≤ _
    have hk : core ≤ pCore 2 (EvenLocalCandidates.localGroup 0) := le_sSup ⟨core_normal,core_isPGroup⟩
    intro x hx
    exact hk (core_selfCentralizing (fun y hy => hx y (hk hy)))
  exact ChapterB.not_minimalParabolic_of_intrinsic_parabolics T L e hgen baseSylow
    (member 0) (member 1) members_sup_eq_top
    (proper_of_core_centralizer hc _ hfirst)
    (proper_of_core_centralizer hc _ baseNormalizer_selfCentralizing)
    (sylow_le_member 0) (sylow_le_member 1)
    (fun a h => ⟨member_invariant 0 a h,member_invariant 1 a h⟩)

open _root_.Rudvalis _root_.Rudvalis.SylowOvergroups
  _root_.Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover
  _root_.Rudvalis.SylowInvariantPair in
theorem no_rudvalis (T : Sylow 2 G) (L : Subgroup G) [L.Normal] [IsSimpleGroup L]
    (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (e : L ≃* _root_.Rudvalis.Model) : ¬ ChapterB.IsMinimalParabolicOver T ⊤ := by
  let : IsSimpleGroup _root_.Rudvalis.Model := e.symm.isSimpleGroup
  have hfirst : locals 0 ≠ ⊤ := by
    intro h
    have hd := card_dvd_of_le (show locals 1 ≤ locals 0 from h ▸ le_top)
    rw [Nat.card_congr secondEquiv.toEquiv, Nat.card_congr firstEquiv.toEquiv,
      max6_card,max4_card] at hd
    norm_num at hd
  have hsecond : locals 1 ≠ ⊤ := by
    intro h
    have hd := card_dvd_of_le (show locals 0 ≤ locals 1 from h ▸ le_top)
    rw [Nat.card_congr secondEquiv.toEquiv, Nat.card_congr firstEquiv.toEquiv,
      max6_card,max4_card] at hd
    norm_num at hd
  have hS : (sylow : Subgroup _root_.Rudvalis.Model) ≤ locals 1 := by
    rw [second_eq_normalizer,elementary_zero_eq_center]
    exact localP.le_normalizer.trans (normalizer_le_normalizer_characteristic_image localP (center localP))
  exact ChapterB.not_minimalParabolic_of_intrinsic_parabolics T L e hgen sylow
    (locals 0) (locals 1) ChapterE.Rudvalis.LocalCover.locals_sup_eq_top
    hfirst hsecond localP_le_max4 hS (fun a h => ⟨locals_invariant 0 a h,locals_invariant 1 a h⟩)

end CFSG.Quasithin.ChapterE.Structure.Sporadic
