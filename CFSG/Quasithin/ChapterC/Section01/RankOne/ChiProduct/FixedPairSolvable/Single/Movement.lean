module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.CubicLocal.Action
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Movement
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.CubicResidual

/-!
# Original Thompson movement of the cubic residual

The cubic residual of the faithful action is self-centralizing. The
nontrivial two-group Thompson image therefore moves it, and its prime order
makes the image commutator the whole residual. The genuine B.6.8 Frattini
bound lifts that equality through the full action kernel. Two-perfection
removes the remaining two-core supplement.

Source: Aschbacher--Smith C.1.26, with B.6.8, printed pp.114--117,132.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.Single
open ChapterB GlaubermanNiles
variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]

theorem residual_moved_of_cubic_image
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* Q) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (hcore : pCore 2 Q = ⊥) (hc : Nat.card (pResidual 2 Q) = 3) :
    pResidual 2 G = ⁅pResidual 2 G,elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  let X := pResidual 2 G
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  let R := pResidual 2 Q
  have hR : IsPGroup 3 R := IsPGroup.of_card (n := 1) (by simpa only [pow_one] using hc)
  have hJq : IsPGroup 2 (J.map q) :=
    (T.isPGroup'.to_le (sSup_le fun _ hA => hA.1)).map q
  have hd : Disjoint (J.map q) R :=
    hJq.disjoint_of_coprime hR (by decide : Nat.Coprime 2 3)
  have hne : ⁅R,J.map q⁆ ≠ ⊥ := by
    intro he
    have hcent : J.map q ≤ centralizer (R : Set Q) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
    have hfit : generalizedFitting Q = R := generalizedFitting_eq_residual_of_cubic hcore hc
    have hJR : J.map q ≤ R := by
      rw [←hfit] at hcent ⊢
      exact hcent.trans (centralizer_generalizedFitting_le Q)
    have hjbot : J.map q = ⊥ := le_bot_iff.mp
      ((le_inf le_rfl hJR).trans (disjoint_iff_inf_le.mp hd))
    exact hJ ((Subgroup.map_eq_bot_iff J).mp hjbot |>.trans_eq hk)
  have hle : ⁅R,J.map q⁆ ≤ R := commutator_le_left _ _
  have him : R = ⁅R,J.map q⁆ := by
    apply (eq_of_le_of_card_ge hle ?_).symm
    have hv := (card_dvd_of_le hle)
    rw [hc] at hv
    rcases (Nat.dvd_prime Nat.prime_three).mp hv with h1 | h3
    · exact (hne ((Subgroup.card_eq_one).mp h1)).elim
    · rw [hc,h3]
  let C := ⁅X,J⁆
  have himage : X.map q ≤ C.map q := by
    rw [show C = ⁅X,J⁆ from rfl,map_commutator]
    rw [show X.map q = R from map_pResidual_of_surjective 2 q hq]
    exact him.le
  have hfr : X ⊓ q.ker ≤ BaumannArgument.coreFrattini X := by
    rw [hk]
    exact RankOneBaumann.residual_centralizer_le_coreFrattini T hP U hU hJ
  have hcover := pResidual_le_sup_of_frattini_kernel 2 C q (pCore 2 X) himage hfr
  have hCX : C ≤ X := commutator_le_left X J
  let D := C.subgroupOf X
  let : D.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left X J)
  have hcover' : (⊤ : Subgroup X) ≤ D ⊔ pCore 2 X := by
    intro x hx
    obtain ⟨c,hc,z,hz,he⟩ := mem_sup_of_normal_right.mp (hcover x.property)
    obtain ⟨z,hz,rfl⟩ := hz
    have he' : (⟨c,hCX hc⟩ : X) * z = x := Subtype.ext he
    rw [←he']
    exact mul_mem_sup hc hz
  have htop : D = ⊤ := top_le_iff.mp (le_normal_of_isPPerfect_of_le_sup_pGroup
    ⊤ D (pCore 2 X) ((isPPerfect_pResidual 2).of_surjective (topEquiv (G := X)).symm.toMonoidHom
      (topEquiv (G := X)).symm.surjective) pCore_isPGroup hcover')
  exact le_antisymm (subgroupOf_eq_top.mp htop) hCX
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.Single
