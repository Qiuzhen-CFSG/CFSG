module
public import Theory.GroupTheory.PGroup.RankOneSquareRoots
public import Theory.SpecificGroups.HeisenbergPrime.SquareRootCenter
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSylowIrreducibility
/-!
# Square roots in the original extraspecial point core

The faithful star Sylow action and its nontrivial action on the extraspecial
center rule out an order-two point core: that case would make the Sylow
an elementary four, contradicting its proved Frattini irreducibility.
The rank-one bound then supplies an order-four square root of every
nonidentity point-core involution. The equality Q* = R₁* lifts that root
to an element of the literal original Q.

The selected critical-actor application retains its original representative,
its nontrivial extraspecial action and its center fixation. Only the genuine
earlier structural and faithful classification implications remain explicit.
This supplies the root needed to test the remaining order-sixteen interval;
it does not assert the full C₄/Q₈ classification of R₁*.

Source: Aschbacher–Smith, 14.7.15(2), printed p.1047.
-/
public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
/-- The original point-core star image is not of order two. -/
theorem extraspecial_point_core_card_ne_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    Nat.card (star F (F.Ri L 1)) ≠ 2 := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  let P := pResidual 2 (HStar F.H)
  let S := star F (T : Subgroup G)
  let R := star F (F.Ri L 1)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  let eP : P ≃* HeisenbergPrime 3 := (residualStarEquiv F).symm.trans e
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have hR : R = S ⊓ centralizer ((center P).map P.subtype : Set (HStar F.H)) := by
    dsimp only [R,S,P]
    rw [point_core_star_eq_centralizer_of_normal h structural hn,
      point_star_eq_center_of_extraspecial_residual h hab structural previous hex hcard hexp]
  have hRS : R ≤ S := hR ▸ inf_le_left
  intro hc
  change Nat.card R = 2 at hc
  have hSc : Nat.card S = 4 := by
    have hm := relIndex_mul_card_of_le hRS
    rw [point_core_star_index_two_of_normal h structural hn,hc] at hm
    exact hm.symm
  have hS2 : IsPGroup 2 S := T.isPGroup'.comap_subtype.map (starMap F)
  let α : S →* MulAut P := (MulAut.conjNormal : HStar F.H →* MulAut P).comp S.subtype
  have hf : Function.Injective α := by
    apply (MonoidHom.ker_eq_bot_iff α).mp
    apply bot_unique
    intro a ha
    have hcp : (a : HStar F.H) ∈ centralizer (P : Set (HStar F.H)) := by
      rw [←MulAut.conjNormal_ker_eq_centralizer P]
      exact ha
    have hp := Theory.GroupTheory.centralizer_pResidual_le_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot 2) hcp
    exact Subtype.ext ((hS2.disjoint_of_coprime (IsExtraspecial.isPGroup 3 P)
      (by decide : Nat.Coprime 2 3)).le_bot ⟨a.property,hp⟩)
  have hm : ¬ ∀ a : S, ∀ z ∈ center P, α a z = z := by
    intro hh
    have hSR : S ≤ R := by
      rw [hR]
      refine le_inf le_rfl ?_
      intro a ha z hz
      obtain ⟨z,hz,rfl⟩ := hz
      have hfz := congrArg (fun p : P => (p : HStar F.H)) (hh ⟨a,ha⟩ z hz)
      change a * (z : HStar F.H) * a⁻¹ = (z : HStar F.H) at hfz
      exact (mul_inv_eq_iff_eq_mul.mp hfz).symm
    have heq := le_antisymm hRS hSR
    have hc' : Nat.card R = 4 := heq ▸ hSc
    omega
  have hel := IsExtraspecial.four_actor_elementary_of_center_movement eP α hf hSc hm
  exact extraspecial_star_sylow_not_elementary h hab structural previous faithful hex hcard hexp hel

/-- Every nonidentity star involution in the point core has an order-four
square root represented in the literal original Q. -/
theorem extraspecial_point_core_square_root
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (a : F.H) (ha : (a : G) ∈ F.Ri L 1)
    (hane : starMap F a ≠ 1) (ha2 : (starMap F a)^2=1) :
    ∃ b : F.H, (b : G) ∈ Q T L ∧
      (starMap F b)^2=starMap F a ∧ orderOf (starMap F b)=4 := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  let R := star F (F.Ri L 1)
  let z : R := ⟨starMap F a,mem_map_of_mem (starMap F) ha⟩
  have hz : z≠1 := fun hh => hane (congrArg Subtype.val hh)
  let : Nontrivial R := nontrivial_of_ne z 1 hz
  have hc : 2<Nat.card R := by
    have hpos : 1<Nat.card R := (one_lt_card_iff_ne_bot R).mpr
      (fun hh => hane (mem_bot.mp (hh ▸ z.property)))
    have hne := extraspecial_point_core_card_ne_two h hab structural previous faithful ⟨e⟩
    change Nat.card R ≠ 2 at hne
    omega
  have hRS : R ≤ star F (T : Subgroup G) := by
    dsimp only [R]
    rw [point_core_star_eq_centralizer_of_normal h structural hn]
    exact inf_le_left
  have hR2 : IsPGroup 2 R :=
    (T.isPGroup'.comap_subtype.map (starMap F)).to_le hRS
  obtain ⟨b,hb,hbo⟩ := hR2.exists_square_root_of_rank_one
    (point_core_rank_one_of_extraspecial_residual h structural hex hcard)
    hc z hz (Subtype.ext ha2)
  have hbQ : (b : HStar F.H) ∈ star F (Q T L) := by
    rw [(core_product_of_point_normal h hab structural hn).2]
    exact b.property
  obtain ⟨q,hq,heq⟩ := hbQ
  refine ⟨q,hq,?_,?_⟩
  · rw [heq]
    exact congrArg Subtype.val hb
  · rw [heq,orderOf_coe]
    exact hbo

/-- The selected original critical actor admits a square root in Q, retaining
its nontrivial extraspecial action and its center fixation. -/
theorem exists_extraspecial_critical_actor_square_root
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    ∃ a b : F.H, (a : G) ∈ c.Uα ∧ starMap F a ≠ 1 ∧ (starMap F a)^2=1 ∧
      (MulAut.conjNormal (starMap F a) : MulAut (pResidual 2 (HStar F.H))) ≠ 1 ∧
      (∀ z ∈ center (pResidual 2 (HStar F.H)),
        (MulAut.conjNormal (starMap F a) : MulAut (pResidual 2 (HStar F.H))) z = z) ∧
      (b : G) ∈ Q T L ∧ (starMap F b)^2=starMap F a ∧
      orderOf (starMap F b)=4 := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  obtain ⟨a,ha,hane,ha2,hnontrivial,hcenter⟩ :=
    exists_extraspecial_critical_actor h hab structural previous hex hcard hexp c hs
  obtain ⟨b,hb,hba,hbo⟩ := extraspecial_point_core_square_root h hab structural previous faithful
    ⟨e⟩ a (critical_le_Ri h structural c ha) hane ha2
  exact ⟨a,b,ha,hane,ha2,hnontrivial,hcenter,hb,hba,hbo⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
