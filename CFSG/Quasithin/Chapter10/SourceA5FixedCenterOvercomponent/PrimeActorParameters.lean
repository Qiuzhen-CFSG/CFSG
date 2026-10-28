module
public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.MarkedOdd
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
/-!
# Prime-field actors of the marked small chief action

The existing B.4/K.2 parameter sieve applies to the actual small involution
and a prime-field PSL₂ actor, leaving p=5 or p=7. An embedded A₅ excludes
p=7 by Lagrange's theorem, since 60 does not divide 168.

Source: Aschbacher–Smith 10.2.1, printed p.743, with B.4.5 and K.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
variable {A V : Type*} [Group A] [Finite A] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
theorem prime_actor_parameters_of_small_involution [IsQuasisimple A] (ρ : Representation (ZMod 2) A V)
    (h : ChapterK.RankOne.SourceHypotheses ρ (generalizedFitting A))
    (t : A) (ht : orderOf t=2)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1))≤2)
    {p : ℕ} (hp : p.Prime) (hp3 : 3<p) (e : A≃*PSL(2,ZMod p)) : p=5 ∨ p=7 := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsSimpleGroup PSL(2,ZMod p) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by simpa using (show 4≤p by omega))
  let : IsSimpleGroup A := e.isSimpleGroup
  have hc : center A=⊥ := (inferInstance : (center A).Normal).eq_bot_or_eq_top.resolve_right
    (fun hh => Group.IsPerfect.not_isSolvable A
      (Group.isSolvable_of_comm (center_eq_top_iff.mp hh).is_comm.comm))
  let d : generalizedFitting A≃*A :=
    (MulEquiv.subgroupCongr generalizedFitting_eq_top_of_quasisimple).trans topEquiv
  let := h.quasisimple
  let dc := (IsQuasisimple.centralQuotientEquiv d.toMonoidHom d.surjective).trans
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot)
  have hm : ClassicalGroup.IsPSL ((generalizedFitting A)⧸center (generalizedFitting A)) 2 (p^1) :=
    ⟨ZMod p,inferInstance,inferInstance,by simp,⟨dc.trans e⟩⟩
  rcases ChapterB.SmallRatioClassification.odd_pslTwo_parameters_of_small_involution
    h t ht hr hp (hp.odd_of_ne_two (by omega)) (Or.inl rfl) (by simp;omega) hm with
      h5 | h7 | h3
  · exact Or.inl h5.1
  · exact Or.inr h7.1
  · omega

omit [Finite A] [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] in
theorem not_prime_seven_actor_of_alternating_five_subgroup (B : Subgroup A) (eB : B≃*alternatingGroup (Fin 5)) :
    ¬Nonempty (A≃*PSL(2,ZMod 7)) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  rintro ⟨eA⟩
  have hd := B.card_subgroup_dvd_card
  have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F:=ZMod 7) (by norm_num)
  have ha : Nat.card A=168 := by
    rw [Nat.card_congr eA.toEquiv]
    rw [Nat.card_zmod] at hc
    norm_num only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul] at hc
    omega
  rw [Nat.card_congr eB.toEquiv,ha,nat_card_alternatingGroup] at hd
  norm_num [Nat.factorial] at hd
end CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
