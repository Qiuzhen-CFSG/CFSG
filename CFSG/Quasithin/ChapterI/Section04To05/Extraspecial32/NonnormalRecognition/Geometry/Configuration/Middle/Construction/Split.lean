module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle.LocalData
public import Theory.SpecificGroups.PSL3Two.SplitBlockActions.SplitParabolic.NaturalModel
public import Theory.ElementaryAbelian.AutomorphismCardEight

/-!
# Split coordinates before constructing the middle subgroup

The faithful conjugation action on the elementary eight identifies its quotient
with its full automorphism group. Binary coordinates give the natural SL₃(2)
action, so a complement yields the genuine split block. This is the construction
of `Parabolics.MarkedTransport`, specialized before any A₃ configuration exists;
its general helpers there are private. No middle subgroup or fusion assertion is
an input. Source: Aschbacher, “A 2-local characterization of M12”, Lemma 3.1,
printed p.36 (the split point normalizer supplied by Lemma 2.8).
-/

public section
open Subgroup
open Matrix.PSL3Two Matrix.PSL3Two.SplitParabolic
open scoped IsMulCommutative
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration.Construction

private theorem eight_coordinates (E : Type*) [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (hc : Nat.card E = 8) : Nonempty (E ≃* E3) := by
  classical
  have hpow : 2 ^ Module.finrank (ZMod 2) (Additive E) = 2 ^ 3 := by
    have hs := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
    change Nat.card E = _ at hs
    simpa only [Nat.card_zmod, hc, show (2 : ℕ) ^ 3 = 8 by decide] using hs.symm
  have hd : Module.finrank (ZMod 2) (Additive E) = 3 :=
    Nat.pow_right_injective (by decide : 1 < 2) hpow
  exact ⟨(Module.finBasisOfFinrankEq (ZMod 2) (Additive E) hd).equivFun.toAddEquiv.toMultiplicativeRight⟩

private theorem action_bijective : Function.Bijective naturalAction := by
  have hi : Function.Injective naturalAction := by
    intro a b hab
    apply Matrix.SpecialLinearGroup.toLin'_injective
    ext v : 1
    exact congrArg (fun f : MulAut E3 => (f (Multiplicative.ofAdd v)).toAdd) hab
  have : IsElementaryAbelian 2 E3 := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro v
      rw [pow_two]
      apply Multiplicative.toAdd.injective
      funext i
      change v.toAdd i + v.toAdd i = 0
      exact CharTwo.add_self_eq_zero _) }
  apply (Nat.bijective_iff_injective_and_card naturalAction).mpr
  refine ⟨hi, ?_⟩
  rw [card_SL, card_mulAut_of_elementary_eight E3 (by simp [Nat.card_eq_fintype_card])]

private noncomputable def actionEquiv : SL ≃* MulAut E3 :=
  MulEquiv.ofBijective naturalAction action_bijective

variable {G : Type*} [Group G] [Finite G]

private noncomputable def conjugationQuotient (E : Subgroup G)
    [IsElementaryAbelian 2 E] (hc : Nat.card E = 8)
    (hself : centralizer (E : Set G) = E)
    (hq : Nat.card (normalizer (E : Set G) ⧸ E.subgroupOf (normalizer (E : Set G))) = 168) :
    (normalizer (E : Set G) ⧸ E.subgroupOf (normalizer (E : Set G))) ≃* MulAut E := by
  have hk : E.subgroupOf (normalizer (E : Set G)) = E.normalizerMonoidHom.ker := by
    rw [normalizerMonoidHom_ker, hself]
  let f := QuotientGroup.lift _ E.normalizerMonoidHom hk.le
  exact MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr
    ⟨(QuotientGroup.injective_lift_iff _ _ _).mpr hk,
      hq.trans (card_mulAut_of_elementary_eight E hc).symm⟩)

private noncomputable def normalizerSplitData (E : Subgroup G)
    [IsElementaryAbelian 2 E] (hc : Nat.card E = 8)
    (hself : centralizer (E : Set G) = E)
    (hq : Nat.card (normalizer (E : Set G) ⧸ E.subgroupOf (normalizer (E : Set G))) = 168)
    (hs : ∃ K : Subgroup (normalizer (E : Set G)),
      (E.subgroupOf (normalizer (E : Set G))).IsComplement' K) :
    SplitNaturalData (E.subgroupOf (normalizer (E : Set G))) := by
  let e := (eight_coordinates E hc).some
  let q := conjugationQuotient E hc hself hq
  refine {
    quotient := q.trans ((MulAut.congr e).trans actionEquiv.symm)
    moduleEquiv := (subgroupOfEquivOfLe E.le_normalizer).trans e
    complement := hs.choose
    splitting := hs.choose_spec
    equivariant := ?_ }
  intro n v
  change e (E.normalizerMonoidHom n ((subgroupOfEquivOfLe E.le_normalizer) v)) =
    naturalAction (actionEquiv.symm ((MulAut.congr e) (q (QuotientGroup.mk' _ n))))
      (e ((subgroupOfEquivOfLe E.le_normalizer) v))
  change _ = actionEquiv (actionEquiv.symm _) _
  rw [MulEquiv.apply_symm_apply]
  change _ = (MulAut.congr e) (E.normalizerMonoidHom n) _
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

variable {z g : G}

/-- Action-compatible coordinates for the point normalizer, requiring only its
actual complement and the already established intersection data. -/
noncomputable def pointSplitData (d : IntersectionData z g)
    (point_split : ∃ K : Subgroup (normalizer (coreIntersection z g : Set G)),
      IsComplement' ((coreIntersection z g).subgroupOf
        (normalizer (coreIntersection z g : Set G))) K) :
    SplitNaturalData ((coreIntersection z g).subgroupOf
      (normalizer (coreIntersection z g : Set G))) := by
  letI := d.elementary
  exact normalizerSplitData _ d.card d.self_centralizing
    ((Nat.card_congr d.normalizer_quotient.some.toEquiv).trans card_PSL) point_split

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration.Construction
end
