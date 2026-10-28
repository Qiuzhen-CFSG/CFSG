module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Conjugator.ActorGeometry
public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis
public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.OddLinear
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.Action
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.Reductions
public import Theory.SpecificGroups.LinearCoefficientEquiv
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Conjugator.RankWitness.Odd.ThreeReduction

/-!
# The odd-characteristic selected-residual reduction

For a Fermat–Mersenne PSL₂ component, the earlier outer-PGL exclusion
forces the actual involutory action to be inner. Prime-field automorphism
coverage supplies this implication with the full component isomorphism.
The checked inner fixed group is a Sylow two-group, so its two-residual
and its modified residual are trivial. Inverse transport then rules out
unequal selected residuals. The outer exclusion remains an explicit
16.4.6 input; this module does not assert that earlier theorem.

The PSL₃(3) model transports live in `Odd.ThreeReduction`. Constructing
an elementary abelian subgroup of order 27 in an actual two-local
normalizer remains a separate obligation. The elementary-cube extraction
below turns that construction into the required subgroup of order p²
and independent commuting order-p element. No model witness existence
is asserted without its missing geometric input.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.5(1–2), 16.4.6, and 16.5.5–6, printed pp.1171–1172,
1184–1186 and 1197. Conjugation means left conjugation throughout.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator.OddCharacteristic
open OuterResidual ComponentTransfer.Intrinsic
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

omit [Finite G] in
/-- The full inner PSL₂ fixed group is a two-group, so even the modified
residual vanishes. No disjointness of model families is needed here. -/
theorem pslTwo_residual_eq_bot_of_inner [Group.IsPerfect L] {p : ℕ}
    (hp : IsFermatOrMersennePrime p) (hL : ClassicalGroup.IsPSL L 2 p)
    (hn : r ∈ normalizer (L : Set G))
    (ha : orderOf (action hn) = 2)
    (hi : ∃ x : L, action hn = MulAut.conj x) :
    modifiedCentralizerResidual L r = ⊥ := by
  have hp5 := OtherPreliminaries.OddLinear.pslTwo_parameter_ge_five hp hL
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hL
  let a := MulAut.congr e (action hn)
  have ha' : orderOf a = 2 := ((MulAut.congr e).orderOf_eq _).trans ha
  have hi' : ∃ x, a = MulAut.conj x := (MulAut.congr_inner_iff e _).mpr hi
  obtain ⟨S, hS⟩ := OtherPreliminaries.OddLinear.pslTwo_inner_involution hF hp hp5 a ha' hi'
  have htwo : IsPGroup 2 a.fixedSubgroup := hS ▸ S.isPGroup'
  have hfixed : IsPGroup 2 (action hn).fixedSubgroup :=
    htwo.of_equiv (MulAut.fixedSubgroupCongr e _).symm
  have hcentral : IsPGroup 2 (ComponentTransfer.centralizerIn L r) :=
    hfixed.of_equiv (centralizerEquivFixed hn).symm
  have hbot : involutionTwoResidual L r = ⊥ :=
    involutionResidual_eq_bot_of_isPGroup L r hcentral
  exact le_bot_iff.mp ((modifiedCentralizerResidual_le L r).trans hbot.le)

/-- Connect the actual actor to 16.4.6 through proved PGL₂ coverage over
the prime field, retaining the full component equivalence. -/
theorem pslTwo_action_inner_of_outer_exclusion (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) {p : ℕ}
    (hp : IsFermatOrMersennePrime p) (hL : ClassicalGroup.IsPSL L 2 p)
    (hno : ∀ (F : Type) [Field F] [Finite F], Odd (Nat.card F) →
      ∀ e : L ≃* PSL(2,F), ¬ PGLShadow.InducesOuterPGL h hr e) :
    ∃ x : L, involutionAction h hr = MulAut.conj x := by
  let := h.component.quasisimple
  have hp5 := OtherPreliminaries.OddLinear.pslTwo_parameter_ge_five hp hL
  let : Fact p.Prime := ⟨hp.1⟩
  have hpodd : Odd p := hp.1.odd_of_ne_two (by omega)
  obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := hL
  let : Fintype F := Fintype.ofFinite F
  let ef : F ≃+* ZMod p := (ZMod.ringEquivOfPrime F hp.1
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let e : L ≃* PSL(2,ZMod p) := eF.trans (Matrix.ProjectiveSpecialLinearGroup.ringEquiv ef)
  let hK : GorensteinWalter.IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, hp.1, hpodd, by omega, by simp⟩
  have hc : 3 < Nat.card (ZMod p) := by simpa using (show 3 < p by omega)
  obtain ⟨A, hA⟩ := Theory.PSL2.primeField_pgl_coverage hpodd (by omega)
    (MulAut.congr e (involutionAction h hr))
  have hin : A ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := ZMod p)).range := by
    by_contra hout
    exact hno (ZMod p) (by simpa using hpodd) e
      ((PGLShadow.inducesOuterPGL_iff h hr e hK hc).mpr ⟨A, hout, hA.symm⟩)
  obtain ⟨x, hx⟩ := hin
  apply (MulAut.congr_inner_iff e _).mp
  refine ⟨x, ?_⟩
  rw [← hA, ← hx]
  exact GorensteinWalter.pgl2InnerAutPSL2_toPGL _ hK hc x

/-- Apply the inner centralizer calculation only after the earlier outer
exclusion has established innerness of this precise action. -/
theorem pslTwo_residual_eq_bot_of_outer_exclusion
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (hL : ClassicalGroup.IsPSL L 2 p)
    (hno : ∀ (F : Type) [Field F] [Finite F], Odd (Nat.card F) →
      ∀ e : L ≃* PSL(2,F), ¬ PGLShadow.InducesOuterPGL h hr e) :
    modifiedCentralizerResidual L r = ⊥ := by
  let := h.component.quasisimple
  exact pslTwo_residual_eq_bot_of_inner hp hL (h.sylow_normalizes (h.le_sylow hr))
    (involutionAction_order h (disjoint_iff.mp (OrderTwo.faithful h)) hr hr2)
    (pslTwo_action_inner_of_outer_exclusion h hr hp hL hno)

/-- The Fermat–Mersenne branch is impossible under unequal residuals,
conditional on the genuine earlier outer-action exclusion. -/
theorem pslTwo_unequal_false_of_outer_exclusion
    (d : ResidualInputs T z L g R)
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (hL : ClassicalGroup.IsPSL L 2 p)
    (hno : ∀ (F : Type) [Field F] [Finite F], Odd (Nat.card F) →
      ∀ (e : L ≃* PSL(2,F)) (r : G) (hr : r ∈ R), orderOf r = 2 →
        ¬ PGLShadow.InducesOuterPGL d.setup hr e)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z)) : False := by
  obtain ⟨hu, hu2⟩ := forward_actor d.setup d.transport
  have hbot := pslTwo_residual_eq_bot_of_outer_exclusion d.setup hu hu2 hp hL
    (fun F _ _ hF e => hno F hF e _ hu hu2)
  have hinv := d.inverse_transport
  simp only [hbot, Subgroup.conjBy, Subgroup.map_bot] at hinv
  exact hne (hinv.symm.trans hbot.symm)

/-- Extract the required order-p² subgroup and independent commuting
order-p element from an actual elementary abelian cube in a two-local.
The nontrivial two-subgroup Q and its ambient normalizer are preserved. -/
theorem witness_of_elementary_cube {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (Q A : Subgroup G) (hQ : Q ≠ ⊥) (hQtwo : IsPGroup 2 Q)
    (hA : IsElementaryAbelian p A) (hcard : Nat.card A = p ^ 3)
    (hAN : A ≤ normalizer (Q : Set G)) : Nonempty (OddRankThreeWitness G) := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsElementaryAbelian p A := hA
  obtain ⟨B, hB⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) p
    (show p ^ 2 ∣ Nat.card A by rw [hcard]; exact pow_dvd_pow p (by decide))
  have hBne : B ≠ ⊤ := by
    intro he
    have hc : p ^ 2 = p ^ 3 := by simpa only [he, card_top, hcard] using hB.symm
    exact (by decide : (2 : ℕ) ≠ 3) (Nat.pow_right_injective hp.one_lt hc)
  obtain ⟨x, hx⟩ := SetLike.exists_not_mem_of_ne_top B hBne
  let E := B.map A.subtype
  let : IsElementaryAbelian p B :=
    { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun b => by
        apply Subtype.ext
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p A) b.val }
  have hxE : (x : G) ∉ E := by
    rintro ⟨b, hb, he⟩
    exact hx ((A.subtype_injective he) ▸ hb)
  refine ⟨{
    p := p
    prime := hp
    odd := hpodd
    Q := Q
    Q_ne := hQ
    Q_two := hQtwo
    E := E
    E_normalizes := (map_subtype_le B).trans hAN
    E_elementary := IsElementaryAbelian.map A.subtype
    E_card := (card_map_of_injective A.subtype_injective).trans hB
    x := x
    x_normalizes := hAN x.property
    x_order := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian _ x.property)
      (fun he => hxE (he ▸ E.one_mem))
    x_independent := hxE
    x_centralizes := ?_ }⟩
  rintro y ⟨b, hb, rfl⟩
  exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (Commute.all b x).eq)

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator.OddCharacteristic
