module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Conjugator.RankWitness.Sporadic.Actions
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Odd elementary lifts for the J4 and Rudvalis residual comparison

The actual central model projection has its full two-group kernel by E1.
An elementary subgroup of odd prime exponent in the image of any specified
subgroup of L therefore lifts inside that subgroup, with the same order.
This applies both to a plane in the whole component and to a plane in a
selected residual. The ambient version retains its precise model image.

The construction takes a Sylow subgroup in the restricted preimage. Odd
exponent makes each lift two-perfect, so the central-kernel image theorem
proves uniqueness. The central-displacement argument also transfers
pointwise fixation without an invariance hypothesis on the lift.

These are covering-group transport lemmas for the J4 and Ru branches of
16.5.6(3); they do not construct a plane in either model, a common nontrivial
two-subgroup, or an independent commuting prime-order element. Thus the
ambient rank-witness construction remains open. The J4/Ru marked tables
and the Ru-specific covering geometry are separate source obligations.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.2 and 16.1.5(9),(11), printed pp.1170–1172; I.2.2(7), pp.410–412;
and Notation 16.5.5 and 16.5.6(3), p.1197. The lifting arguments here use
only the central two-kernel, without asserting the Ru-specific clauses.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16
namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator.Sporadic.JankoFourRudvalis
variable {G S : Type*} [Group G] [Finite G] [Group S]
variable {T : Sylow 2 G} {z g : G} {L R : Subgroup G}

private theorem kernel_two
    (hG : Hypothesis1611 KnownSimple.IsKnownSimple G)
    (d : ResidualInputs T z L g R) (e : L ⧸ center L ≃* S) :
    IsPGroup 2 (modelProjection e).ker := by
  rw [modelProjection_ker,
    hG.evenType.component_center_eq_twoCore d.setup.involution d.setup.component]
  exact pCore_isPGroup

private theorem elementary_twoPerfect {H : Type*} [Group H] {p : ℕ}
    [IsElementaryAbelian p H] (hp : Odd p) : IsPPerfect 2 H := by
  apply (pResidual_eq_top_iff 2 H).mp
  apply top_unique
  intro x _
  apply mem_pResidual_of_orderOf_coprime
  exact hp.coprime_two_left.of_dvd_right
    (orderOf_dvd_of_pow_eq_one
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p H) x))

/-- An odd elementary plane in the image of a specified subgroup lifts
inside that subgroup, with its exact order and full covering kernel retained. -/
theorem exists_elementary_lift_in_subgroup
    (hG : Hypothesis1611 KnownSimple.IsKnownSimple G)
    (d : ResidualInputs T z L g R) (e : L ⧸ center L ≃* S)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (X : Subgroup L) (E : Subgroup S)
    [IsElementaryAbelian p E] (hE : E ≤ X.map (modelProjection e)) :
    ∃ A : Subgroup L, IsElementaryAbelian p A ∧
      A ≤ X ∧
      A.map (modelProjection e) = E ∧ Nat.card A = Nat.card E := by
  let f : X →* X.map (modelProjection e) := (modelProjection e).subgroupMap X
  let j : f.ker →* (modelProjection e).ker := {
    toFun x := ⟨x.val.val, congrArg Subtype.val x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun v : (modelProjection e).ker => (v : L)) h))
  have hk : IsPGroup 2 f.ker := (kernel_two hG d e).of_injective j hj
  obtain ⟨n, hn⟩ := hk.exists_card_eq
  have hcop : Nat.Coprime p (Nat.card f.ker) := by
    rw [hn]
    exact hp.coprime_two_right.pow_right n
  let E0 := E.subgroupOf (X.map (modelProjection e))
  let : IsElementaryAbelian p E0 := IsElementaryAbelian.subgroupOf hE
  obtain ⟨A0, hA0, hm, hc⟩ := exists_elementaryAbelian_map_eq_of_surjective_coprime
    f ((modelProjection e).subgroupMap_surjective X) hcop E0
  let : IsElementaryAbelian p A0 := hA0
  refine ⟨A0.map X.subtype, IsElementaryAbelian.map _, map_subtype_le _, ?_, ?_⟩
  · have hh := congrArg (Subgroup.map (X.map (modelProjection e)).subtype) hm
    rw [map_map, map_subgroupOf_eq_of_le hE] at hh
    rw [map_map]
    convert hh using 1
    congr 1
  · rw [card_map_of_injective X.subtype_injective, hc]
    exact Nat.card_congr (subgroupOfEquivOfLe hE).toEquiv

/-- In particular, a model plane in the selected residual lifts inside that
same residual, rather than merely somewhere in the component. -/
theorem exists_elementary_residual_lift
    (hG : Hypothesis1611 KnownSimple.IsKnownSimple G)
    (d : ResidualInputs T z L g R) (e : L ⧸ center L ≃* S)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (u : G) (E : Subgroup S)
    [IsElementaryAbelian p E] (hE : E ≤ residualImage e u) :
    ∃ A : Subgroup L, IsElementaryAbelian p A ∧
      A ≤ (modifiedCentralizerResidual L u).subgroupOf L ∧
      A.map (modelProjection e) = E ∧ Nat.card A = Nat.card E :=
  exists_elementary_lift_in_subgroup hG d e hp _ E hE

/-- The lift is unique as an embedded subgroup; central two-kernels cannot
produce different odd elementary planes with the same model image. -/
theorem elementary_lift_unique
    (hG : Hypothesis1611 KnownSimple.IsKnownSimple G)
    (d : ResidualInputs T z L g R) (e : L ⧸ center L ≃* S)
    {p : ℕ} (hp : Odd p) (A B : Subgroup L)
    [IsElementaryAbelian p A] [IsElementaryAbelian p B]
    (he : A.map (modelProjection e) = B.map (modelProjection e)) : A = B :=
  (map_eq_map_iff_of_isPPerfect_of_central_kernel (modelProjection e)
    (elementary_twoPerfect hp) (elementary_twoPerfect hp) (kernel_two hG d e)
    ((modelProjection_ker e).symm ▸ le_rfl)).mp he

/-- Fixation of the model plane is exactly fixation of its actual lift.
No invariance of the lifted plane under the actor is assumed. -/
theorem elementary_lift_fixed_iff
    (hG : Hypothesis1611 KnownSimple.IsKnownSimple G)
    (d : ResidualInputs T z L g R) (e : L ⧸ center L ≃* S)
    {p : ℕ} (hp : Odd p) (A : Subgroup L) [IsElementaryAbelian p A]
    (a : MulAut L) :
    A.map (modelProjection e) ≤ (MulAut.centralQuotientAction e a).fixedSubgroup ↔
      A ≤ a.fixedSubgroup := by
  constructor
  · intro h x hx
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    apply MulAut.fixed_of_fixed_mod_central_p_kernel (modelProjection e) a A
      (elementary_twoPerfect hp) (kernel_two hG d e)
      ((modelProjection_ker e).symm ▸ le_rfl) ?_ x hx
    intro y hy
    have he := (MulAut.mem_fixedSubgroup _ _).mp
      (h (mem_map_of_mem (modelProjection e) hy))
    simpa only [modelProjection, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.centralQuotientAction_apply] using he
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := hy
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    change MulAut.centralQuotientAction e a (e (QuotientGroup.mk' (center L) x)) = _
    rw [MulAut.centralQuotientAction_apply, (MulAut.mem_fixedSubgroup _ _).mp (h hx)]
    rfl

/-- The plane lifts into G with the same order; model fixation by an actual
normalizer element proves ambient centralization. -/
theorem elementary_lift_centralizes
    (hG : Hypothesis1611 KnownSimple.IsKnownSimple G)
    (d : ResidualInputs T z L g R) (e : L ⧸ center L ≃* S)
    {p : ℕ} (hp : Odd p) (A : Subgroup L) [IsElementaryAbelian p A]
    (t : normalizer (L : Set G))
    (hfix : A.map (modelProjection e) ≤
      (MulAut.centralQuotientAction e (L.normalizerMonoidHom t)).fixedSubgroup) :
    A.map L.subtype ≤ centralizer ({t.val} : Set G) := by
  have hf := (elementary_lift_fixed_iff hG d e hp A (L.normalizerMonoidHom t)).mp hfix
  rintro x ⟨y, hy, rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  have he := congrArg Subtype.val ((MulAut.mem_fixedSubgroup _ _).mp (hf hy))
  change t.val * (y : G) * t.val⁻¹ = y at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm
/-- An actual ambient elementary subgroup, marked by its model image and
retaining the full residual containment and all quotient-fixed normalizer actors. -/
theorem exists_ambient_elementary_residual_lift
    (hG : Hypothesis1611 KnownSimple.IsKnownSimple G)
    (d : ResidualInputs T z L g R) (e : L ⧸ center L ≃* S)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (u : G) (E : Subgroup S)
    [IsElementaryAbelian p E] (hE : E ≤ residualImage e u) :
    ∃ A : Subgroup G, IsElementaryAbelian p A ∧
      A ≤ modifiedCentralizerResidual L u ∧
      (A.subgroupOf L).map (modelProjection e) = E ∧
      Nat.card A = Nat.card E ∧
      ∀ t : normalizer (L : Set G),
        E ≤ (MulAut.centralQuotientAction e (L.normalizerMonoidHom t)).fixedSubgroup →
        A ≤ centralizer ({t.val} : Set G) := by
  obtain ⟨A, hA, hAX, hmap, hcard⟩ := exists_elementary_residual_lift hG d e hp u E hE
  let : IsElementaryAbelian p A := hA
  have hsub : (A.map L.subtype).subgroupOf L = A := by
    apply map_injective L.subtype_injective
    exact map_subgroupOf_eq_of_le (map_subtype_le A)
  refine ⟨A.map L.subtype, IsElementaryAbelian.map _, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    exact hAX hy
  · rw [hsub, hmap]
  · rw [card_map_of_injective L.subtype_injective, hcard]
  · intro t ht
    exact elementary_lift_centralizes hG d e hp A t (hmap ▸ ht)

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator.Sporadic.JankoFourRudvalis
