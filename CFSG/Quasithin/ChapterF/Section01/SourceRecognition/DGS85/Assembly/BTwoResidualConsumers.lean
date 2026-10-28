module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoResidual
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoRegularConsumers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.LocalActor
public import Theory.SpecificGroups.SL2.FieldCardinality

/-!
# Original Chapter 12 residual orders in the strict distance-two branch

The constructed source action identifies its alpha field with the original
PSL2 parameter by the literal actor-core quotient. Thus q_alpha = 2^n,
and the earlier positive field-power relation gives m = n*r with r > 0
for the actual selected opposite component. No field parameter is replaced.

The residual application retains one opposite-center conjugator for the
whole-core centralizer, the four-core intersection and the multiplication
isomorphism Z_alpha times R_alpha to D_alpha. It supplies the exact original
core formula |Q_alpha| = q_alpha^2 q_beta^2 |R_alpha|, with nonzero elementary
R_alpha. The full reduced Borel B_0 and both odd factors remain inside the
original completion, and the two-core is that of the full original parabolic.

This discharges the earlier action and marking premises of the residual
calculation for the literal Chapter 12 configuration. The missing residual
separation (10.8), residual order, path parameters and recognition remain
source obligations. All commuting branches and general Chapter 15 restoration
also remain with the source assembly.

Source: DGS (1985), (10.4), (10.7)--(10.10), pp.155--165;
Aschbacher--Smith F.1.11--F.1.12 and 12.2.2, pp.263--264,795--796.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.Assembly
universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
local notation "F" => Reduction.reducedFamily ![L,R] (sourceS L H)
local notation "ι" => Subgroup.subtype (G₀ ![L,R] (sourceS L H))

omit [Finite G] in
private theorem alpha_field_card
    {k E : Type*} [Field k] [Finite k] [CharP k 2]
    [AddCommGroup E] [Module (ZMod 2) E]
    (hF : HypothesisF11 ![L,R] (sourceS L H))
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n)) {u : Vertex F}
    (c : BTwoCenterActionData F (base F false) (base F true) u k E)
    (hactor : c.actor = graphLocalGroup F (base F false)) : Nat.card k = 2^n := by
  have hcore : c.actor.pCoreIn 2 = Q F (base F false) := by
    rw [hactor]
    exact CommutingTrivial.graphLocalGroup_core (reduced_triple hF) (base F false)
  have hker : c.quotient.ker = pCore 2 c.actor := by
    rw [c.kernel,←hcore]
    exact comap_map_eq_self_of_injective c.actor.subtype_injective _
  let eA := MulEquiv.subgroupCongr hactor
  let eQ := QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)
  obtain ⟨K,fK,finK,hK,⟨eK⟩⟩ := hL
  let := fK
  let := finK
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  let eL := (reduced_graphLinearQuotient hF false eK).trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  let e := (QuotientGroup.quotientKerEquivOfSurjective c.quotient c.onto).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans (eQ.trans eL))
  exact (Matrix.SL2.field_card_eq_of_equiv e).trans hK

/-- The actual original core order is reduced to the order of one nontrivial
elementary residual, with a common opposite-center conjugator throughout. -/
theorem residual_orders_of_critical_bTwo_source
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    {u t : Vertex F}
    (hc : IsCriticalPair F (base F false) u)
    (hne : ⁅Z F (base F false),Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj (base F true) u)
    (ht : (graph F).Adj (base F false) t) (htne : t ≠ base F true) :
    ∃ q m : ℕ, 2 < q ∧ q = 2^n ∧ 1 < m ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^m) ∧
      (∃ r : ℕ, 0 < r ∧ m = n*r) ∧
      ∃ g : G₀ ![L,R] (sourceS L H),
      g • base F false = base F false ∧ g • base F true = t ∧
      let Q₀ := (parabolic ![L,R] (sourceS L H) 0).pCoreIn 2
      let D₀ := (parabolic ![L,R] (sourceS L H) 1).pCoreIn 2 ⊓ (Q F t).map ι
      let Z₀ := (Z F (base F false)).map ι
      let W₀ := (Z F u).map ι ⊔ (Z F (g • u)).map ι
      let R₀ := D₀ ⊓ centralizer (W₀ : Set G)
      W₀ ⊔ Q₀ = enlargedEndpoint ![L,R] (sourceS L H) 0 ∧
      R₀ = (D₀ ⊓ (Q F u).map ι) ⊓ (Q F (g • u)).map ι ∧
      Q₀ ⊓ centralizer (W₀ : Set G) = R₀ ∧
      R₀ ≠ ⊥ ∧ IsElementaryAbelian 2 D₀ ∧ IsElementaryAbelian 2 R₀ ∧
      D₀ = Z₀ ⊔ R₀ ∧ Disjoint Z₀ R₀ ∧
      (∃ e : Z₀ × R₀ ≃* D₀, ∀ z r, (e (z,r) : G) = (z : G) * (r : G)) ∧
      Nat.card Z₀ = q^2 ∧ Nat.card D₀ = q^2 * Nat.card R₀ ∧
      Nat.card Q₀ = q^2 * (2^m)^2 * Nat.card R₀ ∧
      P₀ ![L,R] (sourceS L H) 0 ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      B₀ ![L,R] (sourceS L H) ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) := by
  obtain ⟨k,f,fin,ch,a,c,hactor,hk,m,hm,hR,hpow,g,hg,hh⟩ :=
    BTwoSource.original_strict_residual (d.hypothesisF11 h hTH) hc hne hb hβu ht htne
      (d.parabolics_not_solvable h hp 0)
  have hq := alpha_field_card (d.hypothesisF11 h hTH) h.linear c hactor
  have hdegrees : ∃ r : ℕ, 0 < r ∧ m = n*r := by
    obtain ⟨r,hr,he⟩ := hpow
    rw [hq,←pow_mul] at he
    exact ⟨r,hr,Nat.pow_right_injective (by decide) he⟩
  exact ⟨Nat.card k,m,hk,hq,hm,hR,hdegrees,(g : G₀ ![L,R] (sourceS L H)),
    c.actor_le g.property,hg,hh⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.OriginalExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
include D h hmany hn hpsl hH

/-- The literal Chapter 12 residual and core orders retain the original
selected R, full endpoint/Borel normalizers and the same opposite conjugator. -/
theorem rankOne_residual_orders_of_critical_bTwo_source
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
    {u t : Vertex (Reduction.reducedFamily ![L,R] (Global.sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) false) u)
    (hne : ⁅Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) false),
      Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) u⁆ ≠ ⊥)
    (hb : b (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) = 2)
    (hβu : (graph (Reduction.reducedFamily ![L,R] (Global.sourceS L H))).Adj
      (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) true) u)
    (ht : (graph (Reduction.reducedFamily ![L,R] (Global.sourceS L H))).Adj
      (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) false) t)
    (htne : t ≠ base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) true) :
    let F := Reduction.reducedFamily ![L,R] (Global.sourceS L H)
    let ι := (G₀ ![L,R] (Global.sourceS L H)).subtype
    ∃ q m : ℕ, 2 < q ∧ q = 2^n ∧ 1 < m ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^m) ∧
      (∃ r : ℕ, 0 < r ∧ m = n*r) ∧
      ∃ g : G₀ ![L,R] (Global.sourceS L H),
      g • base F false = base F false ∧ g • base F true = t ∧
      let Q₀ := (parabolic ![L,R] (Global.sourceS L H) 0).pCoreIn 2
      let D₀ := (parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2 ⊓ (Q F t).map ι
      let Z₀ := (Z F (base F false)).map ι
      let W₀ := (Z F u).map ι ⊔ (Z F (g • u)).map ι
      let R₀ := D₀ ⊓ centralizer (W₀ : Set G)
      W₀ ⊔ Q₀ = enlargedEndpoint ![L,R] (Global.sourceS L H) 0 ∧
      R₀ = (D₀ ⊓ (Q F u).map ι) ⊓ (Q F (g • u)).map ι ∧
      Q₀ ⊓ centralizer (W₀ : Set G) = R₀ ∧
      R₀ ≠ ⊥ ∧ IsElementaryAbelian 2 D₀ ∧ IsElementaryAbelian 2 R₀ ∧
      D₀ = Z₀ ⊔ R₀ ∧ Disjoint Z₀ R₀ ∧
      (∃ e : Z₀ × R₀ ≃* D₀, ∀ z r, (e (z,r) : G) = (z : G) * (r : G)) ∧
      Nat.card Z₀ = q^2 ∧ Nat.card D₀ = q^2 * Nat.card R₀ ∧
      Nat.card Q₀ = q^2 * (2^m)^2 * Nat.card R₀ ∧
      P₀ ![L,R] (Global.sourceS L H) 0 ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      B₀ ![L,R] (Global.sourceS L H) ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) :=
  d.residual_orders_of_critical_bTwo_source
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp hc hne hb hβu ht htne

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
