module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.LieRows.G2
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.LieRows.HigherLinear
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# G₂ root and field comparison with the covering kernels retained

The long-root residual is an extension of SL₂(q) by a group of order q⁵;
the short-root fixed group is an extension of SL₂(q) by a group of order q³.
Their two-parts are q⁶ and q⁴. A field residual is the derived half-field
G₂ group, with two-part at most q³, including the binary endpoint. The
source center bound permits at most one additional factor of two upstairs.
These gaps survive the literal O³ modification and separate the rows.

The exact root extensions and individual Sylow markings are explicit earlier
table inputs, alongside the existing genuine root/field action table. They
assert no comparison. At G₂(2)′ the two actual residuals have orders 24 and
12, so their two-parts distinguish them even without a family-disjointness
premise. All inner involutions there have the individual central marking.

The older `G2.InnerEndpoint` route is incompatible with its own inner-row
order bound. A diagnostic below proves this; the present comparison never
uses that endpoint or removes an order-four component lift.

Source: Aschbacher–Smith, 16.1.2–4,6, printed pp.1170–1172;
I.2.2(5), pp.409–411; and 16.5.5–6(4), p.1197.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.LieRows.G2Complete
open Subgroup Theory.GroupTheory
open ClassificationModels
open Atlas.G2.EvenInvolutionGeometry
open SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Exceptional
open SylowSymmetry.ReverseDelta.Comparison.HigherLinear

/-- Genuine exact sequences and individual markings for the two root lengths. -/
structure RootRows (F : Type*) [Field F] (f : ℕ) : Prop where
  long_residual : ∀ x : Atlas.G2.Model F, IsLongRootElement x →
    Nonempty (TwoKernelExtension (pResidual 2 (MulAut.conj x).fixedSubgroup)
      (Matrix.SpecialLinearGroup (Fin 2) F) (5 * f))
  short_fixed : ∀ x : Atlas.G2.Model F, IsShortRootElement x →
    Nonempty (TwoKernelExtension (MulAut.conj x).fixedSubgroup
      (Matrix.SpecialLinearGroup (Fin 2) F) (3 * f))
  long_central : ∀ x : Atlas.G2.Model F, IsLongRootElement x →
    IsTwoCentralIn (MulAut.innerSubgroup _) (MulAut.conj x)
  short_noncentral : ∀ x : Atlas.G2.Model F, IsShortRootElement x →
    ¬ IsTwoCentralIn (MulAut.innerSubgroup _) (MulAut.conj x)

/-- The source root rows on every actual nonbinary field witness. -/
def RootTable : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (f : ℕ), 2 ≤ f →
    Nat.card F = 2 ^ f → RootRows F f

/-- Individual inner-root markings in the full G₂(2) action on G₂(2)′. -/
def BinaryMarkings : Prop :=
  ∀ x : Atlas.G2.Model (ZMod 2), x ∈ commutator (Atlas.G2.Model (ZMod 2)) →
    IsRootElement x → IsTwoCentralIn (MulAut.innerSubgroup _)
      (Atlas.G2.LieAutomorphismExtensions.binaryConjugation x)

/-- No inner actor satisfying the earlier order bound can admit the old endpoint. -/
theorem no_innerEndpoint {F : Type*} [Field F] {f : ℕ}
    (rows : G2InvolutionRows F f) (b : MulAut (Atlas.G2.Model F))
    (hb : orderOf b = 2) (hi : ∃ x, b = MulAut.conj x) :
    ¬ Nonempty (G2.InnerEndpoint F f b) := by
  obtain ⟨_, _, _, k, hk⟩ := rows.inner_root b hb hi
  rintro ⟨ep⟩
  exact ep.avoids_inner
    ((ep.odd.coprime_two_right.pow_right k).dvd_mul_left.mp (ep.divides.trans hk))

private theorem subgroup_valuation_le {H : Type*} [Group H] [Finite H]
    (K : Subgroup H) : padicValNat 2 (Nat.card K) ≤ padicValNat 2 (Nat.card H) := by
  have he : padicValNat 2 (Nat.card K) + padicValNat 2 K.index =
      padicValNat 2 (Nat.card H) := by
    rw [← padicValNat.mul Nat.card_pos.ne' K.index_ne_zero_of_finite, K.card_mul_index]
  omega

private theorem odd_factor_valuation {n k : ℕ} (hk : Odd k) :
    padicValNat 2 (2 ^ n * k) = n := by
  have hk0 : k ≠ 0 := fun h => by simp [h] at hk
  rw [padicValNat.mul (pow_ne_zero _ (by decide)) hk0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by simpa only [← even_iff_two_dvd,
      Nat.not_even_iff_odd] using hk), add_zero]

private theorem extension_valuation {F : Type*} [Field F] [Finite F]
    {f k : ℕ} (hf : 0 < f) (hF : Nat.card F = 2 ^ f)
    {X : Type*} [Group X] [Finite X]
    (s : TwoKernelExtension X (Matrix.SpecialLinearGroup (Fin 2) F) k) :
    padicValNat 2 (Nat.card X) = k + f := by
  rw [s.card, Atlas.card_sl_two, hF, ← mul_assoc, ← pow_add]
  exact odd_factor_valuation (binary_power_sub_one_odd hf (by decide : 0 < 2))

private theorem g2_valuation {F : Type*} [Field F] [Finite F]
    {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2 ^ f) :
    padicValNat 2 (Nat.card (Atlas.G2.Model F)) = 6 * f := by
  rw [Atlas.G2.card_Model, hF, mul_assoc,
    show (2 ^ f) ^ 6 = 2 ^ (6 * f) by rw [← pow_mul, Nat.mul_comm]]
  apply odd_factor_valuation
  simpa only [← pow_mul, Nat.mul_comm f 6] using
    (binary_power_sub_one_odd hf (by decide : 0 < 6)).mul
      (binary_power_sub_one_odd hf (by decide : 0 < 2))

private theorem central_valuation {F : Type*} [Field F] [Finite F]
    {f : ℕ} (hf : 2 ≤ f) (hF : Nat.card F = 2 ^ f)
    (rows : G2InvolutionRows F f) (roots : RootRows F f)
    (a : MulAut (Atlas.G2.Model F)) (ha2 : orderOf a = 2)
    (ha : IsTwoCentralIn (MulAut.innerSubgroup _) a) :
    padicValNat 2 (Nat.card (pResidual 2 a.fixedSubgroup)) = 6 * f := by
  obtain ⟨x, hx⟩ := (twoCentral_iff_odd_index.mp ha).2.1
  obtain ⟨y, hy, he, _⟩ := rows.inner_root a ha2 ⟨x, hx.symm⟩
  rcases hy with hl | hs
  · obtain ⟨s⟩ := roots.long_residual y hl
    rw [he, extension_valuation (by omega) hF s]
    omega
  · exact (roots.short_noncentral y hs (he ▸ ha)).elim

private theorem noncentral_valuation {F : Type*} [Field F] [Finite F]
    {f : ℕ} (hf : 2 ≤ f) (hF : Nat.card F = 2 ^ f)
    (rows : G2InvolutionRows F f) (roots : RootRows F f)
    (b : MulAut (Atlas.G2.Model F)) (hb2 : orderOf b = 2)
    (hb : ¬ IsTwoCentralIn (MulAut.innerSubgroup _) b) :
    padicValNat 2 (Nat.card (pResidual 2 b.fixedSubgroup)) ≤ 4 * f := by
  by_cases hi : ∃ x, b = MulAut.conj x
  · obtain ⟨y, hy, he, _⟩ := rows.inner_root b hb2 hi
    rcases hy with hl | hs
    · exact (hb (he.symm ▸ roots.long_central y hl)).elim
    · obtain ⟨s⟩ := roots.short_fixed y hs
      have h := subgroup_valuation_le (pResidual 2 b.fixedSubgroup)
      have hc := extension_valuation (by omega) hF s
      rw [he]
      rw [he] at h
      omega
  · obtain ⟨m, hm, hfm, _, ⟨e⟩⟩ := rows.outer_field b hb2 hi
    rw [Nat.card_congr e.toEquiv]
    have h := subgroup_valuation_le (commutator (Atlas.G2.Model (GaloisField 2 m)))
    rw [g2_valuation hm (GaloisField.card 2 m (Nat.ne_of_gt hm))] at h
    omega

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

private theorem covering_valuation_bounds [IsQuasisimple L]
    (hodd : pPrimeCore 2 L = ⊥) (hZ : Nat.card (center L) ≤ 2)
    {S : Type*} [Group S] [Finite S] (e : (L ⧸ center L) ≃* S)
    (u : normalizer (L : Set G)) :
    let n := padicValNat 2 (Nat.card (pResidual 2
      (quotientModelAction e (actionMap le_rfl u)).fixedSubgroup))
    n ≤ padicValNat 2 (Nat.card (modifiedCentralizerResidual L u.val)) ∧
      padicValNat 2 (Nat.card (modifiedCentralizerResidual L u.val)) ≤ n + 1 := by
  obtain ⟨k, hk, hkd, he⟩ := OtherRows.twoResidual_card_factor hodd e u
  have hk2 : k ≤ 2 := (Nat.le_of_dvd Nat.card_pos hkd).trans hZ
  have hkv : padicValNat 2 k ≤ 1 := by
    have : k = 1 ∨ k = 2 := by omega
    rcases this with rfl | rfl <;> simp
  dsimp only
  rw [quotientModelAction_actor, modifiedResidual_twoValuation, he, padicValNat.mul (Nat.ne_of_gt hk) Nat.card_pos.ne']
  change _ ≤ padicValNat 2 k + _ ∧ padicValNat 2 k + _ ≤ _ + 1
  omega

/-- G₂ comparison through the actual quotient action, including the possible
double cover at q=4 and every derived half-field endpoint. -/
theorem separation [IsQuasisimple L]
    (rows : G2InvolutionTable) (roots : RootTable)
    (hodd : pPrimeCore 2 L = ⊥) (hZ : Nat.card (center L) ≤ 2)
    {f : ℕ} (hf : 2 ≤ f) (model : IsG2At (L ⧸ center L) (2 ^ f))
    (u v : normalizer (L : Set G))
    (hu2 : orderOf (actionMap le_rfl u) = 2)
    (hv2 : orderOf (actionMap le_rfl v) = 2)
    (hu : IsTwoCentralIn (componentImage L) (actionMap le_rfl u))
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap le_rfl v)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃*
      modifiedCentralizerResidual L v.val) := by
  obtain ⟨F, hfield, hfin, hcard, ⟨e⟩⟩ := model
  let a := quotientModelAction e (actionMap le_rfl u)
  let b := quotientModelAction e (actionMap le_rfl v)
  have ha := central_valuation hf hcard (rows F f hf hcard) (roots F f hf hcard) a
    ((quotientModelAction_order e u).trans hu2)
    ((quotientModelAction_twoCentral_iff e _).mpr hu)
  have hb := noncentral_valuation hf hcard (rows F f hf hcard) (roots F f hf hcard) b
    ((quotientModelAction_order e v).trans hv2)
    (fun h => hv ((quotientModelAction_twoCentral_iff e _).mp h))
  have hua := (covering_valuation_bounds hodd hZ e u).1
  have hvb := (covering_valuation_bounds hodd hZ e v).2
  rintro ⟨d⟩
  have he := congrArg (padicValNat 2) (Nat.card_congr d.toEquiv)
  change padicValNat 2 (Nat.card (pResidual 2 a.fixedSubgroup)) ≤ _ at hua
  change _ ≤ padicValNat 2 (Nat.card (pResidual 2 b.fixedSubgroup)) + 1 at hvb
  omega

private theorem centerless_residual_card [IsQuasisimple L]
    (hodd : pPrimeCore 2 L = ⊥) (hZ : center L = ⊥)
    {S : Type*} [Group S] (e : (L ⧸ center L) ≃* S)
    (w : normalizer (L : Set G)) :
    Nat.card (involutionTwoResidual L w.val) = Nat.card
      (pResidual 2 (quotientModelAction e (actionMap le_rfl w)).fixedSubgroup) := by
  obtain ⟨k, _, hd, he⟩ := OtherRows.twoResidual_card_factor hodd e w
  rw [hZ, card_bot, Nat.dvd_one] at hd
  rw [quotientModelAction_actor, he, hd, one_mul]

private theorem centerless_fixedResidual_valuation_eq [IsQuasisimple L]
    (hodd : pPrimeCore 2 L = ⊥) (hZ : center L = ⊥)
    {S : Type*} [Group S] (e : (L ⧸ center L) ≃* S)
    (u v : normalizer (L : Set G))
    (d : modifiedCentralizerResidual L u.val ≃* modifiedCentralizerResidual L v.val) :
    padicValNat 2 (Nat.card (pResidual 2
      (quotientModelAction e (actionMap le_rfl u)).fixedSubgroup)) =
    padicValNat 2 (Nat.card (pResidual 2
      (quotientModelAction e (actionMap le_rfl v)).fixedSubgroup)) := by
  rw [← centerless_residual_card hodd hZ e u, ← centerless_residual_card hodd hZ e v,
    ← modifiedResidual_twoValuation, ← modifiedResidual_twoValuation,
    Nat.card_congr d.toEquiv]

private theorem binary_central_card (rows : BinaryG2InvolutionRows)
    (a : MulAut (commutator (Atlas.G2.Model (ZMod 2)))) (ha2 : orderOf a = 2)
    (ha : IsTwoCentralIn (MulAut.innerSubgroup _) a) :
    Nat.card (pResidual 2 a.fixedSubgroup) = 24 := by
  obtain ⟨x, hx⟩ := (twoCentral_iff_odd_index.mp ha).2.1
  obtain ⟨_, _, _, _, ⟨ei⟩⟩ := rows.inner_root a ha2 ⟨x, hx.symm⟩
  exact (Nat.card_congr ei.toEquiv).trans Atlas.G2.BinaryParabolicPair.ResidualAction.card_K

private theorem binary_noncentral_card (rows : BinaryG2InvolutionRows) (marks : BinaryMarkings)
    (b : MulAut (commutator (Atlas.G2.Model (ZMod 2)))) (hb2 : orderOf b = 2)
    (hb : ¬ IsTwoCentralIn (MulAut.innerSubgroup _) b) :
    Nat.card (pResidual 2 b.fixedSubgroup) = 12 := by
  have hbOuter : ¬ ∃ x, b = MulAut.conj x := by
    intro hi
    obtain ⟨y, hy, hr, he, _⟩ := rows.inner_root b hb2 hi
    exact hb (he.symm ▸ marks y hy hr)
  obtain ⟨_, _, _, _, ⟨eo⟩⟩ := rows.outer_root b hb2 hbOuter
  calc
    Nat.card (pResidual 2 b.fixedSubgroup) = Nat.card (alternatingGroup (Fin 4)) :=
      Nat.card_congr eo.toEquiv
    _ = 12 := by rw [nat_card_alternatingGroup, Nat.card_fin]; norm_num

/-- The separate binary branch, using both actual residual carriers. O³
preserves their distinct two-parts, so no family-disjointness input is needed. -/
theorem separation_binary [IsQuasisimple L]
    (rows : BinaryG2InvolutionRows) (marks : BinaryMarkings)
    (hodd : pPrimeCore 2 L = ⊥) (hZ : center L = ⊥)
    (e : (L ⧸ center L) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (u v : normalizer (L : Set G))
    (hu2 : orderOf (actionMap le_rfl u) = 2)
    (hv2 : orderOf (actionMap le_rfl v) = 2)
    (hu : IsTwoCentralIn (componentImage L) (actionMap le_rfl u))
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap le_rfl v)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃*
      modifiedCentralizerResidual L v.val) := by
  let a := quotientModelAction e (actionMap le_rfl u)
  let b := quotientModelAction e (actionMap le_rfl v)
  have ha := binary_central_card rows a ((quotientModelAction_order e u).trans hu2)
    ((quotientModelAction_twoCentral_iff e _).mpr hu)
  have hb := binary_noncentral_card rows marks b ((quotientModelAction_order e v).trans hv2)
    (fun h => hv ((quotientModelAction_twoCentral_iff e _).mp h))
  rintro ⟨d⟩
  have he := centerless_fixedResidual_valuation_eq hodd hZ e u v d
  change padicValNat 2 (Nat.card (pResidual 2 a.fixedSubgroup)) =
    padicValNat 2 (Nat.card (pResidual 2 b.fixedSubgroup)) at he
  rw [ha, hb] at he
  have h24 : padicValNat 2 24 = 3 := odd_factor_valuation (n := 3) (k := 3) (by decide)
  have h12 : padicValNat 2 12 = 2 := odd_factor_valuation (n := 2) (k := 3) (by decide)
  omega

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.LieRows.G2Complete
