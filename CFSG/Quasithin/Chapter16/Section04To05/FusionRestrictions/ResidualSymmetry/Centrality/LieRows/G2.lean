module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.LieRows.Actions
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.LieRows.QuotientActions
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.OtherRows.Marking
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Exceptional.Rows
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Exceptional.Arithmetic
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.Residual

/-!
# G₂ residual-row separation

The G₂ table has two logically different sources of separation.  An outer
field involution has a half-field residual, while an inner root involution has
the parabolic odd bound.  The transfer below compares these rows through the
actual central quotient and therefore retains the covering kernel of the
component.  The arithmetic endpoint is deliberately an explicit input: it is
the small source calculation that removes the possible factor three from the
O³ modification.

The binary endpoint is kept separate.  There the inner residual is the
quaternion--cubic subgroup `K` of order 24 and the outer residual is `A₄` of
order 12.  Its proof uses the trivial-cover clause explicitly; no central
kernel is silently discarded.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
16.1.2--4, pp.1170--1172, I.2.2(5b), pp.409--411, and 16.5.6(4), p.1197.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.LieRows.G2

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry
open CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality
open CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows
open CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta
open CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Exceptional

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

private theorem coprime_dvd_pResidual_iff {H : Type*} [Group H] [Finite H]
    {p n : ℕ} [Fact p.Prime] (hcop : Nat.Coprime n p) :
    n ∣ Nat.card (pResidual p H) ↔ n ∣ Nat.card H := by
  constructor
  · exact fun h => h.trans (card_subgroup_dvd_card _)
  · intro h
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_quotient_pResidual (G := H) p)
    have hc := (pResidual p H).card_mul_index
    rw [index_eq_card, hk] at hc
    exact ((hcop.pow_right k).dvd_mul_right).mp (hc ▸ h)

/-- Coprime odd divisors survive the literal O³ modification. -/
private theorem coprime_dvd_modified_iff_twoResidual
    {u : G} {n : ℕ} (hcop : Nat.Coprime n 3) :
    n ∣ Nat.card (modifiedCentralizerResidual L u) ↔
      n ∣ Nat.card (involutionTwoResidual L u) := by
  classical
  unfold modifiedCentralizerResidual
  split_ifs
  · rw [card_map_of_injective (subtype_injective _)]
    exact coprime_dvd_pResidual_iff hcop
  · rfl

/-- Odd, three-coprime divisors of a modified residual are detected by the
specified quotient action.  The central image and its covering kernel remain
explicit in the proof. -/
private theorem odd_coprime_modified_iff_fixed
    [IsQuasisimple L] (hodd : pPrimeCore 2 L = ⊥)
    {H : Type*} [Group H] [Finite H]
    (e : (L ⧸ center L) ≃* H) (u : normalizer (L : Set G)) {n : ℕ}
    (hn : Odd n) (hcop3 : Nat.Coprime n 3) :
    n ∣ Nat.card (modifiedCentralizerResidual L u.val) ↔
      n ∣ Nat.card (pResidual 2
        (quotientModelAction e (actionMap le_rfl u)).fixedSubgroup) := by
  have hXL : involutionTwoResidual L u.val ≤ L :=
    (involutionTwoResidual_le L u.val).trans inf_le_left
  rw [coprime_dvd_modified_iff_twoResidual hcop3]
  rw [← odd_dvd_centralImage_iff hodd hXL hn]
  rw [Nat.card_congr (quotientResidualEquiv hodd e u).toEquiv]

/-- An arithmetic half-field endpoint used by the outer G₂ row.
The endpoint is intentionally a data record: the source comparison may choose
the quotient of `q⁴ + q² + 1` by its possible factor three, or another
primitive odd divisor. -/
structure OddEndpoint (m : ℕ) where
  n : ℕ
  odd : Odd n
  coprime_three : Nat.Coprime n 3
  divides : n ∣ (2 ^ m) ^ 6 - 1
  avoids_inner : ¬ n ∣ (2 ^ m) ^ 4 - 1

private theorem g2_derived_odd_divisor {m n : ℕ} (hm : 0 < m)
    (hn : Odd n) (hdiv : n ∣ (2 ^ m) ^ 6 - 1) :
    n ∣ Nat.card (commutator (Atlas.G2.Model (GaloisField 2 m))) := by
  rw [← Atlas.G2.EvenFieldFixedResidual.twoResidual_eq_commutator]
  apply (odd_dvd_residual_iff hn).mpr
  rw [Atlas.G2.card_Model, GaloisField.card 2 m (Nat.ne_of_gt hm)]
  exact hdiv.trans ⟨(2 ^ m) ^ 6 * ((2 ^ m) ^ 2 - 1), by ring⟩

/-- Separate a central root row from an outer-field G₂ row.  The root and
field witnesses are taken from the earlier table; only the odd endpoint is a
numerical source input. -/
theorem separation_outer_field
    [IsQuasisimple L] (hodd : pPrimeCore 2 L = ⊥)
    {F : Type*} [Field F] [Finite F] {f : ℕ}
    (e : (L ⧸ center L) ≃* Atlas.G2.Model F)
    (rows : G2InvolutionRows F f)
    (endpoint : ∀ m : ℕ, 0 < m → OddEndpoint m)
    (u v : normalizer (L : Set G))
    (hu2 : orderOf (actionMap le_rfl u) = 2)
    (hv2 : orderOf (actionMap le_rfl v) = 2)
    (hu : IsTwoCentralIn (componentImage L) (actionMap le_rfl u))
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap le_rfl v))
    (hvOuter : ¬ ∃ x : Atlas.G2.Model F,
      quotientModelAction e (actionMap le_rfl v) = MulAut.conj x) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃*
      modifiedCentralizerResidual L v.val) := by
  let _ : Group.IsPerfect L := IsQuasisimple.toIsPerfect
  let a := quotientModelAction e (actionMap le_rfl u)
  let b := quotientModelAction e (actionMap le_rfl v)
  have ha2 : orderOf a = 2 :=
    (quotientModelAction_order e u).trans hu2
  have hb2 : orderOf b = 2 :=
    (quotientModelAction_order e v).trans hv2
  have _hv_used : ¬ IsTwoCentralIn (componentImage L) (actionMap le_rfl v) := hv
  obtain ⟨_, ⟨kcentral, hkcentral, _⟩⟩ :=
    (action_twoCentral_iff u).mp hu
  have haInner : ∃ x : Atlas.G2.Model F, a = MulAut.conj x := by
    refine ⟨e (QuotientGroup.mk' (center L) kcentral), ?_⟩
    dsimp [a]
    rw [quotientModelAction_actor, hkcentral,
      MulAut.centralQuotientAction_conj]
    rfl
  obtain ⟨_, _, hxa, ⟨k, hbound⟩⟩ := rows.inner_root a ha2 haInner
  obtain ⟨m, hm, hfm, _, ⟨eb⟩⟩ := rows.outer_field b hb2 hvOuter
  let ep := endpoint m hm
  have hf2 : 2 ^ f = (2 ^ m) ^ 2 := by
    rw [hfm, Nat.mul_comm, pow_mul]
  have hbound' : Nat.card a.fixedSubgroup ∣ 2 ^ k * ((2 ^ m) ^ 4 - 1) := by
    simpa only [hf2, ← pow_mul, Nat.mul_assoc, Nat.reduceMul] using hbound
  have hnfixed : ep.n ∣ Nat.card (pResidual 2 b.fixedSubgroup) := by
    rw [Nat.card_congr eb.toEquiv]
    exact g2_derived_odd_divisor hm ep.odd ep.divides
  rintro ⟨d⟩
  have hnv : ep.n ∣ Nat.card (modifiedCentralizerResidual L v.val) :=
    (odd_coprime_modified_iff_fixed hodd e v ep.odd ep.coprime_three).mpr hnfixed
  have hnu : ep.n ∣ Nat.card (modifiedCentralizerResidual L u.val) := by
    rw [Nat.card_congr d.toEquiv]
    exact hnv
  have hna : ep.n ∣ Nat.card (pResidual 2 a.fixedSubgroup) :=
    (odd_coprime_modified_iff_fixed hodd e u ep.odd ep.coprime_three).mp hnu
  have hna' : ep.n ∣ Nat.card a.fixedSubgroup :=
    (odd_dvd_residual_iff ep.odd).mp hna
  have hdiv := hna'.trans hbound'
  have hinnerdiv : ep.n ∣ (2 ^ m) ^ 4 - 1 :=
    (ep.odd.coprime_two_right.pow_right k).dvd_mul_left.mp hdiv
  exact ep.avoids_inner hinnerdiv

/- The same transfer applies when the noncentral actor is an inner root.
The earlier row table supplies the root witness and its fixed-subgroup bound;
the endpoint records the additional odd divisor supplied by the source
16.4 geometry.  Keeping that divisor explicit avoids identifying long and
short roots or silently treating an ambient involution as a lift in `L`. -/
structure InnerEndpoint (F : Type*) [Field F] (f : ℕ)
    (b : MulAut (Atlas.G2.Model F)) where
  n : ℕ
  odd : Odd n
  coprime_three : Nat.Coprime n 3
  divides : n ∣ Nat.card b.fixedSubgroup
  avoids_inner : ¬ n ∣ (2 ^ f) ^ 2 - 1

theorem separation_inner_root
    [IsQuasisimple L] (hodd : pPrimeCore 2 L = ⊥)
    {F : Type*} [Field F] [Finite F] {f : ℕ}
    (e : (L ⧸ center L) ≃* Atlas.G2.Model F)
    (rows : G2InvolutionRows F f)
    (endpoint : ∀ b : MulAut (Atlas.G2.Model F), orderOf b = 2 →
      InnerEndpoint F f b)
    (u v : normalizer (L : Set G))
    (hu2 : orderOf (actionMap le_rfl u) = 2)
    (hv2 : orderOf (actionMap le_rfl v) = 2)
    (hu : IsTwoCentralIn (componentImage L) (actionMap le_rfl u))
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap le_rfl v))
    (hvInner : ∃ x : Atlas.G2.Model F,
      quotientModelAction e (actionMap le_rfl v) = MulAut.conj x) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃*
      modifiedCentralizerResidual L v.val) := by
  let _ : Group.IsPerfect L := IsQuasisimple.toIsPerfect
  let a := quotientModelAction e (actionMap le_rfl u)
  let b := quotientModelAction e (actionMap le_rfl v)
  have ha2 : orderOf a = 2 :=
    (quotientModelAction_order e u).trans hu2
  have hb2 : orderOf b = 2 :=
    (quotientModelAction_order e v).trans hv2
  have _hv_used : ¬ IsTwoCentralIn (componentImage L) (actionMap le_rfl v) := hv
  obtain ⟨_, ⟨kcentral, hkcentral, _⟩⟩ :=
    (action_twoCentral_iff u).mp hu
  have haInner : ∃ x : Atlas.G2.Model F, a = MulAut.conj x := by
    refine ⟨e (QuotientGroup.mk' (center L) kcentral), ?_⟩
    dsimp [a]
    rw [quotientModelAction_actor, hkcentral,
      MulAut.centralQuotientAction_conj]
    rfl
  obtain ⟨_, _, _, ⟨k, hbound⟩⟩ := rows.inner_root a ha2 haInner
  obtain ⟨_, _, _, _⟩ := rows.inner_root b hb2 hvInner
  let ep := endpoint b hb2
  have hnfixed : ep.n ∣ Nat.card (pResidual 2 b.fixedSubgroup) := by
    exact (odd_dvd_residual_iff ep.odd).mpr ep.divides
  rintro ⟨d⟩
  have hnv : ep.n ∣ Nat.card (modifiedCentralizerResidual L v.val) :=
    (odd_coprime_modified_iff_fixed hodd e v ep.odd ep.coprime_three).mpr hnfixed
  have hnu : ep.n ∣ Nat.card (modifiedCentralizerResidual L u.val) := by
    rw [Nat.card_congr d.toEquiv]
    exact hnv
  have hna : ep.n ∣ Nat.card (pResidual 2 a.fixedSubgroup) :=
    (odd_coprime_modified_iff_fixed hodd e u ep.odd ep.coprime_three).mp hnu
  have hna' : ep.n ∣ Nat.card a.fixedSubgroup :=
    (odd_dvd_residual_iff ep.odd).mp hna
  have hdiv := hna'.trans hbound
  have hinnerdiv : ep.n ∣ (2 ^ f) ^ 2 - 1 :=
    (ep.odd.coprime_two_right.pow_right k).dvd_mul_left.mp hdiv
  exact ep.avoids_inner hinnerdiv

/-- The binary G₂ endpoint, with the centerless-cover clause explicit. -/
theorem separation_binary
    [IsQuasisimple L] (hodd : pPrimeCore 2 L = ⊥)
    (hZ : center L = ⊥)
    (hthree : ¬ HasEvenLinearThreeType L)
    (e : (L ⧸ center L) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (rows : BinaryG2InvolutionRows)
    (u v : normalizer (L : Set G))
    (hu2 : orderOf (actionMap le_rfl u) = 2)
    (hv2 : orderOf (actionMap le_rfl v) = 2)
    (hu : IsTwoCentralIn (componentImage L) (actionMap le_rfl u))
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap le_rfl v))
    (hvOuter : ¬ ∃ x : commutator (Atlas.G2.Model (ZMod 2)),
      quotientModelAction e (actionMap le_rfl v) = MulAut.conj x) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃*
      modifiedCentralizerResidual L v.val) := by
  let _ : Group.IsPerfect L := IsQuasisimple.toIsPerfect
  let a := quotientModelAction e (actionMap le_rfl u)
  let b := quotientModelAction e (actionMap le_rfl v)
  have ha2 : orderOf a = 2 := (quotientModelAction_order e u).trans hu2
  have hb2 : orderOf b = 2 := (quotientModelAction_order e v).trans hv2
  have _hv_used : ¬ IsTwoCentralIn (componentImage L) (actionMap le_rfl v) := hv
  obtain ⟨_, ⟨kcentral, hkcentral, _⟩⟩ := (action_twoCentral_iff u).mp hu
  have haInner : ∃ x : commutator (Atlas.G2.Model (ZMod 2)),
      a = MulAut.conj x := by
    refine ⟨e (QuotientGroup.mk' (center L) kcentral), ?_⟩
    dsimp [a]
    rw [quotientModelAction_actor, hkcentral,
      MulAut.centralQuotientAction_conj]
    rfl
  obtain ⟨x, hxmem, hxroot, hxa, ⟨ei⟩⟩ := rows.inner_root a ha2 haInner
  obtain ⟨x', hxmem', hxroot', hxb, ⟨eo⟩⟩ :=
    rows.outer_root b hb2 hvOuter
  have hXu : involutionTwoResidual L u.val ≃*
      pResidual 2 a.fixedSubgroup := by
    exact (centralImageEquiv (involutionTwoResidual_le L u.val |>.trans inf_le_left) hZ).trans
      (quotientResidualEquiv hodd e u)
  have hXv : involutionTwoResidual L v.val ≃*
      pResidual 2 b.fixedSubgroup := by
    exact (centralImageEquiv (involutionTwoResidual_le L v.val |>.trans inf_le_left) hZ).trans
      (quotientResidualEquiv hodd e v)
  have hmodu : modifiedCentralizerResidual L u.val = involutionTwoResidual L u.val := by
    simp [modifiedCentralizerResidual, hthree]
  have hmodv : modifiedCentralizerResidual L v.val = involutionTwoResidual L v.val := by
    simp [modifiedCentralizerResidual, hthree]
  have hcu : Nat.card (modifiedCentralizerResidual L u.val) = 24 := by
    rw [hmodu, Nat.card_congr hXu.toEquiv, Nat.card_congr ei.toEquiv]
    exact Atlas.G2.BinaryParabolicPair.ResidualAction.card_K
  have hcv : Nat.card (modifiedCentralizerResidual L v.val) = 12 := by
    rw [hmodv, Nat.card_congr hXv.toEquiv, Nat.card_congr eo.toEquiv]
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  rintro ⟨d⟩
  have heq := Nat.card_congr d.toEquiv
  rw [hcu, hcv] at heq
  omega

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.LieRows.G2
