module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.TerminalConstruction.Binary
public import Theory.GroupTheory.CoprimePrimeFusion
public import Theory.SpecificGroups.BinaryLinear.SevenConjugacy
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Innerness of the literal binary point-quotient action

The natural marking of V/V₁ identifies L₁/O₂(L₁) with GL_(n−1)(2).
Every t in T preserves V and gives a linear intertwiner, hence acts innerly
on this quotient. Coprime fusion lifts its conjugacy on a seven-element
to conjugacy inside L₁. The image of that element in K₁/O₂(K₁) still has
order seven, so the graph-automorphism obstruction proves innerness there.
This uses the original L₁, K₁ and their quotient maps; it needs no
classification of the embedding and no extra action premise. The containing
point-subgroup version applies before ComponentGeometry is constructed, and
also supplies the full point-join quotient in the degree-five component proof.

The actual consumer constructs the escaping cubic overgroup and terminal
configuration in all three surviving models. Together with the previously
proved fusion stage, only component/abelianity and local control remain
with qt-d-1291-natural-source for the full natural-branch assembly.

Source: Aschbacher--Smith, 12.8.3(1), 12.9.7 and the final proof of 12.9.1,
printed pp.850,862--864 of refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The actual ambient Sylow subgroup normalizes the literal two-residual L₁. -/
theorem sylow_normalizes_point_residual
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) : (T : Subgroup G) ≤ normalizer (F.Li L 1 : Set G) := by
  have hi : (T : Subgroup G) ≤ normalizer ((L ⊓ F.H : Subgroup G) : Set G) :=
    (le_inf (h.sylow_normalizes earlier.structural)
      ((F.invariant 1).trans F.H.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have he : F.Li L 1 = (pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype := by
    unfold Li
    rw [if_neg (by omega)]
    rfl
  rw [he]
  exact hi.trans (normalizer_le_normalizer_characteristic_image _ _)

private theorem seven_dvd_linear_card {d : ℕ} (hd : d = 3 ∨ d = 4) :
    7 ∣ Nat.card (BinaryLinear.OuterCyclic.LinearGroup d) := by
  rw [← Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear d).toEquiv,
    Matrix.card_GL_field]
  rcases hd with rfl | rfl <;> norm_num <;> decide

/-- The natural point quotient supplies a seven-element in the original L₁. -/
theorem point_residual_has_seven
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (F : InvariantFlag T V n) : ∃ x : F.Li L 1, orderOf x = 7 := by
  let := h.chosen.elementary
  let : IsElementaryAbelian 2 (V.subgroupOf F.H) :=
    IsElementaryAbelian.subgroupOf ((le_conjugateSpanBy V F.H).trans F.U_le_H)
  let : IsElementaryAbelian 2 (F.tilde V) :=
    IsElementaryAbelian.map (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.H))
  obtain ⟨D⟩ := F.naturalSeedMarking_of_ambient h.rank.1 L h.chosen.normalizes h.naturalMarking
  let e := D.fullQuotientEquiv (by omega)
  have hd : 7 ∣ Nat.card (F.Li L 1 ⧸ pCore 2 (F.Li L 1)) := by
    rw [Nat.card_congr e.toEquiv]
    exact seven_dvd_linear_card (by omega)
  exact exists_prime_orderOf_dvd_card' 7 (hd.trans (card_quotient_dvd_card _))

/-- Sylow conjugation of a seven-element is already realized inside L₁. -/
theorem sylow_conjugate_seven_in_point_residual
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (t : T) (x : F.Li L 1) (hx : orderOf x = 7) :
    IsConj x (F.localConjugation L (T : Subgroup G)
      (sylow_normalizes_point_residual h earlier F) t x) := by
  let := h.chosen.elementary
  let : IsElementaryAbelian 2 (V.subgroupOf F.H) :=
    IsElementaryAbelian.subgroupOf ((le_conjugateSpanBy V F.H).trans F.U_le_H)
  let : IsElementaryAbelian 2 (F.tilde V) :=
    IsElementaryAbelian.map (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.H))
  obtain ⟨D⟩ := F.naturalSeedMarking_of_ambient h.rank.1 L h.chosen.normalizes h.naturalMarking
  let hTN := sylow_normalizes_point_residual h earlier F
  let α := F.localConjugation L (T : Subgroup G) hTN t
  let q := QuotientGroup.mk' (pCore 2 (F.Li L 1))
  let e := D.fullQuotientEquiv (by omega)
  have hTV : (t : G) ∈ normalizer (V : Set G) := by
    simpa only [F.last] using F.invariant n t.property
  obtain ⟨c,hc⟩ := seed_intertwiner_of_normalizes (hLV := h.chosen.normalizes)
    (F.invariant 1) hTN t hTV
  obtain ⟨a,ha⟩ := D.modelConjugation_inner_of_intertwiner (by omega)
    (T : Subgroup G) hTN t c hc
  have hconj : IsConj (q x) (q (α x)) := by
    apply isConj_iff.mpr
    refine ⟨e.symm a, ?_⟩
    apply e.injective
    rw [map_mul,map_mul,map_inv,e.apply_symm_apply]
    have he := D.modelConjugation_actor (by omega) (T : Subgroup G) hTN t x
    rw [← ha] at he
    exact he
  have hcop : Nat.Coprime 7 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := F.Li L 1)).exists_card_eq
    rw [hk]
    exact (by decide : Nat.Coprime 7 2).pow_right k
  exact q.isConj_of_map_isConj_of_prime_order_of_coprime_ker (QuotientGroup.mk'_surjective _) hcop hx
    ((α.orderOf_eq x).trans hx) hconj

/-- Innerness for any Sylow-normalized subgroup containing the original
point residual, with a binary linear quotient. -/
theorem binary_normalized_point_overgroup_sylow_acts_inner
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (J : Subgroup G) (hLJ : F.Li L 1 ≤ J)
    (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G))
    {d : ℕ} (hd : d = 4 ∨ d = 5)
    (model : ClassicalGroup.IsPSL (J ⧸ pCore 2 J) d 2) :
    ∀ t : T, quotientAut (pCore 2 J)
      (J.normalizerMonoidHom ⟨t,hTJ t.property⟩) ∈
      MulAut.innerSubgroup (J ⧸ pCore 2 J) := by
  obtain ⟨k,hk,hfin,hcard,⟨e₀⟩⟩ := model
  let ek := Theory.SpecificGroups.SymplecticSix.fieldEquivZModTwo k hcard
  let e := (e₀.trans (Atlas.fieldEquivPSL d ek)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega : 0 < d))
  obtain ⟨x,hx⟩ := point_residual_has_seven h hn F
  let q := QuotientGroup.mk' (pCore 2 J)
  let xK := inclusion hLJ x
  have hxK : orderOf xK = 7 :=
    (orderOf_injective (inclusion hLJ) (inclusion_injective _) x).trans hx
  have hcop : Nat.Coprime 7 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := J)).exists_card_eq
    rw [hk]
    exact (by decide : Nat.Coprime 7 2).pow_right k
  have hxp : IsPGroup 7 (zpowers xK) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,hxK,pow_one])
  have hxq : orderOf (q xK) = 7 := by
    have hi := injective_comp_subtype_of_coprime_ker q hcop (zpowers xK) hxp
    have he := orderOf_injective (q.comp (zpowers xK).subtype) hi
      (⟨xK,mem_zpowers xK⟩ : zpowers xK)
    exact he.trans ((orderOf_injective (zpowers xK).subtype Subtype.val_injective
      (⟨xK,mem_zpowers xK⟩ : zpowers xK)).symm.trans hxK)
  intro t
  let a := quotientAut (pCore 2 J) (J.normalizerMonoidHom
    ⟨t,hTJ t.property⟩)
  obtain ⟨l,hl⟩ := isConj_iff.mp (sylow_conjugate_seven_in_point_residual h hn earlier F t x hx)
  have hf : a (q xK) = q (inclusion hLJ l) * q xK * (q (inclusion hLJ l))⁻¹ := by
    change quotientAut (pCore 2 J) _ (q xK) = _
    rw [quotientAut_apply_mk, ← map_inv, ← map_mul, ← map_mul]
    apply congrArg q
    apply Subtype.ext
    exact (congrArg (fun z : F.Li L 1 => (z : G)) hl).symm
  have hc : IsConj (e (q xK)) ((MulAut.congr e a) (e (q xK))) := by
    apply isConj_iff.mpr
    refine ⟨e (q (inclusion hLJ l)), ?_⟩
    simpa only [MulAut.congr_apply, MulEquiv.trans_apply, e.symm_apply_apply,map_mul,map_inv] using (congrArg e hf).symm
  obtain ⟨b,hb⟩ := BinaryLinear.inner_of_seven_conjugacy hd (e (q xK))
    ((e.orderOf_eq _).trans hxq) (MulAut.congr e a) hc
  refine ⟨e.symm b, ?_⟩
  apply MulEquiv.ext
  intro y
  apply e.injective
  have he := MulEquiv.congr_fun hb (e y)
  simpa only [MulAut.conj_apply,MulAut.congr_apply,MulEquiv.trans_apply,e.symm_apply_apply,
    map_mul,map_inv,e.apply_symm_apply] using he

/-- Innerness for any relatively normal containing point subgroup with a
binary linear quotient. This form can be used during component construction,
before the other flag components in ComponentGeometry have been identified. -/
theorem binary_containing_point_sylow_acts_inner
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (J : Subgroup G) (hJH : J ≤ F.H) (hLJ : F.Li L 1 ≤ J)
    (hJn : (J.subgroupOf F.H).Normal) {d : ℕ} (hd : d = 4 ∨ d = 5)
    (model : ClassicalGroup.IsPSL (J ⧸ pCore 2 J) d 2) :
    ∀ t : T, quotientAut (pCore 2 J)
      (J.normalizerMonoidHom ⟨t,((F.invariant 1).trans
        ((normal_subgroupOf_iff_le_normalizer hJH).mp hJn)) t.property⟩) ∈
      MulAut.innerSubgroup (J ⧸ pCore 2 J) :=
  binary_normalized_point_overgroup_sylow_acts_inner h hn earlier F J hLJ
    ((F.invariant 1).trans ((normal_subgroupOf_iff_le_normalizer hJH).mp hJn)) hd model

/-- The literal T-action on K₁/O₂(K₁) is inner in both binary-linear rows. -/
theorem binary_sylow_acts_inner
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (C : ComponentGeometry F L) {d : ℕ} (hd : d = 4 ∨ d = 5)
    (model : ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) d 2) : SylowActsInner C :=
  binary_containing_point_sylow_acts_inner h hn earlier F C.K1 C.point_le
    C.contains C.normal hd model

/-- Discharge the binary action obligation from the original natural-module setup. -/
theorem binaryInnerActionInput (K : GroupClass.{u}) : BinaryInnerActionInput K := by
  intro X _ _ T L V n h hn earlier F _ C _ model
  rcases model with model | model
  · exact binary_sylow_acts_inner h hn earlier F C (Or.inl rfl) model
  · exact binary_sylow_acts_inner h hn earlier F C (Or.inr rfl) model

/-- All three surviving models supply the escaping cubic overgroup. -/
theorem cubicOvergroupInput (K : GroupClass.{u}) : CubicOvergroupInput K :=
  cubicOvergroupInput_of_inner (binaryInnerActionInput K)

/-- Construct the actual terminal S₃ configuration from the preceding local
and fusion stages. Component geometry and local control are still discharged
by the natural-source assembly owner, qt-d-1291-natural-source. -/
theorem terminalInput (K : GroupClass.{u}) : TerminalInput K :=
  terminalInput_of_inner (binaryInnerActionInput K)

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
