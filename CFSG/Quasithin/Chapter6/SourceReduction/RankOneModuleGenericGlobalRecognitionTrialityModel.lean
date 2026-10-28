module
public import Theory.Representation.SL2.CoreQuotientDegree
public import Theory.GroupTheory.NoncentralChiefRefinement.OrderBound
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionLayers
public import Theory.SpecificGroups.Triality.ParabolicLocalStructure
public import Theory.SpecificGroups.Triality.Model.QTKEParameters

/-!
# The triality arms chief-layer bound

An actual binary chief factor of a finite group with quotient SL₂(2ᶠ)
above its two-core is an irreducible binary representation. The normal
two-core acts trivially on that factor; the established SL₂ degree bound
therefore gives dimension at least 2f whenever its action is noncentral.
Multiplication of the literal relative quotient orders telescopes along
the chief series, even when its top subgroup is nonabelian.

For the genuine triality arms factor, f = 3n and the two-core has order
2^(9n). Two noncentral chief factors would require order at least
2^(12n). Thus every actual chief series of that core has at most one
noncentral factor, including n = 1. This proves precisely the comparison
needed by the selected diagram factor, whose original normal core
intersection gives at least two. No new irreducibility assertion about
the whole arms Frattini quotient is needed.

The adjacent source extension transports the selected right factor through
the solvable residual of its actual parabolic, then applies this bound.
Source: Aschbacher–Smith 5.2.6, printed pp.650–651; E.2.13(4), p.225;
and F.1.12(I)(4), pp.262–264 (`refs/quasithin.pdf`). The root carrier,
quotient and core order are the existing genuine graph-field triality model.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation NoncentralChiefRefinement
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityComparison

private def chiefRepresentation
    {X : Type*} [Group X] {U : Subgroup X} [U.Normal]
    (s : SeriesOn U) (i : Fin s.series.length) [IsElementaryAbelian 2 (s.Factor i)] :
    Representation (ZMod 2) X (Additive (s.Factor i)) where
  toFun x := (s.action i x).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul (s.action i 1 v.toMul) = v
    rw [map_one]
    rfl
  map_mul' x y := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul (s.action i (x*y) v.toMul) = _
    rw [map_mul]
    rfl

private theorem chiefRepresentation_irreducible
    {X : Type*} [Group X] {U : Subgroup X} [U.Normal]
    (s : SeriesOn U) (i : Fin s.series.length) [IsElementaryAbelian 2 (s.Factor i)] :
    (chiefRepresentation s i).IsIrreducible := by
  let : Nontrivial (s.Factor i) := s.factor_nontrivial i
  rw [Representation.IsIrreducible,isSimpleOrder_iff]
  refine ⟨inferInstance,?_⟩
  intro W
  let K : Subgroup (s.Factor i) := AddSubgroup.toSubgroup' W.toSubmodule.toAddSubgroup
  rcases s.factor_irreducible i K (fun x v hv => W.apply_mem_toSubmodule x hv) with hz | ht
  · left
    apply bot_unique
    intro x hx
    have hx' : x.toMul ∈ K := hx
    rw [hz] at hx'
    exact hx'
  · right
    apply top_unique
    intro x _
    have hx' : x.toMul ∈ K := by rw [ht]; trivial
    exact hx'

private theorem chief_card_ge
    {X F : Type*} [Group X] [Finite X] [Field F] [Finite F] [CharP F 2]
    {U : Subgroup X} [U.Normal] (hU : IsPGroup 2 U)
    (e : (X ⧸ pCore 2 X) ≃* SL(2,F)) (s : SeriesOn U)
    (i : Fin s.series.length) (hi : ¬ s.Central i)
    (m : ℕ) (hm : m ≠ 0) (hF : Nat.card F = 2^m) :
    2^(2*m) ≤ Nat.card (s.Factor i) := by
  let := s.factor_elementary hU i
  let := chiefRepresentation_irreducible s i
  have hnt : ∃ x, chiefRepresentation s i x ≠ 1 := by
    by_contra! ht
    apply hi
    rw [s.central_iff_action]
    intro x v
    exact congrArg Additive.toMul
      (congrArg (fun f => f (Additive.ofMul v)) (ht x))
  have hd := Representation.SL2.core_quotient_irreducible_finrank_bound e
    (chiefRepresentation s i) hnt m hm hF
  have hc : Nat.card (s.Factor i) = 2^Module.finrank (ZMod 2) (Additive (s.Factor i)) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (s.Factor i))
  rw [hc]
  exact Nat.pow_le_pow_right (by decide) hd

private theorem chief_order_bound
    {X F : Type*} [Group X] [Finite X] [Field F] [Finite F] [CharP F 2]
    {U : Subgroup X} [U.Normal] (hU : IsPGroup 2 U)
    (e : (X ⧸ pCore 2 X) ≃* SL(2,F)) (s : SeriesOn U)
    (m : ℕ) (hm : m ≠ 0) (hF : Nat.card F = 2^m) :
    (2^(2*m))^s.noncentralCount ≤ Nat.card U := by
  classical
  have he : (2^(2*m))^s.noncentralCount =
      ∏ i : Fin s.series.length, if ¬ s.Central i then 2^(2*m) else 1 := by
    simp [SeriesOn.noncentralCount,Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.prod_ite]
  have htel : (∏ i : Fin s.series.length, Nat.card (s.Factor i)) = Nat.card U := by
    have hh := s.series.prod_card_section_mul_head
    rw [s.head_eq,s.last_eq] at hh
    change (∏ i : Fin s.series.length, Nat.card (s.Factor i)) *
      Nat.card (⊥ : Subgroup X) = Nat.card U at hh
    simpa only [card_bot,mul_one] using hh
  rw [he,←htel]
  apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
  intro i _
  by_cases hi : s.Central i
  · simp only [hi,not_true_eq_false,if_false]
    have hc : 0 < Nat.card (s.Factor i) := Nat.card_pos
    omega
  · simpa only [hi,not_false_eq_true,if_true,if_false] using
      chief_card_ge hU e s i hi m hm hF

open _root_.Triality.Standard _root_.Triality.Standard.Parabolics

/-- Each noncentral chief factor has binary dimension at least 6n, while
the actual arms two-core has order 2^(9n). Thus there is at most one. -/
theorem arms_noncentralCount_le_one
    {X : Type*} [Group X] [Finite X]
    (n : ℕ) (hn : 0 < n)
    (e : X ≃* localFactor (binaryParameters n hn) .arms)
    (s : SeriesOn (pCore 2 X)) : s.noncentralCount ≤ 1 := by
  let P := binaryParameters n hn
  let a := (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    ((localFactorArmsQuotientEquivPSL2 P rfl).trans
      (Theory.PSL2.sl2QuotientEquiv (ExtensionField P)).symm)
  have hF : Nat.card (ExtensionField P) = 2^(3*n) := by
    rw [card_extensionField,binaryParameters_q,←pow_mul,Nat.mul_comm n 3]
  have hb := chief_order_bound pCore_isPGroup a s (3*n) (by omega) hF
  let c : pCore 2 X ≃* pCore 2 (localFactor P .arms) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  have hc : Nat.card (pCore 2 X) = 2^(9*n) := by
    rw [Nat.card_congr c.toEquiv,localFactor_arms_twoCore_card P rfl,
      binaryParameters_q,←pow_mul,Nat.mul_comm n 9]
  rw [hc,←pow_mul] at hb
  have hd := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb
  by_contra! ht
  nlinarith

/-- The actual triality arms factor cannot have the two original noncentral
core layers supplied by either selected diagram factor. -/
theorem arms_no_two_layers
    {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    {N : Subgroup X} (h : NoncentralCoreLayer N)
    (n : ℕ) (hn : 0 < n) (e : X ≃* localFactor (binaryParameters n hn) .arms) : False := by
  obtain ⟨s⟩ := SeriesOn.exists_series (pCore 2 X)
  have hb := arms_noncentralCount_le_one n hn e s
  have hl := h.two_le_noncentralCount s
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityComparison

