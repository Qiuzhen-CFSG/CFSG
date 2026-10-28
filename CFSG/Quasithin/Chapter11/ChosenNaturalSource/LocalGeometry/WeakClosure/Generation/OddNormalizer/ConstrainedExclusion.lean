module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.ConstrainedField
public import Theory.Representation.PSL3Four.SmallDegree
public import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Section
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.Quotient
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Excluding the last constrained nonbinary pushing-up component

The remaining star image is SL₅(2), and the order reduction forces the
original full quotient to be SL₃(4). A nontrivial binary action of its
perfect covering residual survives in an irreducible section. The two-core
kills that section. If the resulting SL₃(4) action is faithful, its order
does not divide any GLₙ(2) with n ≤ 5. Otherwise the cubic center is the
kernel, and the actual PSL₃(4) degree bound gives dimension at least nine.
Thus the entire binary five-dimensional action is trivial.

The literal component action is perfect and inner, so its actual SL₅(2)
marking supplies just such an action, contradicting its proved nontriviality.
This excludes every constrained component of the original C.2.8 pair.
The endpoint applies it to the actual Hall kernel, with final normalizer
control retained by this task and 11.2.1 assembly by its generation owner.
Source: Aschbacher--Smith C.4.5--8, pp.152--154, and 4.4.6, p.620.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

private theorem no_faithful_full_four_small
    {F Q W : Type*} [Field F] [Finite F] [Group Q] [Finite Q]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (hF : Nat.card F = 4) (e : Q ≃* SL(3,F))
    (ρ : Representation (ZMod 2) Q W) (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) W ≤ 5) : False := by
  let b := Module.finBasis (ZMod 2) W
  let φ := (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp ρ.asGroupHom
  have hφ : Function.Injective φ := by
    apply (Matrix.GeneralLinearGroup.toLin' b).symm.injective.comp
    intro g h he
    exact hf (congrArg Units.val he)
  have hdiv := Subgroup.card_dvd_of_injective φ hφ
  rw [Nat.card_congr e.toEquiv,linear_three_order,hF,Matrix.card_GL_field] at hdiv
  norm_num only [Nat.card_zmod] at hdiv
  clear hφ φ b
  interval_cases hn : Module.finrank (ZMod 2) W <;>
    norm_num [hn,Fin.prod_univ_succ] at hdiv

private theorem full_four_small_irreducible_trivial
    {F Q W : Type*} [Field F] [Finite F] [Group Q] [Finite Q] [IsQuasisimple Q]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (hF : Nat.card F = 4) (e : Q ≃* SL(3,F))
    (ρ : Representation (ZMod 2) Q W) [ρ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) W ≤ 5) : ∀ g, ρ g = 1 := by
  by_contra! hne
  have hk : ρ.ker ≠ ⊤ := by
    intro ht
    obtain ⟨g,hg⟩ := hne
    exact hg (show g ∈ ρ.ker from ht.symm ▸ mem_top g)
  have hkc := (IsQuasisimple.normal_le_center_or_eq_top ρ.ker).resolve_right hk
  have hc : Nat.card (center Q) = 3 := by
    rw [Nat.card_congr (centerCongr e).toEquiv,Atlas.ExceptionalSupport.card_sl_center]
    norm_num [hF]
  have hkcard : Nat.card ρ.ker = 1 ∨ Nat.card ρ.ker = 3 :=
    (Nat.dvd_prime Nat.prime_three).mp (hc ▸ card_dvd_of_le hkc)
  rcases hkcard with h1 | h3
  · exact no_faithful_full_four_small hF e ρ
      ((MonoidHom.ker_eq_bot_iff ρ).mp (eq_bot_of_card_eq ρ.ker h1)) hd
  · have he : ρ.ker = center Q := eq_of_le_of_card_ge hkc (by omega)
    let σ := quotientOfLEKer ρ (center Q) he.ge
    let : σ.IsIrreducible := (quotientOfLEKer_irreducible_iff ρ (center Q) he.ge).mpr inferInstance
    let ec : Q ⧸ center Q ≃* PSL(3,F) :=
      QuotientGroup.congr _ _ e (FixedElementary.map_center e)
    have hnσ : ∃ g, σ g ≠ 1 := by
      obtain ⟨g,hg⟩ := hne
      exact ⟨QuotientGroup.mk' (center Q) g,hg⟩
    have h9 := Representation.PSL3Four.finrank_ge_nine_of_equiv hF ec σ hnσ
    omega

/-- The full SL₃(4) quotient cannot act nontrivially on a binary space of
dimension at most five, even across a two-core extension. -/
theorem full_four_small_action_trivial
    {F X W : Type*} [Field F] [Finite F] [Group X] [Finite X] [Group.IsPerfect X]
    [IsQuasisimple (X ⧸ pCore 2 X)]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (hF : Nat.card F = 4) (e : X ⧸ pCore 2 X ≃* SL(3,F))
    (ρ : Representation (ZMod 2) X W) (hd : Module.finrank (ZMod 2) W ≤ 5) :
    ∀ g, ρ g = 1 := by
  by_contra! hn
  let et : (⊤ : Subgroup X) ≃* X := Subgroup.topEquiv
  let : Group.IsPerfect (⊤ : Subgroup X) := Group.IsPerfect.ofSurjective
    (f := et.symm.toMonoidHom) et.symm.surjective
  have hne : ¬ (⊤ : Subgroup X) ≤ ρ.ker := by
    intro h
    obtain ⟨g,hg⟩ := hn
    exact hg (h (mem_top g))
  obtain ⟨U,N,hi,hN⟩ := QuadraticFourGroup.exists_irreducible_section_surviving_perfect
    (ρ := ρ) ⊤ hne
  let σ := N.quotientRepresentation
  let : σ.IsIrreducible := hi
  have hk := normal_p_subgroup_le_ker σ (pCore 2 X) pCore_isPGroup
  let τ := quotientOfLEKer σ (pCore 2 X) hk
  let : τ.IsIrreducible := (quotientOfLEKer_irreducible_iff σ (pCore 2 X) hk).mpr hi
  have hdτ : Module.finrank (ZMod 2) (U ⧸ N.toSubmodule) ≤ 5 :=
    (Submodule.finrank_quotient_le N.toSubmodule).trans ((Submodule.finrank_le U.toSubmodule).trans hd)
  have ht := full_four_small_irreducible_trivial hF e τ hdτ
  apply hN
  intro x _
  exact ht (QuotientGroup.mk' (pCore 2 X) x)
open CFSG.Quasithin.Chapter12.Section02
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {H M B R W : Subgroup G}
include D S

/-- The last constrained star row is impossible: its actual perfect action
would give a nontrivial binary five-dimensional action of the full SL₃(4)
covering residual. -/
theorem no_constrained_natural
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hN : (B.subgroupOf M).Normal)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K) : False := by
  obtain ⟨hd,⟨em⟩,_⟩ := constrained_natural_field_four D S h hN e K hK hq hout hfK
  obtain ⟨es⟩ := constrained_natural_star_linear_five_two D S h hN e K hK hq hout hfK
  have hF : Nat.card S.field.Carrier = 4 := by rw [S.field.card_eq,hd]; decide
  have hn : M ≤ normalizer (B : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.component_le).mp hN
  have hs : conjugateSpanBy B M = B :=
    le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy _ _)
  let X := (conjugateSpanBy B M).subgroupOf H
  have hXH : conjugateSpanBy B M ≤ H :=
    (conjugateSpanBy_le_self h.component_le).trans h.local_le
  let := h.span_perfect
  let ex := subgroupOfEquivOfLe hXH
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective
    (f := ex.symm.toMonoidHom) ex.symm.surjective
  let ec : (X ⧸ pCore 2 X) ≃* (L ⧸ pCore 2 L) :=
    (QuotientGroup.congr _ _ ex (pCore_map_iso 2 ex)).trans
      ((QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hs)
        (pCore_map_iso 2 (MulEquiv.subgroupCongr hs))).trans e)
  let := S.source.toHypothesis1221.quasisimple
  let : IsQuasisimple (X ⧸ pCore 2 X) := IsQuasisimple.of_mulEquiv ec.symm
  have hnorm := h.constrained_span_normalizes_intrinsic K hK hq
  let j := inclusion hnorm
  let f := (normalizerCoreCentralAction K).comp j
  have he : f.range = coreCentralActorImage K X := by
    ext a
    constructor
    · rintro ⟨x,rfl⟩
      exact mem_map_of_mem _ (show j x ∈ X.subgroupOf _ from x.property)
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨(x : H),hx⟩,rfl⟩
  have hne : f ≠ 1 := by
    intro hf
    apply h.constrained_span_action_nontrivial K hK hq hout
    rw [←he,hf,MonoidHom.range_one]
  let Q := coreCentralQuotient K
  let := hq
  let : IsSimpleGroup Q := hq.simple
  let : Group.IsSolvable (MulAut.Outer Q) := h.constrained_core_central_outer_solvable K hq
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hz : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with hc | hc
    · exact hc
    · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp hc)).elim
  obtain ⟨i,hi,_⟩ := MulAut.perfect_subgroup_exists_inner_lift f.range hz
  let eq : Q ≃* BinaryLinear.OuterCyclic.LinearGroup 5 :=
    (h.constrained_star_central_equiv K hK hq hout hfK).trans
      ((QuotientGroup.congr _ _ es (FixedElementary.map_center es)).trans
        (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide)))
  let ρ : Representation (ZMod 2) X (Fin 5 → ZMod 2) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      (eq.toMonoidHom.comp (i.comp f.rangeRestrict))
  have ht := full_four_small_action_trivial hF (ec.trans em) ρ (by simp)
  apply hne
  apply MonoidHom.ext
  intro x
  have hx : eq (i (f.rangeRestrict x)) = 1 := by
    apply LinearEquiv.ext
    intro v
    exact DFunLike.congr_fun (ht x) v
  have hx' : i (f.rangeRestrict x) = i 1 :=
    eq.injective (hx.trans (by simp))
  exact congrArg Subtype.val (hi hx')
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
