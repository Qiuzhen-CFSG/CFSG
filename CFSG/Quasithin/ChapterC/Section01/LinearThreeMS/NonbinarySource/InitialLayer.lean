module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.QuotientAction
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceFF
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.CaseComparison

/-!
# Recognition of the initial nonbinary linear-three module

The proved B.5.1 alternatives on the actual central-omega action reduce
to natural or doubled natural modules. Irreducible recognition uses the
original projective SL₃ quotient. Sylow-center orders recover the field
degree and exclude the binary SL₄ and SL₅ rows, including the equal-order
PSL₃(4) and SL₄(2) case.

Both surviving rows have the full SL₃ order. The literal map from the
original component core quotient is therefore injective. The normal-kernel
bound then gives C_KR(Ω₁(Z(O₂(KR)))) = O₂(KR), and the supplied full SL₃
marking descends with its original representative equation. In particular,
the cubic scalar center at field four is retained.

These are initial moving-section results. They do not identify the whole
commutator core or prove the radical inequalities in C.1.34.
Source: Aschbacher--Smith B.5.1, K.3.2 and C.1.31--34, pp.135--137;
MS93, the initial module analysis in Sections 2--3. Matrix recognition
uses the attributed ATLAS port; see LICENSES/ATLAS.txt.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open MSCentralOrbit ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
local notation "J" => (K ⊔ R : Subgroup G)
local notation "L" => K.subgroupOf (K ⊔ R)
local notation "T" => R.subgroupOf (K ⊔ R)

private def centerQuotientCongr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    X ⧸ center X ≃* Y ⧸ center Y :=
  QuotientGroup.congr _ _ e (by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro hy
      exact ⟨((centerCongr e).symm ⟨y,hy⟩ : X),
        ((centerCongr e).symm ⟨y,hy⟩).property,
        congrArg Subtype.val ((centerCongr e).apply_symm_apply ⟨y,hy⟩)⟩)

private theorem degree_of_projective_mark
    {X : Type*} [Group X] [Finite X]
    {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 0 < n) (hF : Nat.card F = 2^n)
    (eQ : X ⧸ center X ≃* PSL(3,F)) (E : BinaryField)
    (e : X ≃* SL(3,E.Carrier)) : E.degree = n := by
  let a : PSL(3,E.Carrier) ≃* PSL(3,F) := (centerQuotientCongr e).symm.trans eQ
  let S : Sylow 2 PSL(3,E.Carrier) := Classical.choice inferInstance
  have hE := Matrix.PSL3.LinearThree.card_center_sylow E.Carrier E.degree_pos E.card_eq S
  have hN := Matrix.PSL3.LinearThree.card_center_sylow_of_equiv F hn hF a S
  exact Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) (hE.symm.trans hN)

private theorem no_binary_higher_of_projective_mark
    {X : Type*} [Group X] [Finite X]
    {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (eQ : X ⧸ center X ≃* PSL(3,F)) {d : ℕ} (hd : d=4 ∨ d=5)
    (e : X ≃* SL(d,ZMod 2)) : False := by
  have hdz : 0 < d := by rcases hd with rfl | rfl <;> decide
  let z : (SL(d,ZMod 2) ⧸ center SL(d,ZMod 2)) ≃* SL(d,ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq (BinaryLinear.OuterCyclic.binary_center_eq_bot hdz)).trans
      QuotientGroup.quotientBot
  let a := z.symm.trans ((centerQuotientCongr e).symm.trans eQ)
  let S : Sylow 2 SL(d,ZMod 2) := Classical.choice inferInstance
  have hs := Matrix.PSL3.LinearThree.card_center_sylow_of_equiv F (by omega) hF a S
  have hb := BinaryLinear.sl_sylow_center_card_le_two (by omega : 2 ≤ d) S
  have hp := Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hn
  rw [hs] at hb
  norm_num at hp
  omega

/-- The full FF classification on the actual projective SL₃ actor selects
natural or doubled natural coordinates, preserving the original field degree. -/
theorem natural_or_double_of_projective_source
    {X W : Type*} [Group X] [Finite X] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W) {B : Subgroup X} [IsQuasisimple B]
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ B)
    (hsq : IsSQTK KnownSimple.IsKnownSimple X) (hff : IsFFModule ρ)
    {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (eQ : B ⧸ center B ≃* PSL(3,F)) :
    ∃ E : BinaryField, E.degree = n ∧
      (IsLinearNatural (c.sectionData.action.comp B.subtype) E 3 ∨
        IsRepeatedLinearNatural (c.sectionData.space.toRepresentation.comp B.subtype) E 3 2) := by
  cases c.clause_one with
  | irreducible hi hf hirr hs hext =>
    let : Algebra (ZMod 2) F := ZMod.algebra F 2
    let E : BinaryField := { Carrier := F, degree := n, degree_pos := by omega, card_eq := hF }
    have hff' : IsFFModule c.sectionData.action := by
      obtain ⟨A,hA⟩ := hff
      exact ⟨A,IrreducibleBranch.moved_offender c.sectionData hA⟩
    have hq : quadraticRatio c.sectionData.action ≤ 2 :=
      ((isFFModule_iff_quadraticRatio_le_one _).mp hff').trans (by norm_num)
    let hsource : ChapterK.Linear.Recognition.SourceHypothesis KnownSimple.IsKnownSimple
        c.sectionData.action B :=
      ⟨inferInstance,inferInstance,hsq,c.fitting_eq.symm,inferInstance,hf,hirr,
        (cubicRatio_le_quadraticRatio _).trans hq⟩
    obtain ⟨d⟩ := ChapterK.Linear.Recognition.SourceFF.naturalSourceInput_of_quotient_ff
      hsource (B := E) eQ hff'
    exact ⟨E,rfl,Or.inl ⟨d.natural⟩⟩
  | doubleThree E _ e _ _ =>
    exact ⟨E,degree_of_projective_mark (by omega) hF eQ E e.groupEquiv,Or.inr ⟨e⟩⟩
  | naturalDual d hd _ hn' =>
    obtain ⟨e⟩ := hn'
    exact (no_binary_higher_of_projective_mark hn hF eQ hd e.groupEquiv).elim
  | repeatedNatural d r hd _ _ _ hn' =>
    obtain ⟨e⟩ := hn'
    exact (no_binary_higher_of_projective_mark hn hF eQ hd e.groupEquiv).elim

include h hn
variable [CharP F 2]

/-- The actual central omega action has natural or doubled natural initial
moving section, of exactly the field degree in the original MS-pair. -/
theorem centralOmega_classified_source :
    ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((centralOmegaRepresentation K R).comp (offenderSubgroup (centralOmegaRepresentation K R)).subtype)
      ((centralOmegaComponent K R).subgroupOf (offenderSubgroup (centralOmegaRepresentation K R))),
    ∃ E : BinaryField, E.degree = n ∧
      (IsLinearNatural (c.sectionData.action.comp
        ((centralOmegaComponent K R).subgroupOf (offenderSubgroup (centralOmegaRepresentation K R))).subtype) E 3 ∨
      IsRepeatedLinearNatural (c.sectionData.space.toRepresentation.comp
        ((centralOmegaComponent K R).subgroupOf (offenderSubgroup (centralOmegaRepresentation K R))).subtype) E 3 2) := by
  let e := Classical.choice h.model
  have hBO := (centralOmega_source_conclusion h hn).1
  let c := Classical.choice (centralOmega_source_conclusion h hn).2
  let ρ := centralOmegaRepresentation K R
  let O := offenderSubgroup ρ
  let B := (centralOmegaComponent K R).subgroupOf O
  let a : B ≃* centralOmegaComponent K R := subgroupOfEquivOfLe hBO
  let := centralOmegaComponent_quasisimple h hn
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv a.symm
  have hff : IsFFModule (ρ.comp O.subtype) := by
    obtain ⟨A,hA⟩ := (isFFModule_iff_exists_bestOffender ρ).mp (centralOmega_isFF h hn)
    exact ⟨A.subgroupOf O,(hA.subgroupOf ρ (hA.le_offenderSubgroup ρ)).isOffender _⟩
  exact ⟨c,natural_or_double_of_projective_source (ρ.comp O.subtype) c
    ((centralOmega_actor_sqtk h hn).subgroup O) hff hn h.field_card
    ((centerQuotientCongr a).trans (centralOmegaProjectiveEquiv h hn e))⟩

/-- The source module recognition retains the full SL₃ order, including
its cubic scalar center in even field degree. -/
theorem centralOmegaComponent_card : Nat.card (centralOmegaComponent K R) = Nat.card SL(3,F) := by
  obtain ⟨hBO,_⟩ := centralOmega_source_conclusion h hn
  obtain ⟨c,E,hE,hm⟩ := centralOmega_classified_source h hn
  have he : Nat.card ((centralOmegaComponent K R).subgroupOf
      (offenderSubgroup (centralOmegaRepresentation K R))) = Nat.card SL(3,E.Carrier) := by
    rcases hm with hN | hD
    · obtain ⟨e⟩ := hN
      exact Nat.card_congr e.groupEquiv.toEquiv
    · obtain ⟨e⟩ := hD
      exact Nat.card_congr e.groupEquiv.toEquiv
  rw [Nat.card_congr (subgroupOfEquivOfLe hBO).toEquiv] at he
  rw [he,Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,
    Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,E.card_eq,hE,h.field_card]

theorem centralOmegaCoreMap_injective : Function.Injective (centralOmegaCoreMap h) := by
  have hc : Nat.card (L ⧸ pCore 2 L) ≤ Nat.card (centralOmegaComponent K R) := by
    rw [centralOmegaComponent_card h hn]
    obtain ⟨e⟩ := h.model
    exact (Nat.card_congr (joinQuotientEquiv (R := R) e).toEquiv).le
  exact ((centralOmegaCoreMap_surjective h).bijective_of_nat_card_le hc).1

/-- The literal central omega centralizer is exactly O₂(KR), with no scalar
kernel lost. This is deduced from the marked initial module classification. -/
theorem centralOmega_kernel_eq_core : centralOmegaKernel K R = pCore 2 J := by
  let := component_normal h hn
  let := join_quotient_quasisimple h
  have hb := (QuasisimpleKernel.normal_kernel_structure L T (centralOmegaKernel K R)
    h.component.2 (join_oddIndex h hn).isPGroup
    (by rw [← subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self])
    core_le_centralOmegaKernel (component_not_le_centralOmegaKernel h hn)).1
  have hb' : centralOmegaKernel K R ≤ pCore 2 J ⊔ L :=
    hb.trans (sup_le_sup le_rfl (map_subtype_le _))
  apply le_antisymm _ core_le_centralOmegaKernel
  intro x hx
  obtain ⟨q,hq,k,hk,rfl⟩ := mem_sup_of_normal_left.mp (hb' hx)
  have hkN : k ∈ centralOmegaKernel K R := by
    have hh := (centralOmegaKernel K R).mul_mem
      ((centralOmegaKernel K R).inv_mem (core_le_centralOmegaKernel hq)) hx
    simpa only [inv_mul_cancel_left] using hh
  have he : centralOmegaCoreMap h (QuotientGroup.mk' _ ⟨k,hk⟩) = 1 := by
    rw [centralOmegaCoreMap_mk]
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff k).mpr hkN
  have hkq : (⟨k,hk⟩ : L) ∈ pCore 2 L :=
    (QuotientGroup.eq_one_iff _).mp
      ((centralOmegaCoreMap_injective h hn) (he.trans (map_one _).symm))
  exact (pCore 2 J).mul_mem hq
    (pCoreIn_le_of_subnormal 2 h.component.2.subnormal (mem_map_of_mem (L).subtype hkq))

/-- The actual omega-center component has the original full SL₃ marking,
induced by the original two-core projection. -/
def centralOmegaFullEquiv (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) :
    centralOmegaComponent K R ≃* SL(3,F) :=
  (MulEquiv.ofBijective (centralOmegaCoreMap h)
    ⟨centralOmegaCoreMap_injective h hn,centralOmegaCoreMap_surjective h⟩).symm.trans
      (joinQuotientEquiv (R := R) e)

theorem centralOmegaFullEquiv_mk (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (k : L) :
    centralOmegaFullEquiv h hn e ((centralOmegaProjection K R).subgroupMap L k) =
      e (QuotientGroup.mk' _ ⟨k,k.property⟩) := by
  let a : (L ⧸ pCore 2 L) ≃* centralOmegaComponent K R :=
    MulEquiv.ofBijective (centralOmegaCoreMap h)
      ⟨centralOmegaCoreMap_injective h hn, centralOmegaCoreMap_surjective h⟩
  change (joinQuotientEquiv (R := R) e) (a.symm (a (QuotientGroup.mk' _ k))) = _
  rw [a.symm_apply_apply]
  rfl

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource
