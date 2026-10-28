module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.AlternatingFiveComponent
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentPair
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.PairComponentAlignment
public import Theory.SpecificGroups.SL2.FieldCardinality

/-!
# Natural summands for the actual alternating-five square

Two distinct components in the marked A₅ square leave only B.5's product
row; order excludes the hyperplane alternative. Component alignment and
the internal product force both source factors to have order sixty. Their
full source action cases therefore give natural SL₂(4) modules, with actual
actor isomorphisms and intertwiners. Each has dimension four. On a module of
dimension at most eight the fixed kernel vanishes, so the quotient splitting
and both natural actions lift to the original subspaces.

The original point-section action in Chapter 10 supplies the complete B.5
classification and dimension bound. This does not assume a splitting or
recognize a module from dimension alone.
Source: Aschbacher--Smith B.5.1, B.5.6 and 8.3.12, printed pp.99--105,726,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource
namespace AlternatingFiveSquare
abbrev Five := alternatingGroup (Fin 5)
local instance : IsSimpleGroup Five := alternatingGroup.isSimpleGroup (by simp)
local instance : IsQuasisimple Five := {
  toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  simple := ((QuotientGroup.quotientMulEquivOfEq
    (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }

private theorem card_five : Nat.card Five = 60 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

private theorem pair_components {D : Type*} [Group D] (e : D ≃* (Five × Five)) :
    ∃ A B : Subgroup D, IsComponent D A ∧ IsComponent D B ∧ A ≠ B ∧
      Nat.card A = 60 ∧ Nat.card B = 60 := by
  let P := (MonoidHom.inl Five Five).range
  let Q := (MonoidHom.inr Five Five).range
  let : P.Normal := ⟨by
    rintro _ ⟨x,rfl⟩ g
    exact ⟨g.1*x*g.1⁻¹, by ext <;> simp⟩⟩
  let : Q.Normal := ⟨by
    rintro _ ⟨x,rfl⟩ g
    exact ⟨g.2*x*g.2⁻¹, by ext <;> simp⟩⟩
  let ep : Five ≃* P := MonoidHom.ofInjective
    (show Function.Injective (MonoidHom.inl Five Five) from fun x y h => congrArg Prod.fst h)
  let eq : Five ≃* Q := MonoidHom.ofInjective
    (show Function.Injective (MonoidHom.inr Five Five) from fun x y h => congrArg Prod.snd h)
  have hp : IsComponent (Five × Five) P :=
    ⟨(inferInstance : P.Normal).isSubnormal,IsQuasisimple.of_mulEquiv ep⟩
  have hq : IsComponent (Five × Five) Q :=
    ⟨(inferInstance : Q.Normal).isSubnormal,IsQuasisimple.of_mulEquiv eq⟩
  refine ⟨P.map e.symm.toMonoidHom,Q.map e.symm.toMonoidHom,
    hp.map_equiv e.symm,hq.map_equiv e.symm,?_,?_,?_⟩
  · intro h
    have he := map_injective e.symm.injective h
    obtain ⟨a,ha⟩ := exists_ne (1 : Five)
    have hmem : (a,1) ∈ Q := he ▸ (show (a,1) ∈ P from ⟨a,rfl⟩)
    obtain ⟨b,hb⟩ := hmem
    exact ha (congrArg Prod.fst hb).symm
  · rw [card_map_of_injective e.symm.injective,←Nat.card_congr ep.toEquiv,card_five]
  · rw [card_map_of_injective e.symm.injective,←Nat.card_congr eq.toEquiv,card_five]

variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}

/-- The complete natural pair on the original module. This bundles the
proved splitting at a small generic interface for dependent quotient consumers. -/
structure NaturalEightDecomposition (ρ : Representation (ZMod 2) D V) where
  factors : SourceTwoFactorCase ρ
  fixed_eq_bot : ρ.invariants = ⊥
  dimension : Module.finrank (ZMod 2) V = 8
  decomposition : IsCompl factors.firstSpace.toSubmodule factors.secondSpace.toSubmodule
  first_moved : factors.firstSpace.toSubmodule = moved ρ factors.first
  second_moved : factors.secondSpace.toSubmodule = moved ρ factors.second
  firstField : BinaryField
  secondField : BinaryField
  first_degree : firstField.degree = 2
  second_degree : secondField.degree = 2
  first_natural : IsLinearNatural
    (factors.firstSpace.toRepresentation.comp factors.first.subtype) firstField 2
  second_natural : IsLinearNatural
    (factors.secondSpace.toRepresentation.comp factors.second.subtype) secondField 2

/-- The original A₅ square has the two-factor B.5 row, with both literal
source factors of order sixty. -/
theorem two_factors (e : D ≃* (Five × Five)) (h : NontrivialAdequateAlternative ρ) :
    ∃ d : SourceTwoFactorCase ρ, Nat.card d.first = 60 ∧ Nat.card d.second = 60 := by
  have hcard : Nat.card D = 3600 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_prod,card_five]
  obtain ⟨A,B,hA,hB,hne,hAc,hBc⟩ := pair_components e
  rcases AdequateAlternative.product_rows_of_two_components ρ (Or.inr h) hA hB hne with hpair | hhyper
  · obtain ⟨d⟩ := hpair
    have bounds : 60 ≤ Nat.card d.first ∧ 60 ≤ Nat.card d.second := by
      rcases d.component_alignment hA hB hne with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · exact ⟨hAc ▸ card_le_of_le ha,hBc ▸ card_le_of_le hb⟩
      · exact ⟨hBc ▸ card_le_of_le hb,hAc ▸ card_le_of_le ha⟩
    have hc := d.product.card_eq
    rw [hcard] at hc
    refine ⟨d,?_,?_⟩ <;> nlinarith [bounds.1,bounds.2]
  · obtain ⟨d⟩ := hhyper
    have hd := d.first.card_subgroup_dvd_card
    rw [Nat.card_congr d.firstEquiv.toEquiv,Matrix.PSL3Two.card_SL,hcard] at hd
    norm_num at hd

private theorem linear_three_large (F : BinaryField) :
    60 < Nat.card SL(3,F.Carrier) := by
  rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
  have hq : 2 ≤ Nat.card F.Carrier := Finite.one_lt_card
  have hb : 168 ≤ Nat.card F.Carrier ^ 3 * (Nat.card F.Carrier ^ 3 - 1) *
      (Nat.card F.Carrier ^ 2 - 1) := by
    calc
      168 = 2^3 * (2^3-1) * (2^2-1) := by norm_num
      _ ≤ _ := by gcongr
  omega

private theorem degree_two_of_card_sixty (F : BinaryField)
    (hc : Nat.card SL(2,F.Carrier) = 60) : F.degree = 2 := by
  let : Fintype F.Carrier := Fintype.ofFinite F.Carrier
  rw [BenderSuzuki.External.huppert614_card_specialLinearGroup] at hc
  have hq : Nat.card F.Carrier = 4 := by
    rcases lt_trichotomy (Nat.card F.Carrier) 4 with h | h | h
    · have hb : Nat.card F.Carrier * (Nat.card F.Carrier ^ 2 - 1) ≤ 3 * (3^2-1) := by gcongr <;> omega
      norm_num only [Nat.reducePow,Nat.reduceSub,Nat.reduceMul] at hb
      omega
    · exact h
    · have hb : 5 * (5^2-1) ≤ Nat.card F.Carrier * (Nat.card F.Carrier ^ 2 - 1) := by gcongr <;> omega
      norm_num only [Nat.reducePow,Nat.reduceSub,Nat.reduceMul] at hb
      omega
  apply Nat.pow_right_injective (by decide : 1 < 2)
  exact F.card_eq.symm.trans hq

omit [Finite D] in
/-- At order sixty each actual source factor is the natural SL₂(4) row.
The conclusion includes its original intertwiner, not just its dimension. -/
theorem factor_natural {A : Subgroup D} {U : Subrepresentation ρ}
    (h : SourceFactorCase ρ A U) (hc : Nat.card A = 60) :
    U.toSubmodule = moved ρ A ∧ ∃ F : BinaryField, F.degree = 2 ∧
      IsLinearNatural (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype) F 2 := by
  have exclude (F : BinaryField) (e : A ≃* SL(3,F.Carrier)) : False :=
    (ne_of_gt (linear_three_large F)) ((Nat.card_congr e.toEquiv).symm.trans hc)
  cases h with
  | natural hm hn =>
    cases hn with
    | linearTwo F hn =>
      obtain ⟨e⟩ := hn
      exact ⟨hm,F,degree_two_of_card_sixty F ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc),⟨e⟩⟩
    | symmetricFive hn =>
      obtain ⟨e⟩ := hn
      rw [Nat.card_congr e.groupEquiv.toEquiv] at hc
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] at hc
    | linearThree F _ hn => obtain ⟨e⟩ := hn; exact (exclude F e.groupEquiv).elim
  | doubleNatural F _ _ hn => obtain ⟨e⟩ := hn; exact (exclude F e.groupEquiv).elim
  | exceptional _ h => exact (exclude BinaryField.two h.natural.groupEquiv).elim

private theorem natural_dimension {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) E W) (F : BinaryField) (hd : F.degree = 2)
    (h : IsLinearNatural σ F 2) : Module.finrank (ZMod 2) W = 4 := by
  obtain ⟨e⟩ := h
  have hr := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.Carrier)
  rw [Nat.card_zmod,F.card_eq] at hr
  have hf : Module.finrank (ZMod 2) F.Carrier = 2 :=
    (Nat.pow_right_injective (by decide : 1 < 2) hr).symm.trans hd
  rw [e.linearEquiv.finrank_eq,Module.finrank_pi_fintype]
  simp [hf]

omit [Finite D] in
private theorem natural_of_fixed_zero (hz : ρ.invariants = ⊥)
    (A : Subgroup D) (U : Subrepresentation ρ) (F : BinaryField)
    (hn : IsLinearNatural (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype) F 2) :
    IsLinearNatural (U.toRepresentation.comp A.subtype) F 2 := by
  let f : U.toSubmodule →ₗ[ZMod 2] ((fixed ρ).quotientImage U).toSubmodule :=
    (ρ.invariants.mkQ.comp U.toSubmodule.subtype).codRestrict _ (fun v => ⟨v,v.property,rfl⟩)
  have hi : Function.Injective ρ.invariants.mkQ := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.ker_mkQ,hz]
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      exact Subtype.ext (hi (congrArg Subtype.val h))
    · rintro ⟨v,w,hw,rfl⟩
      exact ⟨⟨w,hw⟩,rfl⟩
  let l := LinearEquiv.ofBijective f hf
  obtain ⟨e⟩ := hn
  exact ⟨{ groupEquiv := e.groupEquiv
           linearEquiv := l.trans e.linearEquiv
           intertwines := fun a v => e.intertwines a (l v) }⟩

/-- The actual degree-eight bound removes the fixed kernel in B.5's
quotient splitting. Both natural factors keep their original action maps. -/
theorem natural_eight [FiniteDimensional (ZMod 2) V]
    (e : D ≃* (Five × Five)) (h : NontrivialAdequateAlternative ρ)
    (hd : Module.finrank (ZMod 2) V ≤ 8) :
    ∃ d : SourceTwoFactorCase ρ,
      ρ.invariants = ⊥ ∧ Module.finrank (ZMod 2) V = 8 ∧
      IsCompl d.firstSpace.toSubmodule d.secondSpace.toSubmodule ∧
      d.firstSpace.toSubmodule = moved ρ d.first ∧
      d.secondSpace.toSubmodule = moved ρ d.second ∧
      ∃ F₁ F₂ : BinaryField, F₁.degree = 2 ∧ F₂.degree = 2 ∧
        IsLinearNatural (d.firstSpace.toRepresentation.comp d.first.subtype) F₁ 2 ∧
        IsLinearNatural (d.secondSpace.toRepresentation.comp d.second.subtype) F₂ 2 := by
  obtain ⟨d,hc₁,hc₂⟩ := two_factors e h
  obtain ⟨hm₁,F₁,hF₁,hn₁⟩ := factor_natural d.firstCase hc₁
  obtain ⟨hm₂,F₂,hF₂,hn₂⟩ := factor_natural d.secondCase hc₂
  have hr₁ := natural_dimension _ F₁ hF₁ hn₁
  have hr₂ := natural_dimension _ F₂ hF₂ hn₂
  have hdim := Submodule.finrank_add_eq_of_isCompl d.decomposition
  rw [hr₁,hr₂] at hdim
  have hquot := ρ.invariants.finrank_quotient_add_finrank
  have hdim' : Module.finrank (ZMod 2) (V ⧸ ρ.invariants) = 8 := hdim.symm
  have hz : Module.finrank (ZMod 2) ρ.invariants = 0 := by omega
  have hzero : ρ.invariants = ⊥ := Submodule.finrank_eq_zero.mp hz
  have hi : Function.Injective ρ.invariants.mkQ := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.ker_mkQ,hzero]
  have hsplit : IsCompl d.firstSpace.toSubmodule d.secondSpace.toSubmodule :=
    (Submodule.orderIsoMapComapOfBijective ρ.invariants.mkQ
      ⟨hi,Submodule.mkQ_surjective _⟩).isCompl_iff.mpr d.decomposition
  exact ⟨d,hzero,by omega,hsplit,hm₁,hm₂,F₁,F₂,hF₁,hF₂,
    natural_of_fixed_zero hzero _ _ F₁ hn₁,natural_of_fixed_zero hzero _ _ F₂ hn₂⟩

end AlternatingFiveSquare
end CFSG.Quasithin.ChapterB.SourceInduction
