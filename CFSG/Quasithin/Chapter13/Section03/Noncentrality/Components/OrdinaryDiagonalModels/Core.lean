module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.SupercriticalSource.StarPlacement.Models
public import Theory.GroupTheory.CComponent.SixCoverTheta
public import Theory.SpecificGroups.BinaryComponentResidual
public import Theory.GroupTheory.PResidual.CubicGenerationModuloTwoCore
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder
public import Theory.Alternating.FivePairOuterTwo

/-!
# The small quotient rows after cubic noncontainment

In ambient three-rank at most two, a normal C-component with quotient A₆,
3.A₆ or PSU₃(3) contains every element of order three. Thus an escaping
cubically generated actor excludes those three rows from the original
five-model list, leaving A₅ or PSL₃(2). Both remaining literal quotient
models have trivial center and two-group outer automorphism quotient.

Source: Aschbacher–Smith, 13.3.14, terminal paragraph, printed p.893,
using the actual A.3.18 cubic-residual and triple-cover calculations.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open SupercriticalSource Chapter1.Section02.LocalModels
universe u v
variable {G : Type u} [Group G] [Finite G]

private theorem map_center_eq {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (center A).map e.toMonoidHom = center B := by
  ext b
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact (centerCongr e ⟨a,ha⟩).property
  · intro hb
    exact ⟨e.symm b,(centerCongr e.symm ⟨b,hb⟩).property,e.apply_symm_apply b⟩

omit [Finite G] in
private theorem le_of_cubic_generation (A K : Subgroup G)
    (hA : closure {a : A | orderOf a = 3} = ⊤)
    (hK : closure {x : G | orderOf x = 3} ≤ K) : A ≤ K := by
  have hm := congrArg (map A.subtype) hA
  rw [MonoidHom.map_closure,←MonoidHom.range_eq_map,range_subtype] at hm
  rw [←hm]
  apply (closure_le _).mpr
  rintro x ⟨a,ha,rfl⟩
  exact hK (subset_closure ((A.orderOf_coe a).trans ha))

/-- In three-rank at most two, an escaping cubically generated actor removes
all three rank-two rows from the five-model list. -/
theorem midSize_small_of_cubic_actor_escape
    {Q : Type v} [Group Q] [Finite Q]
    (K A : Subgroup G) [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (eQ : (K ⧸ pCore 2 K) ≃* Q) (hm : MidSizeModel Q)
    (hr : primeRank 3 G ≤ 2)
    (hA : closure {a : A | orderOf a = 3} = ⊤) (hne : ¬ A ≤ K) :
    IsAlternating Q 5 ∨ ClassicalGroup.IsPSL Q 3 2 := by
  rcases hm with ha | hl | ⟨⟨e⟩⟩ | ⟨hq,_,⟨e⟩⟩ | ⟨F,_,_,J,hF,hJ,⟨e⟩⟩
  · exact Or.inl ha
  · exact Or.inr hl
  · exact (hne (le_of_cubic_generation A K hA
      (SixCComponentTheta.cubic_closure_eq_of_alternating_six K hK (eQ.trans e) hr).le)).elim
  · let ec := QuotientGroup.congr (center (K ⧸ pCore 2 K)) (center Q) eQ (map_center_eq eQ)
    exact (hne (le_of_cubic_generation A K hA
      (SixCComponentTheta.cubic_closure_eq_of_central_quotient_six K hK
        (ec.trans e) hr).le)).elim
  · have hb := Theory.SpecificGroups.BinaryComponentResidual.Facts.of_equiv
      ((eQ.trans e).trans (J.projectiveEquivBinaryG2Derived hF hJ))
      Theory.SpecificGroups.BinaryComponentResidual.g2
    have he := hK.eq_primeToResidual_three_of_outer_twoGroup hb.1 hb.2.1 hr hb.2.2
    apply (hne (le_of_cubic_generation A K hA ?_)).elim
    rw [he]
    apply (closure_le _).mpr
    intro x hx
    apply mem_primeToResidual_of_pow (n := 1)
    change orderOf x = 3 at hx
    simpa only [pow_one,hx] using pow_orderOf_eq_one x

private theorem diagonal_facts_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center B = ⊥) (ho : IsPGroup 2 (MulAut.Outer B)) :
    center A = ⊥ ∧ IsPGroup 2 (MulAut.Outer A) := by
  refine ⟨?_,ho.of_equiv (MulAut.outerCongr e).symm⟩
  apply le_bot_iff.mp
  intro x hx
  exact e.map_eq_one_iff.mp (hz.le ((centerCongr e) ⟨x,hx⟩).property)

/-- Both surviving literal quotient rows are centerless with two-group outer quotient. -/
theorem small_diagonal_model_facts {Q : Type*} [Group Q] [Finite Q]
    (hm : IsAlternating Q 5 ∨ ClassicalGroup.IsPSL Q 3 2) :
    center Q = ⊥ ∧ IsPGroup 2 (MulAut.Outer Q) := by
  rcases hm with ⟨⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
  · exact diagonal_facts_transport e (alternatingGroup.center_eq_bot (by simp))
      Theory.AlternatingFive.outer_isPGroup_two
  · let := Fintype.ofFinite F
    let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
      simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
    let c := (e.trans (Atlas.fieldEquivPSL 3 eF)).trans Matrix.PSL3Two.equiv.symm
    exact diagonal_facts_transport c Matrix.PSL3Two.center_eq_bot
      Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup


end CFSG.Quasithin.Chapter13.Section03.Noncentrality
