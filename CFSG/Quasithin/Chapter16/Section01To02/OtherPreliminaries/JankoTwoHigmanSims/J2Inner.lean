module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Conventions
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.Statements
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.J2Reduction
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.J2CentralClass
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.KernelExclusion
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.J2Inner.CentralAction
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.J2Inner.Noncentral
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.J2Inner.Transport

/-!
# Inner involution centralizers of the fixed J₂ carrier

The exhaustive inner-class reduction identifies the fixed subgroup with one
of the two representative centralizers. The central class has the previously
proved Q₈ * D₈ kernel and A₅ quotient, with its kernel action now proved
self-centralizing. The other class is the actual direct product E₄ × A₅.
Thus every component is A₅: the first class has none, while projection onto
A₅ identifies each component in the second class. Its index is 2520, in
particular divisible by four.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.1.5(8),
16.1.7(f), and the J₂ inner case of the index argument in 16.1.8, pp.1172–1173.
The carrier throughout is the unchanged degree-100 ATLAS permutation group.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.J2Inner
open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.J2

/-- Both inner classes, including the action condition in the extension case. -/
theorem inner_structure (r : MulAut Carrier) (hr : orderOf r = 2)
    (hi : ∃ g : Carrier, r = MulAut.conj g) :
    (IsJ2CoreExtension r.fixedSubgroup ∧
      HasSelfCentralizingNormalTwoSubgroup r.fixedSubgroup) ∨
    Nonempty (r.fixedSubgroup ≃* E4 × A5) := by
  rcases J2Reduction.inner_fixed_representatives r hr hi with ha | ht
  · obtain ⟨e⟩ := ha
    exact Or.inr ⟨e.trans a_centralizer_equiv⟩
  · obtain ⟨e⟩ := ht
    exact Or.inl ⟨extension_transport e.symm J2CentralClass.t_core_shape,
      selfCentralizing_transport e.symm t_selfCentralizing⟩

/-- The exact inner alternatives in source 16.1.5(8). -/
theorem inner_centralizer_alternative (r : MulAut Carrier) (hr : orderOf r = 2)
    (hi : ∃ g : Carrier, r = MulAut.conj g) :
    IsJ2CoreExtension r.fixedSubgroup ∨ Nonempty (r.fixedSubgroup ≃* E4 × A5) :=
  (inner_structure r hr hi).imp And.left id

/-- Every component of an inner involution centralizer is actually A₅. -/
theorem inner_component_equiv (r : MulAut Carrier) (hr : orderOf r = 2)
    (hi : ∃ g : Carrier, r = MulAut.conj g)
    (K : Subgroup r.fixedSubgroup) (hK : IsComponent r.fixedSubgroup K) :
    Nonempty (K ≃* A5) := by
  rcases inner_structure r hr hi with ⟨_, hself⟩ | he
  · exact (hself.not_isComponent K hK).elim
  · obtain ⟨e⟩ := he
    obtain ⟨f⟩ := component_product_equiv (K.map e.toMonoidHom) (hK.map_equiv e)
    exact ⟨(e.subgroupMap K).trans f⟩

/-- If a component exists, the entire fixed subgroup has index 2520. -/
theorem inner_component_index (r : MulAut Carrier) (hr : orderOf r = 2)
    (hi : ∃ g : Carrier, r = MulAut.conj g)
    (K : Subgroup r.fixedSubgroup) (hK : IsComponent r.fixedSubgroup K) :
    r.fixedSubgroup.index = 2520 := by
  rcases inner_structure r hr hi with ⟨_, hself⟩ | he
  · exact (hself.not_isComponent K hK).elim
  · obtain ⟨e⟩ := he
    have hc : Nat.card r.fixedSubgroup = 240 := by
      have hA5 : Nat.card A5 = 60 := by
        rw [nat_card_alternatingGroup, Nat.card_fin]
        decide
      rw [Nat.card_congr e.toEquiv, Nat.card_prod, hA5]
      norm_num [E4, C2, Nat.card_fun]
    have h := r.fixedSubgroup.card_mul_index
    rw [hc, Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] at h
    omega

/-- The index bound needed in the inner J₂ case of source 16.1.8. -/
theorem four_dvd_index_of_inner_component (r : MulAut Carrier) (hr : orderOf r = 2)
    (hi : ∃ g : Carrier, r = MulAut.conj g)
    (K : Subgroup r.fixedSubgroup) (hK : IsComponent r.fixedSubgroup K) :
    4 ∣ r.fixedSubgroup.index := by
  rw [inner_component_index r hr hi K hK]
  decide

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.J2Inner
