module

public import CFSG.Quasithin.Chapter1.Section01.ModelActions115
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import Theory.GroupAction.SylowFixedCentralQuotient
public import Theory.GroupAction.QuasisimpleInnerOddInversion
public import Theory.GroupAction.SylowPointwiseInner
public import Theory.GroupTheory.PCoreCentralQuotient

/-!
# Marked local inputs for the quasisimple involution classification

The local hypotheses keep the original automorphism and Sylow subgroup.
Fixed-point lifting through the literal central quotient, followed by the
central-kernel theorem of A.1.8, gives characteristic two for its full fixed
subgroup. Perfectness retains the automorphism order and lifts innerness.
Odd-core inversion then identifies the center with the two-core; this supplies
the exact quotient and original action required by sporadic conclusion (f).

These are common reductions, not the unfinished universal classification.
The family modules must discharge model innerness or the exceptional actions.
Source: Aschbacher--Smith, proof of 1.1.5(3), printed pp.501--503.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
open Chapter15.Section03.Candidates.ComponentStructure ClassificationModels

variable {L H : Type*} [Group L] [Group H]

/-- The local source inputs retain the original automorphism and source Sylow.
Quasisimplicity and finiteness are separate typeclass hypotheses. -/
structure MarkedInvolution (α : MulAut L) (P : Sylow 2 L) : Prop where
  order_two : orderOf α = 2
  fixes : ∀ x ∈ P, α x = x
  characteristic_two : HasCharacteristicTwo α.fixedSubgroup
  inverts_odd_core : ∀ x ∈ pPrimeCore 2 L, α x = x⁻¹

variable [Finite L] {α : MulAut L} {P : Sylow 2 L}

/-- The full fixed group downstairs has characteristic two. This applies
the central-kernel theorem underlying A.1.8 to the proved surjective map. -/
theorem MarkedInvolution.quotient_fixed_characteristic_two
    (d : MarkedInvolution α P) :
    HasCharacteristicTwo (((center L).quotientAut α).fixedSubgroup) := by
  let q := QuotientGroup.mk' (center L)
  let β := (center L).quotientAut α
  have heq (x : L) : q (α x) = β (q x) :=
    (Subgroup.quotientAut_apply_mk _ α x).symm
  have hk : q.ker ≤ center L := by rw [QuotientGroup.ker_mk']
  exact MonoidHom.centralizer_pCore_le_of_surjective_centralKernel
    (MulAut.fixedSubgroupMap α β q heq)
    (MulAut.fixedSubgroupMap_surjective_of_sylow_fixed α β q
      (QuotientGroup.mk'_surjective _) hk heq
      (d.order_two ▸ pow_orderOf_eq_one α) P d.fixes)
    (MulAut.fixedSubgroupMap_ker_le_center α β q heq hk)
    d.characteristic_two

/-- The actual quotient action retains its order, a fixed Sylow, and the
full characteristic-two fixed subgroup in every specified quotient model. -/
theorem MarkedInvolution.centralQuotient_model_inputs [IsQuasisimple L]
    (d : MarkedInvolution α P) (e : L ⧸ center L ≃* H) :
    orderOf (MulAut.centralQuotientAction e α) = 2 ∧
    HasCharacteristicTwo (MulAut.centralQuotientAction e α).fixedSubgroup ∧
    ∃ Q : Sylow 2 H, ∀ x ∈ Q, MulAut.centralQuotientAction e α x = x := by
  let : Finite H := Finite.of_surjective
    (fun x : L => e (QuotientGroup.mk' (center L) x))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  refine ⟨(MulAut.orderOf_centralQuotientAction e α).trans d.order_two, ?_,
    MulAut.centralQuotientAction_exists_fixed_sylow e α P d.fixes⟩
  change HasCharacteristicTwo ((MulAut.congr e) ((center L).quotientAut α)).fixedSubgroup
  let c := MulAut.fixedSubgroupCongr e ((center L).quotientAut α)
  have hk : c.toMonoidHom.ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff c.toMonoidHom).mpr c.injective
  exact MonoidHom.centralizer_pCore_le_of_surjective_centralKernel c.toMonoidHom
    c.surjective (hk.le.trans bot_le)
    d.quotient_fixed_characteristic_two

/-- Any inner model action lifts to the original automorphism and forces
the center upstairs to be its two-core. -/
theorem MarkedInvolution.inner_and_center_of_quotient_inner [IsQuasisimple L]
    (d : MarkedInvolution α P) (e : L ⧸ center L ≃* H)
    (hi : MulAut.centralQuotientAction e α ∈ (MulAut.conj (G := H)).range) :
    α ∈ (MulAut.conj (G := L)).range ∧ center L = pCore 2 L := by
  obtain ⟨h, hh⟩ := hi
  obtain ⟨g, hg⟩ := (MulAut.centralQuotientAction_inner_iff e α).mp ⟨h, hh.symm⟩
  have hinner : α ∈ (MulAut.conj (G := L)).range := ⟨g, hg.symm⟩
  exact ⟨hinner, MulAut.center_eq_twoCore_of_inner_inverts_oddCore
    α hinner d.inverts_odd_core⟩

/-- Source row (f) uses only model innerness, with no multiplier premise.
The output retains the original action and source Sylow subgroup. -/
theorem MarkedInvolution.sporadic_of_quotient_inner [IsQuasisimple L]
    (d : MarkedInvolution α P) (name : SporadicName) (hn : name ≠ .j3)
    (e : L ⧸ center L ≃* name.Carrier)
    (hi : MulAut.centralQuotientAction e α ∈ (MulAut.conj (G := name.Carrier)).range) :
    ModelAction115 L α := by
  obtain ⟨hinner, hz⟩ := d.inner_and_center_of_quotient_inner e hi
  exact .sporadic name hn
    ⟨(QuotientGroup.quotientMulEquivOfEq hz.symm).trans e⟩
    ⟨hinner, d.order_two, P, fun x => d.fixes x x.property⟩

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
