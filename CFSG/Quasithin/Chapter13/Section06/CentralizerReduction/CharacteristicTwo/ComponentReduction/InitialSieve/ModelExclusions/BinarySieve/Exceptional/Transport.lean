module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve.ActionTransport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelInterface
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.BinaryIdentification
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.QuotientAction

/-!
# Exceptional-model transports for the initial binary sieve

The concrete central quotient inherits simplicity and perfectness from the
component. Sylow conjugacy moves the faithful marked four-group of automorphisms
to fix any prescribed model Sylow subgroup. Neither step identifies the
component with its central quotient or presupposes innerness of the four-group.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve
open A5Module
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}
  {s : Marking L V} {T : Sylow 2 G}

omit [Finite G] in
/-- The model of K/Z(K), including a nontrivial central cover, is simple and perfect. -/
theorem exceptional_model_hypotheses (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K)
    {Q : Type*} [Group Q] (e : NormalizerAction.componentImage K ≃* Q) :
    IsSimpleGroup Q ∧ Group.IsPerfect Q := by
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let f := (NormalizerAction.componentCentralQuotientEquiv K).trans e
  exact ⟨f.isSimpleGroup_congr.mp inferInstance,
    Group.IsPerfect.ofSurjective (f := f.toMonoidHom) f.surjective⟩

/-- A prescribed model Sylow can be used for the intrinsic fixer calculation. -/
theorem exists_model_fixed_four_on_sylow (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K)
    {Q : Type*} [Group Q] (e : NormalizerAction.componentImage K ≃* Q)
    (P : Sylow 2 Q) :
    ∃ A : Subgroup (MulAut Q), IsKleinFour A ∧
      ∀ α ∈ A, ∀ x ∈ P, α x = x := by
  let : Finite Q := Finite.of_injective e.symm e.symm.injective
  obtain ⟨S, A, hA, hfix⟩ := exists_fixed_four_of_equiv K hK a e
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q P S
  let f : Q ≃* Q := MulAut.conj g
  let B := A.map (MulAut.congr f.symm).toMonoidHom
  let eA := A.equivMapOfInjective (MulAut.congr f.symm).toMonoidHom
    (MulAut.congr f.symm).injective
  refine ⟨B, ⟨(Nat.card_congr eA.toEquiv).symm.trans hA.card_four,
    (Monoid.exponent_eq_of_mulEquiv eA).symm.trans hA.exponent_two⟩, ?_⟩
  rintro _ ⟨α, hα, rfl⟩ x hx
  change f.symm (α (f x)) = x
  have hm : (P : Subgroup Q).map f.toMonoidHom = (S : Subgroup Q) :=
    congrArg Sylow.toSubgroup hg
  have hfx : f x ∈ S := by
    change f x ∈ (S : Subgroup Q)
    rw [← hm]
    exact mem_map_of_mem f.toMonoidHom hx
  rw [hfix α hα (f x) hfx, f.symm_apply_apply]

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve
