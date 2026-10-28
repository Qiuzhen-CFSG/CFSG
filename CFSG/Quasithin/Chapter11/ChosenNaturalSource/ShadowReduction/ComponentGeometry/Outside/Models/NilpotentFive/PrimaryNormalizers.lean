module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models.NilpotentFive.PrimaryActions
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.FittingActions
public import Theory.GroupTheory.NormalizerQuotientNilpotent
public import Theory.SpecificGroups.GL2.NoncommutativeCentralizer
public import Theory.SpecificGroups.PSL2.OuterSolvable.SmallDegreeTwoGroup
public import Theory.SpecificGroups.SL2.PrimePlaneAction
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms

/-!
# Primary normalizers for the nilpotent SL₂(5) alternative

Out(SL₂(5)) embeds in the two-group Out(PSL₂(5)). In a finite GL₂ model,
the centralizer of an SL₂(5) subgroup is scalar, so its normalizer quotient
is nilpotent. This applies to the actual omega--Frattini action and, through
the natural power bridge, the full-core Frattini action at every permitted
prime and every homocyclic exponent.

For an extraspecial primary core the Frattini automorphism kernel is inner
and lies in the actual conjugation image. The normalizer quotient therefore
embeds in the proved linear quotient, completing this full-core branch.
The homocyclic lift and the assembly across distinct primes remain separate.
Source: Aschbacher--Smith A.3.6(4), pp.43--45; 11.4.3, p.778.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models.NilpotentFive

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem slFive_outer_two : IsPGroup 2 (MulAut.Outer SL(2, ZMod 5)) := by
  let : Group.IsPerfect SL(2, ZMod 5) := Matrix.SpecialLinearGroup.PrimePlaneAction.perfect (by decide)
  apply (Theory.PSL2.OuterSolvable.SmallDegreeSquares.outer_isPGroup_two
    (F := ZMod 5) (p := 5) (n := 1) (by decide) (by decide) (by decide) (by simp)).of_injective
      (NormalizerOuterQuotient.centralOuterMap SL(2, ZMod 5)) (NormalizerOuterQuotient.centralOuterMap_injective _)

theorem field_normalizer_nilpotent {F : Type*} [Field F] [Finite F]
    (U : Subgroup (GL (Fin 2) F)) (e : U ≃* SL(2, ZMod 5)) :
    Group.IsNilpotent (NormalizerOuterQuotient.Quotient U) := by
  apply NormalizerOuterQuotient.nilpotent_of_centralizer_le_center U
  · rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    apply Matrix.GeneralLinearGroup.centralizer_le_scalar_of_noncommutative
    let : Group.IsPerfect SL(2, ZMod 5) :=
      Matrix.SpecialLinearGroup.PrimePlaneAction.perfect (by decide)
    let : Group.IsPerfect U := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    let : Nontrivial SL(2, ZMod 5) := ⟨⟨1, -1, by
      intro he
      have hh := congrArg (fun g : SL(2, ZMod 5) => g 0 0) he
      exact (by decide : (1 : ZMod 5) ≠ -1) hh⟩⟩
    let : Nontrivial U := e.symm.injective.nontrivial
    exact Group.IsPerfect.not_isMulCommutative U
  · exact slFive_outer_two.of_equiv (MulAut.outerCongr e).symm


theorem elementary_normalizer_nilpotent {p : ℕ} [Fact p.Prime]
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian p V]
    (hc : Nat.card V = p ^ 2) (U : Subgroup (MulAut V))
    (e : U ≃* SL(2, ZMod 5)) : Group.IsNilpotent (NormalizerOuterQuotient.Quotient U) := by
  obtain ⟨f, hf⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le V hc.le
  exact NormalizerOuterQuotient.nilpotent_of_map f U
    (by rw [(MonoidHom.ker_eq_bot_iff f).mpr hf]; exact bot_le)
    (field_normalizer_nilpotent (U.map f) ((U.equivMapOfInjective f hf).symm.trans e))

open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02

theorem omega_normalizer_nilpotent
    {B : Type*} [Group B] [Finite B] [Group.IsPerfect B]
    (h : A36Nilpotent B) {p : ℕ} [Fact p.Prime]
    (hd : p ∣ Nat.card (fittingSubgroup B)) :
    Group.IsNilpotent (NormalizerOuterQuotient.Quotient (RadicalActions.omegaFrattiniAction p B).range) := by
  have hp : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by
    intro he
    have hc := (h.2.2.2 p Fact.out (h.1.symm ▸ hd)).1
    norm_num [he] at hc)
  obtain ⟨e, _⟩ := CenterFrattiniSource.nilpotent_exists_inverting_quotient h hp hd
  let := (RadicalActions.Nilpotent.frattini_shape h hd).1
  apply elementary_normalizer_nilpotent (RadicalActions.Nilpotent.frattini_shape h hd).2
  exact (QuotientGroup.quotientKerEquivRange _).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq ((omegaAction_kernel h hd).trans h.1.symm)).trans e)


theorem coreFrattini_normalizer_nilpotent
    {B : Type*} [Group B] [Finite B] [Group.IsPerfect B]
    (h : A36Nilpotent B) {p : ℕ} [Fact p.Prime]
    (hd : p ∣ Nat.card (fittingSubgroup B)) :
    Group.IsNilpotent (NormalizerOuterQuotient.Quotient (FittingActions.coreFrattiniAction p B).range) := by
  let E := FittingActions.coreOmegaEquiv (Or.inr h) hd
  let f := (MulAut.congr E).toMonoidHom
  have he : f.comp (FittingActions.coreFrattiniAction p B) =
      RadicalActions.omegaFrattiniAction p B := by
    ext b x
    obtain ⟨x, rfl⟩ := E.surjective x
    change E (FittingActions.coreFrattiniAction p B b (E.symm (E x))) = _
    rw [E.symm_apply_apply]
    exact FittingActions.coreOmegaEquiv_equivariant (Or.inr h) hd b x
  apply NormalizerOuterQuotient.nilpotent_of_map f _
    (by rw [(MonoidHom.ker_eq_bot_iff f).mpr (MulAut.congr E).injective]; exact bot_le)
  rw [← MonoidHom.range_comp, he]
  exact omega_normalizer_nilpotent h hd

theorem extraspecial_primary_normalizer_nilpotent
    {B : Type*} [Group B] [Finite B] [Group.IsPerfect B]
    (h : A36Nilpotent B) {p : ℕ} [Fact p.Prime]
    (hd : p ∣ Nat.card (fittingSubgroup B))
    (hs : LocalModels.OddExtraspecialThree p (pCore p B)) :
    Group.IsNilpotent (NormalizerOuterQuotient.Quotient (CharacteristicOuterRestriction.innerActionImage (pCore p B))) := by
  let : IsExtraspecial p (pCore p B) := hs.1.1
  let f := quotientAut (frattini (pCore p B))
  have hk : f.ker ≤ CharacteristicOuterRestriction.innerActionImage (pCore p B) := by
    rw [show f = quotientAut (frattini (pCore p B)) from rfl,
      IsExtraspecial.quotientAut_frattini_ker_eq_range_conj (p := p)]
    rintro a ⟨x, rfl⟩
    exact ⟨x.val, MulAut.conjNormal_val⟩
  apply NormalizerOuterQuotient.nilpotent_of_map f _ hk
  have he : f.comp (MulAut.conjNormal : B →* MulAut (pCore p B)) =
      FittingActions.coreFrattiniAction p B := by
    apply MonoidHom.ext
    intro b
    change f (MulAut.conjNormal b) = f (MulAut.characteristic (pCore p B) (MulAut.conj b))
    rw [characteristic_conj_eq_conjNormal]
  change Group.IsNilpotent (NormalizerOuterQuotient.Quotient (((MulAut.conjNormal : B →* MulAut (pCore p B)).range).map f))
  rw [← MonoidHom.range_comp, he]
  exact coreFrattini_normalizer_nilpotent h hd


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models.NilpotentFive
