module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.GroupTheory.CyclicNormalOddQuotient
public import Theory.SpecificGroups.AlternatingSix.OuterSolvable
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.OuterQuotient
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup
public import Theory.SpecificGroups.Triality.OuterOddSubgroups
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups
public import Theory.SpecificGroups.Tits.OuterOddSubgroups
public import Theory.SpecificGroups.PSL2.OuterSolvable.FieldAutomorphisms

/-!
# Exceptional rank-two cases in the outer-group inspection

The commutator of the actual central quotient PSp₄(2) is identified with A₆
by the faithful six-letter polar representation. Its outer group therefore
has order four, which supplies the required cyclic-normal-subgroup condition.

For the split-octonion G₂ model, inner–field coverage makes the full outer
group a quotient of the cyclic coefficient-field automorphism group. At the
binary derived endpoint, full-group conjugation makes the outer group a quotient
of the known order-two quotient G₂(2)/G₂(2)′. The final model theorems discharge
both coverage premises of the retained conditional reductions.

For PSp₄ the actual central-quotient equivalence transfers the diagram-action
calculation, with semilinear classification discharged. Genuine triality uses
the full cubic coefficient field; Ree uses the supplied fixed-group witness.
Simplicity and perfectness transfer from the source group to those two carriers.
The Tits presentation has a two-group outer quotient. Thus every non-linear
constructor of `LocalModels.RankTwoTheoremC` is covered through its literal
model isomorphism, including all three separate small endpoints.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the proof of
1.3.4 on printed p.510 and Theorem C with Remark A.2.4 on p.33;
GLS3, Theorem 2.5.12, for the inner, diagonal, field and graph factors.
-/

public section

namespace CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
open Subgroup Theory.GroupTheory
open Atlas.G2.LieAutomorphismExtensions

/-- The exact small symplectic carrier in Theorem C has outer order four. -/
theorem symplectic_derived_outer_cyclicNormalOddQuotient :
    HasCyclicNormalOddQuotient
      (MulAut.Outer (commutator (ClassicalGroup.PSp 2 (ZMod 2)))) := by
  have h : HasCyclicNormalOddQuotient (MulAut.Outer (alternatingGroup (Fin 6))) :=
    hasCyclicNormalOddQuotient_of_isPGroup_two
      (IsPGroup.of_card (n := 2) AlternatingSix.ShadowLocal.outer_card)
  exact h.of_injective
    (MulAut.outerCongr
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix).toMonoidHom
    (MulAut.outerCongr
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix).injective

/-- Transport through precisely the small symplectic isomorphism clause. -/
theorem symplectic_derived_model_outer_cyclicNormalOddQuotient
    {S : Type*} [Group S]
    (iso : Nonempty (S ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) :
    HasCyclicNormalOddQuotient (MulAut.Outer S) := by
  obtain ⟨e⟩ := iso
  exact symplectic_derived_outer_cyclicNormalOddQuotient.of_injective
    (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective

/-- Full inner–field coverage, when proved, makes Out(G₂) cyclic.
Injectivity of the semilinear action alone would not suffice. -/
theorem g2_outer_isCyclic_of_coverage {F : Type*} [Field F] [Finite F]
    (hcover : Function.Surjective (semilinearAction (F := F))) :
    IsCyclic (MulAut.Outer (Atlas.G2.Model F)) := by
  let : IsCyclic (F ≃+* F) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  let I := MulAut.innerSubgroup (Atlas.G2.Model F)
  let f := (QuotientGroup.mk' I).comp (fieldAction (F := F))
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective I q
    obtain ⟨z, rfl⟩ := hcover a
    refine ⟨z.right, ?_⟩
    have hg : QuotientGroup.mk' I (MulAut.conj z.left) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨z.left, rfl⟩
    change QuotientGroup.mk' I (fieldAction z.right) =
      QuotientGroup.mk' I (MulAut.conj z.left * fieldAction z.right)
    rw [map_mul, hg, one_mul]
  exact isCyclic_of_surjective f hf

/-- The nonbinary G₂ branch reduces to coverage over the field supplied by
its actual model predicate. The field characteristic follows from its order. -/
theorem g2_model_outer_cyclicNormalOddQuotient_of_coverage
    {S : Type*} [Group S] (f : ℕ) (hf : 2 ≤ f)
    (iso : ClassificationModels.IsG2At S (2 ^ f))
    (hcover : ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
      2 < Nat.card F → Function.Surjective (semilinearAction (F := F))) :
    HasCyclicNormalOddQuotient (MulAut.Outer S) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := iso
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hlarge : 2 < Nat.card F := by
    rw [hcard]
    have hfour : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by decide) hf
    omega
  let : IsCyclic (MulAut.Outer (Atlas.G2.Model F)) :=
    g2_outer_isCyclic_of_coverage (hcover F hlarge)
  exact hasCyclicNormalOddQuotient_of_isCyclic.of_injective
    (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective

/-- Coverage by actual full-group conjugation makes Out(G₂(2)′) a quotient
of G₂(2)/G₂(2)′, which has order two. Faithfulness is not needed here. -/
theorem g2_derived_outer_isCyclic_of_coverage
    (hcover : Function.Surjective binaryConjugation) :
    IsCyclic (MulAut.Outer BinaryDerived) := by
  have hc : Nat.card (Atlas.G2.Model (ZMod 2) ⧸ BinaryDerived) = 2 := by
    change BinaryDerived.index = 2
    rw [binaryDerived_eq]
    exact Atlas.G2.BinaryException.index_H
  let : IsCyclic (Atlas.G2.Model (ZMod 2) ⧸ BinaryDerived) :=
    isCyclic_of_prime_card hc
  apply isCyclic_of_surjective (MulAut.outerAction BinaryDerived)
  intro q
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup BinaryDerived) q
  obtain ⟨g, rfl⟩ := hcover a
  exact ⟨QuotientGroup.mk g, rfl⟩

/-- The binary G₂ reduction uses precisely the commutator-carrier clause,
without substituting an unproved exceptional unitary identification. -/
theorem g2_derived_model_outer_cyclicNormalOddQuotient_of_coverage
    {S : Type*} [Group S]
    (iso : Nonempty (S ≃* commutator (Atlas.G2.Model (ZMod 2))))
    (hcover : Function.Surjective binaryConjugation) :
    HasCyclicNormalOddQuotient (MulAut.Outer S) := by
  obtain ⟨e⟩ := iso
  let := g2_derived_outer_isCyclic_of_coverage hcover
  exact hasCyclicNormalOddQuotient_of_isCyclic.of_injective
    (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective

/-- The nonbinary symplectic clause uses the actual central quotient and the
proved classification of all diagram-preserving automorphisms. -/
theorem symplectic_model_outer_cyclicNormalOddQuotient
    {S : Type*} [Group S] (f : ℕ) (hf : 2 ≤ f)
    (iso : ClassicalGroup.IsPSp S 2 (2 ^ f)) :
    HasCyclicNormalOddQuotient (MulAut.Outer S) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := iso
  let : CharP F 2 :=
    Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
  have hlarge : 2 < Nat.card F := by
    rw [hcard]
    have hfour : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by decide) hf
    omega
  have h := Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.outer_hasCyclicNormalOddQuotient
    hlarge
    Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram
  let e' := e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
  exact h.of_injective (MulAut.outerCongr e').toMonoidHom (MulAut.outerCongr e').injective

/-- The nonbinary G₂ model clause with abstract automorphism coverage discharged. -/
theorem g2_model_outer_cyclicNormalOddQuotient
    {S : Type*} [Group S] (f : ℕ) (hf : 2 ≤ f)
    (iso : ClassificationModels.IsG2At S (2 ^ f)) :
    HasCyclicNormalOddQuotient (MulAut.Outer S) :=
  g2_model_outer_cyclicNormalOddQuotient_of_coverage f hf iso
    (fun _ _ _ _ hlarge => semilinearAction_surjective hlarge)

/-- The small G₂ clause, using exhaustive full-group conjugation on the literal
commutator carrier. No exceptional unitary comparison is assumed. -/
theorem g2_derived_model_outer_cyclicNormalOddQuotient
    {S : Type*} [Group S]
    (iso : Nonempty (S ≃* commutator (Atlas.G2.Model (ZMod 2)))) :
    HasCyclicNormalOddQuotient (MulAut.Outer S) :=
  g2_derived_model_outer_cyclicNormalOddQuotient_of_coverage iso
    binaryConjugation_surjective

/-- The genuine triality clause, for every supplied parameter record, retaining
the cubic coefficient-field action also at field order two. -/
theorem triality_model_outer_cyclicNormalOddQuotient
    {S : Type*} [Group S] [IsSimpleGroup S] [Group.IsPerfect S]
    (f : ℕ) (hf : 1 ≤ f)
    (iso : Triality.Standard.IsTrialityGroupAt (2 ^ f) S) :
    HasCyclicNormalOddQuotient (MulAut.Outer S) := by
  obtain ⟨P, hq, ⟨e⟩⟩ := iso
  let : IsSimpleGroup (Triality.Standard.Carrier P) := e.symm.isSimpleGroup
  let : Group.IsPerfect (Triality.Standard.Carrier P) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact (Triality.Standard.OuterOdd.outer_cyclicNormalOddQuotient P f hf hq).of_injective
    (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective

/-- The general Ree clause uses the fixed group in the supplied root-equation
witness; no existence or comparison with a different Ree model is needed. -/
theorem ree_model_outer_cyclicNormalOddQuotient
    {S : Type*} [Group S] [IsSimpleGroup S] [Group.IsPerfect S]
    (m : ℕ) (hm : 1 ≤ m) (iso : Section02.LocalModels.IsReeF4At S m) :
    HasCyclicNormalOddQuotient (MulAut.Outer S) := by
  obtain ⟨d, ⟨e⟩⟩ := iso
  let : IsSimpleGroup d.fixedGroup := e.symm.isSimpleGroup
  let : Group.IsPerfect d.fixedGroup :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact (ReeF4.LocalBlockInput.outer_cyclicNormalOddQuotient hm d).of_injective
    (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective

/-- The Tits endpoint uses precisely Parrott's presentation carrier. -/
theorem tits_model_outer_cyclicNormalOddQuotient
    {S : Type*} [Group S] (iso : Nonempty (S ≃* Tits.ParrottGroup)) :
    HasCyclicNormalOddQuotient (MulAut.Outer S) := by
  obtain ⟨e⟩ := iso
  exact Tits.OuterOddSubgroups.parrott_hasCyclicNormalOddQuotient.of_injective
    (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective

end CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
