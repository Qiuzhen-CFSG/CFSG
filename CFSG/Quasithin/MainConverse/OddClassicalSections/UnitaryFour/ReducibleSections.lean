module

public import CFSG.Quasithin.MainConverse.SolvableSections
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ReducibleGeometry
public import Theory.GroupTheory.SimpleSectionSolvableReduction.Model
public import CFSG.Quasithin.MainConverse.AlternatingSections.SmallDegrees
public import BenderSuzuki.External.Huppert.II.theorem_10_13

/-!
# Simple sections of reducible subgroups of PSU₄(3)

Source: Aschbacher–Smith, Theorem 0.1.2(4) and condition K, printed pp.4
and 482 of `refs/quasithin.pdf`.

The full SU inverse image of a reducible projective subgroup stabilizes a
nonzero proper subspace. `ReducibleGeometry` proves that it therefore lies
in the projective stabilizer of either a totally isotropic subspace or a
nondegenerate subspace, including the case of a nonzero proper radical.

The two structural stabilizer identifications remain explicit premises:
isotropic stabilizers are solvable or have a solvable kernel with quotient
A₆; nondegenerate stabilizers are solvable or actual copies of PSU₃(3).
Solvable-kernel reduction and the proved A₆ section theorem handle the first
family. For the second, Huppert's simplicity theorem and the actual unitary
catalogue entry extend the PSU₃(3) proper-section premise to all its sections.

These are conditional assembly theorems. The source reducible-section
classification remains unfinished until both stabilizer identifications
and the PSU₃(3) proper-section premise are discharged. Normal subgroups in
the quotient conclusion are normal inside their numerator subgroup.
-/

public noncomputable section

namespace CFSG.Quasithin.MainConverse.UnitaryFourReducible

open CFSG.KnownSimple
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ReducibleGeometry

/-- Huppert II.10.13 applies to the identity form over the field of nine elements. -/
theorem carrierThree_isSimple : IsSimpleGroup (Carrier 3) := by
  let : CharP FiniteField.Nine 3 := charP_of_card_eq_prime_pow (p := 3) (f := 2)
    (by simp [← Nat.card_eq_fintype_card])
  exact BenderSuzuki.External.huppert_II_10_13 (form 3) 3 (by decide)
    (by simp)
    ((form 3).card_fixed_of_prime_frobenius (p := 3) (form_conj_cube 3))

/-- The concrete dimension-three model satisfies the exact source model predicate. -/
theorem carrierThree_isPSU : ClassicalGroup.IsPSU (Carrier 3) 3 3 :=
  ⟨FiniteField.Nine, inferInstance, inferInstance, form 3,
    by simp, form_conj_cube 3, ⟨MulEquiv.refl _⟩⟩

/-- The whole PSU₃(3) model is a concrete unitary catalogue carrier. -/
theorem carrierThree_constructed : IsConstructedCarrier (Carrier 3) := by
  exact .classical (.unitary 3 3
    ⟨(by decide : Nat.Prime 3).isPrimePow, by decide, by simp, by simp⟩ carrierThree_isPSU)

/-- Proper sections together with simplicity and catalogue membership handle every section. -/
theorem carrierThree_isKGroup_of_properK
    (hproper : ¬ IsMulCommutative (Carrier 3) →
      HasProperKSubgroups IsConstructedCarrier (Carrier 3)) :
    IsKGroup IsConstructedCarrier (Carrier 3) := by
  classical
  by_cases hc : IsMulCommutative (Carrier 3)
  · let : Group.IsSolvable (Carrier 3) := Group.isSolvable_of_comm hc.is_comm.comm
    exact solvable_isKGroup_constructed _
  intro S _ hS U f hf
  let := hS
  by_cases hU : U = ⊤
  · subst U
    let : IsSimpleGroup (Carrier 3) := carrierThree_isSimple
    let g : Carrier 3 →* S := f.comp Subgroup.topEquiv.symm.toMonoidHom
    have hg : Function.Surjective g := hf.comp Subgroup.topEquiv.symm.surjective
    exact carrierThree_constructed.of_mulEquiv
      (MulEquiv.ofBijective g ⟨g.injective_of_surjective_of_simple hg, hg⟩).symm
  · exact hproper hc U hU S hS ⊤
      (f.comp (Subgroup.topEquiv (G := U)).toMonoidHom)
      (hf.comp (Subgroup.topEquiv (G := U)).surjective)

private theorem constructed_section_of_containment
    {G S : Type} [Group G] [Group S] [IsSimpleGroup S]
    (U P : Subgroup G) (hle : U ≤ P) (hP : IsKGroup IsConstructedCarrier P)
    (f : U →* S) (hf : Function.Surjective f) : IsConstructedCarrier S := by
  let e := Subgroup.subgroupOfEquivOfLe hle
  exact hP S inferInstance (U.subgroupOf P) (f.comp e.toMonoidHom) (hf.comp e.surjective)

private theorem isKGroup_of_solvableKernelModel {G H : Type} [Group G] [Group H]
    (m : Group.SolvableKernelModel G H) (hH : IsKGroup IsConstructedCarrier H) :
    IsKGroup IsConstructedCarrier G := by
  intro S _ hS U f hf
  let := hS
  by_cases hs : Group.IsSolvable S
  · let := hs
    exact .cyclic (primeCyclic_of_solvable_simple S)
  · obtain ⟨V, g, hg⟩ := m.simple_section hs U f hf
    exact hH S hS V g hg

/-- Conditional assembly using actual stabilizer quotient models and the smaller-group result. -/
theorem simpleSection_of_stabilizer_models
    (hisotropic : ∀ W : Submodule FiniteField.Nine (Space 4), W ≠ ⊥ → W ≠ ⊤ →
      W ≤ orthogonal W → Group.IsSolvable (projectiveStabilizer W) ∨
        Nonempty (Group.SolvableKernelModel (projectiveStabilizer W) (alternatingGroup (Fin 6))))
    (hnondegenerate : ∀ W : Submodule FiniteField.Nine (Space 4), W ≠ ⊥ → W ≠ ⊤ →
      radical W = ⊥ → Group.IsSolvable (projectiveStabilizer W) ∨
        Nonempty (projectiveStabilizer W ≃* Carrier 3))
    (hthree : ¬ IsMulCommutative (Carrier 3) →
      HasProperKSubgroups IsConstructedCarrier (Carrier 3))
    (U : Subgroup (Carrier 4)) (hU : IsReducible U)
    {S : Type} [Group S] [IsSimpleGroup S]
    (f : U →* S) (hf : Function.Surjective f) : IsConstructedCarrier S := by
  rcases reducible_stabilizer_alternative U hU with
    ⟨W, hW0, hWtop, hWiso, hle⟩ | ⟨W, hW0, hWtop, hWrad, hle⟩
  · apply constructed_section_of_containment U (projectiveStabilizer W) hle _ f hf
    rcases hisotropic W hW0 hWtop hWiso with hs | hm
    · let := hs
      exact solvable_isKGroup_constructed _
    · obtain ⟨m⟩ := hm
      exact isKGroup_of_solvableKernelModel m
        (alternatingSix_isKGroup_constructed (MulEquiv.refl _))
  · apply constructed_section_of_containment U (projectiveStabilizer W) hle _ f hf
    rcases hnondegenerate W hW0 hWtop hWrad with hs | he
    · let := hs
      exact solvable_isKGroup_constructed _
    · obtain ⟨e⟩ := he
      exact (IsKGroup.equiv e).mpr (carrierThree_isKGroup_of_properK hthree)

/-- Conditional quotient version; the normal subgroup is relative to `U`. -/
theorem simpleQuotient_of_stabilizer_models
    (hisotropic : ∀ W : Submodule FiniteField.Nine (Space 4), W ≠ ⊥ → W ≠ ⊤ →
      W ≤ orthogonal W → Group.IsSolvable (projectiveStabilizer W) ∨
        Nonempty (Group.SolvableKernelModel (projectiveStabilizer W) (alternatingGroup (Fin 6))))
    (hnondegenerate : ∀ W : Submodule FiniteField.Nine (Space 4), W ≠ ⊥ → W ≠ ⊤ →
      radical W = ⊥ → Group.IsSolvable (projectiveStabilizer W) ∨
        Nonempty (projectiveStabilizer W ≃* Carrier 3))
    (hthree : ¬ IsMulCommutative (Carrier 3) →
      HasProperKSubgroups IsConstructedCarrier (Carrier 3))
    (U : Subgroup (Carrier 4)) (hU : IsReducible U)
    (N : Subgroup U) [N.Normal] [IsSimpleGroup (U ⧸ N)] :
    IsConstructedCarrier (U ⧸ N) :=
  simpleSection_of_stabilizer_models hisotropic hnondegenerate hthree U hU
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end CFSG.Quasithin.MainConverse.UnitaryFourReducible
