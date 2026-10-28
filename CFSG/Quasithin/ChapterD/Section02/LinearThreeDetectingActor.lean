module
public import CFSG.Quasithin.ChapterD.Section02.LinearThreeCentralTypes
public import CFSG.Quasithin.ChapterD.Section02.QuadraticCentralCovers
public import Theory.Representation.BinaryOffender.Homogeneous.LinearThreeInertia
public import Theory.Representation.BinaryOffender.HomogeneousOrbitAction

/-!
# Binary linear-three supports detected by a quadratic actor

An actor faithful on a component supplies minimum-ratio actors on every
irreducible subquotient. Clifford restriction and the Chapter K recognition
then identify all noncentral component types, and occurrence lifts this to
the literal central quotient of any Irr⁺ support. No semisimplicity of the
original module is needed.

On a homogeneous orbit, the same actor preserves the whole central cover
and acts by inner component automorphisms. The full orbit kernel theorem
therefore transfers its small quadratic ratio to the component itself.
The single normal component consumer in Chapter14 uses this to exclude
the four-dimensional cover and construct the same suitable vector.

Source: Aschbacher--Smith D.2.5, K.3.2, F.9.18(2--4),14.6.22,
printed pp.179,455--456,325--326,1038.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.ChapterD
open ChapterB.QuasisimpleSource
universe u
variable {D V : Type u} [Group D] [Finite D] [AddCommGroup V]
  [Module (ZMod 2) V] [Finite V]
  (ρ : Representation (ZMod 2) D V)

private theorem detecting_minimal_actor {K A : Subgroup D}
    (hA : IsElementaryTwo A ∧ IsQuadratic ρ A ∧ fixedCodim ρ A ≤ 2 * rank A) (hf : A ⊓ centralizer (K : Set D) = ⊥) :
    ∃ C, C ≤ A ∧ ¬ C ≤ centralizer (K : Set D) ∧
      C ∈ RPlusBound ρ 2 ∧ IsQuadratic ρ C := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨C,hCA,hC⟩ := exists_RPlusBound_subgroup ρ hA.1
    ((actionRatio_le_nat_iff ρ hA.1 2).mpr hA.2.2)
  refine ⟨C,hCA,?_,hC,fun c hc d hd v => hA.2.1 c (hCA hc) d (hCA hd) v⟩
  intro hc
  exact hC.1.1.1 (le_bot_iff.mp ((le_inf hCA hc).trans_eq hf))

/-- A detecting quadratic actor recognizes every noncentral component type
on every irreducible subquotient, without semisimplicity of the original module. -/
theorem subquotient_linear_three_of_detecting_actor
    {K A : Subgroup D} [IsQuasisimple K]
    (hK : K.IsSubnormal) (hz : center K = ⊥)
    (hs : IsSQTK KnownSimple.IsKnownSimple D) (hm : ClassicalGroup.IsPSL K 3 2)
    (hAN : A ≤ normalizer (K : Set D))
    (hA : IsElementaryTwo A ∧ IsQuadratic ρ A ∧ fixedCodim ρ A ≤ 2 * rank A) (hf : A ⊓ centralizer (K : Set D) = ⊥)
    (U : Subrepresentation ρ) (N : Subrepresentation U.toRepresentation)
    (hi : IsIrreducible N.quotientRepresentation) :
    NaturalLinearThreeTypes N.quotientRepresentation K := by
  let σ := N.quotientRepresentation
  let : Finite (U ⧸ N.toSubmodule) := Module.finite_of_finite (ZMod 2)
  let : Module.Finite (ZMod 2) (U ⧸ N.toSubmodule) := Module.Finite.of_finite
  let : IsIrreducible σ := hi
  let : IsSemisimpleRepresentation (σ.comp K.subtype) :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr
      (subnormal_restriction_semisimple σ K hK)
  have hq : IsQuadratic σ A :=
    quadratic_of_equivariant_surjection U.toRepresentation σ
      N.toSubmodule.mkQ N.toSubmodule.mkQ_surjective (fun _ _ => rfl) A
      (quadratic_subrepresentation ρ U hA.2.1)
  have hd : fixedCodim σ A ≤ 2 * rank A := by
    have hu := fixedCodim_subrepresentation_le ρ U A
    have hn := fixedCodim_quotient_add_subrepresentation_le U.toRepresentation N A
    have ha := hA.2.2
    change fixedCodim N.quotientRepresentation A ≤ 2 * rank A
    omega
  obtain ⟨C,hCA,hnC,hC,hqC⟩ := detecting_minimal_actor σ ⟨hA.1,hq,hd⟩ hf
  exact naturalLinearThreeTypes_of_minimal_actor σ hz hs hm (hCA.trans hAN) hC hqC hnC

/-- The actual central quotient of every Irr⁺ support is natural. -/
theorem central_linear_three_of_detecting_actor
    {K A : Subgroup D} [IsQuasisimple K]
    (hK : K.IsSubnormal) (hz : center K = ⊥)
    (hs : IsSQTK KnownSimple.IsKnownSimple D) (hm : ClassicalGroup.IsPSL K 3 2)
    (hAN : A ≤ normalizer (K : Set D))
    (hA : IsElementaryTwo A ∧ IsQuadratic ρ A ∧ fixedCodim ρ A ≤ 2 * rank A) (hf : A ⊓ centralizer (K : Set D) = ⊥)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ K I) :
    Nonempty (ActionEquiv (centralQuotientRepresentation ρ K I hI.choose)
      (linearNatural BinaryField.two 3)) :=
  central_constituent_linear_three_of_sections ρ K hK
    (fun U N hi => subquotient_linear_three_of_detecting_actor ρ hK hz hs hm hAN hA hf U N hi) hI

/-- A detecting actor bounds the action of the component on the entire
homogeneous orbit, retaining the central kernels of its seeds. -/
theorem linear_three_orbit_bound_of_detecting_actor
    {K P A : Subgroup D} [IsQuasisimple K]
    (hz : center K = ⊥) (hP : IsPGroup 2 P)
    (hAP : A ≤ P) (hA : IsElementaryTwo A ∧ IsQuadratic ρ A ∧ fixedCodim ρ A ≤ 2 * rank A)
    (hf : A ⊓ centralizer (K : Set D) = ⊥)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlusWith ρ K P I)
    (b : ActionEquiv (centralQuotientRepresentation ρ K I hI.isIrrPlus.choose)
      (linearNatural BinaryField.two 3)) :
    quadraticRatio (invariantSubspace ρ K (orbitSpan ρ P I)
      (orbitSpan_component_invariant ρ hI.normalizes hI.isIrrPlus)).toRepresentation ≤ 2 := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨C,hCA,hnC,hC,hqC⟩ := detecting_minimal_actor ρ hA hf
  have hCP := hCA.trans hAP
  have hinj : Function.Injective (centralQuotientRepresentation ρ K I hI.isIrrPlus.choose) := by
    intro x y hxy
    apply b.groupEquiv.injective
    apply specialLinearNatural_injective 3
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := b.linearEquiv.surjective v
    exact (b.intertwines x w).symm.trans
      ((congrArg (fun f => b.linearEquiv (f w)) hxy).trans (b.intertwines y w))
  have hdim : 2 < Module.finrank (ZMod 2) (centralQuotient ρ K I) := by
    rw [b.linearEquiv.finrank_eq]
    change 2 < Module.finrank (ZMod 2) (Fin 3 → ZMod 2)
    rw [Module.finrank_fin_fun]
    decide
  obtain ⟨hD,_⟩ := stable_central_cover_image_bound ρ hI hCP hC hqC hinj hdim hnC
  obtain ⟨hO,hbound⟩ := central_cover_orbit_image_bound ρ hI hCP hC hqC hinj hnC
  have hi : ∀ c : C, ∃ k : K,
      K.normalizerMonoidHom ⟨c,hI.normalizes (hCP c.property)⟩ = MulAut.conj k := by
    intro c
    exact hI.inner_of_natural_map_eq ρ ⟨c,hCP c.property⟩
      b.groupEquiv b.linearEquiv b.intertwines
      ((subspace_map_eq_iff ρ I c.val).mpr (hD ((le_sup_right : C ≤ K ⊔ C) c.property)))
  exact (orbit_component_quadraticRatio_le ρ hz hP hI hCP hi hO).trans hbound

end CFSG.Quasithin.ChapterD
