module
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Statement
public import Theory.Representation.PerfectCentralSectionDisplacement
public import Theory.Representation.BinaryAlternatingNaturalCohomology
public import Theory.Representation.BinaryPermutationNaturalDuality
public import Theory.Representation.BinaryOffender.InvolutionRatio
/-!
# Symmetric-five factor of the dual B.5.13 product case

For a symmetric-five factor, restrict the dual action to the marked alternating
five subgroup. The supplied factor subspace has trivial quotient, and its
natural A₅ quotient has vanishing first cohomology together with its dual. The
central-section displacement lemma therefore bounds the full displacement of an
involution by the four-dimensional natural section. An involution in A₅ then
witnesses the quadratic ratio bound on the original module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.13,
printed pp.110–111, using B.5.1(2) and I.1.6(1).
-/

public section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
namespace CFSG.Quasithin.ChapterB.SourceB513
open SourceInduction QuasisimpleSource
private abbrev natural := BinaryPermutation.alternatingNaturalRepresentation (Fin 5)
private theorem natural_H1 : Subsingleton (H1 natural) :=
  Module.finrank_zero_iff.mp BinaryPermutation.alternatingFive_natural_finrank_H1
private theorem natural_dual_H1 : Subsingleton (H1 natural.dual) := by
  let := natural_H1
  exact (H1Congr natural natural.dual (MulEquiv.refl _)
    (BinaryPermutation.naturalDualEquiv (Fin 5))
    (fun g v => BinaryPermutation.naturalDualEquiv_equivariant (Fin 5) g.val v)).symm.injective.subsingleton
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
 [FiniteDimensional (ZMod 2) V]
theorem quadraticRatio_le_two_of_dual_symmetricFive_section
    (ρ : Representation (ZMod 2) D V) (A : Subgroup D)
    (U : Subrepresentation ρ.dual) (hU : moved ρ.dual A ≤ U.toSubmodule)
    (hn : IsSymmetricNatural (((QuasisimpleSource.fixed ρ.dual).quotientImage U).toRepresentation.comp A.subtype) 5) :
    quadraticRatio ρ ≤ 2 := by
  obtain ⟨n⟩ := hn
  let f : alternatingGroup (Fin 5) →* D :=
    A.subtype.comp (n.groupEquiv.symm.toMonoidHom.comp (alternatingGroup (Fin 5)).subtype)
  have hf : Function.Injective f :=
    A.subtype_injective.comp (n.groupEquiv.symm.injective.comp (alternatingGroup (Fin 5)).subtype_injective)
  let σ := ρ.dual.comp f
  let W : Subrepresentation σ :=
    ⟨U.toSubmodule, fun g _ hw => U.apply_mem_toSubmodule (f g) hw⟩
  let q : U.toSubmodule →ₗ[ZMod 2] ((QuasisimpleSource.fixed ρ.dual).quotientImage U).toSubmodule :=
    { toFun := fun v => ⟨(QuasisimpleSource.fixed ρ.dual).toSubmodule.mkQ v, ⟨v,v.property,rfl⟩⟩
      map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
  let p : W.toRepresentation.IntertwiningMap natural :=
    (n.linearEquiv.toLinearMap.comp q).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g v
      have hh := n.intertwines (n.groupEquiv.symm g.val) (q v)
      rw [n.groupEquiv.apply_symm_apply] at hh
      exact hh)
  have hs : Function.Surjective p := by
    intro w
    obtain ⟨v,hv⟩ := n.linearEquiv.surjective w
    obtain ⟨x,hx,he⟩ := v.property
    refine ⟨⟨x,hx⟩, ?_⟩
    change n.linearEquiv (q ⟨x,hx⟩) = w
    rw [show q ⟨x,hx⟩ = v from Subtype.ext he, hv]
  have hc : p.toLinearMap.ker ≤ (Representation.invariants (W.toRepresentation) : Submodule (ZMod 2) W.toSubmodule) := by
    intro v hv g
    have hz : q v = 0 := n.linearEquiv.injective (by
      change n.linearEquiv (q v) = n.linearEquiv 0
      rw [map_zero]
      exact hv)
    have hx : (v : Module.Dual (ZMod 2) V) ∈ ρ.dual.invariants :=
      (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val hz)
    exact Subtype.ext (hx (f g))
  have ht : HasTrivialQuotient W := by
    intro g v
    exact hU (Submodule.subset_span ⟨f g,(n.groupEquiv.symm g.val).property,v,Submodule.mem_top,rfl⟩)
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let := natural_H1
  let := natural_dual_H1
  obtain ⟨t,htwo⟩ := exists_prime_orderOf_dvd_card' (G := alternatingGroup (Fin 5)) 2
    (by
      have hh : Nat.card (alternatingGroup (Fin 5)) = 60 := by
        rw [nat_card_alternatingGroup]
        norm_num [Nat.card_eq_fintype_card]
      rw [hh]
      decide)
  have hb := fixedCodim_central_section_le W ht p hs hc t
  have hnat := (involution_actor_rank_and_fixedCodim natural t htwo).2.2.2
  have hdim : Module.finrank (ZMod 2) (BinaryPermutation.natural (Fin 5)) = 4 := by
    simpa using BinaryPermutation.finrank_natural_odd (Fin 5) (by decide)
  have hfull : fixedCodim ρ (zpowers (f t)) ≤ 2 := by
    rw [← fixedCodim_zpowers_dual]
    have he : fixedCodim σ (zpowers t) = fixedCodim ρ.dual (zpowers (f t)) := by
      rw [fixedCodim_zpowers_eq_displacement_rank, fixedCodim_zpowers_eq_displacement_rank]
      rfl
    omega
  have htD : orderOf (f t) = 2 := (orderOf_injective f hf t).trans htwo
  obtain ⟨he,hr,hquad,_⟩ := involution_actor_rank_and_fixedCodim ρ (f t) htD
  exact (quadraticRatio_le_two_iff ρ).mpr ⟨zpowers (f t),he,hquad,by omega⟩
end CFSG.Quasithin.ChapterB.SourceB513
