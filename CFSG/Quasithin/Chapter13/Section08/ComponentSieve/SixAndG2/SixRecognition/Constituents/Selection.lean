module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.Constituents.Source
public import Theory.Representation.BinaryOffender.ConjugateSubgroupSaturation
public import Theory.Representation.BinaryOffender.IrreducibleOrbitGeometry
public import Theory.Representation.BinaryOffender.Homogeneous.Basic
public import Theory.Representation.BinaryOffender.InvolutionRatio

/-!
# Selecting natural A₆ sections from offenders

A noncentral constituent of A₆ has a faithful central quotient, hence degree
at least four. Distinct Irr⁺ members have disjoint central images. When the
whole central quotient has dimension below eight, every such member is
therefore invariant under the ambient actor.

For an offender the proved A₆ conjugate-generation bound makes that dimension
at most six. We select a constituent and construct its natural model with
its own compatible actor marking. A common commutator line supplies a cyclic
offender, so the same construction applies there. These are the precise
recognition cases consumed by `Centrality`; no invariance of arbitrary
constituents under a ratio-two bound is asserted.

Source: Aschbacher–Smith 13.8.22–26, printed pp.957–958,962, with A.1.40,
B.4.2/B.4.5 and the binary A₆ degree gap from G.5.1.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.Constituents
open NaturalSix
variable {J E : Type*} [Group J] [Finite J]
  [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]

omit [Finite J] in
/-- A noncentral A₆ constituent has central image of dimension at least four. -/
theorem image_degree_ge_four (ρ : Representation (ZMod 2) J E)
    (C : Subgroup J) (e : C ≃* Alternating)
    (I : Submodule (ZMod 2) E) (hI : IsIrrPlus ρ C I) :
    4 ≤ Module.finrank (ZMod 2) (I.map (fixedSpace ρ C).mkQ) := by
  let : IsSimpleGroup Alternating := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect Alternating := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsSimpleGroup C := e.isSimpleGroup
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let σ := centralQuotientRepresentation ρ C I hI.choose
  have hf : Function.Injective σ := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rcases σ.normal_ker.eq_bot_or_eq_top with hb | ht
    · exact hb
    · exfalso
      apply hI.not_le_fixedSpace ρ
      apply le_fixedSpace_of_commutator_le_fixedSpace ρ C I hI.choose
      apply Submodule.span_le.mpr
      rintro _ ⟨c, hc, v, hv, rfl⟩
      have hh : σ ⟨c, hc⟩ = 1 := (show (⟨c, hc⟩ : C) ∈ σ.ker from ht.symm ▸ mem_top _)
      have hq := LinearMap.congr_fun hh (Submodule.Quotient.mk (⟨v, hv⟩ : I))
      exact (Submodule.Quotient.eq ((fixedSpace ρ C).comap I.subtype)).mp hq
  have hd := ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.SmallParameter.degree_ge_four
    (σ.comp e.symm.toMonoidHom) (hf.comp e.symm.injective)
  rwa [(Homogeneous.centralQuotientImageEquiv ρ C I).finrank_eq] at hd

omit [Finite J] in
/-- Distinct conjugates would contribute two disjoint four-dimensional images. -/
theorem invariant_of_small_central_quotient (ρ : Representation (ZMod 2) J E)
    (C : Subgroup J) [C.Normal] (e : C ≃* Alternating)
    (hsmall : fixedCodim ρ C < 8)
    (I : Submodule (ZMod 2) E) (hI : IsIrrPlus ρ C I) :
    (⊤ : Subgroup J) ≤ subspaceStabilizer ρ I := by
  intro g _
  apply (subspace_map_eq_iff ρ I g).mp
  by_contra hne
  have hn : g ∈ normalizer (C : Set J) := (C.normalizer_eq_top ▸ mem_top g)
  have hg := hI.map_normalizer ρ hn
  have hdis := hI.disjoint_quotientImages ρ hg (Ne.symm hne)
  have hi := image_degree_ge_four ρ C e I hI
  have hj := image_degree_ge_four ρ C e _ hg
  have hd := (I.map (fixedSpace ρ C).mkQ).finrank_sup_add_finrank_inf_eq
    ((I.map (ρ g)).map (fixedSpace ρ C).mkQ)
  rw [hdis.eq_bot, finrank_bot, add_zero] at hd
  have hb := Submodule.finrank_le (I.map (fixedSpace ρ C).mkQ ⊔
    (I.map (ρ g)).map (fixedSpace ρ C).mkQ)
  change _ ≤ fixedCodim ρ C at hb
  omega

/-- The offender bound constructs an ambient-invariant constituent and its natural model. -/
theorem natural_section_of_offender (ρ : Representation (ZMod 2) J E)
    (C : Subgroup J) (hfit : C = generalizedFitting J) (e : C ≃* Alternating)
    (hn : ¬ (⊤ : Submodule (ZMod 2) E) ≤ fixedSpace ρ C)
    (A : Subgroup J) (hA : IsElementaryTwo A)
    (hb : fixedCodim ρ A ≤ rank A) :
    ∃ m : NaturalSection ρ, alternatingGroup (Fin 6) ≤ m.actor.range := by
  let : C.Normal := hfit ▸ inferInstance
  obtain ⟨hC, hc⟩ := component_properties C hfit e
  let := hC
  obtain ⟨n, g, hn', hg⟩ := ChapterK.Alternating.SixDegreeReduction.actorGeneration C hfit e A hA
  have hd := fixedCodim_le_card_mul_of_subgroup_conjugates ρ C A g hg
  simp only [Fintype.card_fin] at hd
  have hsmall : fixedCodim ρ C < 8 := by
    have hh := Nat.mul_le_mul_left n hb
    omega
  obtain ⟨I, hI⟩ := exists_isIrrPlus_of_not_fixed ρ C hn
  have hs := invariant_of_small_central_quotient ρ C e hsmall I hI
  let S : Subrepresentation ρ := ⟨I, fun g v hv => (hs (mem_top g) v).2 hv⟩
  obtain ⟨m, _, hm⟩ := natural_section_of_invariant_irrPlus ρ C hfit hc e S hI A hA (by omega)
  exact ⟨m, hm⟩
omit [FiniteDimensional (ZMod 2) E] in
/-- Nontrivial action of a self-centralizing simple normal component is faithful. -/
theorem faithful_of_component_noncentral (ρ : Representation (ZMod 2) J E)
    (C : Subgroup J) (hfit : C = generalizedFitting J) (e : C ≃* Alternating)
    (hn : ¬ (⊤ : Submodule (ZMod 2) E) ≤ fixedSpace ρ C) :
    Function.Injective ρ := by
  let : C.Normal := hfit ▸ inferInstance
  obtain ⟨hC, hc⟩ := component_properties C hfit e
  let := hC
  have hcomp : IsComponent J C := ⟨(inferInstance : C.Normal).isSubnormal, inferInstance⟩
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases hcomp.normal_dichotomy ρ.ker with h | h
  · exact (hn (fun v _ c => LinearMap.congr_fun (h c.property) v)).elim
  · have hh := commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans h)
    exact bot_unique (hc ▸ hh)

/-- A common commutator line supplies a cyclic offender and hence a natural section. -/
theorem natural_section_of_commutator_line (ρ : Representation (ZMod 2) J E)
    (C : Subgroup J) (hfit : C = generalizedFitting J) (e : C ≃* Alternating)
    (hn : ¬ (⊤ : Submodule (ZMod 2) E) ≤ fixedSpace ρ C)
    (A : Subgroup J) (hA : IsElementaryTwo A)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) ≤ 1) :
    ∃ m : NaturalSection ρ, alternatingGroup (Fin 6) ≤ m.actor.range := by
  obtain ⟨a, ha, hne⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra! h
    exact hA.1 (eq_bot_iff.mpr h)
  let : IsElementaryAbelian 2 A := hA.2
  have ho : orderOf a = 2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a ha) hne
  obtain ⟨hB, hr, _, _⟩ := involution_actor_rank_and_fixedCodim ρ a ho
  have hc : fixedCodim ρ (zpowers a) ≤ rank (zpowers a) := by
    rw [hr, fixedCodim_zpowers_eq_displacement_rank]
    apply (Submodule.finrank_mono ?_).trans hd
    rintro _ ⟨v, rfl⟩
    exact Submodule.subset_span ⟨a, ha, v, Submodule.mem_top, rfl⟩
  exact natural_section_of_offender ρ C hfit e hn _ hB hc

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.Constituents
