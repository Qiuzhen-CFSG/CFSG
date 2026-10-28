module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Basic
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six
public import Theory.Representation.BinaryPermutationNaturalDuality
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.DualCommutator

/-!
# Common commutator lines in the two degree-six models

Self-duality of the natural section identifies its total commutator dimension
with fixed codimension. The checked degree-six elementary-subgroup tables then
show that a nontrivial elementary actor with a commutator line is conjugate to
a single transposition. The augmentation quotient transfers the same bound
from the five-dimensional cover.

Source: Aschbacher–Smith 13.8.26, printed p.962, and B.3.2–4, pp.83–85.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix
open BinaryPermutation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six

private theorem commutator_eq_coinvariants {G U : Type*} [Group G]
    [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) G U) (A : Subgroup G) :
    subspaceCommutator ρ ⊤ A = Representation.Coinvariants.ker (ρ.comp A.subtype) := by
  unfold subspaceCommutator Representation.Coinvariants.ker
  congr 1
  ext v
  constructor
  · rintro ⟨a, ha, u, _, rfl⟩
    exact ⟨(⟨a, ha⟩, u), rfl⟩
  · rintro ⟨⟨a, u⟩, rfl⟩
    exact ⟨a, a.property, u, Submodule.mem_top, rfl⟩

theorem natural_commutator_finrank (A : Subgroup Symmetric) :
    Module.finrank (ZMod 2) (subspaceCommutator symmetricAction ⊤ A) =
      fixedCodim symmetricAction A := by
  have he := fixedCodim_map_equivariant symmetricAction symmetricAction.dual
    (MonoidHom.id Symmetric) (naturalDualEquiv (Fin 6))
    (naturalDualEquiv_equivariant (Fin 6)) A
  simp only [Subgroup.map_id] at he
  rw [he, commutator_eq_coinvariants]
  exact (Representation.finrank_quotient_dual_invariants_eq_commutator (symmetricAction.comp A.subtype)).symm

/-- A nontrivial elementary actor fixing a hyperplane is a transposition group. -/
theorem natural_small_codim_conjugate {A : Subgroup Symmetric}
    (hA : IsElementaryTwo A) (h : fixedCodim symmetricAction A ≤ 1) :
    IsConjugateTo A (disjointTranspositions 6 1) := by
  have hc {B : Subgroup Symmetric} (he : IsConjugateTo A B) :
      fixedCodim symmetricAction B ≤ 1 := by
    obtain ⟨g, rfl⟩ := he
    simpa only [fixedCodim_map_conj] using h
  rcases elementaryTwo_conjugacy hA with he | he | he | he | he | he | he | he | he | he
  · exact he
  · have hh := hc he; rw [fixedCodim_A2.2.2.2] at hh; omega
  · have hh := hc he; rw [fixedCodim_D.2.2.2] at hh; omega
  · have hh := hc he; rw [fixedCodim_exceptional.2.2.2] at hh; omega
  · have hh := hc he; rw [fixedCodim_evenPart.2.2.2] at hh; omega
  · have hh := hc he; rw [fixedCodim_plus.2.2.2] at hh; omega
  · have hh := hc he; rw [fixedCodim_double.2.2.2] at hh; omega
  · have hh := hc he; rw [fixedCodim_triple.2.2.2] at hh; omega
  · have hh := hc he; rw [fixedCodim_klein.2.2.2] at hh; omega
  · have hh := hc he; rw [fixedCodim_twisted.2.2.2] at hh; omega

theorem rank_one_of_natural_commutator_le_one {A : Subgroup Symmetric}
    (hA : IsElementaryTwo A)
    (h : Module.finrank (ZMod 2) (subspaceCommutator symmetricAction ⊤ A) ≤ 1) :
    rank A = 1 := by
  rw [natural_commutator_finrank] at h
  exact (natural_small_codim_conjugate hA h).rank_eq.trans rank_A1

private theorem commutator_map_surjective {G U W : Type*} [Group G]
    [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G U) (σ : Representation (ZMod 2) G W)
    (q : U →ₗ[ZMod 2] W) (hq : Function.Surjective q)
    (he : ∀ g u, q (ρ g u) = σ g (q u)) (A : Subgroup G) :
    (subspaceCommutator ρ ⊤ A).map q = subspaceCommutator σ ⊤ A := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, u, _, rfl⟩
    change q (ρ a u - u) ∈ subspaceCommutator σ ⊤ A
    rw [map_sub, he]
    exact Submodule.subset_span ⟨a, ha, q u, Submodule.mem_top, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, w, _, rfl⟩
    obtain ⟨u, rfl⟩ := hq w
    exact ⟨ρ a u - u, Submodule.subset_span ⟨a, ha, u, Submodule.mem_top, rfl⟩,
      by rw [map_sub, he]⟩

theorem rank_one_of_core_commutator_le_one {A : Subgroup Symmetric}
    (hA : IsElementaryTwo A)
    (h : Module.finrank (ZMod 2)
      (subspaceCommutator (coreRepresentation (Fin 6)) ⊤ A) ≤ 1) : rank A = 1 := by
  apply rank_one_of_natural_commutator_le_one hA
  rw [← commutator_map_surjective (coreRepresentation (Fin 6)) symmetricAction
    (coreToNatural (Fin 6)) coreToNatural_surjective (coreToNatural_equivariant (Ω := Fin 6))]
  exact (Submodule.finrank_map_le _ _).trans h

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix
