module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ReorientedConfiguration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearEnlargement

/-!
# Actual linear quotient markings from the original source models

The source quotient field is attached to the original `L i`, while the
Chapter 9 actors are the intrinsic graph local groups.  In a linear source
row the starred-parabolic construction and its representative formula give a
literal quotient marking at the corresponding graph base vertex.  Conjugating
that base vertex then transports the marking to every vertex in its orbit.

This module records that transport without identifying any nonlinear source
row.  It is the narrow interface used by the Chapter 9 consumers once their
model case has been reduced to the linear alternatives.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- A linear original row gives the actual quotient marking at its graph base. -/
theorem reduced_base_linear_marking (h : HypothesisF11 L S) (i : Bool)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (family L i ⧸ pCore 2 (family L i)) ≃* PSL(2, F)) :
    Nonempty ((graphLocalGroup (Reduction.reducedFamily L S) (base
      (Reduction.reducedFamily L S) i) ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) (base
        (Reduction.reducedFamily L S) i))) ≃* SL(2, F)) := by
  let e₁ := Reduction.reduced_graphLinearQuotient h i e
  let π : SL(2, F) ≃* PSL(2, F) :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi F)
      ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩
  exact ⟨e₁.trans π.symm⟩

/-- Extracting a concrete linear model gives the marking and its field data. -/
theorem reduced_base_linear_marking_of_model (h : HypothesisF11 L S) (i : Bool)
    {n : ℕ}
    (hm : ClassicalGroup.IsPSL (family L i ⧸ pCore 2 (family L i)) 2 (2 ^ n)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      0 < n ∧ Nat.card F = 2 ^ n ∧
      Nonempty ((graphLocalGroup (Reduction.reducedFamily L S) (base
        (Reduction.reducedFamily L S) i) ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) (base
          (Reduction.reducedFamily L S) i))) ≃* SL(2, F)) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hpos : 1 < Nat.card F := Finite.one_lt_card
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    rw [hcard] at hpos
    norm_num at hpos
  exact ⟨F, hF, hfin, inferInstance, hn, hcard,
    reduced_base_linear_marking h i e⟩

/-- Transport the preceding base marking to an arbitrary vertex of the same orbit. -/
theorem reduced_vertex_linear_marking (h : HypothesisF11 L S)
    (v : Vertex (Reduction.reducedFamily L S))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (family L v.type ⧸ pCore 2 (family L v.type)) ≃* PSL(2, F)) :
    Nonempty ((graphLocalGroup (Reduction.reducedFamily L S) v ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) v)) ≃* SL(2, F)) := by
  let F₀ := Reduction.reducedFamily L S
  obtain ⟨e₀⟩ := reduced_base_linear_marking h v.type e
  obtain ⟨g, hg⟩ := Subgroup.CosetGeometry.exists_smul_base F₀ v
  obtain ⟨_, f, _, _, _⟩ := local_quotient_parameter_transport
    (Reduction.reduced_triple h) g hg
  exact ⟨f.symm.trans e₀⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
