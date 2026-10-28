module

public import CFSG.Quasithin.ChapterG.Section09.Setup
public import CFSG.Quasithin.ChapterG.Section09.TensorBounds
public import Theory.Representation.FirstCohomologyLinearTransport
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The common-field tensor construction required in G.9.3

`TensorData` is the output contract for the construction on printed p.356.
It retains irreducible binary constituents, their embeddings into the
original module, and the scalar description of their full binary
endomorphism rings. The tensor equivalence is over this common field and
intertwines both component actions. No existence assertion is assumed or
proved by defining this structure.

The subsequent reductions use the actual tensor equivalence. In particular,
the smaller-degree induction is invoked only after proving strict decrease,
and the terminal numerical bounds retain the original actor rank.

Source: Aschbacher--Smith, combined manuscript, G.9.3, printed pp.354,356.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents

universe u v

variable {G : Type u} [Group G] {V : Type v}
  [AddCommGroup V] [Module (ZMod 2) V]

/-- Output of the common Schur-field construction, not an additional source
hypothesis. All three spaces retain their compatible binary scalar actions. -/
structure TensorData (ρ : Representation (ZMod 2) G V) (L L₂ : Subgroup G) where
  F : Type v
  [field : Field F]
  [binaryAlgebra : Algebra (ZMod 2) F]
  [finiteField : FiniteDimensional (ZMod 2) F]
  I : Type v
  J : Type v
  [addI : AddCommGroup I]
  [addJ : AddCommGroup J]
  [moduleI : Module F I]
  [moduleJ : Module F J]
  [binaryI : Module (ZMod 2) I]
  [binaryJ : Module (ZMod 2) J]
  [towerI : IsScalarTower (ZMod 2) F I]
  [towerJ : IsScalarTower (ZMod 2) F J]
  [finiteI : FiniteDimensional F I]
  [finiteJ : FiniteDimensional F J]
  [moduleV : Module F V]
  [towerV : IsScalarTower (ZMod 2) F V]
  left : Representation F L I
  right : Representation F L₂ J
  left_irreducible : Representation.IsIrreducible (Representation.restrictScalars (k := ZMod 2) left)
  right_irreducible : Representation.IsIrreducible (Representation.restrictScalars (k := ZMod 2) right)
  left_faithful : Function.Injective left
  right_faithful : Function.Injective right
  left_embedding : I →ₗ[ZMod 2] V
  right_embedding : J →ₗ[ZMod 2] V
  left_embedding_injective : Function.Injective left_embedding
  right_embedding_injective : Function.Injective right_embedding
  left_embedding_equivariant : ∀ l x, left_embedding (left l x) = ρ l (left_embedding x)
  right_embedding_equivariant : ∀ l x, right_embedding (right l x) = ρ l (right_embedding x)
  left_schur : ∀ f : Representation.IntertwiningMap
    (Representation.restrictScalars (k := ZMod 2) left) (Representation.restrictScalars left),
      ∃ c : F, ∀ x, f x = c • x
  right_schur : ∀ f : Representation.IntertwiningMap
    (Representation.restrictScalars (k := ZMod 2) right) (Representation.restrictScalars right),
      ∃ c : F, ∀ x, f x = c • x
  tensor : V ≃ₗ[F] I ⊗[F] J
  equal_dimension : Module.finrank F J = Module.finrank F I
  left_tensor : ∀ (l : L) v, tensor (ρ l v) = TensorProduct.map (left l) 1 (tensor v)
  right_tensor : ∀ (l : L₂) v, tensor (ρ l v) = TensorProduct.map 1 (right l) (tensor v)

attribute [instance] TensorData.field TensorData.binaryAlgebra TensorData.finiteField
  TensorData.addI TensorData.addJ TensorData.moduleI TensorData.moduleJ
  TensorData.binaryI TensorData.binaryJ TensorData.towerI TensorData.towerJ
  TensorData.finiteI TensorData.finiteJ TensorData.moduleV TensorData.towerV

namespace TensorData

variable {ρ : Representation (ZMod 2) G V} {L L₂ : Subgroup G}
  (T : TensorData ρ L L₂)

instance finiteBinaryI : FiniteDimensional (ZMod 2) T.I :=
  Module.Finite.trans T.F T.I

instance finiteBinaryJ : FiniteDimensional (ZMod 2) T.J :=
  Module.Finite.trans T.F T.J

/-- Degree of the actual common binary endomorphism field. -/
abbrev n : ℕ := Module.finrank (ZMod 2) T.F

/-- Dimension of either tensor factor over its endomorphism field. -/
abbrev k : ℕ := Module.finrank T.F T.I

theorem n_pos : 0 < T.n := Module.finrank_pos

/-- The common endomorphism field has the source's exact cardinality. -/
theorem field_card : Nat.card T.F = 2 ^ T.n := by
  let : Finite T.F := Module.finite_iff_finite.mp T.finiteField
  exact (FiniteField.pow_finrank_eq_natCard 2 T.F).symm

/-- An actual binary algebra isomorphism identifies the common field with
the standard finite field, rather than only attaching a field-size label. -/
def fieldEquiv : T.F ≃ₐ[ZMod 2] GaloisField 2 T.n :=
  GaloisField.algEquivGaloisField 2 T.n T.field_card

/-- A faithful constituent of a component cannot have field dimension zero
or one: the latter would make its nontrivial perfect actor commutative. -/
theorem two_le_factor_dimension (hL : Theory.GroupTheory.IsComponent G L) :
    2 ≤ T.k := by
  let : Theory.GroupTheory.IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ Subgroup.center L) := Theory.GroupTheory.IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (Subgroup.center L)).nontrivial
  let σ : Representation (ZMod 2) L T.I := Representation.restrictScalars T.left
  let : Representation.IsIrreducible σ := T.left_irreducible
  let : Nontrivial σ.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra (ZMod 2) L) σ.asModule
  let : Nontrivial T.I := σ.asModuleEquiv.injective.nontrivial
  have hk : 0 < T.k := Module.finrank_pos
  by_contra h
  have hdim : Module.finrank T.F T.I = 1 := by change T.k = 1; omega
  apply Group.IsPerfect.not_isMulCommutative L
  refine ⟨⟨fun a b => T.left_faithful ?_⟩⟩
  obtain ⟨c, hc, _⟩ := (T.left a).existsUnique_eq_smul_id_of_finrank_eq_one hdim
  obtain ⟨d, hd, _⟩ := (T.left b).existsUnique_eq_smul_id_of_finrank_eq_one hdim
  ext x
  simp only [map_mul, Module.End.mul_apply, hc, hd, LinearMap.smul_apply,
    LinearMap.id_apply]
  exact smul_comm c d x

/-- The tensor construction, rather than a numerical certificate, gives `d=nk²`. -/
theorem degree_eq : Module.finrank (ZMod 2) V = T.n * T.k ^ 2 :=
  TensorBounds.finrank_eq_square T.tensor T.equal_dimension

/-- Binary degree of the actual left constituent. -/
theorem factor_degree_eq : Module.finrank (ZMod 2) T.I = T.n * T.k :=
  (Module.finrank_mul_finrank (ZMod 2) T.F T.I).symm

/-- A factor of field dimension at least four forces component rank at
least four once the original actor's rank bound has been established. -/
theorem large_factor_rank {m r : ℕ} (hk : 4 ≤ T.k) (hm : m ≤ 2 * r)
    (hd : Module.finrank (ZMod 2) V ≤ 2 * (m + 1)) :
    16 ≤ Module.finrank (ZMod 2) V ∧ 4 ≤ r := by
  have hn := T.n_pos
  have hsq : 16 ≤ T.k ^ 2 := by nlinarith
  have hmul := Nat.mul_le_mul_right (T.k ^ 2) hn
  have hdegree : 16 ≤ Module.finrank (ZMod 2) V := by
    rw [T.degree_eq]
    nlinarith
  exact ⟨hdegree, by omega⟩

/-- The actual left constituent satisfies G.9.1 for a rank-`r` actor and
has strictly smaller degree. This is the input to degree induction, not an
assumption that the classification holds at the original degree. -/
theorem factor_setup_and_degree_lt [Finite G] {r m : ℕ}
    (B : Subgroup L) (hB : IsElementaryAbelian 2 B) (hcard : Nat.card B = 2 ^ r)
    (hm : m ≤ 2 * r) (hn : T.n ≤ r) (hk : 2 ≤ T.k)
    (hd : Module.finrank (ZMod 2) V ≤ 2 * (m + 1)) :
    Setup (Representation.restrictScalars T.left) B r ∧
      Module.finrank (ZMod 2) T.I < Module.finrank (ZMod 2) V := by
  refine ⟨⟨?_, hB, hcard,
    TensorBounds.factor_small_degree T.tensor T.equal_dimension hm hn hd⟩,
    TensorBounds.factor_degree_lt T.tensor T.equal_dimension hk⟩
  intro a b hab
  apply T.left_faithful
  ext x
  exact congrArg (fun f : Module.End (ZMod 2) T.I => f x) hab

/-- The degree-four orthogonal factor left by the smaller-degree
classification contradicts the original small-degree hypothesis. -/
theorem exclude_orthogonal_factor {m r : ℕ}
    (hm : m ≤ 2 * r) (hr : r = 2 * T.n) (hk : T.k = 4)
    (hd : Module.finrank (ZMod 2) V ≤ 2 * (m + 1)) : False := by
  have hpos := T.n_pos
  rw [T.degree_eq, hk] at hd
  rw [hr] at hm
  norm_num at hd
  omega

/-- In the two-dimensional branch the source lower bound uses the original
`m`, irrespective of a maximal-rank subgroup used elsewhere in the proof. -/
theorem dimension_two_bounds {m : ℕ} (hk : T.k = 2)
    (hd : Module.finrank (ZMod 2) V ≤ 2 * (m + 1)) :
    Module.finrank (ZMod 2) V = 4 * T.n ∧ 2 * T.n - 1 ≤ m := by
  have he : Module.finrank (ZMod 2) V = 4 * T.n := by
    rw [T.degree_eq, hk]
    ring
  constructor
  · exact he
  · rw [he] at hd
    omega

/-- Once the three-dimensional classification gives the binary field and
the ambient rank bound, the original actor has rank exactly four. -/
theorem dimension_three_bounds {m : ℕ} (hk : T.k = 3) (hn : T.n = 1)
    (hm : m ≤ 4) (hd : Module.finrank (ZMod 2) V ≤ 2 * (m + 1)) :
    Module.finrank (ZMod 2) V = 9 ∧ m = 4 := by
  have he : Module.finrank (ZMod 2) V = 9 := by
    rw [T.degree_eq, hk, hn]
    norm_num
  exact ⟨he, by omega⟩

end TensorData
end CFSG.Quasithin.ChapterG.Section09.TwoComponents
