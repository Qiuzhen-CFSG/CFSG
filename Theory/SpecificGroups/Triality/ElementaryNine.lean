module
public import Theory.SpecificGroups.Triality.ElementaryNine.Binary
public import Theory.SpecificGroups.Triality.ElementaryCentralKernel
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.ElementaryAbelian.Quotient
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# An elementary subgroup of order nine in genuine binary triality

For every characteristic-two standard parameter, two explicit words in the
signed central and folded arm roots generate an elementary abelian subgroup
of order nine. All root parameters are one, so the construction includes
`³D₄(2)` and works uniformly in every binary exponent.

The binary certificate retains the full Geck lattice. Scalar extension carries
its cube and commutation identities to the genuine elementary fixed points;
two matrix entries prove independence of the ternary exponents. The existing
`ElementaryCentralKernel.toCarrier_injective` then preserves this embedding
through the actual quotient by the elementary group's center. Its range is
the required subgroup, with its cardinality computed from the injective map.

Source: the root parametrizations and subsystem subgroups of GLS3 §§2.4–2.6,
especially Proposition 2.6.2 (`refs/KGroup/GLS3/chapter2.tex`). This supplies
the triality three-rank obstruction used with Aschbacher–Smith A.2.3–4
(printed p.33, PDF p.44) in the proof of 15.3.38 (printed p.1137,
PDF p.1154), `refs/quasithin.pdf`. The final theorem gives the exact witness
consumed by `TwistedRanks.rank_ne_one_of_triality_of_elementary_nine`.
-/

public section
noncomputable section
namespace Triality.Standard.ElementaryNine
open Parabolics Parabolics.RankOneMatrices
open ElementaryCentralKernel ElementaryCentralKernel.FixedRootCommutant
local instance : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b

/-- The four actual elementary fixed roots at parameter one. -/
def seed (P : Parameters) (hp : P.prime = 2) : Fin 4 → ElementaryGroup P :=
  ![centralElementary P true 1 (map_one _), centralElementary P false 1 (map_one _),
    foldedElementary P hp true 1, foldedElementary P hp false 1]

/-- The product of positive and negative arm elements. -/
def second (P : Parameters) (hp : P.prime = 2) : ElementaryGroup P :=
  Binary.secondWord (seed P hp)

/-- The corresponding central-root product conjugated to the highest-root subsystem. -/
def first (P : Parameters) (hp : P.prime = 2) : ElementaryGroup P :=
  Binary.firstWord (seed P hp)

/-- The genuine elementary group's faithful action on the full Geck lattice. -/
def elementaryMatrixHom (P : Parameters) :
    ElementaryGroup P →* Matrix (Fin 28) (Fin 28) (ExtensionField P) :=
  (coordinateHom P).comp (elementaryInclusion P)

theorem elementaryMatrixHom_injective (P : Parameters) :
    Function.Injective (elementaryMatrixHom P) := by
  intro x y h
  apply (elementarySubgroup P).subtype_injective
  apply (fixedSubgroup P).subtype_injective
  apply Subtype.ext
  apply Units.ext
  exact (Matrix.reindexRingEquiv (ExtensionField P) coordinates.symm).injective h

private theorem coordinateHom_simple (P : Parameters) (hp : P.prime = 2)
    (s : Bool) (i : Fin 4) (t : ExtensionField P) :
    coordinateHom P (simpleRoot P s i t) = rootMatrix i s t := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstance
  cases s
  · exact negativeMatrix_coordinates i t
  · exact positiveMatrix_coordinates i t

theorem matrix_seed (P : Parameters) (hp : P.prime = 2) (k : Fin 4) :
    elementaryMatrixHom P (seed P hp k) = constantMatrix k := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstance
  have hc (s : Bool) : elementaryMatrixHom P (centralElementary P s 1 (map_one _)) =
      constantMatrix (if s then 0 else 1) :=
    (coordinateHom_simple P hp s 1 1).trans (central_constant s)
  have ha (s : Bool) : elementaryMatrixHom P (foldedElementary P hp s 1) =
      constantMatrix (if s then 2 else 3) := by
    change coordinateHom P (foldedRoot P s 1) = _
    simp only [foldedRoot, map_mul, map_one, coordinateHom_simple P hp]
    exact folded_constant s
  fin_cases k
  · exact hc true
  · exact hc false
  · exact ha true
  · exact ha false

/-- Scalar extension of binary matrices into the actual cubic coefficient field. -/
def scalarMap (P : Parameters) (hp : P.prime = 2) :
    Matrix (Fin 28) (Fin 28) (ZMod 2) →+*
      Matrix (Fin 28) (Fin 28) (ExtensionField P) := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstance
  exact (ZMod.castHom (dvd_refl 2) (ExtensionField P)).mapMatrix

theorem scalarMap_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (scalarMap P hp) := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstance
  exact Matrix.map_injective (ZMod.castHom (dvd_refl 2) (ExtensionField P)).injective

private theorem scalarMap_constant (P : Parameters) (hp : P.prime = 2) (k : Fin 4) :
    scalarMap P hp (constantMatrix k) = constantMatrix k := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstance
  exact supportMatrix_map (ZMod.castHom (dvd_refl 2) (ExtensionField P)) (constantSupport k)

private theorem map_firstWord {G H : Type*} [Monoid G] [Monoid H]
    (φ : G →* H) (g : Fin 4 → G) :
    φ (Binary.firstWord g) = Binary.firstWord (fun i => φ (g i)) := by
  simp only [Binary.firstWord, map_mul]

private theorem map_secondWord {G H : Type*} [Monoid G] [Monoid H]
    (φ : G →* H) (g : Fin 4 → G) :
    φ (Binary.secondWord g) = Binary.secondWord (fun i => φ (g i)) := φ.map_mul _ _

theorem matrix_first (P : Parameters) (hp : P.prime = 2) :
    elementaryMatrixHom P (first P hp) = scalarMap P hp Binary.firstMatrix := by
  calc
    _ = Binary.firstWord (fun i => elementaryMatrixHom P (seed P hp i)) :=
      map_firstWord _ _
    _ = Binary.firstWord (fun i => scalarMap P hp (constantMatrix i)) :=
      congrArg Binary.firstWord (funext fun i =>
        (matrix_seed P hp i).trans (scalarMap_constant P hp i).symm)
    _ = scalarMap P hp (Binary.firstWord (constantMatrix (F := ZMod 2))) :=
      (map_firstWord (scalarMap P hp).toMonoidHom _).symm
    _ = _ := congrArg (scalarMap P hp) Binary.firstWord_matrix

theorem matrix_second (P : Parameters) (hp : P.prime = 2) :
    elementaryMatrixHom P (second P hp) = scalarMap P hp Binary.secondMatrix := by
  calc
    _ = Binary.secondWord (fun i => elementaryMatrixHom P (seed P hp i)) :=
      map_secondWord _ _
    _ = Binary.secondWord (fun i => scalarMap P hp (constantMatrix i)) :=
      congrArg Binary.secondWord (funext fun i =>
        (matrix_seed P hp i).trans (scalarMap_constant P hp i).symm)
    _ = scalarMap P hp (Binary.secondWord (constantMatrix (F := ZMod 2))) :=
      (map_secondWord (scalarMap P hp).toMonoidHom _).symm
    _ = _ := congrArg (scalarMap P hp) Binary.secondWord_matrix

theorem first_cube (P : Parameters) (hp : P.prime = 2) : first P hp ^ 3 = 1 := by
  apply elementaryMatrixHom_injective P
  calc
    _ = elementaryMatrixHom P (first P hp) ^ 3 := map_pow _ _ _
    _ = scalarMap P hp Binary.firstMatrix ^ 3 := congrArg (fun x => x ^ 3) (matrix_first P hp)
    _ = scalarMap P hp (Binary.firstMatrix ^ 3) := (map_pow _ _ _).symm
    _ = scalarMap P hp 1 := congrArg (scalarMap P hp) Binary.firstMatrix_cube
    _ = _ := (map_one _).trans (map_one _).symm

theorem second_cube (P : Parameters) (hp : P.prime = 2) : second P hp ^ 3 = 1 := by
  apply elementaryMatrixHom_injective P
  calc
    _ = elementaryMatrixHom P (second P hp) ^ 3 := map_pow _ _ _
    _ = scalarMap P hp Binary.secondMatrix ^ 3 := congrArg (fun x => x ^ 3) (matrix_second P hp)
    _ = scalarMap P hp (Binary.secondMatrix ^ 3) := (map_pow _ _ _).symm
    _ = scalarMap P hp 1 := congrArg (scalarMap P hp) Binary.secondMatrix_cube
    _ = _ := (map_one _).trans (map_one _).symm

theorem generators_commute (P : Parameters) (hp : P.prime = 2) :
    Commute (first P hp) (second P hp) := by
  apply elementaryMatrixHom_injective P
  simpa only [map_mul, matrix_first, matrix_second] using
    (Binary.matrices_commute.map (scalarMap P hp)).eq

theorem generators_independent (P : Parameters) (hp : P.prime = 2)
    (i j : Fin 3) (h : first P hp ^ i.val * second P hp ^ j.val = 1) :
    i = 0 ∧ j = 0 := by
  apply Binary.independent i j
  apply scalarMap_injective P hp
  have h' := congrArg (elementaryMatrixHom P) h
  change scalarMap P hp (Binary.firstMatrix ^ i.val * Binary.secondMatrix ^ j.val) =
    scalarMap P hp 1
  simpa only [map_mul, map_pow, map_one, matrix_first, matrix_second] using h'

private def cyclicHom {G : Type*} [Group G] (g : G) (hg : g ^ 3 = 1) :
    Multiplicative (ZMod 3) →* G where
  toFun v := g ^ v.toAdd.val
  map_one' := by simp
  map_mul' u v := by
    change g ^ (u.toAdd + v.toAdd).val = g ^ u.toAdd.val * g ^ v.toAdd.val
    rw [ZMod.val_add, ← pow_eq_pow_mod _ hg, pow_add]

/-- Two ternary coordinates for the constructed subgroup. -/
abbrev Coordinates := Multiplicative (ZMod 3) × Multiplicative (ZMod 3)

/-- The explicit homomorphism into the elementary fixed points. -/
def elementaryEmbedding (P : Parameters) (hp : P.prime = 2) :
    Coordinates →* ElementaryGroup P :=
  (cyclicHom (first P hp) (first_cube P hp)).noncommCoprod
    (cyclicHom (second P hp) (second_cube P hp))
    (fun u v => (generators_commute P hp).pow_pow u.toAdd.val v.toAdd.val)

theorem elementaryEmbedding_apply (P : Parameters) (hp : P.prime = 2) (v : Coordinates) :
    elementaryEmbedding P hp v = first P hp ^ v.1.toAdd.val * second P hp ^ v.2.toAdd.val := by rfl

theorem elementaryEmbedding_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (elementaryEmbedding P hp) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro v hv
  have h := generators_independent P hp
    ⟨v.1.toAdd.val, ZMod.val_lt _⟩ ⟨v.2.toAdd.val, ZMod.val_lt _⟩ hv
  have h₁ : v.1.toAdd = 0 := ZMod.val_injective 3 (congrArg Fin.val h.1)
  have h₂ : v.2.toAdd = 0 := ZMod.val_injective 3 (congrArg Fin.val h.2)
  exact Prod.ext (congrArg Multiplicative.ofAdd h₁) (congrArg Multiplicative.ofAdd h₂)

/-- The same embedding in the genuine central quotient. -/
def embedding (P : Parameters) (hp : P.prime = 2) : Coordinates →* Carrier P :=
  (toCarrier P).comp (elementaryEmbedding P hp)

theorem embedding_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (embedding P hp) :=
  (toCarrier_injective P hp).comp (elementaryEmbedding_injective P hp)

instance coordinates_elementary : IsElementaryAbelian 3 Coordinates where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide +kernel)

/-- The subgroup generated by the two certified root words. -/
def subgroup (P : Parameters) (hp : P.prime = 2) : Subgroup (Carrier P) :=
  (embedding P hp).range

instance subgroup_elementary (P : Parameters) (hp : P.prime = 2) :
    IsElementaryAbelian 3 (subgroup P hp) :=
  IsElementaryAbelian.of_surjective (embedding P hp).rangeRestrict
    (embedding P hp).rangeRestrict_surjective

theorem card_subgroup (P : Parameters) (hp : P.prime = 2) : Nat.card (subgroup P hp) = 9 := by
  change Nat.card (embedding P hp).range = 9
  rw [← Nat.card_congr (MonoidHom.ofInjective (embedding_injective P hp)).toEquiv]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

end Triality.Standard.ElementaryNine

namespace Triality.Standard

/-- Every genuine binary triality group contains an elementary abelian subgroup
of order nine, including the smallest exponent. -/
theorem exists_elementaryAbelian_three_card_nine (f : ℕ) (hf : 0 < f) :
    ∃ E : Subgroup (BinaryCarrier f hf), IsElementaryAbelian 3 E ∧ Nat.card E = 9 :=
  ⟨ElementaryNine.subgroup (binaryParameters f hf) rfl,
    ElementaryNine.subgroup_elementary (binaryParameters f hf) rfl,
    ElementaryNine.card_subgroup (binaryParameters f hf) rfl⟩

end Triality.Standard
