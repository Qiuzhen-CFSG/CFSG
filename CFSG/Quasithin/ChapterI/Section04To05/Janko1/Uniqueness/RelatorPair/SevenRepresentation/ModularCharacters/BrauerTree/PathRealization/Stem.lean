module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.LocalEleven
public import Theory.Representation.CyclicRootBrauerCharacter

/-!
# An unordered real stem for the principal eleven-block

This contract separates the cyclic-block theorem from the source-specific
ordering calculation. It asks for actual simple modules, all eleven ordinary
rows of nonzero eleven-defect, and decomposition identities for genuine lifted
eigenvalue sums. It prescribes neither the edge dimensions nor the order of the
ordinary rows after the trivial endpoint. There is no existence instance.

The root order `15960 = 175560 / 11` contains every eleven-regular element
order of the source group. Its chosen modular root lies in the literal
`ElevenClosure`. Feit's Chapter VII, Corollary 6.8 and Theorem 9.2, supplies the
source route to such a stem; proving that route and the Janko ordering remains
necessary. The final dimension assembly is in `PathRealization.lean`.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree

/-- Vertex sums of the ten edges of a line. This is valid for dimensions as
well as for lifted characters. -/
@[expose] public def lineIncidence {A : Type*} [Add A] (v : Fin 10 → A) : Fin 11 → A :=
  ![v 0, v 0 + v 1, v 1 + v 2, v 2 + v 3, v 3 + v 4,
    v 4 + v 5, v 5 + v 6, v 6 + v 7, v 7 + v 8, v 8 + v 9, v 9]

/-- Ordinary dimensions along the specified principal-block path. The
ordering calculation proves this sequence, without fixing equal-degree rows. -/
@[expose] public def orderedVertexDegree : Fin 11 → ℕ :=
  ![1, 120, 133, 120, 133, 76, 56, 76, 133, 120, 56]

/-- The precise missing real-stem output, before identifying its row ordering. -/
public structure RealStem (G : Type*) [Group G] [Finite G] (d : OrdinaryData G) where
  row : Fin 11 → Fin 15
  row_injective : Function.Injective row
  row_nonzero_defect : ∀ i, ¬ 11 ∣ ordinaryDegree (row i)
  first_row : row 0 = 0
  degree : Fin 10 → ℕ
  rep : ∀ i, Representation ElevenClosure G (Fin (degree i) → ElevenClosure)
  irreducible : ∀ i, Representation.IsIrreducible (rep i)
  inequivalent : Pairwise fun i j => IsEmpty ((rep i).Equiv (rep j))
  roots : Representation.CyclicRootLift ElevenClosure 15960
  decomposition : ∀ (g : G), ¬ 11 ∣ orderOf g → ∀ i,
    d.chi (row i) (ConjClasses.mk g) =
      lineIncidence (fun j => roots.value (rep j) g) i

/-- Pair the product of two lifted simple characters with the prospective
projective character at an edge. The weights are the reciprocal orders of
the actual class centralizers, as specified by `OrdinaryData.centralizers`.
Column nine is the unique eleven-singular class and is omitted. -/
@[expose] public noncomputable def RealStem.tensorCoefficient
    {G : Type*} [Group G] [Finite G] {d : OrdinaryData G}
    (s : RealStem G d) (i j k : Fin 10) : ℂ :=
  ∑ c ∈ (Finset.univ.erase (9 : Fin 15)),
    s.roots.value (s.rep i) (d.representatives c) *
      s.roots.value (s.rep j) (d.representatives c) *
        star (d.chi (s.row k.castSucc) (d.classes c) +
          d.chi (s.row k.succ) (d.classes c)) / (centralizerOrder c : ℂ)

/-- The tensor-product consequence of projective/Brauer reciprocity needed
to determine the source path. This is a separate, unproved output obligation
of the cyclic-block construction, not part of an existence instance. -/
@[expose] public def RealStem.TensorPositive
    {G : Type*} [Group G] [Finite G] {d : OrdinaryData G}
    (s : RealStem G d) : Prop :=
  ∀ i j k, ∃ multiplicity : ℕ, s.tensorCoefficient i j k = (multiplicity : ℂ)

/-- Every regular element has order in the chosen root group. -/
public theorem regular_order_dvd_root_order {G : Type*} [Group G] [Finite G]
    (horder : Nat.card G = 175560) (g : G) (hg : ¬ 11 ∣ orderOf g) :
    orderOf g ∣ 15960 := by
  have hd := orderOf_dvd_natCard g
  rw [horder, show 175560 = 11 * 15960 from rfl] at hd
  exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 11)).mpr hg)).dvd_of_dvd_mul_left hd

/-- Evaluating a genuine lifted decomposition at one gives equalities of
natural dimensions, rather than residues modulo eleven. -/
public theorem RealStem.degree_incidence {G : Type*} [Group G] [Finite G]
    {d : OrdinaryData G} (s : RealStem G d) (i : Fin 11) :
    lineIncidence s.degree i = ordinaryDegree (s.row i) := by
  have h := s.decomposition 1 (by simp) i
  rw [d.degree_value] at h
  simp only [Representation.CyclicRootLift.value_one, Module.finrank_pi,
    Fintype.card_fin] at h
  have hc : lineIncidence (fun j => (s.degree j : ℂ)) i =
      ((lineIncidence (A := ℕ) s.degree i : ℕ) : ℂ) := by
    fin_cases i <;> simp [lineIncidence]
  rw [hc] at h
  exact_mod_cast h.symm

/-- A simple edge module has positive natural dimension. -/
public theorem RealStem.degree_pos {G : Type*} [Group G] [Finite G]
    {d : OrdinaryData G} (s : RealStem G d) (i : Fin 10) : 0 < s.degree i := by
  let : Representation.IsIrreducible (s.rep i) := s.irreducible i
  let : Nontrivial (s.rep i).asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra ElevenClosure G) (s.rep i).asModule
  let : Nontrivial (Fin (s.degree i) → ElevenClosure) :=
    Function.Injective.nontrivial (s.rep i).asModuleEquiv.injective
  simpa using (Module.finrank_pos (R := ElevenClosure)
    (M := Fin (s.degree i) → ElevenClosure))

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree
