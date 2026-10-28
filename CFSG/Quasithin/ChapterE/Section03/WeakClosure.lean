module

public import CFSG.Quasithin.ChapterE.Defs
public import Theory.GroupTheory.ConjugacyFamilySpan
public import Theory.ElementaryAbelian.BinaryQuotientRank

/-!
# The weak-closure subgroups of E.3

These are the actual conjugate-subgroup constructions in Definition E.3.13.
Codimension `i` is expressed by the relative index `2 ^ i`; for an elementary
abelian 2-group this is precisely the source's quotient rank. The construction
is defined for every natural `i`, with the source using `i < m(V)`.

The weak-closure and normalizer properties follow from the general theorem
for conjugacy-invariant families. Sylow conjugacy in `H`, not in the whole
group, proves equality in any containing 2-subgroup of `H`.

Public-name migration: the E.1.5 family construction retains `weakClosure`
and its containment lemma `weakClosure_le`. The E.3.13 construction formerly
also used those names; it is now `indexedWeakClosure`, with containment lemma
`indexedWeakClosure_le`. All other E.3 public names are retained. The identity
`indexedWeakClosure_eq_weakClosure` identifies the indexed construction with
the E.1.5 closure of the conjugate-corank family.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Definition
E.3.13, Remark E.3.14 and Lemma E.3.15, printed p. 233.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE

open Subgroup
open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- All corank-`i` subgroups of ambient conjugates of `V`. -/
def conjugateCorankFamily (V : Subgroup G) (i : ℕ) : Set (Subgroup G) :=
  {A | ∃ g : G, A ≤ V.map (MulAut.conj g).toMonoidHom ∧
    A.relIndex (V.map (MulAut.conj g).toMonoidHom) = 2 ^ i}

/-- The family `Γᵢ(X,V)` in E.3.13. -/
def gamma (V X : Subgroup G) (i : ℕ) : Set (Subgroup G) :=
  {A | A ∈ conjugateCorankFamily V i ∧ A ≤ X}

/-- The subgroup `Wᵢ(X,V)` in E.3.13. -/
def indexedWeakClosure (V X : Subgroup G) (i : ℕ) : Subgroup G :=
  SubgroupFamily.span (conjugateCorankFamily V i) X

/-- E.3.13 specializes the family closure of E.1.5 to conjugate-corank subgroups. -/
theorem indexedWeakClosure_eq_weakClosure (V X : Subgroup G) (i : ℕ) :
    indexedWeakClosure V X i = weakClosure X (conjugateCorankFamily V i) := rfl

/-- The relative centralizer `Cᵢ(X,V) = C_X(Wᵢ(X,V))`. -/
def weakCentralizer (V X : Subgroup G) (i : ℕ) : Subgroup G :=
  X ⊓ centralizer (indexedWeakClosure V X i : Set G)

theorem weakClosure_eq_sSup_gamma (V X : Subgroup G) (i : ℕ) :
    indexedWeakClosure V X i = sSup (gamma V X i) := rfl

theorem conjugateCorankFamily_invariant (V : Subgroup G) (i : ℕ) :
    SubgroupFamily.ConjugationInvariant (conjugateCorankFamily V i) := by
  intro A ⟨g, hAV, hi⟩ h
  have hcomp : (MulAut.conj h).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (h * g)).toMonoidHom := by
    ext x
    simp [mul_assoc]
  have hV : (V.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      V.map (MulAut.conj (h * g)).toMonoidHom := by
    rw [Subgroup.map_map, hcomp]
  refine ⟨h * g, ?_, ?_⟩
  · rw [← hV]
    exact Subgroup.map_mono hAV
  · rw [← hV, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj h).injective]
    exact hi

theorem indexedWeakClosure_le (V X : Subgroup G) (i : ℕ) : indexedWeakClosure V X i ≤ X :=
  SubgroupFamily.span_le _ _

theorem gamma_le_weakClosure {V X A : Subgroup G} {i : ℕ}
    (hA : A ∈ gamma V X i) : A ≤ indexedWeakClosure V X i :=
  SubgroupFamily.le_span hA.1 hA.2

theorem weakClosure_mono (V : Subgroup G) (i : ℕ) :
    Monotone (fun X => indexedWeakClosure V X i) := SubgroupFamily.span_mono _

/-- At corank zero the generators are exactly the whole conjugates of `V`. -/
theorem mem_gamma_zero_iff (V X A : Subgroup G) :
    A ∈ gamma V X 0 ↔
      ∃ g : G, A = V.map (MulAut.conj g).toMonoidHom ∧ A ≤ X := by
  constructor
  · rintro ⟨⟨g, hAV, hi⟩, hAX⟩
    refine ⟨g, le_antisymm hAV ?_, hAX⟩
    exact Subgroup.relIndex_eq_one.mp (by simpa using hi)
  · rintro ⟨g, rfl, hVX⟩
    exact ⟨⟨g, le_rfl, by simp⟩, hVX⟩

/-- The quotient-dimension form of a generator, using the original `V`. -/
theorem mem_gamma_of_quotient_finrank [Finite G] {V X A : Subgroup G}
    [IsElementaryAbelian 2 V] {i : ℕ} (hAV : A ≤ V) (hAX : A ≤ X)
    (hi : Module.finrank (ZMod 2) (Additive (V ⧸ A.subgroupOf V)) = i) :
    A ∈ gamma V X i := by
  have hconj : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  refine ⟨⟨1, ?_, ?_⟩, hAX⟩
  · simpa only [hconj, Subgroup.map_id] using hAV
  · simpa only [hconj, Subgroup.map_id] using
      (Subgroup.relIndex_eq_two_pow_iff_quotient_finrank V A i).mpr hi

/-- The whole module is a generator of the zeroth weak closure whenever it lies in `X`. -/
theorem self_le_weakClosure_zero {V X : Subgroup G} (hVX : V ≤ X) :
    V ≤ indexedWeakClosure V X 0 := by
  have hconj : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  apply gamma_le_weakClosure
  apply (mem_gamma_zero_iff V X V).mpr
  exact ⟨1, by rw [hconj, Subgroup.map_id], hVX⟩

/-- E.3.14: the subgroup generated by the family is weakly closed. -/
theorem weakClosure_weakly_closed [Finite G] (V X : Subgroup G) (i : ℕ) (g : G)
    (h : (indexedWeakClosure V X i).map (MulAut.conj g).toMonoidHom ≤ X) :
    (indexedWeakClosure V X i).map (MulAut.conj g).toMonoidHom = indexedWeakClosure V X i :=
  SubgroupFamily.span_weakly_closed (conjugateCorankFamily_invariant V i) X g h

/-- E.3.14: ambient normalizers of `X` normalize `Wᵢ(X,V)`. -/
theorem normalizer_le_weakClosure_normalizer [Finite G]
    (V X : Subgroup G) (i : ℕ) :
    normalizer (X : Set G) ≤ normalizer (indexedWeakClosure V X i : Set G) :=
  SubgroupFamily.normalizer_le_span_normalizer (conjugateCorankFamily_invariant V i) X

/-- E.3.14: ambient normalizers of `X` also normalize `Cᵢ(X,V)`. -/
theorem normalizer_le_weakCentralizer_normalizer [Finite G]
    (V X : Subgroup G) (i : ℕ) :
    normalizer (X : Set G) ≤ normalizer (weakCentralizer V X i : Set G) := by
  have hN : normalizer (indexedWeakClosure V X i : Set G) ≤
      normalizer (centralizer (indexedWeakClosure V X i : Set G) : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf (Subgroup.centralizer_le_normalizer _)
  exact (le_inf le_rfl ((normalizer_le_weakClosure_normalizer V X i).trans hN)).trans
    Subgroup.inf_normalizer_le_normalizer_inf

/-- E.3.15, retaining the source's relative Sylow hypothesis `S ∈ Syl₂(H)`. -/
theorem weakClosure_eq_in_two_overgroup [Finite G]
    (V H : Subgroup G) (S : Sylow 2 H) (Y : Subgroup G) (i : ℕ)
    (hY : IsPGroup 2 Y) (hYH : Y ≤ H)
    (hWY : indexedWeakClosure V ((S : Subgroup H).map H.subtype) i ≤ Y) :
    indexedWeakClosure V ((S : Subgroup H).map H.subtype) i = indexedWeakClosure V Y i :=
  SubgroupFamily.span_eq_in_relative_p_overgroup
    (conjugateCorankFamily_invariant V i) H S Y hY hYH hWY

/-- The final normalizer assertion of E.3.15. -/
theorem normalizer_le_weakClosure_normalizer_of_two_overgroup [Finite G]
    (V H : Subgroup G) (S : Sylow 2 H) (Y : Subgroup G) (i : ℕ)
    (hY : IsPGroup 2 Y) (hYH : Y ≤ H)
    (hWY : indexedWeakClosure V ((S : Subgroup H).map H.subtype) i ≤ Y) :
    normalizer (Y : Set G) ≤
      normalizer (indexedWeakClosure V ((S : Subgroup H).map H.subtype) i : Set G) := by
  rw [weakClosure_eq_in_two_overgroup V H S Y i hY hYH hWY]
  exact normalizer_le_weakClosure_normalizer V Y i

end CFSG.Quasithin.ChapterE
