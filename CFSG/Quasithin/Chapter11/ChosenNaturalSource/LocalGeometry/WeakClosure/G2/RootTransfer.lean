module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
public import CFSG.Quasithin.ChapterE.Section03.Parameters

/-!
# Root-centralizer transfer in the G₂ weak-closure argument

For a conjugate A of the original V, the inequality 2n < r(G,V) makes
each root centralizer C_V(D), with m(A/D)=2n, normalize A. Their span
therefore normalizes A, and its commutator with A lies in A. This is the
group-theoretic step which puts the three-space in both original modules.

We also give the precise reconstruction step from a common family of
planes. The residuals are the actual N_L(I)^infinity, and uniqueness means
uniqueness among the noncentral C-components of N_G(I), as in 11.1.3.
The root calculations and generation of L by these residuals are separate
model obligations, not consequences of these transfer lemmas.

Source: Aschbacher--Smith, 11.2.2(5), printed p.768, using B.4.6(3).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2
open ChapterE
variable {G : Type*} [Group G]

/-- The source E, formed from the literal relative centralizers in V. -/
def rootCentralizerSpan (V : Subgroup G) (roots : Set (Subgroup G)) : Subgroup G :=
  ⨆ D ∈ roots, V ⊓ centralizer (D : Set G)

/-- The root calculation needed by the transfer. Its construction must specify
the actual root preimages; no normalization or weak-closure bound is a field. -/
structure RootSpan (V A U : Subgroup G) (n : ℕ) where
  roots : Set (Subgroup G)
  le_actor : ∀ D ∈ roots, D ≤ A
  corank : ∀ D ∈ roots, subgroupCorank A D = 2 * n
  moved : ⁅rootCentralizerSpan V roots, A⁆ = U

/-- The strict source r-bound is used on A=V^g, not on an unrelated quotient. -/
theorem rootCentralizerSpan_normalizes {V : Subgroup G} [IsElementaryAbelian 2 V]
    (g : G) {U : Subgroup G} {n : ℕ}
    (h : RootSpan V (V.map (MulAut.conj g).toMonoidHom) U n)
    (hr : (2 * n : ℕ∞) < globalR V) :
    rootCentralizerSpan V h.roots ≤
      normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  apply iSup_le
  intro D
  apply iSup_le
  intro hD
  apply inf_le_right.trans
  apply centralizer_le_normalizer_of_corank_lt_globalR (h.le_actor D hD)
  rw [h.corank D hD, globalR_map_equiv]
  exact_mod_cast hr

/-- The three-space obtained as [E,A] belongs to the original conjugate A. -/
theorem RootSpan.le_conjugate {V : Subgroup G} [IsElementaryAbelian 2 V]
    {g : G} {U : Subgroup G} {n : ℕ}
    (h : RootSpan V (V.map (MulAut.conj g).toMonoidHom) U n)
    (hr : (2 * n : ℕ∞) < globalR V) :
    U ≤ V.map (MulAut.conj g).toMonoidHom := by
  rw [← h.moved]
  exact le_normalizer_iff_commutator_le_right.mp (rootCentralizerSpan_normalizes g h hr)

/-- The source Δ(U,V): the actual L-conjugates of the flag plane lying in U. -/
def planeFamily (L P U : Subgroup G) : Set (Subgroup G) :=
  {I | I ≤ U ∧ ∃ l : L, I = P.map (MulAut.conj (l : G)).toMonoidHom}

/-- The subgroup recovered from the local residuals at a family of planes. -/
def planeResidualSpan (L : Subgroup G) (planes : Set (Subgroup G)) : Subgroup G :=
  ⨆ I ∈ planes, localResidual L I

/-- Equality of planes identifies the two component spans using relative
noncentral-component uniqueness, without asserting ambient normality. -/
theorem eq_of_common_planes {L K : Subgroup G} {planes other : Set (Subgroup G)}
    (he : planes = other)
    (hL : planeResidualSpan L planes = L)
    (hK : planeResidualSpan K other = K)
    (hu : ∀ I ∈ planes, Source.UniqueNoncentralComponent (normalizer (I : Set G)) I
      (localResidual L I))
    (hk : ∀ I ∈ other, Source.NoncentralComponent (normalizer (I : Set G)) I
      (localResidual K I)) : K = L := by
  subst other
  rw [← hK, ← hL]
  apply iSup_congr
  intro I
  apply iSup_congr
  intro hI
  exact (hu I hI).2 _ (hk I hI)

/-- The common-plane calculation recovers the actual conjugating element in M. -/
theorem mem_normalizer_of_common_planes (L P U : Subgroup G) (g : G)
    (he : planeFamily L P U = planeFamily
      (L.map (MulAut.conj g).toMonoidHom) (P.map (MulAut.conj g).toMonoidHom) U)
    (hL : planeResidualSpan L (planeFamily L P U) = L)
    (hK : planeResidualSpan (L.map (MulAut.conj g).toMonoidHom)
      (planeFamily (L.map (MulAut.conj g).toMonoidHom)
        (P.map (MulAut.conj g).toMonoidHom) U) = L.map (MulAut.conj g).toMonoidHom)
    (hu : ∀ I ∈ planeFamily L P U,
      Source.UniqueNoncentralComponent (normalizer (I : Set G)) I (localResidual L I))
    (hk : ∀ I ∈ planeFamily (L.map (MulAut.conj g).toMonoidHom)
        (P.map (MulAut.conj g).toMonoidHom) U,
      Source.NoncentralComponent (normalizer (I : Set G)) I
        (localResidual (L.map (MulAut.conj g).toMonoidHom) I)) :
    g ∈ normalizer (L : Set G) :=
  mem_normalizer_iff_map_conj_eq.mpr (eq_of_common_planes he hL hK hu hk)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2
