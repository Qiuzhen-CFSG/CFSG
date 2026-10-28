module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.Basic
public import CFSG.Quasithin.ChapterI.Section06To08.Basic
public import Theory.GroupTheory.TINormalizerControl
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The natural-module branch of 12.2.16 on the original chosen module

A marked binary natural action is transitive on nonzero vectors: extend an
isomorphism of their one-dimensional spans and lift the resulting linear
automorphism through the original quotient map. With no centralizer escape,
local TI then makes every global transporter normalize V. This proves the
natural-module branch of 12.2.16 without assuming global fusion control.

The other six module alternatives require their own fusion analysis. The
arbitrary-fusion lemma below makes that remaining obligation explicit.
Source: Aschbacher--Smith, 12.2.16, printed pp.799--800.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Natural coordinates give an actual L-conjugator of any two nonzero vectors. -/
theorem natural_vector_transitive {L V : Subgroup G} {d : ℕ}
    (hnatural : Chapter6.Source.IsConjugationModel L V
      (Representation.specialLinearNatural (k := ZMod 2) d))
    {x y : G} (hx : x ∈ V) (hy : y ∈ V) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ l ∈ L, l * x * l⁻¹ = y := by
  obtain ⟨e, f, hf⟩ := hnatural
  let x' : Fin d → ZMod 2 := (f ⟨x, hx⟩).toAdd
  let y' : Fin d → ZMod 2 := (f ⟨y, hy⟩).toAdd
  have hx0 : x' ≠ 0 := by
    intro he
    have he' : f ⟨x, hx⟩ = 1 := he
    exact hx1 (congrArg Subtype.val (f.map_eq_one_iff.mp he'))
  have hy0 : y' ≠ 0 := by
    intro he
    have he' : f ⟨y, hy⟩ = 1 := he
    exact hy1 (congrArg Subtype.val (f.map_eq_one_iff.mp he'))
  let ex := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (Fin d → ZMod 2) x' hx0
  let ey := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (Fin d → ZMod 2) y' hy0
  obtain ⟨a, ha⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  have haxy : a x' = y' := by
    have he := ha (ex 1)
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at he
    simpa [ex, ey] using he.symm
  obtain ⟨s, hs⟩ := (BinaryLinear.OuterCyclic.slEquivLinear d).surjective a
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (e.symm s)
  have hel : e (QuotientGroup.mk' (pCore 2 L) l) = s := by rw [hl, e.apply_symm_apply]
  refine ⟨l, l.property, ?_⟩
  have he := hf l ⟨x, hx⟩
  rw [hel] at he
  have hsy : Representation.specialLinearNatural d s x' = y' := by
    change BinaryLinear.OuterCyclic.slEquivLinear d s x' = y'
    rw [hs, haxy]
  change ((f.symm (Multiplicative.ofAdd (Representation.specialLinearNatural d s x'))) : G) =
    (l : G) * x * (l : G)⁻¹ at he
  rw [hsy] at he
  simpa only [y', ofAdd_toAdd, f.symm_apply_apply] using he.symm

variable {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}

/-- Local TI and the contrary assumption place each point centralizer in N(V). -/
theorem point_centralizer_le_chosen_normalizer
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V)
    {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    centralizer ({v} : Set G) ≤ normalizer (V : Set G) := by
  have hTI := ((structural G T L h).2.2 V D).2.2.1
  exact (le_inf (hnone v hv hv1) le_rfl).trans
    (inf_elementCentralizer_le_normalizer_of_trivial_intersections hTI hv hv1)

/-- The remaining fusion input has the original module and original L-normalizer. -/
theorem globalTI_of_fusion
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V)
    (hfusion : ∀ x y : G, x ∈ V → y ∈ V → x ≠ 1 → y ≠ 1 →
      (∃ g : G, g * x * g⁻¹ = y) →
      ∃ m ∈ normalizer (L : Set G), m * x * m⁻¹ = y) :
    IsTISubgroup V := by
  apply (isTISubgroup_iff V).mpr
  intro g hg x hx hgx
  by_contra hx1
  have hy1 : g * x * g⁻¹ ≠ 1 := fun he =>
    hx1 ((MulAut.conj g).map_eq_one_iff.mp he)
  have hgM := conjugator_mem_of_centralizer_le (hnone x hx hx1)
    (hfusion x (g * x * g⁻¹) hx hgx hx1 hy1 ⟨g, rfl⟩)
  rcases ((structural G T L h).2.2 V D).2.2.1 g hgM with hd | he
  · have hy : g * x * g⁻¹ ∈ V ⊓ V.map (MulAut.conj g).toMonoidHom :=
      ⟨hgx, mem_map_of_mem _ hx⟩
    exact hy1 (mem_bot.mp (hd ▸ hy))
  · exact hg (mem_normalizer_iff_map_conj_eq.mpr he)

/-- Full 12.2.16 for row (a), keeping the actual chosen V and its natural marking. -/
theorem globalTI_of_natural
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V) {d : ℕ}
    (hnatural : Chapter6.Source.IsConjugationModel L V
      (Representation.specialLinearNatural (k := ZMod 2) d)) :
    IsTISubgroup V := by
  apply globalTI_of_fusion h D structural hnone
  intro x y hx hy hx1 hy1 _
  obtain ⟨l, hl, he⟩ := natural_vector_transitive hnatural hx hy hx1 hy1
  exact ⟨l, L.le_normalizer hl, he⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
