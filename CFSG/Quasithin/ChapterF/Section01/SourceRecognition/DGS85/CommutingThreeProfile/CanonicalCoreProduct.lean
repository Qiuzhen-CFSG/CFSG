module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.NormalCoreProduct

/-!
# The canonical middle-core product

Three-core generation makes N = (Q_x ∩ Q_m)(Q_y ∩ Q_m) normal in the
starred middle endpoint. Its local transitivity identifies N with the join
of Q_v ∩ Q_m over every neighbor v of m. Conjugation now proves normality
in the full vertex stabilizer, even when that stabilizer is larger than
the starred endpoint.

The Suzuki source application in `SuzukiCoreDichotomy` uses this full
normality to obtain invariance under the entire opposite quotient Borel.
No equality N = Q_m is assumed or inferred here.

Source: DGS85, Groups and Graphs, (12.1)(c), (12.3), printed pp.178--180.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G]

/-- The two intersections generate all neighboring core intersections. -/
theorem middle_core_product_eq_neighbor_span (F : Bool → Subgroup G)
    (hQ : ∀ v, Q F v ≤ U F v)
    {x y m : Vertex F} (hxm : (graph F).Adj x m) (hym : (graph F).Adj y m)
    (A : Subgroup G) (hA : A ≤ stabilizer F m)
    (hgen : A = (Q F x ⊔ Q F y) ⊔ Q F m)
    (htrans : ∀ v, (graph F).Adj m v → ∃ g ∈ A, g • y = v) :
    (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m) =
      ⨆ v : Vertex F, ⨆ (_ : (graph F).Adj m v), Q F v ⊓ Q F m := by
  let N := (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m)
  have hn : A ≤ normalizer (N : Set G) := middle_core_product_normalizer F hQ hxm hym A hgen
  apply le_antisymm
  · exact sup_le (le_iSup_of_le x (le_iSup_of_le hxm.symm le_rfl))
      (le_iSup_of_le y (le_iSup_of_le hym.symm le_rfl))
  · apply iSup_le
    intro v
    apply iSup_le
    intro hv
    obtain ⟨g,hg,hgy⟩ := htrans v hv
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom)
      (show Q F y ⊓ Q F m ≤ N from le_sup_right)
    have heN : N.map (MulAut.conj g).toMonoidHom = N :=
      mem_normalizer_iff_map_conj_eq.mp (hn hg)
    rw [map_inf _ _ _ (MulAut.conj g).injective, ← Q_translate, ← Q_translate,
      hgy, show g • m = m from hA hg, heN] at hh
    exact hh

/-- The actual full vertex stabilizer normalizes the proposed middle-core product. -/
theorem middle_core_product_full_normalizer (F : Bool → Subgroup G)
    (hQ : ∀ v, Q F v ≤ U F v)
    {x y m : Vertex F} (hxm : (graph F).Adj x m) (hym : (graph F).Adj y m)
    (A : Subgroup G) (hA : A ≤ stabilizer F m)
    (hgen : A = (Q F x ⊔ Q F y) ⊔ Q F m)
    (htrans : ∀ v, (graph F).Adj m v → ∃ g ∈ A, g • y = v) :
    stabilizer F m ≤ normalizer (((Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m) : Subgroup G) : Set G) := by
  let N := (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m)
  have he : N = ⨆ v : Vertex F, ⨆ (_ : (graph F).Adj m v), Q F v ⊓ Q F m :=
    middle_core_product_eq_neighbor_span F hQ hxm hym A hA hgen htrans
  have hall (v : Vertex F) (hv : (graph F).Adj m v) : Q F v ⊓ Q F m ≤ N := by
    rw [he]
    exact le_iSup_of_le v (le_iSup_of_le hv le_rfl)
  have hmap (g : G) (hg : g ∈ stabilizer F m) : N.map (MulAut.conj g).toMonoidHom ≤ N := by
    have hfactor (v : Vertex F) (hv : (graph F).Adj m v) :
        (Q F v ⊓ Q F m).map (MulAut.conj g).toMonoidHom ≤ N := by
      rw [map_inf _ _ _ (MulAut.conj g).injective, ← Q_translate, ← Q_translate,
        show g • m = m from hg]
      apply hall
      have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hv
      change (graph F).Adj (g • m) (g • v) at hh
      rwa [show g • m = m from hg] at hh
    change ((Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m)).map _ ≤ N
    rw [Subgroup.map_sup]
    exact sup_le (hfactor x hxm.symm) (hfactor y hym.symm)
  intro g hg
  apply mem_normalizer_iff.mpr
  intro a
  constructor
  · intro ha
    exact hmap g hg (mem_map_of_mem (MulAut.conj g).toMonoidHom ha)
  · intro ha
    have hh := hmap g⁻¹ ((stabilizer F m).inv_mem hg)
      (mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom ha)
    change g⁻¹ * (g * a * g⁻¹) * (g⁻¹)⁻¹ ∈ N at hh
    simpa only [mul_assoc, inv_inv, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
