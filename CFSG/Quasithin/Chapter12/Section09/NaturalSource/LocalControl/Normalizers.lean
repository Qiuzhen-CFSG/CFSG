module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Stages
public import CFSG.Quasithin.Chapter12.Section08.Setup.Completion

/-!
# Reducing the intermediate flag normalizers to the plane centralizer

The original natural L-action gives
N_G(Vᵢ)=C_G(Vᵢ)N_L(Vᵢ). For i≥2 its centralizer lies in C_G(V₂),
so a bound C_G(V₂)≤M gives Gᵢ≤M. The source TI property then gives
Gᵢ≤M∩N_G(V). Conversely, the i=2 assertion bounds the plane centralizer.
This is the opening reduction of 12.9.7; the plane-centralizer bound is
still a source obligation, not an assumed conclusion of 12.9.1.

Source: Aschbacher--Smith, 12.9.7, printed p.862 of refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- Full action on every flag space reduces 12.9.7 to the plane centralizer. -/
theorem flag_normalizers_of_plane_centralizer
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n)
    (hplane : centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G)) :
    ∀ i, 1 < i → i < n → F.Gi i ≤ seedNormalizer (normalizer (L : Set G)) V := by
  let := h.chosen.elementary
  intro i hi hin g hg
  have hf := NormalGeometry.normalizer_factorization h.naturalMarking.geometryAction
    (F.Vi i) (F.le_seed i)
  have hgM : g ∈ normalizer (L : Set G) := by
    obtain ⟨c, hc, l, hl, rfl⟩ := (show g ∈
      (centralizer (F.Vi i : Set G) : Set G) * (L ⊓ normalizer (F.Vi i : Set G) : Subgroup G)
      from hf ▸ hg)
    exact (normalizer (L : Set G)).mul_mem
      (hplane (centralizer_le (F.monotone (by omega)) hc)) (L.le_normalizer hl.1)
  exact h.flag_normalizer_le earlier.structural F (by omega) (by omega) ⟨hgM, hg⟩

/-- Conversely, the i=2 assertion of 12.9.7 bounds the plane centralizer. -/
theorem flag_normalizers_iff_plane_centralizer
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) :
    (∀ i, 1 < i → i < n → F.Gi i ≤ seedNormalizer (normalizer (L : Set G)) V) ↔
      centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G) := by
  refine ⟨fun hc => ?_, flag_normalizers_of_plane_centralizer h earlier F⟩
  exact (Subgroup.centralizer_le_normalizer _).trans
    ((hc 2 (by decide) (by have := h.rank; omega)).trans inf_le_left)


end CFSG.Quasithin.Chapter12.Section09.NaturalSource
