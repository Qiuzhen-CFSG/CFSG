module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.Inputs

/-!
# Reapplying the cover reduction at the actual full normalizer

The extension supplied by 1.2.4 contains L, remains outside M, and is ordinary
by the earlier outside-component criterion. Perfectness excludes containment
of Y₊. Repeating the local construction gives a cover of the same order, so
containment identifies the components. Their identical centres then identify
the two plane labels and the literal opposite residual. No uniform product
with an arbitrarily fixed residual is assumed.
Source: Aschbacher--Smith, proof of 15.3.38, printed p.1136.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open LocalCover LocalCover.SourceBorel GlobalGeometry
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem outside_sqtk {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (d : CharacteristicTwo.LocalData G) (H : Subgroup G) (hH : H ∈ d.Hplus) :
    IsSQTK κ (H ⧸ pCore 2 H) := by
  let R := H.pCoreIn 2
  have hHN : H ≤ normalizer (R : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hN : IsTwoLocal (normalizer (R : Set G)) := ⟨R, hH.1.1, isPGroup_pCoreIn 2 H, rfl⟩
  have hsq : IsSQTK κ H := (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp
    ((hG.twoLocal_sqtk hN).subgroup (H.subgroupOf (normalizer (R : Set G))))
  refine ⟨?_, hsq.isKGroup.quotient _⟩
  intro p hp ho
  let _ : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (hsq.stronglyQuasithin p hp ho)

omit [Finite G] in
/-- Matching first planes match the opposite planes, including both permitted
orientations of the original natural action. -/
theorem opposite_plane_eq {V₁ V₂ A B C D : Subgroup G}
    (h : PlaneOrder V₁ V₂ A B) (k : PlaneOrder V₁ V₂ C D) (he : A = C) : B = D := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases k with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> first | rfl | exact he.symm

/-- The source normalizer equality, with the repeated local reduction and its
plane compatibility discharged. -/
theorem normalizer_eq {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (embeddings : EarlierEmbeddings κ) {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L) : I = normalizer (r.cover.borel.W₁ : Set G) := by
  let V := r.cover.borel.W₁
  obtain ⟨i, hi⟩ := r.plane
  let : IsElementaryAbelian 2 V := d.action.elementary_of_le (by simpa only [V, hi] using d.action.plane_le i)
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by
    change 1 < Nat.card r.cover.borel.W₁
    rw [hi, d.action.card_plane]; decide)
  let : IsKleinFour V := ⟨by simpa only [V, hi] using d.action.card_plane i, IsElementaryAbelian.exponent_eq_prime⟩
  let N := normalizer (V : Set G)
  have hZ : (center L).map L.subtype = V := r.cover.center_plane
  obtain ⟨hN, K, hK, hLK, hKn, _⟩ := normalizer_component_extension embeddings h.outside
    s.earlier.sylow (outside_sqtk hG d) h.component_le (component_isCComponent h.component)
    (h.normalizes_component s.earlier) hZ
  let B := K.map N.subtype
  have hBN : B ≤ N := map_subtype_le _
  have hBK : B.subgroupOf N = K := comap_map_eq_self_of_injective N.subtype_injective _
  let : Group.IsPerfect K := hK.perfect
  let : Group.IsPerfect B := Group.IsPerfect.map N.subtype
  have hYB : ¬ d.Yplus ≤ B := yplus_not_le_perfect_normalizer d.Yplus B V hBN (r.noncentral s)
  have hBM : ¬ B ≤ d.M := fun hb => h.outside_component s.earlier (hLK.trans hb)
  have hthree : IsPGroup 3 (d.Yplus ⧸ pCore 2 d.Yplus) :=
    IsPGroup.of_exponent_dvd_pow (n := 1) (by simpa only [pow_one] using s.earlier.quotient_exponent)
  have hBout : ¬ (B.subgroupOf N).map N.subtype ≤ d.M := by
    rwa [map_subgroupOf_eq_of_le hBN]
  have hBC : IsComponent N (B.subgroupOf N) :=
    (Candidates.ComponentStructure.cComponent_ordinary_iff_outside hN s.earlier.sylow
      s.earlier.exclusion s.earlier.odd (inf_le_left.trans d.sylow_le)
      (s.earlier.normalizer_eq N hN) hthree
      (s.earlier.intersection_characteristic_two N hN) (hBK ▸ hK)).mpr hBout
  have hB3 : primeRank 3 B = 2 := by
    have hBN3 : primeRank 3 B ≤ primeRank 3 N := by
      rw [← primeRank_congr 3 (subgroupOfEquivOfLe hBN)]
      exact primeRank_subgroup_le 3 _
    exact le_antisymm (hBN3.trans (s.earlier.rank N hN))
      (h.component_rank.ge.trans (primeRank_mono 3 hLK))
  obtain ⟨b⟩ := local_result s (show Setup d N B from
    ⟨hN, hBN, hBC, hB3, h.residual_rank, hYB⟩)
  have hLB : L = B := eq_of_le_of_card_ge hLK (by rw [r.card, b.card])
  have hfirst : r.cover.borel.W₁ = b.cover.borel.W₁ :=
    r.cover.center_plane.symm.trans ((congrArg centerImage hLB).trans b.cover.center_plane)
  have hsecond := opposite_plane_eq r.cover.borel.planes b.cover.borel.planes hfirst
  apply SetLike.coe_injective
  calc
    (I : Set G) = (L : Set G) * (planeResidual d.M d.Y r.cover.borel.W₂ : Set G) *
      (d.S : Set G) := r.product
    _ = (B : Set G) * (planeResidual d.M d.Y b.cover.borel.W₂ : Set G) *
      (d.S : Set G) := by simp only [hLB, hsecond]
    _ = (N : Set G) := b.product.symm

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
