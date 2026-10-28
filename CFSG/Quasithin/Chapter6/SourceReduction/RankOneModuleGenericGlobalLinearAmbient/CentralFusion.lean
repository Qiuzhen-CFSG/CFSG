module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.LocalCentralizer
public import Theory.SpecificGroups.PSL3.LinearAmbientGeometry.AffineFusion
public import Theory.GroupTheory.DisjointConjugateCenter

/-!
# Fusion on the original central line

The actual affine factors are transitive on their nonzero core vectors.
Their centralizer calculation shows that a conjugator between two nonzero
central-line elements normalizes S, hence belongs to the whole normalizer
intersection. A nontrivial normal subgroup of a two-group meets its center,
so this same line contains an involution central in the original Sylow T.
The two root planes then fuse every involution of S to that line inside
L ∨ O²(H). Both orientations and field four are retained.

Source: Aschbacher–Smith §5.3.3 and §5.3.6–7, printed pp.659–660.
These are the literal source groups; no full-normalizer realization or
ambient recognition is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
include d h hH hp hm hF he hmax

/-- The full intersection is transitive on the nonzero original central line. -/
theorem Preparation.linear_center_transitive
    (z w : G) (hz : z ∈ centerIn (sourceS L H)) (hw : w ∈ centerIn (sourceS L H))
    (hz1 : z ≠ 1) (hw1 : w ≠ 1) :
    ∃ g ∈ normalizer (L : Set G) ⊓ normalizer (residual H : Set G), g * z * g⁻¹ = w := by
  have hc := (d.linear_involution_geometry h hH hp F hm hF he hmax).1
  rw [← centerIn_eq_map_center] at hc
  obtain ⟨a⟩ := d.linear_factor_affine h hH hp F hm hF he 0
  obtain ⟨g,hg,hgw⟩ := Matrix.PSL3.LinearAmbientGeometry.affine_core_transitive L a z w
    ((hc ▸ hz).1) ((hc ▸ hw).1) hz1 hw1
  have hn : g ∈ normalizer (sourceS L H : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro x ⟨y,hy,rfl⟩
      rw [← d.linear_factor_centralizer h hH hp F hm hF he hmax 0 w hw hw1]
      refine ⟨L.mul_mem (L.mul_mem hg ((d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he 0) hy))
        (L.inv_mem hg),mem_centralizer_singleton_iff.mpr ?_⟩
      change (g*y*g⁻¹)*w = w*(g*y*g⁻¹)
      rw [← hgw]
      have hh := congrArg (MulAut.conj g) (hz.2 y hy)
      simpa only [map_mul,MulAut.conj_apply] using hh
    · exact (card_map_of_injective (MulAut.conj g).injective).ge
  refine ⟨g,?_,hgw⟩
  rw [← d.linear_center_normalizer h hH hp F hm hF he hmax,centerIn_eq_map_center]
  exact normalizer_le_normalizer_characteristic_image (sourceS L H) (center (sourceS L H)) hn

/-- The original central line contains a nonidentity involution central in T. -/
theorem Preparation.linear_exists_sylow_central_involution :
    ∃ z : G, z ∈ centerIn (sourceS L H) ∧ orderOf z = 2 ∧
      (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
  let Z := centerIn (sourceS L H)
  have hST := sourceS_le_sylow h.sylow_normalizes hH.1.1.2
  have hZT : Z ≤ (T : Subgroup G) := inf_le_left.trans hST
  have hgeo := d.linear_involution_geometry h hH hp F hm hF he hmax
  have hne : Z ≠ ⊥ := by
    rw [← one_lt_card_iff_ne_bot]
    change 1 < Nat.card (centerIn (sourceS L H))
    rw [centerIn_eq_map_center,card_map_of_injective (sourceS L H).subtype_injective,hgeo.2.1]
    exact Finite.one_lt_card
  have hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G) := by
    rw [d.linear_center_normalizer h hH hp F hm hF he hmax]
    exact le_inf h.sylow_normalizes (hH.1.1.2.trans (le_normalizer_residual H))
  obtain ⟨z,hz1⟩ := ne_bot_iff_exists_ne_one.mp
    (inf_centerIn_ne_bot T.isPGroup' hne hZT hTZ)
  have hz : (z : G) ∈ Z := z.property.1
  have hz2 : (z : G) ^ 2 = 1 := hgeo.2.2.2.1 z (by rwa [← centerIn_eq_map_center])
  refine ⟨z,hz,orderOf_eq_prime hz2 (fun hh => hz1 (Subtype.ext hh)),?_⟩
  exact fun x hx => mem_centralizer_singleton_iff.mpr (z.property.2.2 x hx)

/-- Every involution of S is fused to the fixed central involution within the factor join. -/
theorem Preparation.linear_sourceS_involution_fused
    (z : G) (hz : z ∈ centerIn (sourceS L H)) (hz1 : z ≠ 1)
    (x : G) (hxS : x ∈ sourceS L H) (hx : orderOf x = 2) :
    ∃ g ∈ L ⊔ residual H, g * z * g⁻¹ = x := by
  have hgeo := d.linear_involution_geometry h hH hp F hm hF he hmax
  have hzV : z ∈ L.pCoreIn 2 ⊓ (residual H).pCoreIn 2 := by
    rw [← hgeo.1,← centerIn_eq_map_center]
    exact hz
  have hxV : x ∈ L.pCoreIn 2 ∨ x ∈ (residual H).pCoreIn 2 := by
    by_cases hxZ : x ∈ (center (sourceS L H)).map (sourceS L H).subtype
    · exact Or.inl ((hgeo.1 ▸ hxZ).1)
    · have hx2 : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
      have hxC : x ∈ sourceS L H ⊓ centralizer ({x} : Set G) :=
        ⟨hxS,mem_centralizer_singleton_iff.mpr rfl⟩
      rcases hgeo.2.2.2.2 x hxS hx2 hxZ with hc | hc
      · exact Or.inl (hc ▸ hxC)
      · exact Or.inr (hc ▸ hxC)
  have hx1 : x ≠ 1 := by intro hh; simp [hh] at hx
  have finish (i : Fin 2) (hzi : z ∈ (![L,residual H] i).pCoreIn 2)
      (hxi : x ∈ (![L,residual H] i).pCoreIn 2) :
      ∃ g ∈ L ⊔ residual H, g * z * g⁻¹ = x := by
    obtain ⟨a⟩ := d.linear_factor_affine h hH hp F hm hF he i
    obtain ⟨g,hg,hgz⟩ := Matrix.PSL3.LinearAmbientGeometry.affine_core_transitive
      (![L,residual H] i) a z x hzi hxi hz1 hx1
    refine ⟨g,?_,hgz⟩
    fin_cases i
    · exact (le_sup_left : L ≤ L ⊔ residual H) hg
    · exact (le_sup_right : residual H ≤ L ⊔ residual H) hg
  exact hxV.elim (finish 0 hzV.1) (finish 1 hzV.2)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
