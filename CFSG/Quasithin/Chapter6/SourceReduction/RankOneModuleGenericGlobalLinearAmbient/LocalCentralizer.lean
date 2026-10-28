module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.CentralLine
public import Theory.SpecificGroups.PSL3.LinearAmbientGeometry.AffineCentralizer

/-!
# Local involution centralizers in the prepared linear row

The affine translation calculation gives C_{Lᵢ}(z) = S for every nonidentity
z in Z(S). An element of N_G(Lᵢ) fixing z therefore preserves S. Source
§5.3.5 identifies its normalizer with N_G(L₁) ∩ N_G(L₂), discharging both
local intersection bounds in §5.3.7, including q=4 and both orientations.

The last theorem applies these bounds to the proved core alternatives. Its
only additional local assumptions are that z is central in T and
O₂(C_G(z)) ≤ S; it does not assert those assumptions in the even-degree
exceptional case or identify the ambient group.
Source: Aschbacher–Smith §5.3.7, printed p.660 (`refs/quasithin.pdf`).
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

omit hmax in
/-- Each literal source factor has its actual affine-plane isomorphism. -/
theorem Preparation.linear_factor_affine (i : Fin 2) :
    Nonempty (![L,residual H] i ≃* Matrix.SL2.Affine F) := by
  rcases he with he | he <;> obtain ⟨e⟩ := he <;> fin_cases i
  · obtain ⟨a⟩ := (BlockComparison.linear_parabolic_factor d h hH.1.1.2 hp F hm hF 0 true e.left).2.1
    exact ⟨a.trans (Matrix.PSL3.LinearThree.pointLocalEquivAffine F)⟩
  · obtain ⟨a⟩ := (BlockComparison.linear_parabolic_factor d h hH.1.1.2 hp F hm hF 1 false e.right).2.1
    exact ⟨a.trans (Matrix.PSL3.LinearThree.lineLocalEquivAffine F)⟩
  · obtain ⟨a⟩ := (BlockComparison.linear_parabolic_factor d h hH.1.1.2 hp F hm hF 0 false e.left).2.1
    exact ⟨a.trans (Matrix.PSL3.LinearThree.lineLocalEquivAffine F)⟩
  · obtain ⟨a⟩ := (BlockComparison.linear_parabolic_factor d h hH.1.1.2 hp F hm hF 1 true e.right).2.1
    exact ⟨a.trans (Matrix.PSL3.LinearThree.pointLocalEquivAffine F)⟩

/-- A nonidentity central element of S has centralizer exactly S in either factor. -/
theorem Preparation.linear_factor_centralizer
    (i : Fin 2) (z : G) (hz : z ∈ centerIn (sourceS L H)) (hne : z ≠ 1) :
    (![L,residual H] i) ⊓ centralizer ({z} : Set G) = sourceS L H := by
  have ha := d.linear_factor_affine h hH hp F hm hF he i
  obtain ⟨a⟩ := ha
  obtain ⟨P,hP⟩ := d.sylow i
  rw [inf_eq_left.mpr (d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he i)] at hP
  have hzV : z ∈ (![L,residual H] i).pCoreIn 2 := by
    have hh := (d.linear_involution_geometry h hH hp F hm hF he hmax).1
    rw [← centerIn_eq_map_center] at hh
    have hzi := hh ▸ hz
    fin_cases i
    · exact hzi.1
    · exact hzi.2
  exact Matrix.PSL3.LinearAmbientGeometry.affine_sylow_centralizer _ _ a P hP z hzV hne
    (fun x hx => mem_centralizer_singleton_iff.mpr (hz.2 x hx))

/-- The actual full-normalizer intersection bound in §5.3.7. -/
theorem Preparation.linear_normalizer_centralizer_le_inter
    (i : Fin 2) (z : G) (hz : z ∈ centerIn (sourceS L H)) (hne : z ≠ 1) :
    centralizer ({z} : Set G) ⊓ normalizer (![L,residual H] i : Set G) ≤
      normalizer (L : Set G) ⊓ normalizer (residual H : Set G) := by
  have hc := d.linear_factor_centralizer h hH hp F hm hF he hmax i z hz hne
  have hn : centralizer ({z} : Set G) ⊓ normalizer (![L,residual H] i : Set G) ≤
      normalizer (sourceS L H : Set G) := by
    rw [← hc]
    exact (le_inf inf_le_right (inf_le_left.trans (centralizer ({z} : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  rw [← d.linear_center_normalizer h hH hp F hm hF he hmax,centerIn_eq_map_center]
  exact hn.trans (normalizer_le_normalizer_characteristic_image (sourceS L H) (center (sourceS L H)))

/-- The core alternative closes once its containment in S is established. -/
theorem Preparation.linear_centralizer_le_inter_of_core_le
    (z : G) (hz : orderOf z = 2) (hzS : z ∈ centerIn (sourceS L H))
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hR : (centralizer ({z} : Set G)).pCoreIn 2 ≤ sourceS L H) :
    centralizer ({z} : Set G) ≤
      normalizer (L : Set G) ⊓ normalizer (residual H : Set G) := by
  have hz' : z ∈ (center (sourceS L H)).map (sourceS L H).subtype := by
    rwa [← centerIn_eq_map_center]
  have hne : z ≠ 1 := by
    intro he
    simp [he] at hz
  have hN := d.linear_root_normalizers h hH hp F hm hF he hmax
  have hRN : centralizer ({z} : Set G) ≤
      normalizer ((centralizer ({z} : Set G)).pCoreIn 2 : Set G) :=
    (centralizer ({z} : Set G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  rcases d.linear_centralizer_core_alternative h hH hp F hm hF he hmax z hz hz' hzT hR with hZ | hV | hV
  · rw [← d.linear_center_normalizer h hH hp F hm hF he hmax,centerIn_eq_map_center,hZ]
    exact Chapter5.Section03.omega_center_pCoreIn_normalized _ _ rfl
  · rw [hV,hN.1] at hRN
    exact (le_inf le_rfl hRN).trans
      (d.linear_normalizer_centralizer_le_inter h hH hp F hm hF he hmax 0 z hzS hne)
  · rw [hV,hN.2.1] at hRN
    exact (le_inf le_rfl hRN).trans
      (d.linear_normalizer_centralizer_le_inter h hH hp F hm hF he hmax 1 z hzS hne)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
