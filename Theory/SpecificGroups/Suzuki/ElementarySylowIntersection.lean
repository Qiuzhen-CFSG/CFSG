module
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry
public import Theory.GroupTheory.PCoreSurjective

/-!
# Elementary intersections of generating Suzuki Sylows

Suppose a finite group's quotient by its two-core is an actual matrix
Suzuki group with parameter n > 0. An elementary subgroup contained in two
Sylows which generate the group lies in its two-core. Indeed, its quotient
image lies in the first omega, hence the center, of each quotient Sylow.
It therefore centralizes the generated quotient and is a normal two-group.
Lifting the quotient two-core gives the claimed containment.

Source: the Suzuki root-group omega calculation of Huppert--Blackburn,
Finite Groups III, XI.3.1, transported in SylowOmegaGeometry. The application
to the literal denominator in DGS, Groups and Graphs (1985), 12.3(a), p.179,
is CommutingThreeProfile.SuzukiIntersectionDenominator.
-/

@[expose] public noncomputable section
open Subgroup
namespace BenderSuzuki.MatrixGroups
variable {A : Type*} [Group A] [Finite A]

/-- An elementary subgroup common to two generating Sylows lies in the actual two-core. -/
theorem elementary_le_core_of_generating_suzuki_sylows
    {n : ℕ} (hn : 0 < n) (e : (A ⧸ pCore 2 A) ≃* SuzukiMatrixGroup n)
    (T R : Sylow 2 A) (hgen : (T : Subgroup A) ⊔ R = ⊤)
    (W : Subgroup A) [IsElementaryAbelian 2 W]
    (hWT : W ≤ T) (hWR : W ≤ R) : W ≤ pCore 2 A := by
  let π := QuotientGroup.mk' (pCore 2 A)
  let T' := T.mapSurjective (f := π) (QuotientGroup.mk'_surjective _)
  let R' := R.mapSurjective (f := π) (QuotientGroup.mk'_surjective _)
  let D := W.map π
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map π
  have hc (P : Sylow 2 (A ⧸ pCore 2 A)) (hDP : D ≤ P) :
      D ≤ centralizer (P : Set (A ⧸ pCore 2 A)) := by
    have hΩ : D ≤ omegaOneAmbient (P : Subgroup (A ⧸ pCore 2 A)) := by
      rw [← omegaOneAmbient_eq_self D]
      exact omegaOneAmbient_mono hDP
    rw [suzukiSylow_omega_eq_center hn e P] at hΩ
    intro d hd p hp
    obtain ⟨z, hz, he⟩ := hΩ hd
    rw [← he]
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨p, hp⟩)
  have hgen' : (T' : Subgroup (A ⧸ pCore 2 A)) ⊔ R' = ⊤ := by
    change (T : Subgroup A).map π ⊔ (R : Subgroup A).map π = ⊤
    rw [← Subgroup.map_sup, hgen, map_top_of_surjective π (QuotientGroup.mk'_surjective _)]
  have hcentral : (⊤ : Subgroup (A ⧸ pCore 2 A)) ≤ centralizer (D : Set (A ⧸ pCore 2 A)) := by
    rw [← hgen']
    exact sup_le (le_centralizer_iff.mp (hc T' (map_mono hWT)))
      (le_centralizer_iff.mp (hc R' (map_mono hWR)))
  let : D.Normal := normalizer_eq_top_iff.mp (top_unique
    (hcentral.trans (Subgroup.centralizer_le_normalizer _)))
  have hd : D ≤ pCore 2 (A ⧸ pCore 2 A) :=
    le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 D⟩
  have hk : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  exact (map_le_iff_le_comap.mp hd).trans
    (π.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective _) hk).le

end BenderSuzuki.MatrixGroups
