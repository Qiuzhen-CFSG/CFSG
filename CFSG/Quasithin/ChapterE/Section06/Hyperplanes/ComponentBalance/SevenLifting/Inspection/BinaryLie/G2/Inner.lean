module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.Obstructions
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Quotient
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Quotient
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.Semilinear
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.PrimeRankZero
public import Theory.Representation.QuadraticFourGroup.Recognition.FactorSylows.Linear
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Inner involutions in the G₂ seven-component inspection

A perfect subgroup of a full parabolic has trivial determinant or line-scalar
character, so lies in the corresponding local subgroup. Its three-rank is at
most one: the actual SL₂ map has a two-group kernel and SL₂ in characteristic
two has cyclic Sylow three-subgroups. The normalizer cover therefore excludes
both A₇ and its perfect central three-cover from every involution centralizer.
This uses only containment of the embedded subgroup, not component membership
in the larger involution centralizer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the Theorem C
inspection in E.6.18, printed p.252, and Remark A.2.4, printed p.33.
The imported octonion geometry carries its ATLAS source attribution.
-/

public section

open Subgroup Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie.G2

private theorem perfect_hom_trivial {X C : Type*} [Group X] [Group.IsPerfect X]
    [CommMonoid C] (f : X →* C) : f = 1 := by
  let φ := f.toHomUnits
  let : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have : Subsingleton φ.range := inferInstance
  ext x
  exact congrArg (fun y : φ.range => (y.val : C))
    (Subsingleton.elim (⟨φ x, x, rfl⟩ : φ.range) 1)

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem rank_of_two_kernel {X : Type*} [Group X] [Finite X]
    (f : X →* SL(2,F)) (hk : IsPGroup 2 f.ker) : primeRank 3 X ≤ 1 := by
  have hz : primeRank 3 f.ker = 0 := by
    apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
    intro hd
    obtain ⟨n, hn⟩ := hk.exists_card_eq
    rw [hn] at hd
    exact (by decide : ¬ 3 ∣ 2) ((by decide : Nat.Prime 3).dvd_of_dvd_pow hd)
  have hsl : primeRank 3 SL(2,F) ≤ 1 := by
    let P : Sylow 3 SL(2,F) := default
    exact P.primeRank_le_one_of_isCyclic
      (Matrix.SL2.odd_pGroup_isCyclic_of_injective P.isPGroup' (by decide)
        (P : Subgroup SL(2,F)).subtype (P : Subgroup SL(2,F)).subtype_injective)
  have h := primeRank_le_ker_add (p := 3) f
  omega

private theorem rank_local_short : primeRank 3 (local₁ (F := F)) ≤ 1 := by
  apply rank_of_two_kernel (shortSLHom (F := F))
  rw [shortSLHom_ker]
  exact radical₁_isTwoGroup.comap_subtype

private theorem rank_local_long : primeRank 3 (local₂ (F := F)) ≤ 1 := by
  apply rank_of_two_kernel (longSLHom (F := F))
  rw [longSLHom_ker]
  exact radical₂_isTwoGroup.comap_subtype

omit [Finite F] in
private theorem perfect_le_short_local (L : Subgroup (Model F)) [Group.IsPerfect L]
    (hL : L ≤ parabolic₁) : L ≤ local₁ := by
  let f : L →* shortPlaneStabilizer (F := F) :=
    inclusion (hL.trans parabolic₁_le_shortPlaneStabilizer)
  have hχ := perfect_hom_trivial (shortDet.comp f)
  intro x hx
  rw [local₁_eq_shortSpecial]
  exact ⟨f ⟨x, hx⟩, congrArg (fun χ : L →* F => χ ⟨x, hx⟩) hχ, rfl⟩

omit [Finite F] in
private theorem perfect_le_long_local (L : Subgroup (Model F)) [Group.IsPerfect L]
    (hL : L ≤ parabolic₂) : L ≤ local₂ := by
  let f : L →* pointStabilizer (K := F) := inclusion (hL.trans parabolic_le_pointStabilizer)
  have hχ := perfect_hom_trivial (lineScalarHom.comp f)
  intro x hx
  have hm : f ⟨x, hx⟩ ∈ (lineScalarHom (K := F)).ker :=
    congrArg (fun χ : L →* Fˣ => χ ⟨x, hx⟩) hχ
  rw [lineScalarHom_kernel] at hm
  rwa [local₂_eq_fixingFirstVector]

/-- Every perfect subgroup of either full parabolic has three-rank at most one. -/
private theorem parabolic_perfect_rank (L : Subgroup (Model F)) [Group.IsPerfect L]
    (hL : L ≤ parabolic₁ ∨ L ≤ parabolic₂) : primeRank 3 L ≤ 1 := by
  rcases hL with hL | hL
  · exact (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion (perfect_le_short_local L hL))
      (inclusion_injective _)).trans rank_local_short
  · exact (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion (perfect_le_long_local L hL))
      (inclusion_injective _)).trans rank_local_long

/-- Normalizer coverage excludes seven subgroups centralizing any involution. -/
theorem not_seven_centralizing_involution (t : Model F) (ht : orderOf t = 2)
    (L : Subgroup (Model F)) [Group.IsPerfect L]
    (hL : L ≤ centralizer ({t} : Set (Model F))) : ¬ IsSeven L := by
  intro hs
  have htn : t ≠ 1 := by intro h; simp [h] at ht
  have hp : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
    simpa only [Nat.card_zpowers, pow_one] using ht)
  obtain ⟨g, hg⟩ := Atlas.G2.EvenLocal.NormalizerCover.normalizer_conjugate_le_parabolic
    (zpowers t) (zpowers_ne_bot.mpr htn) hp
  have hLN : L ≤ normalizer (zpowers t : Set (Model F)) := by
    apply hL.trans
    have he : centralizer (zpowers t : Set (Model F)) =
        centralizer ({t} : Set (Model F)) := by
      rw [zpowers_eq_closure, centralizer_closure]
    rw [← he]
    exact centralizer_le_normalizer _
  let J := L.map (MulAut.conj g).toMonoidHom
  let : Group.IsPerfect J := Group.IsPerfect.map _
  have hJ : J ≤ parabolic₁ ∨ J ≤ parabolic₂ :=
    hg.imp ((map_mono hLN).trans ·) ((map_mono hLN).trans ·)
  have hu := parabolic_perfect_rank J hJ
  have hl := (hs.of_equiv ((MulAut.conj g).subgroupMap L)).two_le_primeRank
  change 2 ≤ primeRank 3 J at hl
  omega
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie.G2
