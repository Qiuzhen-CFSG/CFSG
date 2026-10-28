module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.M22Shadow.Setup

/-!
# The actual image and Sylow subgroup in the dihedral shadow case

All images here use the range restriction of the published conjugation action
on V = Q⟨r,z⟩. The local residual is O²(N_L(V)), embedded in the original
ambient group. The marked involutions act trivially on the abelian V; hence
T = T_L⟨z,r⟩ gives T⁺ = T_L⁺. Restriction and surjective image transport prove
that this is Sylow in the faithful action image M⁺.

The earlier local geometry must supply the displayed generation and stability
premises. No component classification or representation recognition is assumed
or asserted here.

Source: Aschbacher–Smith, proof of Lemma 16.4.7, printed pp.1186–1187.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow.SixDimensional.DihedralCase
variable {G : Type*} [Group G]
noncomputable abbrev Image (L : Subgroup G) (g r z : G) := (shadowAction L g r z).range
noncomputable def imageSubgroup (L : Subgroup G) (g r z : G) (A : Subgroup G) :
    Subgroup (Image L g r z) :=
  (A.subgroupOf (shadowOvergroup L g r z)).map (shadowAction L g r z).rangeRestrict

def localNormalizer (L : Subgroup G) (r z : G) : Subgroup G :=
  L ⊓ normalizer (shadowSpace L r z : Set G)

noncomputable def localResidual (L : Subgroup G) (r z : G) : Subgroup G :=
  (pResidual 2 (localNormalizer L r z)).map (localNormalizer L r z).subtype

theorem localNormalizer_le (L : Subgroup G) (g r z : G) :
    localNormalizer L r z ≤ shadowOvergroup L g r z :=
  (inf_le_inf_right _ L.le_normalizer).trans le_sup_left

theorem imageSubgroup_mono (L : Subgroup G) (g r z : G) :
    Monotone (imageSubgroup L g r z) := by
  intro A B h
  exact map_mono (comap_mono h)

theorem imageSubgroup_sup (L : Subgroup G) (g r z : G) (A B : Subgroup G)
    (hA : A ≤ shadowOvergroup L g r z) (hB : B ≤ shadowOvergroup L g r z) :
    imageSubgroup L g r z (A ⊔ B) =
      imageSubgroup L g r z A ⊔ imageSubgroup L g r z B := by
  simp only [imageSubgroup, subgroupOf_sup hA hB, Subgroup.map_sup]

theorem imageSubgroup_eq_bot (L : Subgroup G) (g r z : G) (A : Subgroup G)
    (hA : A ≤ centralizer (shadowSpace L r z : Set G)) :
    imageSubgroup L g r z A = ⊥ := by
  apply le_bot_iff.mp
  rintro a ⟨m, hm, rfl⟩
  apply mem_bot.mpr
  apply Subtype.ext
  change shadowAction L g r z m = 1
  change m ∈ (shadowAction L g r z).ker
  rw [shadowAction_ker]
  exact hA hm
theorem shadowSpace_le_centralizer (L : Subgroup G) (r z : G)
    [IsMulCommutative (shadowSpace L r z)] :
    shadowSpace L r z ≤ centralizer (shadowSpace L r z : Set G) := by
  intro x hx
  exact mem_centralizer_iff.mpr fun y hy => setLike_mul_comm hy hx

theorem sylow_image [Finite G] (L : Subgroup G) (g r z : G) (T : Sylow 2 G)
    (hT : (T : Subgroup G) ≤ shadowOvergroup L g r z) :
    ∃ S : Sylow 2 (Image L g r z),
      (S : Subgroup (Image L g r z)) = imageSubgroup L g r z T := by
  exact ⟨(T.subtype hT).mapSurjective (shadowAction L g r z).rangeRestrict_surjective, rfl⟩

theorem sylow_le_shadowOvergroup (L : Subgroup G) (g r z : G) (T : Sylow 2 G)
    (hTL : componentSylow T L ≤ normalizer (shadowSpace L r z : Set G))
    (hTN : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hgen : (T : Subgroup G) = componentSylow T L ⊔ (zpowers z ⊔ zpowers r)) :
    (T : Subgroup G) ≤ shadowOvergroup L g r z := by
  apply le_trans (le_inf hTN ?_) le_sup_left
  rw [hgen]
  refine sup_le hTL ((sup_le ?_ ?_).trans (shadowSpace L r z).le_normalizer)
  · exact le_sup_right.trans le_sup_right
  · exact le_sup_left.trans le_sup_right

theorem sylow_image_eq (L : Subgroup G) (g r z : G) (T : Sylow 2 G)
    [IsMulCommutative (shadowSpace L r z)]
    (hT : (T : Subgroup G) ≤ shadowOvergroup L g r z)
    (hgen : (T : Subgroup G) = componentSylow T L ⊔ (zpowers z ⊔ zpowers r)) :
    imageSubgroup L g r z T = imageSubgroup L g r z (componentSylow T L) := by
  have hparts := hgen ▸ hT
  have hTL := (le_sup_left : componentSylow T L ≤ _).trans hparts
  have hE := (le_sup_right : zpowers z ⊔ zpowers r ≤ _).trans hparts
  have hcent : zpowers z ⊔ zpowers r ≤ centralizer (shadowSpace L r z : Set G) :=
    (sup_le (le_sup_right.trans le_sup_right) (le_sup_left.trans le_sup_right)).trans
      (shadowSpace_le_centralizer L r z)
  conv_lhs => rw [hgen]
  rw [imageSubgroup_sup _ _ _ _ _ _ hTL hE, imageSubgroup_eq_bot _ _ _ _ _ hcent, sup_bot_eq]

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow.SixDimensional.DihedralCase
