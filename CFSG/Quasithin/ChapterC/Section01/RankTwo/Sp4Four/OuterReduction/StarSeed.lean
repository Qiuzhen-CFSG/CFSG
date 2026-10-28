module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.InnerContainment
public import Theory.Representation.SymplecticNaturalNormalizer.SeedCentralizer

/-!
# Outer removal from the literal fixed cover seed

The seed is exactly U intersect C(S), restricted to the actual radical T.
Its characteristic orbit span contains that seed, so its star centralizer
centralizes every fixed cover vector. The natural fixed-line argument puts
this star centralizer in A O2(G). Characteristic minimality and the literal
source cut then force A O2(G)=G. This discharges the field-line premise of
the earlier inner-containment consumer without splitting the central layer.

Source: MS93 (3.4), p.868, and its use in Section 7, p.933. The source cut
still requires the earlier graph comparisons; it is not asserted here.
-/

public section

open Subgroup Representation Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {G F : Type*} [Group G]
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

theorem starCentralizer_le_component_core_of_cover_seed
    (A T U S : Subgroup G) [A.Normal] [U.Normal] [Finite U] [IsElementaryAbelian 2 U]
    (hUT : U ≤ T) (hS : IsPGroup 2 S)
    (hcent : centralizer (A.map (QuotientGroup.mk' (pCore 2 G)) : Set (G ⧸ pCore 2 G)) ≤
      A.map (QuotientGroup.mk' (pCore 2 G)))
    (hcard : 2 < Nat.card F)
    (e : A.map (QuotientGroup.mk' (pCore 2 G)) ≃* Sp F)
    (ρ : Representation (ZMod 2) (G ⧸ pCore 2 G) (Vector F))
    (hA : ∀ b : A.map (QuotientGroup.mk' (pCore 2 G)), ∀ w,
      ρ (b : G ⧸ pCore 2 G) w = symplecticNatural 2 (e b) w)
    (π : S →* L (K := F))
    (σ : Representation (ZMod 2) (L (K := F)) (Additive U))
    (hact : ∀ s : S, ∀ u : U,
      ((σ (π s) (Additive.ofMul u)).toMul : G) = (s:G)*u*(s:G)⁻¹)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (hproj : ∀ x : G, ∀ u : U,
      p (Additive.ofMul (MulAut.conjNormal x u)) =
        ρ (QuotientGroup.mk' (pCore 2 G) x) (p (Additive.ofMul u))) :
    (starCentralizer T ((U ⊓ centralizer (S : Set G)).subgroupOf T)).map T.subtype ≤
      A ⊔ pCore 2 G := by
  let Y := (U ⊓ centralizer (S : Set G)).subgroupOf T
  have hY : U ⊓ centralizer (S : Set G) ≤ (starSpan T Y).map T.subtype := by
    have he : Y.map T.subtype = U ⊓ centralizer (S : Set G) :=
      map_subgroupOf_eq_of_le (inf_le_left.trans hUT)
    rw [← he]
    exact map_mono (le_starSpan T Y)
  have hpre := SymplecticNaturalNormalizer.centralizer_cover_seed_le_component_preimage
    U S hS (QuotientGroup.mk' (pCore 2 G))
    (A.map (QuotientGroup.mk' (pCore 2 G))) hcent hcard e ρ hA π σ hact p hp hproj
  have hc : (starCentralizer T Y).map T.subtype ≤
      (A.map (QuotientGroup.mk' (pCore 2 G))).comap (QuotientGroup.mk' (pCore 2 G)) := by
    rw [starCentralizer_map]
    exact inf_le_right.trans ((centralizer_le hY).trans hpre)
  simpa only [comap_map_eq,QuotientGroup.ker_mk'] using hc

theorem component_core_eq_top_of_cover_seed
    (A T U S : Subgroup G) [A.Normal] [U.Normal] [Finite U] [IsElementaryAbelian 2 U]
    (hgen : A ⊔ T = ⊤) (hmin : CharacteristicMinimal A T)
    (hcut : (A ⊔ (T ⊓ centralizer
        ((starSpan T ((U ⊓ centralizer (S : Set G)).subgroupOf T)).map T.subtype : Set G))) ⊓
        pCore 2 G ≤ T ⊓ centralizer
          ((starSpan T ((U ⊓ centralizer (S : Set G)).subgroupOf T)).map T.subtype : Set G))
    (hUT : U ≤ T) (hS : IsPGroup 2 S)
    (hcent : centralizer (A.map (QuotientGroup.mk' (pCore 2 G)) : Set (G ⧸ pCore 2 G)) ≤
      A.map (QuotientGroup.mk' (pCore 2 G)))
    (hcard : 2 < Nat.card F)
    (e : A.map (QuotientGroup.mk' (pCore 2 G)) ≃* Sp F)
    (ρ : Representation (ZMod 2) (G ⧸ pCore 2 G) (Vector F))
    (hA : ∀ b : A.map (QuotientGroup.mk' (pCore 2 G)), ∀ w,
      ρ (b : G ⧸ pCore 2 G) w = symplecticNatural 2 (e b) w)
    (π : S →* L (K := F))
    (σ : Representation (ZMod 2) (L (K := F)) (Additive U))
    (hact : ∀ s : S, ∀ u : U,
      ((σ (π s) (Additive.ofMul u)).toMul : G) = (s:G)*u*(s:G)⁻¹)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (hproj : ∀ x : G, ∀ u : U,
      p (Additive.ofMul (MulAut.conjNormal x u)) =
        ρ (QuotientGroup.mk' (pCore 2 G) x) (p (Additive.ofMul u))) :
    A ⊔ pCore 2 G = ⊤ := by
  have he := starCentralizer_eq_top_of_minimal A T hmin
    ((U ⊓ centralizer (S : Set G)).subgroupOf T) hcut
  have hinner := starCentralizer_le_component_core_of_cover_seed
    A T U S hUT hS hcent hcard e ρ hA π σ hact p hp hproj
  rw [he, ← MonoidHom.range_eq_map, range_subtype] at hinner
  apply top_unique
  rw [← hgen]
  exact sup_le le_sup_left hinner

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
