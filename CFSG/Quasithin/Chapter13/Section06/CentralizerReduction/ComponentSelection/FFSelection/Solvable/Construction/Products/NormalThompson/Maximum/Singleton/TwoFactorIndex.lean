module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton

/-!
# Restriction indices when the complementary factor is S₃

The star image of each global maximum lies in the actual offender actor.
An internal-product projection identifies its restriction index with the
order of its elementary image in the complementary coordinate. An elementary
subgroup of S₃ has order at most two. Thus restricting to the selected full
preimage loses at most one binary dimension when the other factor is S₃.

The final applications combine this index calculation with fixed-part
replacement. They keep the coordinate intersection and the fixed-part
centralizer bound explicit; those premises are not proved by the native
product declaration alone. These conditional applications do not complete
the singleton witness construction in 13.6.13.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.2.4, printed pp.75–76, and 13.6.13, printed p.929.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
open CFSG.Quasithin.ChapterB.SourceInduction
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives

private theorem elementary_s3_card {D : Type*} [Group D] [Finite D]
    (e : D ≃* Equiv.Perm (Fin 3)) (A : Subgroup D) [IsElementaryAbelian 2 A] :
    Nat.card A ≤ 2 := by
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hD : Nat.card D = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hd : 2 ^ n ∣ 6 := by simpa only [hn, hD] using A.card_subgroup_dvd_card
  have hnle : n ≤ 1 := by
    by_contra h
    have h4 : 4 ∣ 6 := (pow_dvd_pow 2 (show 2 ≤ n by omega)).trans hd
    norm_num at h4
  rw [hn]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) hnle).trans (by decide)

private theorem projection_index {D : Type*} [Group D] [Finite D]
    {F K : Subgroup D} (h : InternalProduct F K) (e : F ≃* Equiv.Perm (Fin 3))
    (A : Subgroup D) [IsElementaryAbelian 2 A] : K.relIndex A ≤ 2 := by
  rw [← h.ker_fst, relIndex_ker]
  let : IsElementaryAbelian 2 (A.map h.fst) := IsElementaryAbelian.map h.fst
  exact elementary_s3_card e _

private def swapProduct {D : Type*} [Group D]
    {A B : Subgroup D} (h : InternalProduct A B) : InternalProduct B A where
  equiv := MulEquiv.prodComm.trans h.equiv
  apply_eq b a := by
    change h.equiv (a, b) = (b : D) * a
    have hc := congrArg h.equiv (show (a, (1 : B)) * (1, b) = (1, b) * (a, 1) by simp)
    rw [map_mul, map_mul, h.apply_eq, h.apply_eq] at hc
    simpa only [h.apply_eq, OneMemClass.coe_one, mul_one, one_mul] using hc

variable {G : Type*} [Group G] [Finite G]
private theorem image_le_actor
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (E : Subgroup (Gv v))
    (hE : E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v))) :
    E.map (starMk z v) ≤ FFFactors.offenderActor (starRepresentation z v) := by
  have hmap : (elementaryAbelianMaxJ (⊤ : Subgroup (Gv v))).map (starMk z v) =
      JGstar z v := starImage_intrinsic_thompson z v ⊤ (Gv v)
        (by rw [← MonoidHom.range_eq_map, range_subtype])
  apply (map_mono (le_sSup hE)).trans
  change (elementaryAbelianMaxJ (⊤ : Subgroup (Gv v))).map (starMk z v) ≤ _
  rw [hmap]
  exact (minimalSolvable_global_thompson L T z v hz S hS hX).1

private theorem preimage_index {D Y : Type*} [Group D] [Group Y] [Finite D] [Finite Y]
    (q : Y →* D) (I : Subgroup D) {F K : Subgroup I} (h : InternalProduct F K)
    (e : F ≃* Equiv.Perm (Fin 3))
    (E : Subgroup Y) [IsElementaryAbelian 2 E] (hEI : E.map q ≤ I) :
    ((K.map I.subtype).comap q).relIndex E ≤ 2 := by
  rw [relIndex_comap]
  conv_lhs => rw [← map_subgroupOf_eq_of_le hEI]
  rw [relIndex_map_map_of_injective _ _ I.subtype_injective]
  let : IsElementaryAbelian 2 (E.map q) := IsElementaryAbelian.map q
  let : IsElementaryAbelian 2 ((E.map q).subgroupOf I) := IsElementaryAbelian.subgroupOf hEI
  exact projection_index h e _

/-- If the second factor is S₃, restriction to the first full preimage
loses at most one binary dimension. E is an actual global maximum. -/
theorem minimalSolvable_twoFactor_first_index_le_two
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e₂ : c.second ≃* Equiv.Perm (Fin 3))
    (E : Subgroup (Gv v))
    (hE : E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v))) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    ((c.first.map I.subtype).comap (starMk z v)).relIndex E ≤ 2 := by
  dsimp only
  let : IsElementaryAbelian 2 E := hE.2.1
  exact preimage_index (starMk z v) _ (swapProduct c.product) e₂ E
    (image_le_actor L T z v hz S hS hX E hE)

/-- The symmetric restriction-index calculation when the first factor is S₃. -/
theorem minimalSolvable_twoFactor_second_index_le_two
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e₁ : c.first ≃* Equiv.Perm (Fin 3))
    (E : Subgroup (Gv v))
    (hE : E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v))) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    ((c.second.map I.subtype).comap (starMk z v)).relIndex E ≤ 2 := by
  dsimp only
  let : IsElementaryAbelian 2 E := hE.2.1
  exact preimage_index (starMk z v) _ c.product e₁ E
    (image_le_actor L T z v hz S hS hX E hE)

/-- A literal first-coordinate witness. The native selection supplies ambient
normality and the complementary S₃ supplies the index; the remaining module
centralizer and coordinate-intersection premises are visible in the type. -/
theorem minimalSolvable_twoFactor_first_maximum_of_centralizer
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hfix : Tv T v ≤ centralizer ({z} : Set G))
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor (starRepresentation z v)) =
      @Subgroup.map c.first _ (FFFactors.offenderActor (starRepresentation z v)) _
        c.first.subtype (pResidual 2 c.first)) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := c.first.map I.subtype
    centralizer (singletonFixed z v H : Set (Gv v)) ≤ H.comap (starMk z v) →
    ∀ E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v)),
      E.map (starMk z v) ⊓ H ≠ ⊥ →
      ∃ B ∈ elementaryAbelianMaxSubgroups (H.comap (starMk z v)),
        B.map (starMk z v) ≠ ⊥ := by
  intro I H hcentral E hE hne
  let : H.Normal := minimalSolvable_twoFactor_first_normal L T z v hz S hS hfix hX c e₁ hF
  exact star_maximum_of_singleton_centralizer_index_two z v hz H hcentral E hE hne
    (minimalSolvable_twoFactor_first_index_le_two L T z v hz S hS hX c e₂ E hE)

/-- The same literal preimage construction for a selected second coordinate. -/
theorem minimalSolvable_twoFactor_second_maximum_of_centralizer
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hfix : Tv T v ≤ centralizer ({z} : Set G))
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor (starRepresentation z v)) =
      @Subgroup.map c.second _ (FFFactors.offenderActor (starRepresentation z v)) _
        c.second.subtype (pResidual 2 c.second)) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := c.second.map I.subtype
    centralizer (singletonFixed z v H : Set (Gv v)) ≤ H.comap (starMk z v) →
    ∀ E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v)),
      E.map (starMk z v) ⊓ H ≠ ⊥ →
      ∃ B ∈ elementaryAbelianMaxSubgroups (H.comap (starMk z v)),
        B.map (starMk z v) ≠ ⊥ := by
  intro I H hcentral E hE hne
  let : H.Normal := minimalSolvable_twoFactor_second_normal L T z v hz S hS hfix hX c e₂ hF
  exact star_maximum_of_singleton_centralizer_index_two z v hz H hcentral E hE hne
    (minimalSolvable_twoFactor_second_index_le_two L T z v hz S hS hX c e₁ E hE)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
end
