module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.PointNormalizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.Containment
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.NilpotentFixedCover
public import Theory.SpecificGroups.SL2.FiveSylowNormalizer

/-!
# The intrinsic and ambient Sylow normalizers in the nilpotent case

The Cartan factorization and coprime intersection formula put
N_L(T_L) ∩ Y inside T. Consequently an odd subgroup of L ∩ Y normalizing
T is trivial. Source 11.0.4 supplies the required containment in L for
source-prime subgroups, including all cubic subgroups in the symplectic
case. Thus Y ∩ N_G(T) has order prime to three in that case.

The remaining nilpotent-Fitting component has an SL₂(5) quotient, so its
intrinsic Sylow normalizer contains an element of order three. In the
original symplectic geometry this element cannot normalize the full T.
The last theorem applies this to the actual moved-component sieve. The
source component-action conclusion still requires the ambient action
argument; normalization of T ∩ I alone does not supply it.

Source: Aschbacher--Smith 11.0.4 and 11.5.6(3), pp.760,780--781.
The Cartan owner retains clause (3); qt-d-1222-natural-closure retains
discharge of the preceding geometry.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)

/-- The actual Cartan normalizer meets Y only inside the Sylow two-subgroup. -/
theorem cartanNormalizer_inter_Y_le_sylow
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (hcart : LocalGeometry.IsCartan T L E.X) (hd : Disjoint E.X E.Y) :
    LocalGeometry.cartanNormalizer T L ⊓ E.Y ≤ (T : Subgroup G) := by
  rintro g ⟨hg,hgY⟩
  obtain ⟨t,ht,x,hx,he⟩ := CartanActions.cartanNormalizer_factorization D hcart hg
  let H := E.G₁
  let S := (T : Subgroup G).subgroupOf H
  let X := E.X.subgroupOf H
  let Y := E.Y.subgroupOf H
  let : Y.Normal :=
    (normal_subgroupOf_iff_le_normalizer E.Y_le_G₁).mpr E.G₁_normalizes_Y
  have ho : Odd (Nat.card X) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv]
    exact hcart.odd
  have hcop : Nat.Coprime (Nat.card S) (Nat.card X) := by
    have hp : IsPGroup 2 S := T.isPGroup'.comap_subtype
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    change Nat.card S = 2 ^ n at hn
    rw [hn]
    exact (Nat.coprime_two_left.mpr ho).pow_left n
  let a : H := ⟨g,E.Y_le_G₁ hgY⟩
  have ha : a ∈ ((S : Set H) * (X : Set H)) ∩ Y := by
    exact ⟨⟨⟨t,hT ht⟩,ht,⟨x,hX hx⟩,hx,Subtype.ext he⟩,hgY⟩
  rw [set_mul_inter_normal_of_coprime S X Y hcop] at ha
  obtain ⟨s,hs,y,hy,hsy⟩ := ha
  have hy1 : (y : G) = 1 := disjoint_def.mp hd hy.1 hy.2
  have he' : (s : G) * (y : G) = g := congrArg Subtype.val hsy
  rw [hy1,mul_one] at he'
  exact he' ▸ hs.1

omit [Finite G] in
/-- An element of L normalizing T preserves the literal source subgroup T_L. -/
theorem local_sylowNormalizer_le_cartanNormalizer :
    L ⊓ normalizer (T : Set G) ≤ LocalGeometry.cartanNormalizer T L := by
  let B := L ⊓ normalizer (T : Set G)
  have hBL : B ≤ normalizer (L : Set G) := inf_le_left.trans L.le_normalizer
  have hBT : B ≤ normalizer (T : Set G) := inf_le_right
  have hJ := (le_inf hBL hBT).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hQ : B ≤ normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
    hJ.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hTL : B ≤ normalizer (LocalGeometry.sourceTL T L : Set G) :=
    (le_inf hBT ((le_inf hBL hQ).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _))).trans
        inf_normalizer_le_normalizer_inf
  exact le_inf inf_le_left hTL

/-- An odd subgroup in L and Y cannot normalize the full T nontrivially. -/
theorem odd_point_sylowNormalizer_eq_bot_of_le_component
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (hcart : LocalGeometry.IsCartan T L E.X) (hd : Disjoint E.X E.Y)
    (B : Subgroup G) (hBo : Odd (Nat.card B)) (hBL : B ≤ L)
    (hBY : B ≤ E.Y) (hBT : B ≤ normalizer (T : Set G)) : B = ⊥ := by
  have hBS : B ≤ (T : Subgroup G) :=
    (le_inf ((le_inf hBL hBT).trans local_sylowNormalizer_le_cartanNormalizer) hBY).trans
      (E.cartanNormalizer_inter_Y_le_sylow hT hX hcart hd)
  obtain ⟨n,hn⟩ := T.isPGroup'.exists_card_eq
  have hcop : Nat.Coprime (Nat.card B) (Nat.card (T : Subgroup G)) := by
    rw [hn]
    exact (Nat.coprime_two_right.mpr hBo).pow_right n
  exact le_bot_iff.mp ((le_inf le_rfl hBS).trans (disjoint_of_coprime_natCard hcop).le_bot)

/-- Source 11.0.4 discharges containment in L for a source-prime subgroup. -/
theorem sourcePrime_point_sylowNormalizer_eq_bot
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hc : LocalGeometry.Preliminary.SourcePrime D E.input p)
    (B : Subgroup G) (hB : IsPGroup p B) (hBY : B ≤ E.Y)
    (hBT : B ≤ normalizer (T : Set G)) : B = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  have hBL := LocalGeometry.Preliminary.pSubgroup_le_component D E.input hp hc B hB
    (hBT.trans hNG)
  obtain ⟨n,hn⟩ := hB.exists_card_eq
  exact E.odd_point_sylowNormalizer_eq_bot_of_le_component hT hX hcart
    (E.cartan_disjoint_Y hcart.odd hCX hz) B (by rw [hn]; exact ho.pow) hBL hBY hBT

/-- The actual symplectic marking supplies the cubic source-prime containment. -/
theorem symplectic_threeSubgroup_point_sylowNormalizer_eq_bot
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (m : ActionEquiv D.centralQuotientAction
      (Representation.restrictScalars (k := ZMod 2)
        (symplecticNatural (k := E.input.field.Carrier) 2)))
    (B : Subgroup G) (hB : IsPGroup 3 B) (hBY : B ≤ E.Y)
    (hBT : B ≤ normalizer (T : Set G)) : B = ⊥ := by
  have hBL := LocalGeometry.Preliminary.sp4_threeSubgroup_le_component D E.input m B hB
    (hBT.trans hNG)
  obtain ⟨n,hn⟩ := hB.exists_card_eq
  exact E.odd_point_sylowNormalizer_eq_bot_of_le_component hT hX hcart
    (E.cartan_disjoint_Y hcart.odd hCX hz) B (by rw [hn]; exact (by decide : Odd 3).pow) hBL hBY hBT

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry



open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)

/-- The literal component Sylow normalizer has an element of order three. -/
theorem nilpotent_component_exists_sylow_cubic (hT : (T : Subgroup G) ≤ E.G₁)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (hn : Chapter1.Section02.A36Nilpotent
      ((I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁)))) :
    ∃ b : G, b ∈ I ∧ b ∈ normalizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G) ∧
      orderOf b = 3 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := E.nilpotent_component_twoFitting_quotient hI hn
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (twoFittingCore I))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨S,hS⟩ := E.exists_component_sylow_intersection hT hI
  have hd := three_dvd_sylow_normalizer_of_sl2_five_quotient hF f hf S
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' (G := normalizer (S : Set I)) 3 hd
  have hm : (S : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I := by
    rw [hS,subgroupOf_map_subtype]
  have hbN : (b.val : G) ∈ normalizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G) := by
    rw [←hm]
    exact (S : Subgroup I).le_normalizer_map I.subtype (mem_map_of_mem I.subtype b.property)
  exact ⟨b.val,b.val.property,hbN,(Subgroup.orderOf_coe b.val).trans
    ((Subgroup.orderOf_coe b).trans hb)⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry

open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)

/-- The ambient point-centralizer Sylow normalizer has order prime to three. -/
theorem symplectic_three_not_dvd_point_sylowNormalizer
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (m : ActionEquiv D.centralQuotientAction
      (Representation.restrictScalars (k := ZMod 2)
        (symplecticNatural (k := E.input.field.Carrier) 2))) :
    ¬ 3 ∣ Nat.card (E.Y ⊓ normalizer (T : Set G) : Subgroup G) := by
  intro hd
  let N := E.Y ⊓ normalizer (T : Set G)
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := N) 3 hd
  let B := (zpowers g).map N.subtype
  have hB : IsPGroup 3 B := (IsPGroup.of_card (n := 1)
    (by simp only [Nat.card_zpowers,hg,pow_one] : Nat.card (zpowers g) = 3 ^ 1)).map N.subtype
  have hbot := E.symplectic_threeSubgroup_point_sylowNormalizer_eq_bot
    hT hX hcart hCX hz hNG m B hB
    ((map_subtype_le _).trans inf_le_left) ((map_subtype_le _).trans inf_le_right)
  have hgb : (g : G) ∈ B := mem_map_of_mem N.subtype (mem_zpowers g)
  rw [hbot, mem_bot] at hgb
  have hgone : g = 1 := Subtype.ext hgb
  rw [hgone,orderOf_one] at hg
  omega

/-- An intrinsic cubic normalizer element cannot normalize the full Sylow subgroup. -/
theorem symplectic_nilpotent_component_cubic_not_full_sylowNormalizer
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (m : ActionEquiv D.centralQuotientAction
      (Representation.restrictScalars (k := ZMod 2)
        (symplecticNatural (k := E.input.field.Carrier) 2)))
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (hn : Chapter1.Section02.A36Nilpotent
      ((I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁)))) :
    ∃ b : G, b ∈ I ∧ b ∈ normalizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G) ∧
      orderOf b = 3 ∧ b ∉ normalizer (T : Set G) := by
  obtain ⟨b,hbI,hbS,hb⟩ := E.nilpotent_component_exists_sylow_cubic hT hI hn
  refine ⟨b,hbI,hbS,hb,?_⟩
  intro hbT
  let x : (E.Y ⊓ normalizer (T : Set G) : Subgroup G) := ⟨b,hI.1 hbI,hbT⟩
  have ho : orderOf x = 3 := (Subgroup.orderOf_coe x).symm.trans hb
  exact E.symplectic_three_not_dvd_point_sylowNormalizer hT hX hcart hCX hz hNG m
    (ho ▸ orderOf_dvd_natCard x)

/-- The original moved-component sieve supplies the nilpotent row for this restriction. -/
theorem symplectic_moved_component_cubic_not_full_sylowNormalizer
    (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (m : ActionEquiv D.centralQuotientAction
      (Representation.restrictScalars (k := ZMod 2)
        (symplecticNatural (k := E.input.field.Carrier) 2)))
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (hthree : 1 ≤ primeRank 3 E.L₁)
    (hexception : E.L₁ < E.K → Even E.input.field.degree)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (hmoved : ¬ ⁅I,E.X⁆ ≤ E.Y.pCoreIn 2) :
    ∃ b : G, b ∈ I ∧ b ∈ normalizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G) ∧
      orderOf b = 3 ∧ b ∉ normalizer (T : Set G) := by
  let c : LocalGeometry.Coordinates D E.input.field := .sp4 m
  have hc := E.cartan_coprime_of_local_action hp hX hcart.odd
    (fun _ hprime hdiv => (c.cartan_primeRank hcart hprime hdiv).ge) hCX hz
  have hr := E.three_rank_Y_le_one hp hc hexception hz hthree
  have ho : Odd E.input.field.degree := by
    apply Nat.not_even_iff_odd.mp
    intro he
    exact hmoved ((E.cartan_actions_of_even_marked hp hT hX c hcart hXR hCX hz hNG he).1 I hI)
  obtain ⟨hn,_,_⟩ := E.moved_component_nilpotent_fitting_case hp hT hX c hcart
    hXR hCX hz hNG hr ho hI hmoved
  exact E.symplectic_nilpotent_component_cubic_not_full_sylowNormalizer
    hT hX hcart hCX hz hNG m hI hn

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
