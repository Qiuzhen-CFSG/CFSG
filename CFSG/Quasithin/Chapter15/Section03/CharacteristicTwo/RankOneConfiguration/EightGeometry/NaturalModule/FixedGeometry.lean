module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Basic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry.PlaneIntersections
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry.NaturalFixedSpace
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry.SylowFixedSpace
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry.SpanSplitting
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Local
public import Theory.GroupTheory.SpecificGroups.KleinFourResidualAction

/-!
# Fixed geometry for the natural-eight action in 15.3.32

The rank-one choice makes Y₊ centralize V₁. Two-perfectness and the genuine
source line V₂=[V₂,Y₊] make its action on V₂ fixed-point free, so
C_{Z_S}(Y₊)=Z₁. The B.2.14 summand C_{U_I}(I) therefore lies in Z₁.
It is nontrivial: otherwise U_I=U_L would contain all four elements of Z_S,
whereas a Sylow two-subgroup fixes at most two vectors in the natural module.
Consequently C_{Z_S}(L)=Z₁ and |Z₁|=2. Since C_{U_L}(L)=1 and V₂≤U_L,
the decomposition of Z_S gives Z_S∩U_L=Z_S∩V₂.

The helper takes the compatible natural action, its actual A₈ component
marking, the indicated genuine preliminary conclusions, and the universal
splitting clause of B.2.14 explicitly. Constructing that action and assembling
all of source 15.3.32 remain with the NaturalModule owner.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.2.14 on p.78,
15.3.2–12 on pp.1121–1124 and 15.3.32 on pp.1132–1133.
-/

@[expose] public section

open Subgroup BinaryPermutation
open Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem second_plane_fixed_eq_bot (d : LocalData G)
    (hV₂ : d.V₂ = ⁅d.V₂, d.Yplus⁆) :
    d.V₂ ⊓ centralizer (d.Yplus : Set G) = ⊥ := by
  let _ := d.action.elementary_of_le (d.action.plane_le (Multiplicative.ofAdd (1 : ZMod 2)))
  have hcard : Nat.card d.V₂ = 4 := d.action.card_plane _
  let _ : Nontrivial d.V₂ := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : IsKleinFour d.V₂ := ⟨hcard, IsElementaryAbelian.exponent_eq_prime (p := 2) (G := d.V₂)⟩
  have hYN : d.Yplus ≤ normalizer (d.V₂ : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr hV₂.ge
  let ρ : d.Yplus →* MulAut d.V₂ := d.V₂.normalizerMonoidHom.comp (inclusion hYN)
  apply eq_bot_iff.mpr
  intro v hv
  apply mem_bot.mpr
  by_contra hv1
  have hf : ∀ y : d.Yplus, ρ y (⟨v, hv.1⟩ : d.V₂) = ⟨v, hv.1⟩ := by
    intro y
    apply Subtype.ext
    change (y : G) * v * (y : G)⁻¹ = v
    rw [hv.2 y y.property, mul_inv_cancel_right]
  have hρ := IsKleinFour.action_eq_one_of_twoPerfect_of_fixed_ne_one ρ
    (yplus_isPPerfect d) (fun he => hv1 (congrArg Subtype.val he)) hf
  have hcentral : d.V₂ ≤ centralizer (d.Yplus : Set G) := by
    intro w hw y hy
    have he := congrArg (fun f : d.Yplus →* MulAut d.V₂ => f ⟨y, hy⟩ ⟨w, hw⟩) hρ
    have hh := congrArg Subtype.val he
    change y * w * y⁻¹ = w at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hbot : d.V₂ = ⊥ := hV₂.trans (commutator_eq_bot_iff_le_centralizer.mpr hcentral)
  rw [hbot, Subgroup.card_bot] at hcard
  contradiction

/-- Two-perfectness and the full V₂ commutator identify the Y₊-fixed line in Z_S. -/
theorem yplus_fixed_eq_firstLine (d : LocalData G)
    (hRank : primeRank 3 d.Yplus = 1) (hYRank : 2 ≤ primeRank 3 d.Y)
    (hV₂ : d.V₂ = ⁅d.V₂, d.Yplus⁆) :
    d.ZS ⊓ centralizer (d.Yplus : Set G) = d.ZS ⊓ d.V₁ := by
  have hcase := rank_one_choice d hRank hYRank
  have hfirst : d.V₁ ≤ centralizer (d.Yplus : Set G) := by
    apply le_centralizer_iff.mpr
    rw [hcase.2]
    exact (map_subtype_le _).trans inf_le_right
  have hnorm : (d.ZS ⊓ d.V₂ : Subgroup G) ≤ normalizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G) := by
    let _ := d.action.elementary
    have hVV : d.V ≤ centralizer (d.V : Set G) :=
      le_centralizer_iff_isMulCommutative.mpr inferInstance
    exact ((inf_le_left.trans inf_le_left).trans hVV).trans
      ((centralizer_le (inf_le_left.trans inf_le_left)).trans (Subgroup.centralizer_le_normalizer _))
  apply le_antisymm ?_ (inf_le_inf_left _ hfirst)
  intro z hz
  have hzs : z ∈ (d.ZS ⊓ d.V₁ : Subgroup G) ⊔ (d.ZS ⊓ d.V₂) :=
    (fixedPlane_eq_sup_intersections d).le hz.1
  change z ∈ (((d.ZS ⊓ d.V₁ : Subgroup G) ⊔ (d.ZS ⊓ d.V₂) : Subgroup G) : Set G) at hzs
  rw [coe_mul_of_right_le_normalizer_left _ _ hnorm] at hzs
  obtain ⟨x, hx, y, hy, hxy⟩ := hzs
  change x * y = z at hxy
  have hyC : y ∈ centralizer (d.Yplus : Set G) := by
    have h := (centralizer (d.Yplus : Set G)).mul_mem
      ((centralizer (d.Yplus : Set G)).inv_mem (hfirst hx.2)) hz.2
    rwa [← hxy, inv_mul_cancel_left] at h
  have hy1 : y = 1 := (second_plane_fixed_eq_bot d hV₂).le ⟨hy.2, hyC⟩
  rw [hy1, mul_one] at hxy
  exact hxy ▸ hx

/-- Compatibility transports the Sylow fixed-space bound to the actual U_L. -/
theorem componentModule_sylow_fixed_card_le_two (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (a : NaturalEightAction I (d.componentModule I c.L))
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S) :
    Nat.card (d.componentModule I c.L ⊓ centralizer (d.S : Set G) : Subgroup G) ≤ 2 := by
  let Q := P.mapSurjective a.onto
  let U := d.componentModule I c.L
  let C := U ⊓ centralizer (d.S : Set G)
  let f : C → fixedSpace (naturalRepresentation (Fin 8)) (Q : Subgroup _) := fun v =>
    ⟨Multiplicative.toAdd (a.coordinates ⟨v, v.property.1⟩), by
      intro g
      obtain ⟨s, hs, he⟩ := g.property
      have hsS : (s : G) ∈ d.S := hP ▸ mem_map_of_mem I.subtype hs
      have hc := a.compatible s (⟨v, v.property.1⟩ : U)
      have hh : U.normalizerMonoidHom ⟨s, a.normalizes s.property⟩
          (⟨v, v.property.1⟩ : U) = ⟨v, v.property.1⟩ := by
        apply Subtype.ext
        change (s : G) * (v : G) * (s : G)⁻¹ = v
        rw [v.property.2 s hsS, mul_inv_cancel_right]
      rw [hh, he] at hc
      exact (congrArg Multiplicative.toAdd hc).symm⟩
  have hi : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    have he : a.coordinates (⟨v, v.property.1⟩ : U) = a.coordinates ⟨w, w.property.1⟩ :=
      congrArg Subtype.val h
    exact congrArg (fun u : U => (u : G)) (a.coordinates.injective he)
  exact (Nat.card_le_card_of_injective f hi).trans (natural_sylow_fixed_card_le_two Q)

/-- The central summand is the first fixed line, after the source B.2.14 application. -/
theorem span_fixed_eq_firstLine (hB : SourceB214Splitting.{u})
    (d : LocalData G) {I : Subgroup G} (hchar : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (hI : I = c.L ⊔ d.S) (hYL : d.Yplus ≤ c.L)
    (hRank : primeRank 3 d.Yplus = 1) (hYRank : 2 ≤ primeRank 3 d.Y)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hV₂ : d.V₂ = ⁅d.V₂, d.Yplus⁆) (hseed : d.V₂ ≤ localSpan d.Z d.Yplus)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hZ : Nat.card d.Z = 2) (hZS : Nat.card d.ZS = 4)
    (hOmega : d.ZS = Stellmacher.omegaOneCenterAmbient d.S)
    (a : NaturalEightAction I (d.componentModule I c.L)) :
    d.UI I ⊓ centralizer (I : Set G) = d.ZS ⊓ d.V₁ := by
  obtain ⟨_, hZSUI, _⟩ := span_eq_firstLine_sup_componentModule d c hnormal hI hYL hV₂
    hseed hindex hZ hZS
  have hsplit := span_split_of_source hB d hchar c hnormal hI P hP hZ
  have hCZS := span_fixed_le_ZS d hchar P hP hOmega
  have hCY : (d.UI I ⊓ centralizer (I : Set G) : Subgroup G) ≤ centralizer (d.Yplus : Set G) :=
    inf_le_right.trans (centralizer_le (hYL.trans (component_le c)))
  have hCZ₁ : (d.UI I ⊓ centralizer (I : Set G) : Subgroup G) ≤ d.ZS ⊓ d.V₁ :=
    (le_inf hCZS hCY).trans (yplus_fixed_eq_firstLine d hRank hYRank hV₂).le
  have hne : d.UI I ⊓ centralizer (I : Set G) ≠ ⊥ := by
    intro hbot
    rw [hbot, sup_bot_eq] at hsplit
    have hZSUL : d.ZS ≤ d.componentModule I c.L := hZSUI.trans hsplit.le
    have hc := card_le_of_le (le_inf hZSUL (show d.ZS ≤ centralizer (d.S : Set G) from inf_le_right))
    have hb := componentModule_sylow_fixed_card_le_two d c a P hP
    rw [hZS] at hc
    omega
  apply eq_of_le_of_card_ge hCZ₁
  rw [card_plane_intersection d hindex hZ hZS 1]
  exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hne

/-- The fixed line and fixed-plane identities of 15.3.32, conditional on the
compatible natural action and the universal splitting clause of B.2.14. -/
theorem fixed_geometry (hB : SourceB214Splitting.{u})
    (d : LocalData G) {I : Subgroup G} (hchar : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (hI : I = c.L ⊔ d.S) (hYL : d.Yplus ≤ c.L)
    (hRank : primeRank 3 d.Yplus = 1) (hYRank : 2 ≤ primeRank 3 d.Y)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hV₂ : d.V₂ = ⁅d.V₂, d.Yplus⁆) (hseed : d.V₂ ≤ localSpan d.Z d.Yplus)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hZ : Nat.card d.Z = 2) (hZS : Nat.card d.ZS = 4)
    (hOmega : d.ZS = Stellmacher.omegaOneCenterAmbient d.S)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8))
    (a : NaturalEightAction I (d.componentModule I c.L))
    (hactor : a.actor = e.toMonoidHom.comp (d.starMap I)) :
    d.ZS ⊓ centralizer (c.L : Set G) = d.ZS ⊓ d.V₁ ∧
      Nat.card (d.ZS ⊓ d.V₁ : Subgroup G) = 2 ∧
      d.ZS ⊓ d.componentModule I c.L = d.ZS ⊓ d.V₂ := by
  obtain ⟨hVU, hZSUI, _⟩ := span_eq_firstLine_sup_componentModule d c hnormal hI hYL hV₂
    hseed hindex hZ hZS
  have hfixed := span_fixed_eq_firstLine hB d hchar c hnormal hI hYL hRank hYRank P hP
    hV₂ hseed hindex hZ hZS hOmega a
  have hline : d.ZS ⊓ centralizer (c.L : Set G) = d.ZS ⊓ d.V₁ := by
    apply le_antisymm ?_ ?_
    · intro z hz
      apply hfixed.le
      refine ⟨hZSUI hz.1, ?_⟩
      have hCI : I ≤ centralizer ({z} : Set G) := by
        rw [hI]
        exact sup_le (fun l hl => mem_centralizer_singleton_iff.mpr (hz.2 l hl))
          (fun s hs => mem_centralizer_singleton_iff.mpr (hz.1.2 s hs))
      exact fun i hi => mem_centralizer_singleton_iff.mp (hCI hi)
    · exact le_inf inf_le_left
        (hfixed.ge.trans (inf_le_right.trans (centralizer_le (component_le c))))
  refine ⟨hline, card_plane_intersection d hindex hZ hZS 1, le_antisymm ?_ (inf_le_inf_left _ hVU)⟩
  intro z hz
  have hnorm : (d.ZS ⊓ d.V₂ : Subgroup G) ≤ normalizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G) := by
    let _ := d.action.elementary
    have hVV : d.V ≤ centralizer (d.V : Set G) :=
      le_centralizer_iff_isMulCommutative.mpr inferInstance
    exact ((inf_le_left.trans inf_le_left).trans hVV).trans
      ((centralizer_le (inf_le_left.trans inf_le_left)).trans (Subgroup.centralizer_le_normalizer _))
  have hzs := (fixedPlane_eq_sup_intersections d).le hz.1
  change z ∈ (((d.ZS ⊓ d.V₁ : Subgroup G) ⊔ (d.ZS ⊓ d.V₂) : Subgroup G) : Set G) at hzs
  rw [coe_mul_of_right_le_normalizer_left _ _ hnorm] at hzs
  obtain ⟨x, hx, y, hy, hxy⟩ := hzs
  change x * y = z at hxy
  have hxU : x ∈ d.componentModule I c.L := by
    have hh := (d.componentModule I c.L).mul_mem hz.2
      ((d.componentModule I c.L).inv_mem (hVU hy.2))
    rwa [← hxy, mul_inv_cancel_right] at hh
  have hxC : x ∈ centralizer (c.L : Set G) := (hline.ge hx).2
  have hx1 : x = 1 := (componentModule_inf_centralizer_eq_bot d c e hmark a hactor).le ⟨hxU, hxC⟩
  rw [hx1, one_mul] at hxy
  exact hxy ▸ hy

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry

end
