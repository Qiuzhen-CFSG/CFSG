module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.FiveCore
public import Theory.GroupAction.ThreeActionFivePlane
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms

/-!
# The original five-core Frattini action

The supercritical subgroup supplied by the moved five-core has Frattini
quotient of order 25 in both actual model cases. The marked Sylow
three-subgroup supplements the intrinsic O₂(L₁). Since L₁ is two-perfect,
its nontrivial action cannot vanish on that Sylow subgroup. This action
survives the five-group Frattini kernel.

Orbit counting proves irreducibility on the quotient. The original
V-star has order two and centralizes L₁-star, so its nonidentity element
acts by inversion. The Sylow image and both automorphism actions use the
literal quotient H → H/O₂(H); no abstract replacement of an actor occurs.

The binary displacement bounds, five-core centralization and component
selection are subsequent obligations. Earlier geometry and the contrary
nonabelian branch remain explicit.
Source: Aschbacher--Smith, proof of 12.6.26, printed p.832.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

private theorem five_model_frattini_card {Y : Type*} [Group Y] [Finite Y]
    (h5 : IsPGroup 5 Y)
    (hm : (Nat.card Y = 25 ∧ Nonempty (Y ≃* (Multiplicative (ZMod 5) × Multiplicative (ZMod 5)))) ∨
       (Nat.card Y = 125 ∧ IsExtraspecial 5 Y ∧ Nonempty (Y ≃* HeisenbergPrime 5))) :
    Nat.card (Y ⧸ frattini Y) = 25 := by
  let : Fact (IsPGroup 5 Y) := ⟨h5⟩
  rcases hm with ⟨hc,⟨e⟩⟩ | ⟨hc,he,_⟩
  · let : IsElementaryAbelian 5 (Multiplicative (ZMod 5) × Multiplicative (ZMod 5)) :=
      { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide +kernel) }
    let : IsElementaryAbelian 5 Y := IsElementaryAbelian.of_injective e.toMonoidHom e.injective
    exact (Nat.card_congr (frattiniQuotientEquivOfIsElementaryAbelian (R := Y) (p := 5)).toEquiv).trans hc
  · let : IsExtraspecial 5 Y := he
    have hh := card_eq_card_quotient_mul_card_subgroup (frattini Y)
    have hPhi : Nat.card (frattini Y) = 5 := by
      rw [IsExtraspecial.frattini_eq_center (p := 5),IsExtraspecial.center_order_p 5 Y]
    rw [hc,hPhi] at hh
    omega

private theorem point_sylow_action_ne_one
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (P : Sylow 3 (D.fullSetup hZ T z).L₁)
    {A : Type*} [Group A] (a : (D.fullSetup hZ T z).L₁ →* A) (ha : a ≠ 1) :
    a.comp (P : Subgroup (D.fullSetup hZ T z).L₁).subtype ≠ 1 := by
  let E := D.fullSetup hZ T z
  obtain ⟨f,_,hk,_,_,hs⟩ := S.original_point_residual_quotient D hZ z hz hTz
  obtain ⟨e,he⟩ := hs P
  have hmap : (P : Subgroup E.L₁).map f = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨y,hy⟩ := e.surjective x
    exact ⟨y.val,y.property,(he y).symm.trans hy⟩
  have hgen : (P : Subgroup E.L₁) ⊔ pCore 2 E.L₁ = ⊤ := by
    have hh := congrArg (comap f) hmap
    rwa [comap_map_eq,hk,comap_top] at hh
  intro hzero
  have hp : (P : Subgroup E.L₁).map a = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro x hx
    exact DFunLike.congr_fun hzero (⟨x,hx⟩ : P)
  have hr : a.range = (pCore 2 E.L₁).map a := by
    have hh := congrArg (map a) hgen
    simpa only [Subgroup.map_sup,hp,bot_sup_eq,←MonoidHom.range_eq_map] using hh.symm
  have h2 : IsPGroup 2 a.range := hr ▸ (pCore_isPGroup (p := 2) (G := E.L₁)).map a
  have heq := (isPPerfect_embedded_pResidual 2 (L ⊓ E.Gz)).hom_eq_one_of_isPGroup h2 a.rangeRestrict
  apply ha
  apply MonoidHom.ext
  intro x
  exact congrArg Subtype.val (DFunLike.congr_fun heq x)

/-- The original marked Sylow action is irreducible on the supercritical
Frattini quotient, and every nonidentity element of V-star inverts it. -/
theorem SourceHypothesis.original_five_supercritical_frattini
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (hm : ¬ Nonabelian.Setup.star H V ≤
      centralizer (pCore 5 (H ⧸ pCore 2 H) : Set (H ⧸ pCore 2 H)))
    (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    let E := D.fullSetup hZ T z
    let R := pCore 5 (H ⧸ pCore 2 H)
    let P₀ := (P : Subgroup E.L₁).map E.L₁.subtype
    ∃ (Y : Subgroup R) (hY : IsSupercriticalPSubgroup 5 Y),
      letI : Y.Characteristic := hY.characteristic
      let a := (MulAut.characteristic Y).comp
        (MulAut.conjNormal : (H ⧸ pCore 2 H) →* MulAut R)
      let b := (quotientAut (frattini Y)).comp a
      ((Nat.card Y = 25 ∧ Nonempty (Y ≃* (Multiplicative (ZMod 5) × Multiplicative (ZMod 5)))) ∨
       (Nat.card Y = 125 ∧ IsExtraspecial 5 Y ∧ Nonempty (Y ≃* HeisenbergPrime 5))) ∧
      Nat.card (Y ⧸ frattini Y) = 25 ∧
      (Nonabelian.Setup.star H P₀).map b ≠ ⊥ ∧
      (∀ B : Subgroup (Y ⧸ frattini Y),
        (∀ p ∈ Nonabelian.Setup.star H P₀, ∀ x ∈ B, b p x ∈ B) → B = ⊥ ∨ B = ⊤) ∧
      (∀ v : Nonabelian.Setup.star H V, v ≠ 1 →
        ∀ x : Y ⧸ frattini Y, b v.val x = x⁻¹) := by
  let E := D.fullSetup hZ T z
  let R := pCore 5 (H ⧸ pCore 2 H)
  let P₀ := (P : Subgroup E.L₁).map E.L₁.subtype
  let U := Nonabelian.Setup.star H V
  obtain ⟨Y,hY,hmodels,hV,hL⟩ :=
    S.original_five_supercritical_models D hZ z hz hTV hTz hbound hns hH hn hm
  let : Y.Characteristic := hY.characteristic
  let a := (MulAut.characteristic Y).comp
    (MulAut.conjNormal : (H ⧸ pCore 2 H) →* MulAut R)
  have h5 : IsPGroup 5 Y := (pCore_isPGroup (p := 5) (G := H ⧸ pCore 2 H)).to_subgroup Y
  have hcard : Nat.card (Y ⧸ frattini Y) = 25 := five_model_frattini_card h5 hmodels
  have hLH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  let j := (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hLH)
  have hj : j.range = Nonabelian.Setup.star H E.L₁ := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact mem_map_of_mem _ y.property
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y.val,hy⟩,rfl⟩
  have haj : a.comp j ≠ 1 := by
    intro he
    apply hL
    rw [←hj]
    apply (Subgroup.map_eq_bot_iff _).mpr
    rintro _ ⟨y,rfl⟩
    exact DFunLike.congr_fun he y
  have haP : (a.comp j).comp (P : Subgroup E.L₁).subtype ≠ 1 :=
    point_sylow_action_ne_one S D hZ z hz hTz P _ haj
  have hPrange : (j.comp (P : Subgroup E.L₁).subtype).range = Nonabelian.Setup.star H P₀ := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact mem_map_of_mem _ (mem_map_of_mem E.L₁.subtype y.property)
    · rintro ⟨y,⟨w,hw,hew⟩,rfl⟩
      refine ⟨⟨w,hw⟩,?_⟩
      change QuotientGroup.mk' (pCore 2 H) _ = QuotientGroup.mk' (pCore 2 H) _
      exact congrArg _ (Subtype.ext hew)
  let A := Nonabelian.Setup.star H P₀
  have hmP : A.map a ≠ ⊥ := by
    intro he
    apply haP
    apply MonoidHom.ext
    intro p
    have hp : j p.val ∈ A := hPrange.le ⟨p,rfl⟩
    exact mem_bot.mp (he ▸ mem_map_of_mem a hp)
  have hA : IsPGroup 3 A := by
    let : IsElementaryAbelian 3 A := (S.original_point_sylow_star D hZ z hz hTz hH P).1
    exact IsElementaryAbelian.isPGroup 3 A
  have hVcard : Nat.card U = 2 :=
    (S.original_nonabelian_geometry D hZ z hz hTV hTz hbound hH hn).2.1
  have hcomm : A ≤ centralizer (U : Set (H ⧸ pCore 2 H)) :=
    (map_mono (comap_mono (map_subtype_le _))).trans
      (S.original_point_residual_star_centralizes D hZ z hz hTV hTz hbound hH hn)
  exact ⟨Y,hY,hmodels,hcard,
    Theory.GroupAction.five_frattini_plane_action h5 hcard a A U hA hmP hVcard hV hcomm⟩
end CFSG.Quasithin.Chapter12.Section06
