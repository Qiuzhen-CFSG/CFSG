module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.CartanIntersection
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.ResidualIncidence.Generation
public import Theory.AtlasPort.LinearGroups.G2.CubicCartan
public import Theory.GroupTheory.PerfectSolvableSectionLift

/-!
# The literal G₂ Cartan lines over the field of order four

The Borel projection gives two characters on the original Cartan. Its
restriction is injective because both the original quotient kernel and the
unipotent kernel are two-groups; the known Cartan order makes it an equivalence.
The characters l and lm identify the point and plane residual intersections,
using the same alignment and residual quotient maps throughout.

Over the field of order four, a cubic in the plane residual centralizes the
point residual modulo its full two-core, by the actual root commutators.
Conversely, the point quotient is centerless, so its own odd Cartan factor
meets that action kernel trivially. The two-character decomposition therefore
gives exactly C_X(L₁/O₂(L₁)) = X ∩ L₂. The possible central part of the chosen
module is retained throughout.

Source: Aschbacher--Smith B.4.6(14), used in 11.1.2, printed p.764.
The split-octonion calculations use the licensed ATLAS port; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation
open scoped commutatorElement
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation
open G2.ResidualIncidence
public noncomputable section
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))

private abbrev q : L →* Atlas.G2.Model S.field.Carrier :=
  (MulAut.conj (alignment S m).val).symm.toMonoidHom.comp (G2.coordinates S m).quotientMap

private theorem q_ker : (q S m).ker = pCore 2 L := by
  ext x
  change (MulAut.conj (alignment S m).val).symm
    (m.groupEquiv (QuotientGroup.mk' (pCore 2 L) x)) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff x

private theorem q_local (i : Fin 2) :
    (((G2.flag S m).Li i).subgroupOf L).map (q S m) = standardLocal S.field.Carrier i := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    have h := (localProjection S m i ⟨y,hy⟩).property
    rwa [localProjection_coe] at h
  · intro hx
    obtain ⟨y,hy⟩ := localProjection_surjective S m i ⟨x,hx⟩
    refine ⟨⟨y,(localResidual_le _ y.property).1⟩,y.property,?_⟩
    exact (localProjection_coe S m i y).symm.trans (congrArg Subtype.val hy)

private theorem q_cartan_borel {X : Subgroup G} (hX : IsCartan T L X) (x : X) :
    q S m ⟨x,(hX.1 x.property).1⟩ ∈ Atlas.G2.borel := by
  have hn (i : Fin 2) : (G2.coordinates S m).quotientMap ⟨x,(hX.1 x.property).1⟩ ∈
      (G2.coordinates S m).modelStabilizer ((G2.flag S m).space i.castSucc) :=
    ((G2.coordinates S m).mem_normalizer_preimage_iff _ _).mp
      ((G2.flag S m).cartan_normalizes (G2.flag_inner_unique S m) hX i.castSucc x.property)
  have hh (i : Fin 2) : q S m ⟨x,(hX.1 x.property).1⟩ ∈ standardParabolic S.field.Carrier i := by
    have h := hn i
    rw [modelStabilizer_flag,mem_map_equiv] at h
    exact h
  have h₀ := hh 0
  have h₁ := hh 1
  change _ ∈ Atlas.G2.LieParabolicSetup.parabolic₂ at h₀
  change _ ∈ Atlas.G2.LieParabolicSetup.parabolic₁ at h₁
  exact Atlas.G2.LieParabolicSetup.parabolics_intersection.le ⟨h₁,h₀⟩

include m in
private theorem cartan_cube (hd : S.field.degree = 2)
    {X : Subgroup G} (hX : IsCartan T L X) (x : X) : x^3 = 1 := by
  let e := (Coordinates.g2 m).cartanTorusEquiv hX
  have hc : Nat.card S.field.Carrierˣ = 3 := by rw [Nat.card_units,S.field.card_eq,hd]; decide
  have hp (a : S.field.Carrierˣ) : a^3 = 1 := by rw [←hc]; exact pow_card_eq_one'
  apply e.injective
  rw [map_pow,map_one]
  exact Prod.ext (hp _) (hp _)

omit [Finite G] in
private theorem core_kernel_of_commutators {B : Subgroup G} {x : G}
    (hn : x ∈ normalizer (B : Set G))
    (hc : ∀ b ∈ B, ⁅x,b⁆ ∈ B.pCoreIn 2) :
    x ∈ Closure.coreQuotientCentralizer B := by
  refine ⟨⟨x,hn⟩,MonoidHom.mem_ker.mpr ?_,rfl⟩
  apply MulEquiv.ext
  intro z
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) z
  rw [Closure.coreQuotientAction_apply_mk]
  apply QuotientGroup.eq_iff_div_mem.mpr
  obtain ⟨r,hr,he⟩ := hc b b.property
  have he' : r = B.normalizerMonoidHom ⟨x,hn⟩ b / b := by
    apply Subtype.ext
    simpa only [subtype_apply,div_eq_mul_inv,coe_mul,coe_inv,
      normalizerMonoidHom_apply_apply_coe,commutatorElement_def] using he
  exact he' ▸ hr

/-- The original plane Cartan factor acts trivially on the actual point
residual modulo its full two-core. -/
theorem marked_plane_cartan_centralizes_point (hd : S.field.degree = 2)
    {X : Subgroup G} (hX : IsCartan T L X) :
    X ⊓ (G2.flag S m).Li 1 ≤ Closure.coreQuotientCentralizer ((G2.flag S m).Li 0) := by
  let f := G2.flag S m
  have hn : X ≤ normalizer (f.Li 0 : Set G) :=
    ((le_inf ((hX.1.trans inf_le_left).trans L.le_normalizer)
      ((f.cartan_normalizes (G2.flag_inner_unique S m) hX 0).trans
        (normalizer _).le_normalizer)).trans inf_normalizer_le_normalizer_inf).trans
          (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
  have hk : IsPGroup 2 ((q S m).subgroupMap ((f.Li 0).subgroupOf L)).ker := by
    rw [ker_subgroupMap,q_ker]
    exact pCore_isPGroup.comap_subtype
  rintro x ⟨hx,hxl⟩
  let xL : L := ⟨x,(hX.1 hx).1⟩
  have hxs : q S m xL ∈ Atlas.G2.LieParabolicSetup.local₁ := by
    rw [←show standardLocal S.field.Carrier 1 = Atlas.G2.LieParabolicSetup.local₁ from rfl,
      ←q_local S m 1]
    exact mem_map_of_mem _ hxl
  have hx3 : q S m xL ^ 3 = 1 := by
    rw [←map_pow]
    have hp : xL^3 = 1 := Subtype.ext (congrArg (fun a : X => (a : G)) (cartan_cube S m hd hX ⟨x,hx⟩))
    rw [hp,map_one]
  have hc := Atlas.G2.CubicCartan.short_borel_cubic_commutators
    (by simpa [hd] using S.field.card_eq) (q S m xL) hxs (q_cartan_borel S m hX ⟨x,hx⟩) hx3
  apply core_kernel_of_commutators (hn hx)
  intro b hb
  let bL : L := ⟨b,(localResidual_le _ hb).1⟩
  have hmem : ⁅xL,bL⁆ ∈ (f.Li 0).subgroupOf L :=
    (f.Li 0).mul_mem ((mem_normalizer_iff.mp (hn hx) b).mp hb) ((f.Li 0).inv_mem hb)
  have hcore := mem_pCoreIn_of_map_mem (q S m) ((f.Li 0).subgroupOf L) hk hmem (by
    rw [map_commutatorElement,q_local]
    exact hc.2 (q S m bL) (by
      rw [←show standardLocal S.field.Carrier 0 = Atlas.G2.LieParabolicSetup.local₂ from rfl,
        ←q_local S m 0]
      exact mem_map_of_mem _ hb))
  have ha := mem_map_of_mem L.subtype hcore
  rw [map_pCoreIn_of_injective 2 _ _ L.subtype_injective,
    map_subgroupOf_eq_of_le (show f.Li 0 ≤ L from (localResidual_le _).trans inf_le_left)] at ha
  exact ha


private def characters {X : Subgroup G} (hX : IsCartan T L X) :
    X →* S.field.Carrierˣ × S.field.Carrierˣ :=
  Atlas.G2.EvenBorelTorus.projection.comp
    (((q S m).comp (inclusion (hX.1.trans inf_le_left))).codRestrict
      Atlas.G2.borel (q_cartan_borel S m hX))

private theorem characters_injective {X : Subgroup G} (hX : IsCartan T L X) :
    Function.Injective (characters S m hX) := by
  let r := (q S m).comp (inclusion (hX.1.trans inf_le_left))
  have hkq : IsPGroup 2 r.ker := by
    change IsPGroup 2 ((q S m).ker.comap (inclusion (hX.1.trans inf_le_left)))
    rw [q_ker]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  have ho : Odd (Nat.card r.ker) := hX.odd.of_dvd_nat (card_subgroup_dvd_card _)
  have hr : Function.Injective r := (MonoidHom.ker_eq_bot_iff r).mp
    (card_eq_one.mp (hkq.card_eq_or_dvd.resolve_right ho.not_two_dvd_nat))
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hu : r x ∈ Atlas.G2.unipotent := by
    change Atlas.G2.EvenBorelTorus.projection
      ⟨r x,q_cartan_borel S m hX x⟩ = 1 at hx
    have hh := MonoidHom.mem_ker.mpr hx
    rw [Atlas.G2.EvenBorelTorus.projection_ker] at hh
    exact hh
  have hc : IsPGroup 2 (Subgroup.zpowers (r x)) :=
    Atlas.G2.LieParabolicSetup.unipotent_isTwoGroup.to_le (zpowers_le.mpr hu)
  have hod : Odd (Nat.card (Subgroup.zpowers (r x))) := by
    rw [Nat.card_zpowers]
    exact hX.odd.of_dvd_nat ((orderOf_map_dvd r x).trans (orderOf_dvd_natCard (x := x)))
  have hz : r x = 1 := by
    have he : Subgroup.zpowers (r x) = ⊥ :=
      card_eq_one.mp (hc.card_eq_or_dvd.resolve_right hod.not_two_dvd_nat)
    exact he.le (mem_zpowers (r x))
  exact hr (hz.trans r.map_one.symm)

private theorem odd_inf_comap_map {A B : Type*} [Group A] [Group B]
    (r : A →* B) (hk : IsPGroup 2 r.ker)
    (R X : Subgroup A) (ho : Odd (Nat.card X))
    (hn : r.ker ≤ normalizer (R : Set A)) :
    X ⊓ (R.map r).comap r = X ⊓ R := by
  apply le_antisymm
  · refine le_inf inf_le_left ?_
    have hp : IsPPerfect 2 (X ⊓ (R.map r).comap r : Subgroup A) := by
      intro N hN htwo
      let := hN
      apply index_eq_one.mp
      change Nat.card (_ ⧸ N) = 1
      exact htwo.card_eq_or_dvd.resolve_right (fun hd =>
        ho.not_two_dvd_nat ((hd.trans N.card_quotient_dvd_card).trans
          (card_dvd_of_le inf_le_left)))
    apply le_of_isPPerfect_of_le_sup_of_normalizes _ R r.ker hp hk hn
    simpa only [comap_map_eq] using
      (inf_le_right : X ⊓ (R.map r).comap r ≤ (R.map r).comap r)
  · exact inf_le_inf_left X (le_comap_map _ _)

private theorem cartan_residual_iff {X : Subgroup G} (hX : IsCartan T L X)
    (i : Fin 2) (x : X) :
    q S m ⟨x,(hX.1 x.property).1⟩ ∈ standardLocal S.field.Carrier i ↔
      (x : G) ∈ (G2.flag S m).Li i := by
  let f := G2.flag S m
  have hle : f.Li i ≤ L := (localResidual_le _).trans inf_le_left
  have hkN : (q S m).ker ≤ normalizer ((f.Li i).subgroupOf L : Set L) := by
    rw [q_ker,← subgroupOf_normalizer_eq hle]
    have hp : pCore 2 L ≤ (T : Subgroup G).subgroupOf L := by
      rw [←(Coordinates.g2 m).innerSylow_coe]
      exact pCore_isPGroup.le_sylow_of_normal _
    exact hp.trans (comap_mono (f.sylow_normalizes_Li i))
  have he := odd_inf_comap_map (q S m)
    (by rw [q_ker]; exact pCore_isPGroup)
    ((f.Li i).subgroupOf L) (X.subgroupOf L)
    (by rw [Nat.card_congr (subgroupOfEquivOfLe (hX.1.trans inf_le_left)).toEquiv]; exact hX.odd) hkN
  rw [q_local] at he
  exact ⟨fun hx => (he.le ⟨x.property,hx⟩).2,
    fun hx => (he.ge ⟨x.property,hx⟩).2⟩

section Model
open Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.SplitOctonion
variable {F : Type*} [Field F] [CharP F 2]

private theorem torus_mem_point (l m : Fˣ) :
    Atlas.G2.torus l m ∈ local₂ ↔ l = 1 := by
  rw [local₂_eq_fixingFirstVector]
  change (Atlas.G2.torus l m).val (basisVector 0) = basisVector 0 ↔ _
  rw [torus_first_basis]
  constructor
  · intro h
    exact Units.ext (by simpa [basisVector] using congrFun h 0)
  · rintro rfl
    simp

private theorem torus_mem_plane (l m : Fˣ) :
    Atlas.G2.torus l m ∈ local₁ ↔ l * m = 1 := by
  constructor
  · intro ht
    rw [local₁_eq_shortSpecial] at ht
    obtain ⟨g,hg,he⟩ := ht
    have he' : g.val = Atlas.G2.torus l m := he
    have hg' : (shortRepresentation g).det = 1 := hg
    have hrep : shortRepresentation g = !![(l : F),0;0,(m : F)] := by
      ext i j
      change g.val.val (basisVector (j.castLE (by decide : 2 ≤ 8)))
        (i.castLE (by decide : 2 ≤ 8)) = _
      rw [he']
      fin_cases i <;> fin_cases j <;>
        simp [Atlas.G2.torus,Atlas.G2.torusEquiv,Atlas.G2.torusLinear,
          Atlas.G2.torusWeights,basisVector]
    rw [hrep,Matrix.det_fin_two] at hg'
    exact Units.ext (by simpa using hg')
  · intro h
    have hm : m = l⁻¹ := by
      exact (eq_inv_iff_mul_eq_one.mpr (by simpa only [mul_comm] using h))
    rw [hm]
    exact short_torus_mem_local₁ l

private theorem projection_residual (b : borel (K := F)) :
    ((EvenBorelTorus.projection b).1 = 1 ↔ b.val ∈ local₂) ∧
    ((EvenBorelTorus.projection b).1 * (EvenBorelTorus.projection b).2 = 1 ↔
      b.val ∈ local₁) := by
  obtain ⟨⟨u,t⟩,he⟩ := (borelProductEquiv (K := F)).surjective b
  have he' : u.val * t.val = b.val := congrArg Subtype.val he
  obtain ⟨⟨l,m⟩,ht⟩ := t.property
  change Atlas.G2.torus l m = t.val at ht
  let uB : borel (K := F) := ⟨u,(show unipotent ≤ borel (K := F) from le_sup_left) u.property⟩
  let tB : borel (K := F) := ⟨Atlas.G2.torus l m,mem_sup_right ⟨(l,m),rfl⟩⟩
  have hb : b = uB * tB := Subtype.ext (by simpa [uB,tB,ht] using he'.symm)
  have hu : EvenBorelTorus.projection uB = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [EvenBorelTorus.projection_ker]
    exact u.property
  have hp : EvenBorelTorus.projection b = (l,m) := by
    rw [hb,map_mul,hu,one_mul]
    exact EvenBorelTorus.projection_torus (l,m)
  rw [hp,hb]
  constructor
  · simpa only [coe_mul,uB,tB,(local₂ (F := F)).mul_mem_cancel_left (unipotent_le_local₂ u.property)] using
      (torus_mem_point l m).symm
  · simpa only [coe_mul,uB,tB,(local₁ (F := F)).mul_mem_cancel_left (unipotent_le_local₁ u.property)] using
      (torus_mem_plane l m).symm

private def shear : (Fˣ × Fˣ) ≃* (Fˣ × Fˣ) where
  toFun p := (p.1,p.1*p.2)
  invFun p := (p.1,p.1⁻¹*p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_mul' p r := by ext <;> simp [mul_comm,mul_left_comm]

end Model

private def cartanEquiv {X : Subgroup G} (hX : IsCartan T L X) :
    X ≃* S.field.Carrierˣ × S.field.Carrierˣ := by
  have hc : Nat.card X = Nat.card (S.field.Carrierˣ × S.field.Carrierˣ) := by
    rw [(Coordinates.g2 m).cartan_card hX,Nat.card_prod,Nat.card_units,S.field.card_eq,pow_two]
  let := Fintype.ofFinite X
  let := Fintype.ofFinite (S.field.Carrierˣ × S.field.Carrierˣ)
  exact (MulEquiv.ofBijective (characters S m hX)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨characters_injective S m hX,by simpa only [Nat.card_eq_fintype_card] using hc⟩)).trans shear

private theorem cartanEquiv_membership {X : Subgroup G} (hX : IsCartan T L X)
    (i : Fin 2) (x : X) :
    (if i = 0 then (cartanEquiv S m hX x).1 else (cartanEquiv S m hX x).2) = 1 ↔
      (x : G) ∈ (G2.flag S m).Li i := by
  rw [←cartan_residual_iff S m hX i x]
  have hp := projection_residual
    (⟨q S m ⟨x,(hX.1 x.property).1⟩,q_cartan_borel S m hX x⟩ : Atlas.G2.borel)
  fin_cases i
  · exact hp.1
  · exact hp.2

/-- The literal G₂ Cartan splits into the intersections with its two residuals. -/
theorem marked_cartan_split {X : Subgroup G} (hX : IsCartan T L X) :
    (X ⊓ (G2.flag S m).Li 0) ⊔ (X ⊓ (G2.flag S m).Li 1) = X ∧
      Disjoint (X ⊓ (G2.flag S m).Li 0) (X ⊓ (G2.flag S m).Li 1) := by
  let e := cartanEquiv S m hX
  have h₀ := cartanEquiv_membership S m hX 0
  have h₁ := cartanEquiv_membership S m hX 1
  constructor
  · apply le_antisymm (sup_le inf_le_left inf_le_left)
    intro x hx
    let a := e.symm (1,(e ⟨x,hx⟩).2)
    let b := e.symm ((e ⟨x,hx⟩).1,1)
    have ha : (a : G) ∈ X ⊓ (G2.flag S m).Li 0 := ⟨a.property,(h₀ a).mp (by simp [a,e])⟩
    have hb : (b : G) ∈ X ⊓ (G2.flag S m).Li 1 := ⟨b.property,(h₁ b).mp (by simp [b,e])⟩
    have hab : (a : G) * b = x := by
      change ((a*b : X) : G) = x
      have he : a*b = ⟨x,hx⟩ := e.injective (by simp [a,b])
      exact congrArg Subtype.val he
    rw [←hab]
    exact mul_mem_sup ha hb
  · apply disjoint_def.mpr
    intro x hx hy
    have he : e ⟨x,hx.1⟩ = 1 := Prod.ext ((h₀ _).mpr hx.2) ((h₁ _).mpr hy.2)
    exact congrArg Subtype.val (e.map_eq_one_iff.mp he)

omit [Finite G] in
private theorem kernel_commutator {B : Subgroup G} {x b : G}
    (hx : x ∈ Closure.coreQuotientCentralizer B) (hb : b ∈ B) :
    ⁅x,b⁆ ∈ B.pCoreIn 2 := by
  obtain ⟨a,ha,rfl⟩ := hx
  let k : B := ⟨b,hb⟩
  have he := congrArg (fun f : MulAut (B ⧸ pCore 2 B) =>
    f (QuotientGroup.mk' (pCore 2 B) k)) (MonoidHom.mem_ker.mp ha)
  rw [Closure.coreQuotientAction_apply_mk] at he
  change QuotientGroup.mk' (pCore 2 B) (B.normalizerMonoidHom a k) =
    QuotientGroup.mk' (pCore 2 B) k at he
  have hh : B.normalizerMonoidHom a k * k⁻¹ ∈ pCore 2 B :=
    (QuotientGroup.eq_one_iff (N := pCore 2 B) _).mp (by
      change QuotientGroup.mk' (pCore 2 B) (B.normalizerMonoidHom a k * k⁻¹) = 1
      rw [map_mul,map_inv,he,mul_inv_cancel])
  exact ⟨B.normalizerMonoidHom a k * k⁻¹,hh,rfl⟩

omit [Finite G] in
private theorem odd_point_kernel_trivial (B X : Subgroup G)
    (hz : center (B ⧸ pCore 2 B) = ⊥) (ho : Odd (Nat.card X)) :
    (X ⊓ B) ⊓ Closure.coreQuotientCentralizer B = ⊥ := by
  have hcore : (X ⊓ B) ⊓ Closure.coreQuotientCentralizer B ≤ B.pCoreIn 2 := by
    rintro x ⟨⟨hxX,hxB⟩,hx⟩
    let a : B := ⟨x,hxB⟩
    let r := QuotientGroup.mk' (pCore 2 B)
    have hc : r a ∈ center (B ⧸ pCore 2 B) := by
      apply mem_center_iff.mpr
      intro b
      obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) b
      obtain ⟨c,hc,hce⟩ := kernel_commutator hx b.property
      have hin : ⁅a,b⁆ ∈ pCore 2 B := by
        have he : c = ⁅a,b⁆ := Subtype.ext hce
        exact he ▸ hc
      have hone : r ⁅a,b⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hin
      rw [map_commutatorElement] at hone
      exact (commutatorElement_eq_one_iff_mul_comm.mp hone).symm
    have he : r a = 1 := mem_bot.mp (hz ▸ hc)
    exact ⟨a,(QuotientGroup.eq_one_iff a).mp he,rfl⟩
  have htwo := (isPGroup_pCoreIn 2 B).to_le hcore
  apply card_eq_one.mp
  exact htwo.card_eq_or_dvd.resolve_right (fun hd =>
    ho.not_two_dvd_nat (hd.trans (card_dvd_of_le (inf_le_left.trans inf_le_left))))

/-- B.4.6(14) on the original quotient and Cartan: the point-section
centralizer is exactly the intersection with the plane residual. -/
theorem marked_point_kernel_eq_plane (hd : S.field.degree = 2)
    {X : Subgroup G} (hX : IsCartan T L X) :
    X ⊓ Closure.coreQuotientCentralizer ((G2.flag S m).Li 0) =
      X ⊓ (G2.flag S m).Li 1 := by
  let B := (G2.flag S m).Li 0
  let C := Closure.coreQuotientCentralizer B
  let e := cartanEquiv S m hX
  have hz : center (B ⧸ pCore 2 B) = ⊥ := by
    let eB := flag_Li_quotientEquiv S m 0
    apply bot_unique
    intro x hx
    apply eB.map_eq_one_iff.mp
    exact Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot.le ((centerCongr eB) ⟨x,hx⟩).property
  have hdis := odd_point_kernel_trivial B X hz hX.odd
  have hplane : X ⊓ (G2.flag S m).Li 1 ≤ C :=
    marked_plane_cartan_centralizes_point S m hd hX
  apply le_antisymm _ (le_inf inf_le_left hplane)
  rintro x ⟨hxX,hxC⟩
  let a := e.symm (1,(e ⟨x,hxX⟩).2)
  let b := e.symm ((e ⟨x,hxX⟩).1,1)
  have haB : (a : G) ∈ B :=
    (cartanEquiv_membership S m hX 0 a).mp (by simp [a,e])
  have hbP : (b : G) ∈ (G2.flag S m).Li 1 :=
    (cartanEquiv_membership S m hX 1 b).mp (by simp [b,e])
  have hab : a*b = ⟨x,hxX⟩ := e.injective (by simp [a,b])
  have haC : (a : G) ∈ C := by
    have hh := C.mul_mem hxC (C.inv_mem (hplane ⟨b.property,hbP⟩))
    have he : (a : G) = x * (b : G)⁻¹ := by
      exact eq_mul_inv_of_mul_eq (congrArg Subtype.val hab)
    rwa [←he] at hh
  have ha : (a : G) = 1 := hdis.le ⟨⟨a.property,haB⟩,haC⟩
  have hx : x = b := by
    have hh := congrArg Subtype.val hab
    change (a:G)*(b:G) = x at hh
    simpa only [ha,one_mul] using hh.symm
  exact ⟨hxX,hx ▸ hbP⟩

/-- The calculation is independent of which original Sylow-invariant
flag witness is supplied; no conjugation of the Cartan is made. -/
theorem g2_point_kernel_eq_plane (hd : S.field.degree = 2)
    (f : InvariantFlag (.g2 m)) {X : Subgroup G} (hX : IsCartan T L X) :
    X ⊓ Closure.coreQuotientCentralizer (f.Li 0) = X ⊓ f.Li 1 := by
  have hr (i : Fin 2) : f.Li i = (G2.flag S m).Li i := by
    change localResidual L ((Coordinates.g2 m).preimage (f.space i.castSucc)) = _
    rw [G2.flag_inner_unique S m i.castSucc (f.space i.castSucc)
      (f.dimension i.castSucc) (inf_le_left.trans (f.invariant i.castSucc))]
    rfl
  rw [hr 0,hr 1]
  exact marked_point_kernel_eq_plane S m hd hX

/-- The two residual factors of every original marked G₂ flag generate X. -/
theorem g2_cartan_split (f : InvariantFlag (.g2 m))
    {X : Subgroup G} (hX : IsCartan T L X) :
    (X ⊓ f.Li 0) ⊔ (X ⊓ f.Li 1) = X ∧ Disjoint (X ⊓ f.Li 0) (X ⊓ f.Li 1) := by
  have hr (i : Fin 2) : f.Li i = (G2.flag S m).Li i := by
    change localResidual L ((Coordinates.g2 m).preimage (f.space i.castSucc)) = _
    rw [G2.flag_inner_unique S m i.castSucc (f.space i.castSucc)
      (f.dimension i.castSucc) (inf_le_left.trans (f.invariant i.castSucc))]
    rfl
  rw [hr 0,hr 1]
  exact marked_cartan_split S m hX

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation
