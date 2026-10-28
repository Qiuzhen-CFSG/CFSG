module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryCoverPlacement
public import Theory.AtlasPort.LinearGroups.G2.LieSylowCenter
public import Theory.SpecificGroups.G2.MultiplierOrdinary
public import Theory.AtlasPort.LinearGroups.G2.EvenThreeRank
public import Theory.GroupTheory.GeneralizedFitting.ComponentRankNormality


/-!
# G₂ root centralization and original component placement

An index-two centralizer meets every field-sized root group nontrivially.
The six-root product equations then kill each noncentral coordinate. Thus
an order-sixteen subgroup in the specified Sylow lies in its full center,
forcing the same field degree to be at least four. The ordinary multiplier
calculation kills the original component center. Its cubic rank makes the
component normal in its actual strongly quasithin overgroup.

The scalar torus also gives centralizer index at least fifteen in the
original Sylow normalizer. NonFFSourceDoubledBinaryG2Placement applies all
these facts to the canonical inner image on the chosen paired plane, lifts
centralization to the original component Sylow, and places it in Q.
Source: Aschbacher–Smith 7.7.6, printed p.706, refs/quasithin.pdf.
Root formulas use the licensed ATLAS port; see LICENSES/ATLAS.txt.
-/

public noncomputable section

open Subgroup
open Atlas.G2 Atlas.G2.LieParabolicSetup
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryG2Placement

private def rootHom {F : Type*} [Field F] (i : Fin 6) : Multiplicative F →* unipotent (K := F) where
  toFun t := ⟨unipotentProduct (Pi.single i t.toAdd), unipotentProduct_mem _⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by
    apply Subtype.ext
    fin_cases i <;> simp [unipotentProduct,
      rootA_add, rootB_add, rootC_add, rootD_add, rootE_add, rootF_add]

private theorem index_comap_le {X Y : Type*} [Group X] [Group Y] [Finite Y]
    (C : Subgroup Y) (f : X →* Y) : (C.comap f).index ≤ C.index := by
  rw [C.index_comap]
  exact (relIndex_le_of_le_right (H := C) (le_top : f.range ≤ ⊤)
    (by simpa using C.index_ne_zero_of_finite)).trans_eq C.relIndex_top_right

private theorem nontrivial_root_fixer {F : Type*} [Field F] [Finite F]
    (hF : 2 < Nat.card F) (x : unipotent (K := F))
    (hi : (centralizer ({x} : Set (unipotent (K := F)))).index ≤ 2) (i : Fin 6) :
    ∃ a : F, a ≠ 0 ∧ Commute (unipotentProduct (Pi.single i a)) x.val := by
  let C := (centralizer ({x} : Set (unipotent (K := F)))).comap (rootHom i)
  have hc : C.index ≤ 2 :=
    (index_comap_le (centralizer ({x} : Set (unipotent (K := F)))) (rootHom i)).trans hi
  have hn : C ≠ ⊥ := by
    intro h
    rw [h,index_bot] at hc
    exact (not_le_of_gt hF) hc
  obtain ⟨a,ha,hane⟩ := C.bot_or_exists_ne_one.resolve_left hn
  refine ⟨a.toAdd,hane,?_⟩
  exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha)

/-- Index at most two forces a concrete G₂ Sylow element into its full center. -/
private theorem g2_coordinate_central {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F) (x : unipotent (K := F))
    (hi : (centralizer ({x} : Set (unipotent (K := F)))).index ≤ 2) :
    x ∈ center (unipotent (K := F)) := by
  have hx : x.val ∈ unipotentRange := by simpa only [unipotent_eq_range] using x.property
  obtain ⟨t,ht⟩ := hx
  have hroot (i : Fin 6) : ∃ a : F, a ≠ 0 ∧
      unipotentProductParameters (Pi.single i a) t =
        unipotentProductParameters t (Pi.single i a) := by
    obtain ⟨a,ha,hc⟩ := nontrivial_root_fixer hF x hi i
    rw [←ht] at hc
    exact ⟨a,ha,unipotentProduct_injective (by
      rw [←unipotentProduct_mul,←unipotentProduct_mul]; exact hc.eq)⟩
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hthree : (3 : F) = 1 := by linear_combination htwo
  obtain ⟨a,ha,he⟩ := hroot 4
  have h5 : t 5 = 0 := by
    have h := congrFun he 3
    have hz : a * t 5 = 0 := by
      simpa [unipotentProductParameters, Pi.single_apply, sub_eq_add_neg] using h
    exact (mul_eq_zero.mp hz).resolve_left ha
  obtain ⟨b,hb,he⟩ := hroot 1
  have h4 : t 4 = 0 := by
    have h := congrFun he 0
    have hz : b * t 4 = 0 := by
      simpa [unipotentProductParameters, Pi.single_apply, h5] using h
    exact (mul_eq_zero.mp hz).resolve_left hb
  obtain ⟨c,hc,he⟩ := hroot 2
  have h3 : t 3 = 0 := by
    have h := congrFun he 0
    have hz : c * t 3 = 0 := by
      simpa [unipotentProductParameters, Pi.single_apply, h5,hthree] using h.symm
    exact (mul_eq_zero.mp hz).resolve_left hc
  obtain ⟨d,hd,he⟩ := hroot 3
  have h2 : t 2 = 0 := by
    have h := congrFun he 0
    have hz : t 2 * d = 0 := by
      simpa [unipotentProductParameters, Pi.single_apply, h5,hthree] using h
    exact (mul_eq_zero.mp hz).resolve_right hd
  obtain ⟨e,he0,he⟩ := hroot 4
  have h1 : t 1 = 0 := by
    have h := congrFun he 0
    have hz : t 1 * e = 0 := by
      simpa [unipotentProductParameters, Pi.single_apply, h5] using h
    exact (mul_eq_zero.mp hz).resolve_right he0
  have hcoord : t = ![t 0,0,0,0,0,0] := by
    ext i; fin_cases i <;> simp [h1,h2,h3,h4,h5]
  have hhighest : x.val ∈ highestRoot (F := F) := by
    refine ⟨Multiplicative.ofAdd (t 0),?_⟩
    change rootA (t 0) = x.val
    rw [←ht,hcoord]; simp [unipotentProduct]
  rw [←unipotent_center] at hhighest
  obtain ⟨y,hy,hyx⟩ := hhighest
  exact (Subtype.ext hyx : y = x) ▸ hy

private theorem centralizer_comap_equiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (x : X) :
    (centralizer ({e x} : Set Y)).comap e.toMonoidHom = centralizer ({x} : Set X) := by
  ext y
  simp only [mem_comap, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    ← map_mul, e.injective.eq_iff]

/-- The moving subgroup centralizes its specified full G₂ Sylow. -/
theorem g2_centralizes {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassificationModels.IsG2At G (2^n))
    (P : Sylow 2 G) (A : Subgroup G)
    (hAP : A ≤ (P : Subgroup G))
    (hi : ((centralizer (A : Set G)).subgroupOf (P : Subgroup G)).index ≤ 2) :
    A ≤ (center P).map (P : Subgroup G).subtype := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let R := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let c : P ≃* unipotent (K := F) :=
    (e.subgroupMap (P : Subgroup G)).trans (R.equiv (sylow (F := F)))
  have hbig : 2 < Nat.card F := by
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn
    norm_num at hh
    omega
  intro a ha
  let x : P := ⟨a,hAP ha⟩
  have hC : (centralizer ({x} : Set P)) = (centralizer ({a} : Set G)).subgroupOf
      (P : Subgroup G) := by
    ext y
    simp only [mem_centralizer_singleton_iff, mem_subgroupOf, x]
    exact Subtype.ext_iff
  have hidx : (centralizer ({x} : Set P)).index ≤ 2 := by
    rw [hC]
    apply le_trans _ hi
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero index_ne_zero_of_finite)
      (index_dvd_of_le (comap_mono (centralizer_le (Set.singleton_subset_iff.mpr ha))))
  have hcidx : (centralizer ({c x} : Set (unipotent (K := F)))).index ≤ 2 := by
    rw [← (centralizer ({c x} : Set _)).index_comap_of_surjective
      (f := c.toMonoidHom) c.surjective,centralizer_comap_equiv]
    exact hidx
  refine ⟨x,mem_center_iff.mpr ?_,rfl⟩
  intro y
  apply c.injective
  simpa only [map_mul] using mem_center_iff.mp (g2_coordinate_central hbig (c x) hcidx) (c y)

/-- Sixteen central elements force degree at least four in the same G₂ field. -/
theorem g2_degree_ge_four {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassificationModels.IsG2At G (2^n))
    (P : Sylow 2 G) (A : Subgroup G) (hA : Nat.card A = 16)
    (hAP : A ≤ (P : Subgroup G))
    (hi : ((centralizer (A : Set G)).subgroupOf (P : Subgroup G)).index ≤ 2) :
    4 ≤ n := by
  have hAZ := g2_centralizes hn hm P A hAP hi
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let R := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let c : P ≃* unipotent (K := F) :=
    (e.subgroupMap (P : Subgroup G)).trans (R.equiv (sylow (F := F)))
  have hcard : Nat.card (center P) = 2^n := by
    rw [Nat.card_congr (centerCongr c).toEquiv]
    exact (Nat.card_congr (centerEquivHighestRoot unipotent
      (fiveRootSubgroup_le_unipotent _ _) le_rfl).toEquiv).trans hF
  have hb := Nat.card_le_card_of_injective (inclusion hAZ) (inclusion_injective hAZ)
  rw [card_map_of_injective (P : Subgroup G).subtype_injective,hcard,hA] at hb
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hb

/-- The actual component has trivial center in the field range forced above. -/
theorem g2_center_eq_bot {K : Type*} [Group K] [Finite K]
    [Theory.GroupTheory.IsQuasisimple K]
    {n : ℕ} (hn : 4 ≤ n) (hm : ClassificationModels.IsG2At (K ⧸ center K) (2^n)) :
    center K = ⊥ := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  exact PerfectCentralCovering.center_eq_bot_of_centralQuotientEquiv
    (Atlas.G2.MultiplierOrdinary.even_universalProjection_ker_eq_bot_of_card_pow hF (by omega)) e


private def scalarNormalizer {F : Type*} [Field F] :
    Fˣ →* normalizer (unipotent (K := F) : Set (Model F)) :=
  ((torusHom (K := F)).comp (MonoidHom.inl Fˣ Fˣ)).codRestrict _ (fun a => by
    apply le_normalizer_iff.mpr (fun t ht u hu => torus_normalizes_unipotent ht hu)
    exact ⟨(a,1),rfl⟩)

private theorem g2_standard_index {F : Type*} [Field F] [Finite F] [CharP F 2]
    (A : Subgroup (Model F)) (hne : A ≠ ⊥)
    (hAZ : A ≤ (center (unipotent (K := F))).map unipotent.subtype) :
    Nat.card F - 1 ≤ ((centralizer (A : Set (Model F))).subgroupOf
      (normalizer (unipotent (K := F) : Set (Model F)))).index := by
  let C := (centralizer (A : Set (Model F))).subgroupOf
    (normalizer (unipotent (K := F) : Set (Model F)))
  obtain ⟨a,ha,hane⟩ := A.bot_or_exists_ne_one.resolve_left hne
  have hroot := hAZ ha
  rw [unipotent_center] at hroot
  obtain ⟨c,hc⟩ := hroot
  have hc0 : c.toAdd ≠ 0 := by
    intro h0
    apply hane
    rw [←hc]
    change rootA c.toAdd = 1
    rw [h0,rootA_zero]
  have hk : C.comap (scalarNormalizer (F := F)) = ⊥ := by
    apply bot_unique
    intro t ht
    have hcomm := mem_centralizer_iff.mp ht a ha
    change a * torus t 1 = torus t 1 * a at hcomm
    have hfix : torus t 1 * a * (torus t 1)⁻¹ = a :=
      (mul_inv_eq_iff_eq_mul).mpr hcomm.symm
    rw [←hc] at hfix
    change torus t 1 * rootA c.toAdd * (torus t 1)⁻¹ = rootA c.toAdd at hfix
    rw [torus_rootA] at hfix
    have he : (t : F) * c.toAdd = c.toAdd := by
      simpa using rootA_injective hfix
    exact Units.ext (mul_right_cancel₀ hc0 (he.trans (one_mul _).symm))
  have hi := index_comap_le C (scalarNormalizer (F := F))
  rw [hk,index_bot,Nat.card_units] at hi
  exact hi

private theorem centralizer_map_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (A : Subgroup G) :
    (centralizer (A : Set G)).map e.toMonoidHom = centralizer (A.map e.toMonoidHom : Set H) := by
  apply le_antisymm (map_centralizer_le_centralizer_image (A : Set G) e.toMonoidHom)
  intro x hx
  obtain ⟨y,rfl⟩ := e.surjective x
  refine ⟨y,?_,rfl⟩
  intro a ha
  apply e.injective
  simpa only [map_mul] using hx (e a) (mem_map_of_mem e.toMonoidHom ha)

/-- The actual G₂ Sylow normalizer has index at least fifteen over the
centralizer of the moving sixteen. -/
theorem g2_normalizer_index {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassificationModels.IsG2At G (2^n))
    (P : Sylow 2 G) (A : Subgroup G) (hA : Nat.card A = 16)
    (hAP : A ≤ (P : Subgroup G))
    (hi : ((centralizer (A : Set G)).subgroupOf (P : Subgroup G)).index ≤ 2) :
    15 ≤ ((centralizer (A : Set G)).subgroupOf (normalizer (P : Set G))).index := by
  have hAZ := g2_centralizes hn hm P A hAP hi
  have hn4 := g2_degree_ge_four hn hm P A hA hAP hi
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let P₀ := (sylow (F := F)).mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G P₀ P
  let f := e.symm.trans (MulAut.conj g)
  have hP : (unipotent (K := F)).map f.toMonoidHom = (P : Subgroup G) := by
    have hh := congrArg Sylow.toSubgroup hg
    change ((unipotent (K := F)).map e.symm.toMonoidHom).map
      (MulAut.conj g).toMonoidHom = (P : Subgroup G) at hh
    change (unipotent (K := F)).map ((MulAut.conj g).toMonoidHom.comp e.symm.toMonoidHom) = _
    rw [←map_map]
    exact hh
  have hZ : ((center (unipotent (K := F))).map unipotent.subtype).map f.toMonoidHom =
      (center P).map (P : Subgroup G).subtype := by
    rw [map_embeddedCenter _ _ f.injective,hP]
  let A₀ := A.map f.symm.toMonoidHom
  have hA₀ : A₀.map f.toMonoidHom = A := by
    change (A.map f.symm.toMonoidHom).map f.toMonoidHom = A
    rw [map_map]
    rw [show f.toMonoidHom.comp f.symm.toMonoidHom = MonoidHom.id _ by
      ext x; exact f.apply_symm_apply x, map_id]
  have hAZ₀ : A₀ ≤ (center (unipotent (K := F))).map unipotent.subtype := by
    apply (map_le_map_iff_of_injective (f := f.toMonoidHom) f.injective).mp
    rw [hA₀,hZ]
    exact hAZ
  have hcard : Nat.card A₀ = 16 := (card_map_of_injective f.symm.injective).trans hA
  have hne : A₀ ≠ ⊥ := by intro hh; rw [hh,card_bot] at hcard; omega
  have hb := g2_standard_index A₀ hne hAZ₀
  have hlarge : 16 ≤ Nat.card F := hF ▸ Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn4
  have hN : (normalizer (unipotent (K := F) : Set (Model F))).map f.toMonoidHom =
      normalizer (P : Set G) := by
    rw [map_equiv_normalizer_eq,hP]
    rfl
  have hC : (centralizer (A₀ : Set (Model F))).map f.toMonoidHom = centralizer (A : Set G) := by
    rw [centralizer_map_equiv,hA₀]
  change 15 ≤ (centralizer (A : Set G)).relIndex (normalizer (P : Set G))
  rw [←hC,←hN,relIndex_map_map_of_injective _ _ f.injective]
  exact (by omega : 15 ≤ Nat.card F - 1).trans hb

/-- The surviving G₂ component is normal relative to its actual SQTK overgroup. -/
theorem g2_component_normal {G : Type*} [Group G] [Finite G]
    (H K : Subgroup G) (hK : Theory.GroupTheory.IsComponentIn K H)
    (hH : IsStronglyQuasithin H) {n : ℕ} (hn : 4 ≤ n)
    (hm : ClassificationModels.IsG2At (K ⧸ center K) (2^n)) :
    (K.subgroupOf H).Normal := by
  let := hK.quasisimple
  have hz := g2_center_eq_bot hn hm
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let eK : K ≃* Model F := QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hz.symm).trans e)
  let e₀ := (subgroupOfEquivOfLe hK.1).trans eK
  have hz₀ : center (K.subgroupOf H) = ⊥ := by
    apply card_eq_one.mp
    rw [Nat.card_congr (centerCongr (subgroupOfEquivOfLe hK.1)).toEquiv,hz,card_bot]
  apply hK.2.normal_of_centerless_primeRank (p := 3) hz₀
  · rw [Theory.GroupTheory.primeRank_equiv 3 e₀]
    exact Atlas.G2.EvenThreeRank.two_le_primeRank
  · exact hH 3 Nat.prime_three (by decide)

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryG2Placement
