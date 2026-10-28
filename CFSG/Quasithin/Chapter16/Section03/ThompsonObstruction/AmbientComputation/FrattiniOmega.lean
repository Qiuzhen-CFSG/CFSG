module

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.Contracts
public import Theory.Frattini.DihedralOmega

/-!
# The central Frattini omega in the compatible Thompson product

Given the independently constructed rank geometry and compatible product
J(T) = R × T_L × ⟨w⟩, the Frattini and omega computations are transported
through that specific product. Both dihedral factors contribute their central
involutions to the first omega; the order-two factor contributes nothing.
The larger dihedral Frattini subgroup is kept separate from its first omega.

This is a conditional helper for Aschbacher–Smith, printed p.1182 / PDF p.1199,
the calculation following Lemma 16.3.12. The source theorem's assembly owner
must construct RankGeometry and Decomposition from the original hypotheses.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation
open Subgroup Stellmacher ChapterB
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}

/-- The genuine D₈ component Sylow center has an ambient involution generator. -/
theorem center_component_generator (d : Prepared T z t L) (r : RankGeometry d) :
    ∃ v : G, orderOf v = 2 ∧ ambientCenter (componentSylow T L) = zpowers v := by
  obtain ⟨e⟩ := r.component_dihedral
  have hc : Nat.card (center (componentSylow T L)) = 2 := by
    rw [Nat.card_congr (centerCongr e).toEquiv]
    rw [show center (DihedralGroup 4) = zpowers (DihedralGroup.r 2) by
      simpa using DihedralFrattini.center_eq_half (n := 2) (by omega)]
    rw [Nat.card_zpowers]
    apply orderOf_eq_prime (by decide : (DihedralGroup.r 2 : DihedralGroup 4) ^ 2 = 1)
    decide
  have hca : Nat.card (ambientCenter (componentSylow T L)) = 2 := by
    rw [ambientCenter, Subgroup.card_map_of_injective (componentSylow T L).subtype_injective, hc]
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card'
    (G := ambientCenter (componentSylow T L)) 2 (by rw [hca])
  have hvG : orderOf (v : G) = 2 := by
    exact (orderOf_injective (ambientCenter (componentSylow T L)).subtype
      (ambientCenter (componentSylow T L)).subtype_injective v).trans hv
  refine ⟨v, hvG, ?_⟩
  symm
  apply eq_of_le_of_card_ge (zpowers_le.mpr v.property)
  rw [Nat.card_zpowers, hvG, hca]

/-- The entire Frattini subgroup retains the possibly larger Frattini of R. -/
theorem frattini_maxJ_eq (d : Prepared T z t L) (r : RankGeometry d)
    (c : Decomposition d) :
    (frattini (elementaryAbelianMaxJ (T : Subgroup G))).map
        (elementaryAbelianMaxJ (T : Subgroup G)).subtype =
      (frattini c.R).map c.R.subtype ⊔ ambientCenter (componentSylow T L) := by
  let C := componentSylow T L
  let W := zpowers c.w
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  have hR : IsPGroup 2 c.R := T.isPGroup'.of_injective
    (inclusion (c.R_le.trans inf_le_left)) (inclusion_injective _)
  have hC : IsPGroup 2 C := T.isPGroup'.of_injective
    (inclusion (show C ≤ (T : Subgroup G) from inf_le_left)) (inclusion_injective _)
  have hW : IsPGroup 2 W := T.isPGroup'.of_injective
    (inclusion (zpowers_le.mpr (candidate_mem_and_centralizes d c.candidate).1))
    (inclusion_injective _)
  obtain ⟨eC⟩ := r.component_dihedral
  have hCPhi : frattini C = center C :=
    DihedralFrattini.frattini_eq_center_of_equiv_four eC
  have hWPhi : frattini W = ⊥ := by
    let : IsElementaryAbelian 2 W :=
      IsElementaryAbelian.zpowers_of_pow_eq_one (c.involution ▸ pow_orderOf_eq_one c.w)
    let : Fact (IsPGroup 2 W) := ⟨hW⟩
    exact frattini_eq_bot_of_isElementaryAbelian (p := 2)
  let f : (c.R × C × W) →* G := J.subtype.comp c.product.toMonoidHom
  have hmap : (frattini (c.R × C × W)).map f = (frattini J).map J.subtype := by
    change (frattini (c.R × C × W)).map (J.subtype.comp c.product.toMonoidHom) = _
    rw [← map_map, frattini_map_equiv c.product]
  change (frattini J).map J.subtype = _
  rw [← hmap, frattini_prod hR (isPGroup_prod hC hW), frattini_prod hC hW, hCPhi, hWPhi]
  apply le_antisymm
  · rintro x ⟨⟨a, b, w⟩, hx, rfl⟩
    have hw : w = 1 := hx.2.2
    have ha : (a : G) ∈ (frattini c.R).map c.R.subtype := mem_map_of_mem c.R.subtype hx.1
    have hb : (b : G) ∈ ambientCenter C := mem_map_of_mem C.subtype hx.2.1
    change (c.product (a, b, w) : G) ∈ _
    rw [c.product_apply, hw, Subgroup.coe_one, mul_one]
    exact ((frattini c.R).map c.R.subtype ⊔ ambientCenter C).mul_mem
      ((le_sup_left : (frattini c.R).map c.R.subtype ≤ _) ha)
      ((le_sup_right : ambientCenter C ≤ _) hb)
  · apply sup_le
    · rintro x ⟨a, ha, rfl⟩
      refine ⟨(a, 1, 1), ⟨ha, (center C).one_mem, (⊥ : Subgroup W).one_mem⟩, ?_⟩
      change (c.product (a, 1, 1) : G) = (a : G)
      simp only [c.product_apply, Subgroup.coe_one, mul_one]
    · rintro x ⟨b, hb, rfl⟩
      refine ⟨(1, b, 1), ⟨(frattini c.R).one_mem, hb, (⊥ : Subgroup W).one_mem⟩, ?_⟩
      change (c.product (1, b, 1) : G) = (b : G)
      simp only [c.product_apply, Subgroup.coe_one, one_mul, mul_one]

/-- Multiplication compatibility identifies the two intrinsic centers in G. -/
theorem omegaFrattini_eq_centers (d : Prepared T z t L) (r : RankGeometry d)
    (c : Decomposition d) :
    thompsonFrattiniOmega (T : Subgroup G) =
      ambientCenter c.R ⊔ ambientCenter (componentSylow T L) := by
  let C := componentSylow T L
  let W := zpowers c.w
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  have hR : IsPGroup 2 c.R := T.isPGroup'.of_injective
    (inclusion (c.R_le.trans inf_le_left)) (inclusion_injective _)
  have hC : IsPGroup 2 C := T.isPGroup'.of_injective
    (inclusion (show C ≤ (T : Subgroup G) from inf_le_left)) (inclusion_injective _)
  have hW : IsPGroup 2 W := T.isPGroup'.of_injective
    (inclusion (zpowers_le.mpr (candidate_mem_and_centralizes d c.candidate).1))
    (inclusion_injective _)
  obtain ⟨n, hn, ⟨eR⟩⟩ := c.dihedral
  obtain ⟨eC⟩ := r.component_dihedral
  have hRO : (⊤ : Subgroup c.R).omegaFrattini = center c.R :=
    DihedralFrattini.omegaFrattini_top_of_equiv hn eR
  have hCO : (⊤ : Subgroup C).omegaFrattini = center C :=
    DihedralFrattini.omegaFrattini_top_of_equiv (n := 2) (by omega) eC
  have hWO : (⊤ : Subgroup W).omegaFrattini = ⊥ := by
    let : IsElementaryAbelian 2 W :=
      IsElementaryAbelian.zpowers_of_pow_eq_one (c.involution ▸ pow_orderOf_eq_one c.w)
    let : Fact (IsPGroup 2 W) := ⟨hW⟩
    rw [omegaFrattini_top, frattini_eq_bot_of_isElementaryAbelian (p := 2)]
    exact le_antisymm (omegaOneAmbient_le _) bot_le
  let f : (c.R × C × W) →* G := J.subtype.comp c.product.toMonoidHom
  have hmap : ((⊤ : Subgroup (c.R × C × W)).omegaFrattini).map f =
      thompsonFrattiniOmega (T : Subgroup G) := by
    change ((⊤ : Subgroup (c.R × C × W)).omegaFrattini).map
      (J.subtype.comp c.product.toMonoidHom) = J.omegaFrattini
    rw [← map_map, omegaFrattini_top_map_equiv c.product, omegaFrattini_map_subtype]
  rw [← hmap, omegaFrattini_top_prod hR (isPGroup_prod hC hW),
    omegaFrattini_top_prod hC hW, hRO, hCO, hWO]
  apply le_antisymm
  · rintro x ⟨⟨a, b, w⟩, hx, rfl⟩
    have hw : w = 1 := hx.2.2
    have ha : (a : G) ∈ ambientCenter c.R := mem_map_of_mem c.R.subtype hx.1
    have hb : (b : G) ∈ ambientCenter C := mem_map_of_mem C.subtype hx.2.1
    change (c.product (a, b, w) : G) ∈ _
    rw [c.product_apply, hw, Subgroup.coe_one, mul_one]
    exact (ambientCenter c.R ⊔ ambientCenter C).mul_mem ((le_sup_left : ambientCenter c.R ≤ _ ) ha)
      ((le_sup_right : ambientCenter C ≤ _) hb)
  · apply sup_le
    · rintro x ⟨a, ha, rfl⟩
      refine ⟨(a, 1, 1), ⟨ha, (center C).one_mem, (⊥ : Subgroup W).one_mem⟩, ?_⟩
      change (c.product (a, 1, 1) : G) = (a : G)
      simp only [c.product_apply, Subgroup.coe_one, mul_one]
    · rintro x ⟨b, hb, rfl⟩
      refine ⟨(1, b, 1), ⟨(center c.R).one_mem, hb, (⊥ : Subgroup W).one_mem⟩, ?_⟩
      change (c.product (1, b, 1) : G) = (b : G)
      simp only [c.product_apply, Subgroup.coe_one, one_mul, mul_one]


/-- The original central involution and the component center both lie in Z(T). -/
theorem centers_le_ambientCenter (d : Prepared T z t L) (r : RankGeometry d)
    (c : Decomposition d) :
    ambientCenter c.R ⊔ ambientCenter (componentSylow T L) ≤
      ambientCenter (T : Subgroup G) := by
  rw [c.center_eq]
  apply sup_le
  · apply zpowers_le.mpr
    refine ⟨⟨z, d.counterexample.localSetup.mem_sylow⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro a
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp
      (d.counterexample.localSetup.sylow_centralizes a.property)
  · intro x hx
    have hxT : x ∈ (T : Subgroup G) :=
      (show ambientCenter (componentSylow T L) ≤ (T : Subgroup G) from
        (map_subtype_le _).trans inf_le_left) hx
    refine ⟨⟨x, hxT⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro a
    apply Subtype.ext
    exact (r.component_center_central a.property x hx).symm

/-- The source's Frattini omega is the product of the two central involutions. -/
theorem exists_frattiniOmega_generator (d : Prepared T z t L) (r : RankGeometry d)
    (c : Decomposition d) :
    ∃ v : G, orderOf v = 2 ∧ ambientCenter (componentSylow T L) = zpowers v ∧
      thompsonFrattiniOmega (T : Subgroup G) = zpowers z ⊔ zpowers v := by
  obtain ⟨v, hv, hvC⟩ := center_component_generator d r
  refine ⟨v, hv, hvC, ?_⟩
  rw [omegaFrattini_eq_centers d r c, c.center_eq, hvC]

/-- The omega of the Thompson Frattini subgroup lies in the actual Sylow center. -/
theorem thompsonFrattiniOmega_le_ambientCenter (d : Prepared T z t L)
    (r : RankGeometry d) (c : Decomposition d) :
    thompsonFrattiniOmega (T : Subgroup G) ≤ ambientCenter (T : Subgroup G) := by
  rw [omegaFrattini_eq_centers d r c]
  exact centers_le_ambientCenter d r c

/-- Every element of T centralizes its Thompson Frattini omega. -/
theorem sylow_le_centralizer_thompsonFrattiniOmega (d : Prepared T z t L)
    (r : RankGeometry d) (c : Decomposition d) :
    (T : Subgroup G) ≤ centralizer (thompsonFrattiniOmega (T : Subgroup G) : Set G) := by
  intro a ha x hx
  obtain ⟨b, hb, rfl⟩ := thompsonFrattiniOmega_le_ambientCenter d r c hx
  exact (congrArg Subtype.val (mem_center_iff.mp hb ⟨a, ha⟩)).symm

end CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation
