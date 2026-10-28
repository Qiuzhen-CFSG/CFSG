module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.LieParabolics.Linear.Inner
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.EndpointExtension
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FiveEndpointResidual
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree.Products
/-!
# The complete ordinary degree-five source-parabolic family

The original outer Sylow action reverses the marked flag. The already
constructed endpoint parabolic escapes M_L, so the three invariant flag
possibilities identify it with the literal endpoint orbit. Its extension
by N_S(L) has quotient S₃ ≀ C₂ over its own two-core. A symbolic element
of its two-residual has nonidentity sixth power, excluding a central
product of A₃ blocks. The singleton endpoint family generates with M_L.
For inner actions, reuse the two endpoint minimal parabolics.

This proves OrdinaryLinearParabolicGeometry for degree five at the same
original marking, without placement or exchanged-selection hypotheses.
The marker application retains d, Z₁, row and both source primes. Degree
four's outer source-family construction and cubic Ru remain with
qt-e-15122-ordinary-pre-exclusion; source placement and final nonblock
premise discharge remain with qt-e-15122-pre-exclusion-catalogue.

Source: Aschbacher--Smith 15.1.22(7), printed pp.1099--1100,
refs/quasithin.pdf. All quotient and residual conventions are literal.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

private theorem linear_embedded_center_centralizer
    {C : Type*} [Group C] (f : C →* G) (hf : Function.Injective f)
    (U : Subgroup C) (hU : U.map f = d.SL) :
    (centralizer ((center U).map U.subtype : Set C)).map f ≤
      centralizer ((center d.SL).map d.SL.subtype : Set G) := by
  rintro _ ⟨x,hx,rfl⟩
  apply mem_centralizer_iff.mpr
  rintro _ ⟨z,hz,rfl⟩
  obtain ⟨u,hu,heu⟩ := (show (z : G) ∈ U.map f from hU.symm ▸ z.property)
  have huc : (⟨u,hu⟩ : U) ∈ center U := by
    apply mem_center_iff.mpr
    intro v
    apply Subtype.ext
    apply hf
    change f ((v : C) * u) = f (u * (v : C))
    rw [map_mul,map_mul,heu]
    have hv : f v ∈ d.SL := hU ▸ mem_map_of_mem f v.property
    exact congrArg Subtype.val (mem_center_iff.mp hz (⟨f v,hv⟩ : d.SL))
  have hc := (mem_centralizer_iff.mp hx) u (mem_map_of_mem U.subtype huc)
  change (z : G) * f x = f x * z
  rw [←heu,←map_mul,←map_mul,hc]

omit [Finite G] in
private theorem inner_normalizer_mem_product {A : Subgroup G}
    (x : normalizer (A : Set G))
    (hi : A.normalizerMonoidHom x ∈ MulAut.innerSubgroup A) :
    (x : G) ∈ A ⊔ centralizer (A : Set G) := by
  obtain ⟨a,ha⟩ := hi
  let aN : normalizer (A : Set G) := ⟨a,A.le_normalizer a.property⟩
  have haN : A.normalizerMonoidHom aN = MulAut.conj a := by ext y; rfl
  have hk : aN⁻¹*x ∈ A.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker,map_mul,map_inv,haN,ha,inv_mul_cancel]
  rw [normalizerMonoidHom_ker] at hk
  have hm := (A ⊔ centralizer (A : Set G)).mul_mem
    (mem_sup_left a.property) (mem_sup_right (show (a : G)⁻¹*x ∈ centralizer (A : Set G) from hk))
  simpa only [mul_inv_cancel_left] using hm

private theorem not_aThreeProduct_of_residual_image
    (P : Subgroup G) {H : Type*} [Group H]
    (f : P →* H) (hf : Function.Surjective f)
    (hH : ∃ y ∈ pResidual 2 H, y^6 ≠ 1) : ¬ IsAThreeProduct P := by
  rintro ⟨F,hF,hc,hgen⟩
  obtain ⟨y,hy,hy6⟩ := hH
  rw [←map_pResidual_of_surjective 2 f hf] at hy
  obtain ⟨x,hx,rfl⟩ := hy
  apply hy6
  rw [←map_pow,ChapterC.alternatingThree_product_pow_six F
    (fun A hA => (hF A hA).2) hc (hgen.symm ▸ hx),map_one]

/-- The graph-action endpoint in the ordinary degree-five component belongs
 to the literal source family and generates with the original M_L. -/
theorem PreExclusionSource.binaryLinear_five_outer_source_parabolic
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : d.L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (hout : ¬ d.S ≤ d.L ⊔ centralizer (d.L : Set G)) :
    ∃ B : Subgroup G, d.IsSourceParabolic B ∧ d.ML ⊔ B = d.L := by
  classical
  have hnL := d.S_le_G1.trans (s.binaryLinear_normal (h := h) hG hL (.inr rfl) e)
  have hcore : pCore 2 d.L = ⊥ := by
    rw [←(s.ordinary hL).center_eq]
    apply (center d.L).eq_bot_iff_card.mpr
    rw [Nat.card_congr (centerCongr e).toEquiv,
      (Theory.SpecificGroups.BinaryComponentResidual.linear (.inr rfl)).1,card_bot]
  let e0 : (d.L ⧸ pCore 2 d.L) ≃* Matrix.SpecialLinearGroup (Fin (4+1)) (ZMod 2) :=
    ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot).trans e
  let q := coreFlagMap d.L e0
  have hqi : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).mp
    ((coreFlagMap_ker d.L e0).trans hcore)
  let a : d.L ≃* LinearGroup 5 := MulEquiv.ofBijective q ⟨hqi,coreFlagMap_surjective d.L e0⟩
  let f := d.L.subtype.comp a.symm.toMonoidHom
  have hf : Function.Injective f := d.L.subtype_injective.comp a.symm.injective
  have hfq : f.comp q = d.L.subtype := by
    ext x
    exact congrArg Subtype.val (a.symm_apply_apply x)
  have hqf (x : LinearGroup 5) : q (a.symm x) = x := a.apply_symm_apply x
  have hr : f.range = d.L := by
    rw [MonoidHom.range_comp,a.symm.toMonoidHom.range_eq_top_of_surjective a.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  obtain ⟨Q,hQ⟩ := s.component_sylow
  obtain ⟨b,hb,hctrl⟩ := exists_core_flag_control d.L d.S hnL Q hQ (.inr rfl) e0
  have ho : ∃ x : d.S, coreFlagAction d.L d.S hnL e0 x ∉ MulAut.innerSubgroup _ := by
    obtain ⟨x,hx,hxo⟩ := SetLike.not_le_iff_exists.mp hout
    refine ⟨⟨x,hx⟩,fun hi => hxo ?_⟩
    let α := d.L.normalizerMonoidHom ⟨x,hnL hx⟩
    have he : coreFlagAction d.L d.S hnL e0 ⟨x,hx⟩ = MulAut.congr a α := by
      apply MulEquiv.ext
      intro y
      obtain ⟨z,rfl⟩ := a.surjective y
      change _ = a (α (a.symm (a z)))
      rw [a.symm_apply_apply]
      exact (coreFlagAction_equivariant d.L d.S hnL e0 ⟨x,hx⟩ z).symm
    rw [he,←MulAut.map_innerSubgroup_congr a] at hi
    apply inner_normalizer_mem_product ⟨x,hnL hx⟩
    simpa only [MulEquiv.symm_apply_apply] using mem_map_equiv.mp hi
  have hselect := hctrl.resolve_left (fun hi => by
    obtain ⟨x,hx⟩ := ho
    exact hx (hi.1 x))
  obtain ⟨B,hflag,hSB,hnB,hfit,⟨eB⟩,hgen,houtB⟩ :=
    s.binaryLinear_endpoint_parabolic (h := h) hG hM hu hL (.inr rfl) e
  have hBL : B < d.L := hflag.1
  let U := Q.mapSurjective (f := q) (coreFlagMap_surjective d.L e0)
  have hQS : (Q : Subgroup d.L) = d.SL.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [hQ,map_subgroupOf_eq_of_le d.SL_le_L]
  have hbU : (U : Subgroup (LinearGroup 5)) = cutStabilizer b Set.univ := by
    change (Q : Subgroup d.L).map q = _
    rw [hQS]
    exact hb
  have hUf : (U : Subgroup (LinearGroup 5)).map f = d.SL := by
    change ((Q : Subgroup d.L).map q).map f = _
    rw [map_map,hfq,hQ]
  let C := cutStabilizer b {i : Fin 4 | i.val=0 ∨ i.val=3}
  have hCf : C.map f ≤ d.ML := by
    dsimp only [C]
    rw [←sylow_center_centralizer_eq_endCuts (by decide) U b hbU]
    exact (le_inf (hr ▸ map_le_range f _)
      (linear_embedded_center_centralizer f hf U hUf)).trans
      (s.linear_centralizer_le (h := h) hG hM hu hL (.inr rfl) e)
  have hlift (X : Subgroup (LinearGroup 5)) :
      EquivariantLift.lift d.L q X = X.map f := by
    have hsub : (X.map f).subgroupOf d.L = X.map a.symm.toMonoidHom := by
      rw [show f = d.L.subtype.comp a.symm.toMonoidHom from rfl,←map_map]
      change ((X.map a.symm.toMonoidHom).map d.L.subtype).comap d.L.subtype = _
      exact comap_map_eq_self_of_injective d.L.subtype_injective _
    have hi : ((X.map f).subgroupOf d.L).map q = X := by
      rw [hsub,map_map]
      have he : q.comp a.symm.toMonoidHom = MonoidHom.id _ := by
        apply MonoidHom.ext
        intro y
        exact hqf y
      rw [he,map_id]
    have hh := EquivariantLift.lift_map_subgroupOf d.L q (X.map f)
      (hr ▸ map_le_range f X) (by rw [coreFlagMap_ker,hcore]; exact bot_le)
    rwa [hi] at hh
  have hE : B = EquivariantLift.lift d.L q
      (cutStabilizer b {i : Fin 4 | i.val=0 ∨ i.val=3}ᶜ) := by
    rcases hselect.2 B hSB hBL hnB with he | he | he
    · exact (houtB (he.symm ▸ (s.local_intersections (h := h) hG hu hM.1.2).2.1)).elim
    · exact (houtB (he.symm ▸ ((hlift C).symm ▸ hCf))).elim
    · exact he
  have hsn : d.sylowNormalizer = d.S := inf_eq_left.mpr hnL
  refine ⟨B,⟨hBL.le,inf_le_left.trans hnB,hfit,?_,?_⟩,hgen⟩
  · right
    rw [hsn]
    exact endpoint_extension_wreath d.L d.S hnL (T.isPGroup'.to_le d.S_le_T)
      Q hQ (.inr rfl) e0 b hb B hE hnB eB ho
  · let E := cutStabilizer b {i : Fin 4 | i.val=0 ∨ i.val=3}ᶜ
    have he : E.map f = B := (hlift E).symm.trans hE.symm
    let eb : E ≃* B := (E.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr he)
    exact not_aThreeProduct_of_residual_image B eb.symm.toMonoidHom eb.symm.surjective
      (five_endpoint_residual_not_exponent_six b)

/-- The full degree-five source family under the same original marking.
 Inner actions use the two nodes; graph actions use the endpoint orbit. -/
theorem PreExclusionSource.binaryLinear_five_parabolic_geometry
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : d.L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
    Nonempty (d.OrdinaryLinearParabolicGeometry e) := by
  by_cases hi : d.S ≤ d.L ⊔ centralizer (d.L : Set G)
  · exact s.binaryLinear_inner_parabolic_geometry (h := h) hG hM hu hL (.inr rfl) e hi
  · obtain ⟨B,hB,hgen⟩ := s.binaryLinear_five_outer_source_parabolic (h := h) hG hM hu hL e hi
    refine ⟨⟨{B},?_,?_,?_⟩⟩
    · intro P hP
      obtain rfl := Set.mem_singleton_iff.mp hP
      exact hB
    · simpa only [csSup_singleton] using hgen
    · exact fun K hK hlt => s.linear_flag_overgroup (h := h) (by decide) e K hK hlt

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The complete degree-five source family is available at the original marker,
 retaining the same component, prime, row, Z₁ and model isomorphism. -/
theorem PreparedChosenModule.source_preExclusion_binaryLinear_five_geometry
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (IsComponent d.G1 (d.L.subgroupOf d.G1) →
        ∀ e : d.L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2),
          Nonempty (d.OrdinaryLinearParabolicGeometry e)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL e => s.binaryLinear_five_parabolic_geometry (h := h) hG hM hu hL e⟩

end CFSG.Quasithin.Chapter15.Section01
