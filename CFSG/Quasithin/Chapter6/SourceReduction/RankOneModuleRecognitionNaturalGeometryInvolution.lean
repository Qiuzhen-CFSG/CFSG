module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryHyperplanes
public import Theory.GroupTheory.TwoFixedLinesIrreducible
public import Theory.GroupTheory.Commutator.SmallNormalizedImage

/-!
# The common involution in the odd critical geometry

The natural action is transitive on nonzero vectors and its Sylow-line
normalizer is transitive on the nonzero line vectors. Hence an involution
centralizer is transitive on the conjugate natural layers and lines
containing that involution. Transporting a Sylow central element along
the line gives an ambient Sylow in the centralizer which still normalizes
the original layer. Its two-core therefore normalizes every such layer.

At parameter two, B.2.14 applied after quotienting by the common
involution puts the centralizer closure of the four-element line inside
the two-core and centralizes it modulo that involution. The exact
index-two neighbor calculation then forces both a moving natural layer
and the original layer to escape the two-core. These are the centralizer
and closure inputs to the remaining transvection argument; naturalness
is explicit and is discharged by the owner of source 6.1.27.

Source: Aschbacher–Smith, 6.1.19, printed pp.674–675.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open ConjugateFixedSpaces
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

omit [Finite G] in
/-- The actual natural action is transitive on nonidentity layer elements. -/
theorem natural_layer_point_transitive
    (hnat : IsNaturalModule L (layer L R) n)
    {x y : G} (hx : x ∈ layer L R) (hx1 : x ≠ 1)
    (hy : y ∈ layer L R) (hy1 : y ≠ 1) :
    ∃ l ∈ L, (MulAut.conj l) x = y := by
  obtain ⟨F, _, _, _, _, e, f, hf⟩ := hnat
  have hx0 : (f ⟨x,hx⟩).toAdd ≠ 0 := by
    intro hh
    apply hx1
    have he : f ⟨x,hx⟩ = 1 := Multiplicative.toAdd.injective hh
    exact congrArg Subtype.val (f.injective (he.trans f.map_one.symm))
  have hy0 : (f ⟨y,hy⟩).toAdd ≠ 0 := by
    intro hh
    apply hy1
    have he : f ⟨y,hy⟩ = 1 := Multiplicative.toAdd.injective hh
    exact congrArg Subtype.val (f.injective (he.trans f.map_one.symm))
  obtain ⟨g,hg⟩ := Matrix.SL2.exists_mulVec_eq F _ _ hx0 hy0
  obtain ⟨q,hq⟩ := e.surjective g
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  have hlg : e (QuotientGroup.mk' (pCore 2 L) l) = g := by rw [hl,hq]
  refine ⟨l,l.property,?_⟩
  have hh := hf l ⟨x,hx⟩
  rw [hlg] at hh
  change (f.symm (Multiplicative.ofAdd (g.val.mulVec (f ⟨x,hx⟩).toAdd)) : G) = _ at hh
  rw [hg,ofAdd_toAdd,f.symm_apply_apply] at hh
  exact hh.symm

/-- The natural-line normalizer inside L is transitive on its nonidentity
elements, using the same ambient conjugation action as the layer model. -/
theorem natural_line_point_transitive
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    {x y : G} (hx : x ∈ ZS (T : Subgroup G) L R) (hx1 : x ≠ 1)
    (hy : y ∈ ZS (T : Subgroup G) L R) (hy1 : y ≠ 1) :
    ∃ l ∈ L ⊓ normalizer (ZS (T : Subgroup G) L R : Set G),
      (MulAut.conj l) x = y := by
  have hZcard := (hnat.sylow_intersection_geometry T h.sylow_normalizes_L).1
  obtain ⟨F, _, _, _, hF, e, f, hf⟩ := hnat
  let W := sylowSpace (T : Subgroup G) e
  have hW : W.toAddSubgroup = coordinateSpace f (ZS (T : Subgroup G) L R) :=
    AddSubgroup.ext (mem_sylowSpace_iff (T : Subgroup G) e f hf)
  have hc : Nat.card W = Nat.card F := by
    change Nat.card W.toAddSubgroup = Nat.card F
    rw [hW,coordinateSpace_card f (show ZS (T : Subgroup G) L R ≤ layer L R from inf_le_left),hF]
    exact hZcard
  have hd : Module.finrank F W = 1 := by
    apply Nat.pow_right_injective (Finite.one_lt_card (α := F))
    change Nat.card F ^ Module.finrank F W = Nat.card F ^ 1
    rw [← Module.natCard_eq_pow_finrank,hc,pow_one]
  let v := (f ⟨x,hx.1⟩).toAdd
  let w := (f ⟨y,hy.1⟩).toAdd
  have hv : v ∈ W := by
    change v ∈ W.toAddSubgroup
    rw [hW]
    simpa [v] using hx
  have hw : w ∈ W := by
    change w ∈ W.toAddSubgroup
    rw [hW]
    simpa [w] using hy
  have hv0 : v ≠ 0 := by
    intro hh
    apply hx1
    have he : f ⟨x,hx.1⟩ = 1 := Multiplicative.toAdd.injective hh
    exact congrArg Subtype.val (f.injective (he.trans f.map_one.symm))
  have hw0 : w ≠ 0 := by
    intro hh
    apply hy1
    have he : f ⟨y,hy.1⟩ = 1 := Multiplicative.toAdd.injective hh
    exact congrArg Subtype.val (f.injective (he.trans f.map_one.symm))
  obtain ⟨g,hg⟩ := Matrix.SL2.exists_mulVec_eq F v w hv0 hw0
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hd hv hv0
  have hmap : W.map (Matrix.SpecialLinearGroup.toLin' g).toLinearMap ≤ W := by
    rw [hspan,Submodule.map_span,Set.image_singleton]
    apply Submodule.span_le.mpr
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    change g.val.mulVec v ∈ Submodule.span F {v}
    rw [← hspan,hg]
    exact hw
  obtain ⟨q,hq⟩ := e.surjective g
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  have hlg : e (QuotientGroup.mk' (pCore 2 L) l) = g := by rw [hl,hq]
  refine ⟨l,⟨l.property,?_⟩,?_⟩
  · apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨z,hz,rfl⟩
      let t := (f ⟨z,hz.1⟩).toAdd
      have ht : t ∈ W := by
        change t ∈ W.toAddSubgroup
        rw [hW]
        simpa [t] using hz
      have him := hmap (show g.val.mulVec t ∈ W.map (Matrix.SpecialLinearGroup.toLin' g).toLinearMap
        from ⟨t,ht,rfl⟩)
      change g.val.mulVec t ∈ W.toAddSubgroup at him
      rw [hW] at him
      have hh := hf l ⟨z,hz.1⟩
      rw [hlg] at hh
      change (f.symm (Multiplicative.ofAdd (g.val.mulVec t)) : G) ∈ ZS (T : Subgroup G) L R at him
      change (f.symm (Multiplicative.ofAdd (g.val.mulVec t)) : G) = (l : G)*z*(l : G)⁻¹ at hh
      change (l : G)*z*(l : G)⁻¹ ∈ ZS (T : Subgroup G) L R
      rwa [hh] at him
    · exact (card_map_of_injective (MulAut.conj (l : G)).injective).ge
  · have hh := hf l ⟨x,hx.1⟩
    rw [hlg] at hh
    change (f.symm (Multiplicative.ofAdd (g.val.mulVec v)) : G) = _ at hh
    rw [hg] at hh
    simp only [w,ofAdd_toAdd,f.symm_apply_apply] at hh
    exact hh.symm

omit [Finite G] in
private theorem centralizer_transitive_of_point_transitive
    (B : Subgroup G) {z : G} (_hz : z ∈ B) (hz1 : z ≠ 1)
    (ht : ∀ y ∈ B, y ≠ 1 → ∃ l ∈ normalizer (B : Set G), (MulAut.conj l) z = y)
    {a : G} (hza : z ∈ B.map (MulAut.conj a).toMonoidHom) :
    ∃ c ∈ centralizer ({z} : Set G),
      B.map (MulAut.conj a).toMonoidHom = B.map (MulAut.conj c).toMonoidHom := by
  obtain ⟨y,hy,hay⟩ := hza
  have hy1 : y ≠ 1 := by
    intro he
    apply hz1
    simpa [he] using hay.symm
  obtain ⟨l,hl,hlz⟩ := ht y hy hy1
  refine ⟨a*l,?_,?_⟩
  · apply mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      (a*l)*z*(a*l)⁻¹ = (MulAut.conj a) ((MulAut.conj l) z) := by
        simp only [MulAut.conj_apply]; group
      _ = z := by rw [hlz]; exact hay
  · have he : B.map (MulAut.conj (a*l)).toMonoidHom =
        (B.map (MulAut.conj l).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
      rw [map_map]
      congr 1
      ext b
      change (a*l)*b*(a*l)⁻¹ = a*(l*b*l⁻¹)*a⁻¹
      group
    have hn : B.map (MulAut.conj l).toMonoidHom = B := mem_normalizer_iff_map_conj_eq.mp hl
    rw [he,hn]

omit [Finite G] in
/-- The centralizer of a nonidentity natural vector is transitive on the
conjugate natural modules containing that vector, with literal conjugators. -/
theorem natural_layer_centralizer_transitive
    (hnat : IsNaturalModule L (layer L R) n)
    {z a : G} (hz : z ∈ layer L R) (hz1 : z ≠ 1)
    (hza : z ∈ (layer L R).map (MulAut.conj a).toMonoidHom) :
    ∃ c ∈ centralizer ({z} : Set G),
      (layer L R).map (MulAut.conj a).toMonoidHom =
        (layer L R).map (MulAut.conj c).toMonoidHom := by
  apply centralizer_transitive_of_point_transitive (layer L R) hz hz1 ?_ hza
  intro y hy hy1
  obtain ⟨l,hl,he⟩ := natural_layer_point_transitive hnat hz hz1 hy hy1
  exact ⟨l,normalizer_commutator_ge_right R L hl,he⟩

/-- The analogous centralizer transitivity for the natural Sylow line. -/
theorem natural_line_centralizer_transitive
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    {z a : G} (hz : z ∈ ZS (T : Subgroup G) L R) (hz1 : z ≠ 1)
    (hza : z ∈ (ZS (T : Subgroup G) L R).map (MulAut.conj a).toMonoidHom) :
    ∃ c ∈ centralizer ({z} : Set G),
      (ZS (T : Subgroup G) L R).map (MulAut.conj a).toMonoidHom =
        (ZS (T : Subgroup G) L R).map (MulAut.conj c).toMonoidHom := by
  apply centralizer_transitive_of_point_transitive (ZS (T : Subgroup G) L R) hz hz1 ?_ hza
  intro y hy hy1
  obtain ⟨l,hl,he⟩ := natural_line_point_transitive h hnat hz hz1 hy hy1
  exact ⟨l,hl.2,he⟩

/-- Every nonidentity element of Z_S is central in an ambient Sylow which
still contains and normalizes Z_S and normalizes the original natural layer. -/
theorem natural_line_central_sylow
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    {z : G} (hz : z ∈ ZS (T : Subgroup G) L R) (hz1 : z ≠ 1) :
    ∃ P : Sylow 2 G,
      (P : Subgroup G) ≤ centralizer ({z} : Set G) ∧
      ZS (T : Subgroup G) L R ≤ P ∧
      (P : Subgroup G) ≤ normalizer (ZS (T : Subgroup G) L R : Set G) ∧
      (P : Subgroup G) ≤ normalizer (layer L R : Set G) := by
  let := h.ZS_elementary
  obtain ⟨z₀,hz₀⟩ := ne_bot_iff_exists_ne_one.mp
    (inf_centralizer_ne_bot_of_pGroups (T : Subgroup G) (ZS (T : Subgroup G) L R)
      T.isPGroup' (IsElementaryAbelian.isPGroup 2 _) h.sylow_normalizes_ZS h.ZS_ne_bot)
  have hz₀1 : (z₀ : G) ≠ 1 := fun he => hz₀ (Subtype.ext he)
  obtain ⟨l,hl,he⟩ := natural_line_point_transitive h hnat z₀.property.1 hz₀1 hz hz1
  let P := T.mapSurjective (f := (MulAut.conj l).toMonoidHom) (MulAut.conj l).surjective
  have hZl : (ZS (T : Subgroup G) L R).map (MulAut.conj l).toMonoidHom = ZS (T : Subgroup G) L R :=
    mem_normalizer_iff_map_conj_eq.mp hl.2
  have hBl : (layer L R).map (MulAut.conj l).toMonoidHom = layer L R :=
    mem_normalizer_iff_map_conj_eq.mp (normalizer_commutator_ge_right R L hl.1)
  refine ⟨P,?_,?_,?_,?_⟩
  · rintro _ ⟨t,ht,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (MulAut.conj l) (z₀.property.2 t ht)
    simp only [map_mul,he] at hh
    exact hh
  · rw [←hZl]
    exact map_mono h.ZS_le_T
  · have hh := (map_mono (f := (MulAut.conj l).toMonoidHom) h.sylow_normalizes_ZS).trans
      (le_normalizer_map (MulAut.conj l).toMonoidHom)
    rwa [hZl] at hh
  · have hh := (map_mono (f := (MulAut.conj l).toMonoidHom) h.sylow_normalizes_layer).trans
      (le_normalizer_map (MulAut.conj l).toMonoidHom)
    rwa [hBl] at hh

/-- The involution centralizer has characteristic two, and its two-core
normalizes every conjugate natural layer containing that involution. -/
theorem natural_line_centralizer_core_geometry
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    {z : G} (hz : z ∈ ZS (T : Subgroup G) L R) (hz1 : z ≠ 1) :
    centralizer ({z} : Set G) ∈ Chapter1.He G ∧
      ∀ a : G, z ∈ (layer L R).map (MulAut.conj a).toMonoidHom →
        (centralizer ({z} : Set G)).pCoreIn 2 ≤
          normalizer ((layer L R).map (MulAut.conj a).toMonoidHom : Set G) := by
  obtain ⟨P,hPC,hZP,hPZ,hPB⟩ := natural_line_central_sylow h hnat hz hz1
  let C := centralizer ({z} : Set G)
  let := h.ZS_elementary
  have ho : orderOf z = 2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian z hz) hz1
  have hC : C ∈ Chapter1.He G := Chapter1.twoLocal_mem_He_of_sylow_le P
    (h.simpleQTKE.evenCharacteristic P) (isTwoLocal_involution_centralizer ho) hPC
  have hQP : C.pCoreIn 2 ≤ (P : Subgroup G) := by
    have hh := pCoreIn_le_sylow C (P.subtype hPC)
    change C.pCoreIn 2 ≤ ((P : Subgroup G).subgroupOf C).map C.subtype at hh
    rwa [map_subgroupOf_eq_of_le hPC] at hh
  have hCN : C ≤ normalizer (C.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
      using (pCore 2 C).le_normalizer_map C.subtype
  refine ⟨hC,?_⟩
  intro a hza
  obtain ⟨c,hc,he⟩ := natural_layer_centralizer_transitive hnat hz.1 hz1 hza
  rw [he]
  have hQc : (C.pCoreIn 2).map (MulAut.conj c).toMonoidHom = C.pCoreIn 2 :=
    mem_normalizer_iff_map_conj_eq.mp (hCN hc)
  have hh := (map_mono (f := (MulAut.conj c).toMonoidHom) (hQP.trans hPB)).trans
    (le_normalizer_map (MulAut.conj c).toMonoidHom)
  rwa [hQc] at hh

/-- For the four-element natural Sylow line, its closure under an
involution centralizer lies in that centralizer's two-core and is central
in the two-core modulo the same involution. This is the B.2.14 step in
the parameter-two part of 6.1.19. -/
theorem natural_four_line_centralizer_closure
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n) (hn : n = 2)
    {z : G} (hz : z ∈ ZS (T : Subgroup G) L R) (hz1 : z ≠ 1) :
    conjugateSpanBy (ZS (T : Subgroup G) L R) (centralizer ({z} : Set G)) ≤
        (centralizer ({z} : Set G)).pCoreIn 2 ∧
      ⁅conjugateSpanBy (ZS (T : Subgroup G) L R) (centralizer ({z} : Set G)),
        (centralizer ({z} : Set G)).pCoreIn 2⁆ ≤ zpowers z := by
  let C := centralizer ({z} : Set G)
  let B := (ZS (T : Subgroup G) L R).subgroupOf C
  have hzC : z ∈ C := mem_centralizer_singleton_iff.mpr rfl
  let Z := zpowers (⟨z,hzC⟩ : C)
  have hZc : Z ≤ center C := by
    apply zpowers_le.mpr
    apply mem_center_iff.mpr
    intro c
    exact Subtype.ext (mem_centralizer_singleton_iff.mp c.property)
  let : Z.Normal := ⟨fun x hx c => by
    rw [mem_center_iff.mp (hZc hx) c,mul_inv_cancel_right]
    exact hx⟩
  have hZB : Z ≤ B := zpowers_le.mpr hz
  have hBC : ZS (T : Subgroup G) L R ≤ C := by
    let := h.ZS_elementary
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      ((le_centralizer (ZS (T : Subgroup G) L R) hx) z hz).symm
  let := h.ZS_elementary
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hBC
  obtain ⟨P,hPC,hBP,hPN,_⟩ := natural_line_central_sylow h hnat hz hz1
  let P' := P.subtype hPC
  have hBP' : B ≤ P' := fun b hb => hBP hb
  have hPN' : (P' : Subgroup C) ≤ normalizer (B : Set C) := by
    apply le_normalizer_iff.mpr
    intro p hp b hb
    exact le_normalizer_iff.mp hPN p hp b hb
  have ho : orderOf z = 2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian z hz) hz1
  have hZcard : Nat.card Z = 2 := by
    rw [Nat.card_zpowers,Subgroup.orderOf_mk,ho]
  have hBcard : Nat.card B = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBC).toEquiv]
    have hh := (hnat.sylow_intersection_geometry T h.sylow_normalizes_L).1
    rw [hn] at hh
    exact hh
  let q := QuotientGroup.mk' Z
  have hq := QuotientGroup.mk'_surjective Z
  have hcard : Nat.card (B.map q) = 2 := by
    have hh := (q.ker.subgroupOf B).index_mul_card
    change q.ker.relIndex B * Nat.card (q.ker.subgroupOf B) = Nat.card B at hh
    rw [relIndex_ker,QuotientGroup.ker_mk',
      Nat.card_congr (subgroupOfEquivOfLe hZB).toEquiv,hZcard,hBcard] at hh
    omega
  have hc : ⁅B,(P' : Subgroup C)⁆ ≤ Z := by
    have hh := commutator_le_ker_of_normalized_image_card_le_two q (P' : Subgroup C) B hPN' hcard.le
    rwa [commutator_comm,QuotientGroup.ker_mk'] at hh
  have hchar : centralizer (pCore 2 C : Set C) ≤ pCore 2 C := Chapter1.mem_He_iff.mp
    (natural_line_centralizer_core_geometry h hnat hz hz1).1
  have hqchar : centralizer (pCore 2 (C ⧸ Z) : Set (C ⧸ Z)) ≤ pCore 2 (C ⧸ Z) :=
    q.centralizer_pCore_le_of_surjective_centralKernel hq (by rwa [QuotientGroup.ker_mk']) hchar
  let Pq := P'.mapSurjective hq
  have hBc : B.map q ≤ centralizer (Pq : Set (C ⧸ Z)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    change ⁅B.map q,(P' : Subgroup C).map q⁆ = ⊥
    rw [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
    exact hc
  let : IsElementaryAbelian 2 (B.map q) := IsElementaryAbelian.map q
  have hr := centralSeed_normalClosure_reduced Pq (B.map q) (map_mono hBP') hBc hqchar
  have he : (normalClosure (B : Set C)).map q = normalClosure (B.map q : Set (C ⧸ Z)) :=
    map_normalClosure (B : Set C) q hq
  rw [←he] at hr
  have hZQ : Z ≤ pCore 2 C := (hZc.trans (center_le_centralizer _)).trans hchar
  have hpre : (pCore 2 (C ⧸ Z)).comap q = pCore 2 C :=
    q.comap_pCore_of_ker_isPGroup hq (by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup.to_le hZQ)
  have hcore : normalClosure (B : Set C) ≤ pCore 2 C := by
    rw [←hpre]
    exact map_le_iff_le_comap.mp hr.le_pCore
  have hcentral : ⁅normalClosure (B : Set C),pCore 2 C⁆ ≤ Z := by
    have hmap : (pCore 2 C).map q ≤ pCore 2 (C ⧸ Z) := by
      rw [←hpre,map_comap_eq_self_of_surjective hq]
    have hzero : ⁅(normalClosure (B : Set C)).map q,(pCore 2 C).map q⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr
        (hr.le_centralizer_pCore.trans (centralizer_le hmap))
    rw [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at hzero
    exact hzero
  let Q := conjugateSpanBy (ZS (T : Subgroup G) L R) C
  have hspan : (normalClosure (B : Set C)).map C.subtype = Q := by
    apply le_antisymm
    · apply map_le_iff_le_comap.mpr
      let : (Q.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer
        (le_normalizer_conjugateSpanBy _ _)
      change normalClosure (B : Set C) ≤ Q.subgroupOf C
      exact normalClosure_le_normal (fun b hb => le_conjugateSpanBy _ _ hb)
    · change conjugateSpanBy (ZS (T : Subgroup G) L R) C ≤ _
      rw [conjugateSpanBy_eq_iSup_conj]
      apply iSup_le
      intro c
      rintro _ ⟨b,hb,rfl⟩
      refine ⟨c*⟨b,hBC hb⟩*c⁻¹,?_,rfl⟩
      exact (inferInstance : (normalClosure (B : Set C)).Normal).conj_mem
        _ (le_normalClosure hb) c
  refine ⟨?_,?_⟩
  · change Q ≤ C.pCoreIn 2
    rw [←hspan]
    exact map_mono hcore
  · have hh := map_mono (f := C.subtype) hcentral
    rw [map_commutator,hspan] at hh
    rw [show Z.map C.subtype = zpowers z by exact C.subtype.map_zpowers ⟨z,hzC⟩] at hh
    exact hh

namespace NaturalEscapeGraph.OddConfiguration
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)

/-- The common endpoint involution gives the actual characteristic-two
centralizer and line closure used in the transvection step. The original
natural layer and a displayed neighbor both escape that centralizer's
two-core. No abelianness or component classification is assumed here. -/
theorem exists_involution_centralizer_geometry
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M) :
    n = 2 ∧ ∃ z : G,
      z ∈ ZS (T : Subgroup G) L R ⊓
        (ZS (T : Subgroup G) L R).map (MulAut.conj d.representative).toMonoidHom ∧
      orderOf z = 2 ∧
      let C := centralizer ({z} : Set G)
      let Q := conjugateSpanBy (ZS (T : Subgroup G) L R) C
      C ∈ Chapter1.He G ∧ Q ≤ C.pCoreIn 2 ∧ ⁅Q,C.pCoreIn 2⁆ ≤ zpowers z ∧
      ¬ layer L R ≤ C.pCoreIn 2 ∧
      ∃ a : G, z ∈ (layer L R).map (MulAut.conj a).toMonoidHom ∧
        ¬ (layer L R).map (MulAut.conj a).toMonoidHom ≤ C.pCoreIn 2 := by
  obtain ⟨hn,hi⟩ := d.parameter_and_intersection h hnat hE hs hNS
  obtain ⟨z,hz⟩ := ne_bot_iff_exists_ne_one.mp
    ((one_lt_card_iff_ne_bot _).mp (hi ▸ (by decide : 1 < 2)))
  have hz1 : (z : G) ≠ 1 := fun he => hz (Subtype.ext he)
  have ho : orderOf (z : G) = 2 := by
    let := h.ZS_elementary
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (z : G) z.property.1) hz1
  let C := centralizer ({(z : G)} : Set G)
  obtain ⟨hC,hall⟩ := natural_line_centralizer_core_geometry h hnat z.property.1 hz1
  obtain ⟨hQ,hcomm⟩ := natural_four_line_centralizer_closure h hnat hn z.property.1 hz1
  obtain ⟨a,k,hplace,hVA,hout,hYi,hFi,hEY,hVF,hYF⟩ :=
    d.intersecting_hyperplanes h hnat hE hs hNS
  let V := (layer L R).map (MulAut.conj (k : G)).toMonoidHom
  let E := (layer L R).map (MulAut.conj a).toMonoidHom
  have hZE : (ZS (T : Subgroup G) L R).map (MulAut.conj d.representative).toMonoidHom ≤ E :=
    hEY.symm.le.trans (le_normalizer_iff_commutator_le_left.mp inf_le_right)
  have hZV : ZS (T : Subgroup G) L R ≤ V := by
    have hHZ : d.H ≤ Subgroup.normalizer (ZS (T : Subgroup G) L R : Set G) := d.overgroup.trans
      (sup_le (Subgroup.centralizer_le_normalizer _) h.sylow_normalizes_ZS)
    have he : (ZS (T : Subgroup G) L R).map (MulAut.conj (k : G)).toMonoidHom =
        ZS (T : Subgroup G) L R := mem_normalizer_iff_map_conj_eq.mp (hHZ k.property)
    rw [←he]
    exact map_mono (show ZS (T : Subgroup G) L R ≤ layer L R from inf_le_left)
  have hzE : (z : G) ∈ E := hZE z.property.2
  have hzV : (z : G) ∈ V := hZV z.property.1
  have hEN : ¬ E ≤ C.pCoreIn 2 := by
    intro he
    have hEV : E ≤ Subgroup.normalizer (V : Set G) := he.trans (hall (k : G) hzV)
    have hf1 : (E ⊓ Subgroup.normalizer (V : Set G)).relIndex E = 1 :=
      relIndex_eq_one.mpr (le_inf le_rfl hEV)
    rw [hFi] at hf1
    norm_num at hf1
  have hBN : ¬ layer L R ≤ C.pCoreIn 2 := by
    intro hb
    obtain ⟨c,hc,he⟩ := natural_layer_centralizer_transitive hnat z.property.1.1 hz1 hzE
    apply hEN
    change (layer L R).map (MulAut.conj a).toMonoidHom ≤ C.pCoreIn 2
    rw [he]
    have hCN : C ≤ Subgroup.normalizer (C.pCoreIn 2 : Set G) := by
      simpa only [pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
        using (pCore 2 C).le_normalizer_map C.subtype
    have hh := map_mono (f := (MulAut.conj c).toMonoidHom) hb
    have hn : (C.pCoreIn 2).map (MulAut.conj c).toMonoidHom = C.pCoreIn 2 :=
      mem_normalizer_iff_map_conj_eq.mp (hCN hc)
    rwa [hn] at hh
  exact ⟨hn,z,z.property,ho,hC,hQ,hcomm,hBN,a,hzE,hEN⟩

end NaturalEscapeGraph.OddConfiguration

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
