module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree
public import CFSG.Quasithin.ChapterI.Section03.GeneralTwoOrbit.Source
public import CFSG.Quasithin.ChapterI.Section03.SylowAutomorphisms
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Theory.SpecificGroups.PairedFourCentralizerGeneration
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.CentralProduct

/-!
# The commuting component pair in the double cubic branch

Under the contradictory centralization of the second cubic module, two-layer
balance identifies the same component at each nonidentity cubic vector. The
original exchange and conjugation actors give the corresponding identifications
for the first module and its conjugate. Centralizer generation in the actual
A₆ or PSL₃(2) model then forces the component to normalize, and hence centralize,
its exchanged conjugate. The original Sylow generators normalize their direct
product and the exchange actor interchanges its factors.

The source-facing wrapper uses the ordinary-layer identity and trivial odd core
provided by the preceding component analysis. No balance or centralizer-generation
conclusion is included among its premises.

Source: Aschbacher–Smith, Lemma 2.4.34, printed p.548, through the construction of
I = KKˢT; the component models and layer identity are 2.4.32–33.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.DoubleA3.Noncentrality
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G]

abbrev centralizerTwoLayer (i : G) : Subgroup G :=
  (twoComponentLayer (centralizer ({i} : Set G))).map (centralizer ({i} : Set G)).subtype

omit [Finite G] in
private theorem twoLayer_map (e : G ≃* G) (i : G) :
    (centralizerTwoLayer i).map e.toMonoidHom = centralizerTwoLayer (e i) := by
  let a := (e.subgroupMap (centralizer ({i} : Set G))).trans
    (MulEquiv.subgroupCongr (CentralizerSmallKernelTransport.map_centralizer e i))
  have he : e.toMonoidHom.comp (centralizer ({i} : Set G)).subtype =
      (centralizer ({e i} : Set G)).subtype.comp a.toMonoidHom := by ext x; rfl
  change ((twoComponentLayer (centralizer ({i} : Set G))).map _).map _ = _
  rw [map_map,he,←map_map,map_twoComponentLayer_equiv]

omit [Finite G] in
private theorem centralizer_normalizes_twoLayer (i : G) :
    centralizer ({i} : Set G) ≤ normalizer (centralizerTwoLayer i : Set G) :=
  (centralizer ({i} : Set G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (twoComponentLayer _))

/-- Genuine two-layer balance on the intersection of two commuting involution
centralizers. No universal balance premise is assumed. -/
theorem component_le_twoLayer_of_commuting
    (i j : G) (hi : orderOf i = 2) (hij : Commute i j) (K : Subgroup G)
    (hK : IsComponentIn K (centralizer ({i} : Set G)))
    (hKj : K ≤ centralizer ({j} : Set G)) : K ≤ centralizerTwoLayer j := by
  let H := centralizer ({j} : Set G)
  let iH : H := ⟨i,mem_centralizer_singleton_iff.mpr hij.eq⟩
  let J := centralizer ({iH} : Set H)
  let K' := K.subgroupOf H
  have hKJ : K' ≤ J := by
    intro k hk
    exact mem_centralizer_singleton_iff.mpr (Subtype.ext
      (mem_centralizer_singleton_iff.mp (hK.1 hk)))
  let f : J →* centralizer ({i} : Set G) :=
    ((H.subtype.comp J.subtype).codRestrict _ (fun x =>
      mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))))
  have hcomp : IsComponent J (K'.subgroupOf J) := by
    refine ⟨hK.2.1.comap f,?_⟩
    let := hK.quasisimple
    exact IsQuasisimple.of_mulEquiv
      ((subgroupOfEquivOfLe hKJ).trans (subgroupOfEquivOfLe hKj)).symm
  have hp : IsPGroup 2 (zpowers iH) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,←Subgroup.orderOf_coe iH]
    simpa only [pow_one] using hi)
  have hc : centralizer (zpowers iH : Set H) = J := by
    rw [zpowers_eq_closure,centralizer_closure]
  have hb := ChapterI.LayerBalance.map_twoLayer_centralizer_le
    (ChapterI.SylowAutomorphisms.hasTwoSchreier H) (zpowers iH) hp
  rw [hc] at hb
  have hk := (map_mono (f := J.subtype)
    (ChapterI.Balance.ordinary_isTwoComponent hcomp).le_twoComponentLayer).trans hb
  rw [map_subgroupOf_eq_of_le hKJ] at hk
  have hh := map_mono (f := H.subtype) hk
  rwa [map_subgroupOf_eq_of_le hKj] at hh

private theorem alternatingFour_involution_conjugacy :
    ∀ a b : Equiv.Perm (Fin 4), a.sign = 1 → b.sign = 1 →
      a ^ 2 = 1 → b ^ 2 = 1 → a ≠ 1 → b ≠ 1 →
      ∃ t : Equiv.Perm (Fin 4), t.sign = 1 ∧ t * a * t⁻¹ = b := by
  decide +kernel

omit [Finite G] in
/-- The nonidentity vectors of the actual cubic block form one conjugacy class. -/
theorem cubic_module_conjugacy (L : Subgroup G) (hL : ChapterC.IsAlternatingBlock L 3)
    (a b : G) (ha : a ∈ sourceModule L) (hb : b ∈ sourceModule L)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) : ∃ t ∈ L, t*a*t⁻¹ = b := by
  let : IsElementaryAbelian 2 (sourceModule L) := hL.2.1.elementary.map L.subtype
  let aL : L := ⟨a,map_subtype_le _ ha⟩
  let bL : L := ⟨b,map_subtype_le _ hb⟩
  have ha2 : aL ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian a ha)
  have hb2 : bL ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian b hb)
  obtain ⟨e⟩ := hL.equiv_alternatingFour
  have hea : (e aL : Equiv.Perm (Fin 4)) ^ 2 = 1 := by
    exact congrArg Subtype.val (by simpa only [map_pow,map_one] using congrArg e ha2)
  have heb : (e bL : Equiv.Perm (Fin 4)) ^ 2 = 1 := by
    exact congrArg Subtype.val (by simpa only [map_pow,map_one] using congrArg e hb2)
  have hane : (e aL : Equiv.Perm (Fin 4)) ≠ 1 := by
    intro he
    have h0 : e aL = 1 := Subtype.ext he
    have h1 : aL = 1 := e.injective (h0.trans e.map_one.symm)
    exact ha1 (congrArg Subtype.val h1)
  have hbne : (e bL : Equiv.Perm (Fin 4)) ≠ 1 := by
    intro he
    have h0 : e bL = 1 := Subtype.ext he
    have h1 : bL = 1 := e.injective (h0.trans e.map_one.symm)
    exact hb1 (congrArg Subtype.val h1)
  obtain ⟨t,ht,he⟩ := alternatingFour_involution_conjugacy (e aL) (e bL)
    (Equiv.Perm.mem_alternatingGroup.mp (e aL).property)
    (Equiv.Perm.mem_alternatingGroup.mp (e bL).property) hea heb hane hbne
  let tA : alternatingGroup (Fin 4) := ⟨t,Equiv.Perm.mem_alternatingGroup.mpr ht⟩
  refine ⟨e.symm tA,(e.symm tA).property,?_⟩
  have he' : tA * e aL * tA⁻¹ = e bL := Subtype.ext he
  have hh := congrArg e.symm he'
  have hh' : e.symm tA * aL * (e.symm tA)⁻¹ = bL := by
    simpa only [map_mul,map_inv,e.symm_apply_apply] using hh
  exact congrArg Subtype.val hh'

/-- Balance and the cubic action identify the same layer at every nonidentity
vector of a cubic block centralizing the marked component. -/
theorem component_layer_on_cubic (L : Subgroup G) (hL : ChapterC.IsAlternatingBlock L 3)
    (i : G) (hi : orderOf i = 2) (hiU : i ∈ sourceModule L)
    (K : Subgroup G) (hK : IsComponentIn K (centralizer ({i} : Set G)))
    (hbase : K = centralizerTwoLayer i)
    (hcomm : sourceModule L ≤ centralizer (K : Set G)) :
    ∀ u ∈ sourceModule L, u ≠ 1 → K = centralizerTwoLayer u := by
  intro u hu hu1
  have hi1 : i ≠ 1 := by intro he;rw [he,orderOf_one] at hi;omega
  obtain ⟨a,ha,he⟩ := cubic_module_conjugacy L hL i u hiU hu hi1 hu1
  let : IsElementaryAbelian 2 (sourceModule L) := hL.2.1.elementary.map L.subtype
  let : CommGroup (sourceModule L) := IsMulCommutative.instCommGroup
  have hic : Commute i u := by
    exact congrArg Subtype.val (mul_comm (⟨i,hiU⟩ : sourceModule L) ⟨u,hu⟩)
  have hKu : K ≤ centralizer ({u} : Set G) := by
    intro k hk
    exact mem_centralizer_singleton_iff.mpr (hcomm hu k hk)
  have hle := component_le_twoLayer_of_commuting i u hi hic K hK hKu
  have hmap : K.map (MulAut.conj a).toMonoidHom = centralizerTwoLayer u := by
    rw [hbase,twoLayer_map]
    change centralizerTwoLayer (a*i*a⁻¹) = _
    rw [he]
  exact eq_of_le_of_card_ge hle (by
    rw [←hmap,card_map_of_injective (MulAut.conj a).injective])

variable {M : Subgroup G} {d : MinimalBlockSetup M} {T : Sylow 2 G}

/-- The actual cubic vectors and their original x-conjugates all select the
same conjugate component through the proved two-layer balance theorem. -/
theorem source_layers (c : SourcePairCoordinates d T) (g : SourceCentralizerGeometry c)
    (K : Subgroup G) (hK : IsComponentIn K (centralizer ({g.z₂} : Set G)))
    (hbase : K = centralizerTwoLayer g.z₂)
    (hcomm : c.U₂ ≤ centralizer (K : Set G)) :
    (∀ u ∈ c.U₂, u ≠ 1 → K = centralizerTwoLayer u) ∧
    (∀ u ∈ c.U₁, u ≠ 1 → K.map (MulAut.conj c.s⁻¹).toMonoidHom = centralizerTwoLayer u) ∧
    (∀ u ∈ c.V₁, u ≠ 1 → K.map (MulAut.conj c.s⁻¹).toMonoidHom = centralizerTwoLayer u) := by
  have hsecond := component_layer_on_cubic c.L c.cubic_second g.z₂ g.order_second
    g.second_mem K hK hbase hcomm
  have hsU : c.U₁.map (MulAut.conj c.s).toMonoidHom = c.U₂ :=
    (sourceModule_map_equiv (d.block.map d.H.subtype) (MulAut.conj c.s)).trans
      (congrArg sourceModule c.exchange)
  have hfirst (u : G) (hu : u ∈ c.U₁) (hu1 : u ≠ 1) :
      K.map (MulAut.conj c.s⁻¹).toMonoidHom = centralizerTwoLayer u := by
    let v := MulAut.conj c.s u
    have hv : v ∈ c.U₂ := hsU ▸ mem_map_of_mem (MulAut.conj c.s).toMonoidHom hu
    have hv1 : v ≠ 1 := fun he => hu1 ((MulAut.conj c.s).injective (he.trans (map_one _).symm))
    rw [hsecond v hv hv1,twoLayer_map]
    congr 1
    dsimp [v,MulAut.conj_apply]
    group
  have hz1 : g.z₁ ≠ 1 := by
    intro he
    have ho := g.order_first
    rw [he,orderOf_one] at ho
    omega
  have hcross := hfirst g.z₁ g.first_mem hz1
  have hxN : c.x ∈ normalizer (K.map (MulAut.conj c.s⁻¹).toMonoidHom : Set G) := by
    rw [hcross]
    exact centralizer_normalizes_twoLayer g.z₁ g.x_first
  refine ⟨hsecond,hfirst,?_⟩
  rintro v ⟨u,hu,rfl⟩ hv1
  have hu1 : u ≠ 1 := by intro he;apply hv1;rw [he,map_one]
  have hm := congrArg (fun A : Subgroup G => A.map (MulAut.conj c.x⁻¹).toMonoidHom)
    (hfirst u hu hu1)
  have hxmap : (K.map (MulAut.conj c.s⁻¹).toMonoidHom).map
      (MulAut.conj c.x⁻¹).toMonoidHom = K.map (MulAut.conj c.s⁻¹).toMonoidHom :=
    mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (K.map (MulAut.conj c.s⁻¹).toMonoidHom : Set G)).inv_mem hxN)
  rw [hxmap,twoLayer_map] at hm
  exact hm


omit [Finite G] in
private theorem simple_normalizer_centralizes (K L : Subgroup G) [IsSimpleGroup K]
    (hn : K ≤ normalizer (L : Set G)) (z : G) (hz : z ∈ K)
    (hzc : z ∈ centralizer (L : Set G)) (hz1 : z ≠ 1) :
    K ≤ centralizer (L : Set G) := by
  let C := (centralizer (L : Set G)).subgroupOf K
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    (hn.trans (normalizer_le_normalizer_centralizer L))
  rcases (inferInstance : C.Normal).eq_bot_or_eq_top with hb | ht
  · have hm : (⟨z,hz⟩ : K) ∈ C := hzc
    rw [hb] at hm
    exact (hz1 (congrArg Subtype.val (mem_bot.mp hm))).elim
  · intro k hk
    exact (show (⟨k,hk⟩ : K) ∈ C from ht ▸ mem_top _)

omit [Finite G] in
private theorem disjoint_of_simple_commuting (K L : Subgroup G) [IsSimpleGroup K]
    [Group.IsPerfect K] (hc : K ≤ centralizer (L : Set G)) : Disjoint K L := by
  have hz : center K = ⊥ := by
    rcases (inferInstance : (center K).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp hz)).elim
  apply disjoint_def.mpr
  intro x hx hy
  have hcenter : (⟨x,hx⟩ : K) ∈ center K := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hc y.property x hy).symm
  rw [hz] at hcenter
  exact congrArg Subtype.val (mem_bot.mp hcenter)

/-- Under the original contradictory centralization, the two marked component
conjugates commute and form a direct pair normalized by the actual Sylow T. -/
theorem commuting_components (c : SourcePairCoordinates d T) (g : SourceCentralizerGeometry c)
    (K : Subgroup G) (hK : IsComponentIn K (centralizer ({g.z₂} : Set G)))
    (hbase : K = centralizerTwoLayer g.z₂)
    (hfirst : d.block.map d.H.subtype ≤ K)
    (hmodel : Nonempty (K ≃* alternatingGroup (Fin 6)) ∨ Nonempty (K ≃* Matrix.PSL3Two.PSL))
    (hcomm : c.U₂ ≤ centralizer (K : Set G)) :
    let Ks := K.map (MulAut.conj c.s⁻¹).toMonoidHom
    K ≤ centralizer (Ks : Set G) ∧ Disjoint K Ks ∧ K ≠ Ks ∧
      (T : Subgroup G) ≤ normalizer (K ⊔ Ks : Subgroup G) ∧
      c.x ∈ normalizer (K : Set G) ∧ c.x ∈ normalizer (Ks : Set G) ∧
      K.map (MulAut.conj c.s).toMonoidHom = Ks ∧
      Ks.map (MulAut.conj c.s).toMonoidHom = K ∧ IsSimpleGroup K := by
  let Ks := K.map (MulAut.conj c.s⁻¹).toMonoidHom
  obtain ⟨h₂,h₁,hV⟩ := source_layers c g K hK hbase hcomm
  have hz1 : g.z₁ ≠ 1 := by
    intro he
    have ho := g.order_first
    rw [he,orderOf_one] at ho
    omega
  have hKs : Ks = centralizerTwoLayer g.z₁ := h₁ g.z₁ g.first_mem hz1
  have hnK : centralizer ({g.z₂} : Set G) ≤ normalizer (K : Set G) :=
    by rw [hbase]; exact centralizer_normalizes_twoLayer g.z₂
  have hnKs : centralizer ({g.z₁} : Set G) ≤ normalizer (Ks : Set G) :=
    by rw [hKs]; exact centralizer_normalizes_twoLayer g.z₁
  have hxK := hnK g.x_second
  have hxKs := hnKs g.x_first
  have hUK : c.U₁ ≤ K := (map_subtype_le _).trans hfirst
  have hVK : c.V₁ ≤ K := by
    rintro v ⟨u,hu,rfl⟩
    exact ((normalizer (K : Set G)).inv_mem hxK u).mp (hUK hu)
  have hUT : c.U₁ ≤ (T : Subgroup G) :=
    (c.first.module_le.trans inf_le_left).trans c.original.T_le
  have hVT : c.V₁ ≤ (T : Subgroup G) := by
    rintro v ⟨u,hu,rfl⟩
    exact ((T : Subgroup G).le_normalizer ((T : Subgroup G).inv_mem c.x_mem) u).mp (hUT hu)
  let U := c.U₁.subgroupOf K
  let V := c.V₁.subgroupOf K
  have hp : IsPGroup 2 (U ⊔ V : Subgroup K) :=
    (T.isPGroup'.comap_of_injective K.subtype K.subtype_injective).to_le
      (sup_le (fun u hu => hUT hu) (fun v hv => hVT hv))
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  let : IsElementaryAbelian 2 c.U₁ := c.cubic_first.2.1.elementary.map (d.block.map d.H.subtype).subtype
  let : IsElementaryAbelian 2 c.V₁ := IsElementaryAbelian.map (MulAut.conj c.x⁻¹).toMonoidHom
  have hU : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUK
  have hV' : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf hVK
  have hcU : Nat.card U = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUK).toEquiv).trans (c.first.cubic_module_card c.cubic_first)
  have hcV : Nat.card V = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hVK).toEquiv]
    exact (card_map_of_injective (MulAut.conj c.x⁻¹).injective).trans
      (c.first.cubic_module_card c.cubic_first)
  have hnoncomm : ¬ V ≤ centralizer (U : Set K) := by
    intro hh
    apply c.noncommuting
    intro v hv u hu
    exact congrArg Subtype.val (hh (show (⟨v,hVK hv⟩ : K) ∈ V from hv)
      ⟨u,hUK hu⟩ hu)
  have hgen := Theory.SpecificGroups.PairedFourCentralizerGeneration.eq_top_of_paired_four
    hmodel P U V ((normalizer (Ks : Set G)).subgroupOf K) hU hV' hcU hcV
      (le_sup_left.trans hP) (le_sup_right.trans hP) hnoncomm (by
        intro u hu hu1 k hk
        have huG : (u : G) ≠ 1 := fun he => hu1 (Subtype.ext he)
        have he : Ks = centralizerTwoLayer (u : G) := hu.elim
          (fun h => h₁ u h huG) (fun h => hV u h huG)
        rw [he]
        exact centralizer_normalizes_twoLayer (u : G)
          (mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
            (mem_centralizer_singleton_iff.mp hk))))
  have hKKs : K ≤ normalizer (Ks : Set G) := by
    intro k hk
    exact (show (⟨k,hk⟩ : K) ∈ (normalizer (Ks : Set G)).subgroupOf K from hgen ▸ mem_top _)
  let : IsSimpleGroup K := by
    rcases hmodel with he | he
    · obtain ⟨e⟩ := he
      let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
      exact e.isSimpleGroup
    · obtain ⟨e⟩ := he
      let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
      exact e.isSimpleGroup
  let := hK.quasisimple
  have hzc : g.z₁ ∈ centralizer (Ks : Set G) := by
    intro k hk
    have hh : k ∈ centralizer ({g.z₁} : Set G) := by
      rw [hKs] at hk
      exact (map_subtype_le _) hk
    exact mem_centralizer_singleton_iff.mp hh
  have hcentral := simple_normalizer_centralizes K Ks hKKs g.z₁ (hUK g.first_mem) hzc hz1
  have hdisj := disjoint_of_simple_commuting K Ks hcentral
  have hne : K ≠ Ks := by
    intro he
    have hh : Disjoint K K := by simpa only [←he] using hdisj
    have hb : K = ⊥ := disjoint_self.mp hh
    exact hK.ne_bot hb
  have hSK : (sourceR d ⊔ zpowers c.x) ≤ normalizer (K : Set G) := by
    rw [←g.second_span]
    exact (map_subtype_le _).trans hnK
  have hSKs : (sourceR d ⊔ zpowers c.x) ≤ normalizer (Ks : Set G) := by
    rw [←g.first_span]
    exact (map_subtype_le _).trans hnKs
  have hsK : K.map (MulAut.conj c.s).toMonoidHom = Ks := by
    rw [hbase,twoLayer_map,hKs]
    change centralizerTwoLayer (c.s*g.z₂*c.s⁻¹) = _
    rw [g.exchange_second]
  have hsKs : Ks.map (MulAut.conj c.s).toMonoidHom = K := by
    rw [hKs,twoLayer_map,hbase]
    change centralizerTwoLayer (c.s*g.z₁*c.s⁻¹) = _
    rw [g.exchange]
  have hsN : c.s ∈ normalizer (K ⊔ Ks : Subgroup G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (K ⊔ Ks).map (MulAut.conj c.s).toMonoidHom = K ⊔ Ks
    rw [Subgroup.map_sup,hsK,hsKs,sup_comm]
  refine ⟨hcentral,hdisj,hne,?_,hxK,hxKs,hsK,hsKs,inferInstance⟩
  rw [g.sylow_span]
  exact sup_le ((le_inf hSK hSKs).trans (normalizer_inf_normalizer_le_normalizer_sup K Ks)) (zpowers_le.mpr hsN)

/-- Application of the commuting-pair construction to the ordinary layer and
trivial odd core supplied by the preceding original source component analysis. -/
theorem source_commuting_components
    (c : SourcePairCoordinates d T) (g : SourceCentralizerGeometry c)
    (K : Subgroup G) (hK : IsComponentIn K (centralizer ({g.z₂} : Set G)))
    (hE : K = (componentLayer (centralizer ({g.z₂} : Set G))).map
      (centralizer ({g.z₂} : Set G)).subtype)
    (ho : pPrimeCore 2 (centralizer ({g.z₂} : Set G)) = ⊥)
    (hfirst : d.block.map d.H.subtype ≤ K)
    (hmodel : Nonempty (K ≃* alternatingGroup (Fin 6)) ∨ Nonempty (K ≃* Matrix.PSL3Two.PSL))
    (hcomm : c.U₂ ≤ centralizer (K : Set G)) :
    let Ks := K.map (MulAut.conj c.s⁻¹).toMonoidHom
    K ≤ centralizer (Ks : Set G) ∧ Disjoint K Ks ∧ K ≠ Ks ∧
      (T : Subgroup G) ≤ normalizer (K ⊔ Ks : Subgroup G) ∧
      c.x ∈ normalizer (K : Set G) ∧ c.x ∈ normalizer (Ks : Set G) ∧
      K.map (MulAut.conj c.s).toMonoidHom = Ks ∧
      Ks.map (MulAut.conj c.s).toMonoidHom = K ∧ IsSimpleGroup K := by
  apply commuting_components c g K hK ?_ hfirst hmodel hcomm
  change K = (twoComponentLayer (centralizer ({g.z₂} : Set G))).map _
  rw [ChapterI.Balance.twoComponentLayer_eq_componentLayer ho]
  exact hE

end CFSG.Quasithin.Chapter2.DoubleA3.Noncentrality
