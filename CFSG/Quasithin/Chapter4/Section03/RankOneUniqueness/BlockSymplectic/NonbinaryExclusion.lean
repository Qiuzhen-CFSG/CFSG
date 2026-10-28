module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockSymplectic.Nonbinary
public import Theory.Representation.SL2NaturalTransport

/-!
# The nonbinary symplectic action cannot occur in the crossed configuration

The full W determines the natural plane in U(K)/C_U(K). Root commutators
place U(K) in the original L and put the crossed fixed layer in the kernel
of the original quotient. The crossed natural quotient therefore maps into
the nonsplit plane radical, where every equivariant natural map vanishes.
This contradicts the crossing obstruction. Every marking is constructed
from the natural block action; there is no field-four or fixed-layer premise.

This extends the checked Sp₄(4) proof to all fields 2^n, n > 1, so the B.5
symplectic action row can be excluded directly before the MS field restriction.
The source assembly still owns the large-G₂ action row.
Source: Aschbacher--Smith I.2.3(3) and 4.3.7, pp.413,615--616.
-/
public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonbinarySymplectic
open ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
/-- The original quotient coordinates retain precisely W times the K-fixed layer as kernel. -/
theorem BlockSymplecticParabolic.natural_quotient_modulo_fixed
    {c : SourceConfiguration T L} (m : BlockSymplecticParabolic c)
    (hf : generalizedFitting c.K = pCore 2 c.K) :
    ∃ q : c.blockLayer →* Multiplicative (Fin 2 → m.F), Function.Surjective q ∧
      q.ker = (c.blockFullModule ⊔
        (c.blockLayer ⊓ centralizer (c.K.map c.H.subtype : Set G))).subgroupOf c.blockLayer ∧
      ∀ (l : L) (u : c.blockLayer),
        q (blockConjugateBy L c.blockLayer
          ((c.le_I.trans c.I_le_H).trans c.blockLayer_normalized) l u) =
          Multiplicative.ofAdd ((Plane.quotientMap (m.localMap l)).val.mulVec (q u).toAdd) := by
  let W := c.blockFullModule
  let f : c.K →* G := c.H.subtype.comp c.K.subtype
  have hfi : Function.Injective f := c.H.subtype_injective.comp c.K.subtype_injective
  have hfr : f.range = c.K.map c.H.subtype := by
    rw [MonoidHom.range_comp, range_subtype]
  have hU : (blockU c.K).map f = c.blockLayer := by rw [← map_map]
  let A := L.comap f
  let B := W.comap f
  have hLA : A.map f = L := map_comap_eq_self (by rw [hfr]; exact c.le_component)
  have hWL : W ≤ L := by
    have hs : conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)) = L :=
      le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy _ _)
    simpa only [hs] using c.c28.module_le
  have hWB : B.map f = W := map_comap_eq_self (hWL.trans (by rw [hfr]; exact c.le_component))
  have hBU : B ≤ blockU c.K := by
    intro b hb
    apply (mem_map_iff_mem hfi).mp
    rw [hU]
    exact c.fullModule_le_blockLayer hf hb
  have hBne : B ≠ ⊥ := by
    intro he
    have hWne := c.c28.module_nontrivial
    apply hWne
    change W = ⊥
    rw [← hWB, he, Subgroup.map_bot]
  have hBA : ⁅B,A⁆ = B := by
    apply map_injective hfi
    rw [map_commutator, hWB, hLA]
    have hs : conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)) = L :=
      le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy _ _)
    exact (show W = ⁅W,L⁆ from by simpa only [hs] using c.c28.module_commutator).symm
  have hIN : c.I ≤ normalizer (L : Set G) := by
    rw [c.I_eq]
    exact sup_le L.le_normalizer (c.c28.radical_le.trans inf_le_right)
  have hcore : L.pCoreIn 2 ≤ c.I.pCoreIn 2 := pCoreIn_mono_of_normalizes c.le_I hIN
  have hfix : B ≤ centralizer (A.pCoreIn 2 : Set c.K) := by
    intro w hw a ha
    apply hfi
    change f a * f w = f w * f a
    have haL : f a ∈ L.pCoreIn 2 := by
      have hm := mem_map_of_mem f ha
      rwa [map_pCoreIn_of_injective 2 A f hfi,hLA] at hm
    obtain ⟨v,hv,hvw⟩ := c.c28.module_le_center_radical hw
    have hc := congrArg (fun x : c.I.pCoreIn 2 => (x : G))
      (mem_center_iff.mp hv ⟨f a,hcore haL⟩)
    change f a * (v : G) = (v : G) * f a at hc
    change (v : G) = f w at hvw
    rwa [hvw] at hc
  have hplace : A.map (m.model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.K))) =
      planeLocal := by
    apply le_antisymm
    · rintro _ ⟨a,ha,rfl⟩
      let l : L := ⟨f a,ha⟩
      have he := m.quotient_compatibility (inclusion le_sup_left l) a rfl
      exact he ▸ (m.localMap l).property
    · intro g hg
      obtain ⟨l,hl⟩ := m.local_surjective ⟨g,hg⟩
      obtain ⟨k,hk,hkl⟩ := c.le_component l.property
      let a : c.K := ⟨k,hk⟩
      have ha : f a = l.val := hkl
      refine ⟨a,?_,?_⟩
      · change f a ∈ L
        rw [ha]
        exact l.property
      · exact (m.quotient_compatibility (inclusion le_sup_left l) a ha).symm.trans
          (congrArg Subtype.val hl)
  obtain ⟨q,hq,hker,hact⟩ := ChapterC.SymplecticNonbinary.symplectic_natural_quotient m.card m.large m.model m.linear
    A B hBU hBne hBA hfix hplace
  let e : blockU c.K ≃* c.blockLayer :=
    ((blockU c.K).equivMapOfInjective c.K.subtype c.K.subtype_injective).trans
      (((blockU c.K).map c.K.subtype).equivMapOfInjective c.H.subtype c.H.subtype_injective)
  have he (u : blockU c.K) : (e u).val = f u.val := rfl
  have hei (u : c.blockLayer) : f (e.symm u).val = u.val :=
    congrArg Subtype.val (e.apply_symm_apply u)
  have hZ : (blockU c.K ⊓ center c.K).map f =
      c.blockLayer ⊓ centralizer (c.K.map c.H.subtype : Set G) := by
    apply le_antisymm
    · rintro _ ⟨u,hu,rfl⟩
      refine ⟨?_,?_⟩
      · rw [←hU]
        exact mem_map_of_mem f hu.1
      · rintro y ⟨k,hk,rfl⟩
        exact congrArg f (mem_center_iff.mp hu.2 ⟨k,hk⟩)
    · intro z hz
      obtain ⟨u,hu,huz⟩ := (hU.symm ▸ hz.1 : z ∈ (blockU c.K).map f)
      refine ⟨u,⟨hu,?_⟩,huz⟩
      apply mem_center_iff.mpr
      intro a
      apply hfi
      change f a * f u = f u * f a
      rw [huz]
      exact hz.2 (f a) (mem_map_of_mem c.H.subtype a.property)
  refine ⟨q.comp e.symm.toMonoidHom,hq.comp e.symm.surjective,?_,?_⟩
  · ext u
    change e.symm u ∈ q.ker ↔ _
    rw [hker]
    change (e.symm u).val ∈ B ⊔ (blockU c.K ⊓ center c.K) ↔
      u.val ∈ W ⊔ (c.blockLayer ⊓ centralizer (c.K.map c.H.subtype : Set G))
    rw [←hZ,←hWB,←Subgroup.map_sup,←hei u]
    exact (mem_map_iff_mem hfi).symm
  · intro l u
    obtain ⟨k,hk,hkl⟩ := c.le_component l.property
    let a : c.K := ⟨k,hk⟩
    have ha : f a = l.val := hkl
    have haA : a ∈ A := by change f a ∈ L; rw [ha]; exact l.property
    have hc : e.symm (blockConjugateBy L c.blockLayer
        ((c.le_I.trans c.I_le_H).trans c.blockLayer_normalized) l u) =
        blockConjugate c.K a (e.symm u) := by
      apply e.injective
      rw [e.apply_symm_apply]
      apply Subtype.ext
      rw [he]
      change l.val * u.val * l.val⁻¹ = f (a * (e.symm u).val * a⁻¹)
      rw [map_mul,map_mul,map_inv,ha,hei]
    change q (e.symm _) = _
    rw [hc,hact a haA]
    have hg : (⟨m.model.quotientIso (QuotientGroup.mk' (pCore 2 c.K) a),
        hplace ▸ mem_map_of_mem _ haA⟩ : planeLocal (F := m.F)) = m.localMap l := by
      apply Subtype.ext
      exact (m.quotient_compatibility (inclusion le_sup_left l) a ha).symm
    rw [hg]
    rfl


/-- The literal natural actor quotient kills precisely the original O₂(L). -/
theorem BlockSymplecticParabolic.rankOneMap_ker
    {c : SourceConfiguration T L} (m : BlockSymplecticParabolic c) :
    (Plane.quotientMap.comp m.localMap).ker = pCore 2 L := by
  rw [←MonoidHom.comap_ker,Plane.quotientMap_ker,
    ←planeLocal_core_eq m.card m.large]
  exact m.localMap.comap_pCore_of_ker_isPGroup m.local_surjective m.local_kernel_two


omit [Finite G] in
private theorem local_image {c : SourceConfiguration T L} (m : BlockSymplecticParabolic c) :
    (L.comap (c.H.subtype.comp c.K.subtype)).map
      (m.model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.K))) =
        planeLocal := by
  let f : c.K →* G := c.H.subtype.comp c.K.subtype
  apply le_antisymm
  · rintro _ ⟨a,ha,rfl⟩
    let l : L := ⟨f a,ha⟩
    have he := m.quotient_compatibility (inclusion le_sup_left l) a rfl
    exact he ▸ (m.localMap l).property
  · intro g hg
    obtain ⟨l,hl⟩ := m.local_surjective ⟨g,hg⟩
    obtain ⟨k,hk,hkl⟩ := c.le_component l.property
    let a : c.K := ⟨k,hk⟩
    have ha : f a = l.val := hkl
    refine ⟨a,?_,?_⟩
    · change f a ∈ L
      rw [ha]
      exact l.property
    · exact (m.quotient_compatibility (inclusion le_sup_left l) a ha).symm.trans
        (congrArg Subtype.val hl)

/-- The actual local residual moves the entire original block layer. -/
theorem BlockSymplecticParabolic.block_commutator_eq
    {c : SourceConfiguration T L} (m : BlockSymplecticParabolic c)
    (hb : IsBlock c.K) : ⁅c.blockLayer,L⁆ = c.blockLayer := by
  let f : c.K →* G := c.H.subtype.comp c.K.subtype
  have hfr : f.range = c.K.map c.H.subtype := by
    rw [MonoidHom.range_comp,range_subtype]
  have hL : (L.comap f).map f = L := map_comap_eq_self (by rw [hfr]; exact c.le_component)
  have hh := congrArg (Subgroup.map f)
    (ChapterC.SymplecticNonbinary.SymplecticRootModule.commutator_eq hb.short m.card m.large m.model m.linear
      (L.comap f) (local_image m))
  rw [map_commutator,hL] at hh
  simpa only [f,←Subgroup.map_map] using hh

/-- I.2.3 on the original quotient places the fixed layer in local-core commutators. -/
theorem BlockSymplecticParabolic.fixed_le_core_commutator
    {c : SourceConfiguration T L} (m : BlockSymplecticParabolic c)
    (hb : IsBlock c.K) :
    c.blockLayer ⊓ centralizer (c.K.map c.H.subtype : Set G) ≤
      ⁅c.blockLayer,L.pCoreIn 2⁆ := by
  let f : c.K →* G := c.H.subtype.comp c.K.subtype
  have hfi : Function.Injective f := c.H.subtype_injective.comp c.K.subtype_injective
  have hfr : f.range = c.K.map c.H.subtype := by
    rw [MonoidHom.range_comp,range_subtype]
  have hL : (L.comap f).map f = L := map_comap_eq_self (by rw [hfr]; exact c.le_component)
  have hU : (blockU c.K).map f = c.blockLayer := by rw [←Subgroup.map_map]
  have hh := map_mono (f := f)
    (ChapterC.SymplecticNonbinary.SymplecticRootModule.fixed_le_core_commutator hb.short m.card m.large m.model m.linear
      (L.comap f) (local_image m))
  rw [map_commutator,hU,map_pCoreIn_of_injective 2 _ f hfi,hL] at hh
  intro z hz
  apply hh
  obtain ⟨u,hu,huz⟩ := (hU.symm ▸ hz.1 : z ∈ (blockU c.K).map f)
  refine ⟨u,⟨hu,?_⟩,huz⟩
  apply mem_center_iff.mpr
  intro a
  apply hfi
  change f a * f u = f u * f a
  rw [huz]
  exact hz.2 (f a) (mem_map_of_mem c.H.subtype a.property)

/-- The block layer already normalizes L; its full commutator identity puts it in L. -/
theorem BlockSymplecticParabolic.blockLayer_le_local
    {c : SourceConfiguration T L} (m : BlockSymplecticParabolic c)
    (hb : IsBlock c.K) : c.blockLayer ≤ L := by
  have hUR : c.blockLayer ≤ c.I.pCoreIn 2 :=
    c.blockLayer_le_blockCore.trans
      ((map_mono (pCoreIn_le_of_subnormal 2 c.component.subnormal)).trans
        c.c28.ambient_core_le_radical)
  have hUL : c.blockLayer ≤ normalizer (L : Set G) :=
    hUR.trans (c.c28.radical_le.trans inf_le_right)
  rw [←m.block_commutator_eq hb,commutator_comm]
  exact le_normalizer_iff_commutator_le_left.mp hUL

/-- Crossing preserves the actual L, without a fixed-layer containment premise. -/
theorem BlockSymplecticParabolic.crossed_le_local
    {V : Subgroup G} {c : SourceConfiguration T L} (m : BlockSymplecticParabolic c)
    (D : Chapter12.Section02.ChosenModule T L V) (hb : IsBlock c.K) :
    c.crossedBlockLayer ≤ c.blockLocal := by
  have hL : L.map (MulAut.conj c.t⁻¹).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp
      (D.sylow_normalizes_component ((T : Subgroup G).inv_mem c.crossing_mem))
  exact ((map_mono (f := (MulAut.conj c.t⁻¹).toMonoidHom)
    (m.blockLayer_le_local hb)).trans_eq hL).trans le_sup_left

/-- The crossed quotient retains the crossed fixed layer in its exact kernel. -/
theorem BlockSymplecticParabolic.crossed_natural_quotient_modulo_fixed
    {V : Subgroup G} {c : SourceConfiguration T L} (m : BlockSymplecticParabolic c)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K) :
    ∃ q : c.crossedBlockLayer →* Multiplicative (Fin 2 → m.F), Function.Surjective q ∧
      q.ker = (c.blockFullModule ⊔
        (c.blockLayer ⊓ centralizer (c.K.map c.H.subtype : Set G)).map
          (MulAut.conj c.t⁻¹).toMonoidHom).subgroupOf c.crossedBlockLayer ∧
      ∀ (l : L) (u : c.crossedBlockLayer),
        q (blockConjugateBy L c.crossedBlockLayer (c.crossedBlockLayer_normalized D) l u) =
          Multiplicative.ofAdd ((Plane.quotientMap (m.localMap l)).val.mulVec (q u).toAdd) := by
  obtain ⟨p,hp,hpk,hpa⟩ := m.natural_quotient_modulo_fixed hf
  let π := Plane.quotientMap.comp m.localMap
  have hπ : Function.Surjective π := Plane.quotientMap_surjective.comp m.local_surjective
  let : π.ker.Characteristic := m.rankOneMap_ker.symm ▸ inferInstance
  have ht : c.t ∈ normalizer (L : Set G) := D.sylow_normalizes_component c.crossing_mem
  have hti := (normalizer (L : Set G)).inv_mem ht
  let a : MulAut L := {
    toFun l := ⟨c.t * l.val * c.t⁻¹,(mem_normalizer_iff.mp ht _).mp l.property⟩
    invFun l := ⟨c.t⁻¹ * l.val * c.t,(by
      simpa only [inv_inv] using (mem_normalizer_iff.mp hti l.val).mp l.property)⟩
    left_inv l := by apply Subtype.ext; dsimp; group
    right_inv l := by apply Subtype.ext; dsimp; group
    map_mul' l k := by apply Subtype.ext; dsimp; group }
  obtain ⟨e,he⟩ := Representation.SL2NaturalTransport.quotient_automorphism_coordinates π hπ a
  let b : c.blockLayer ≃* c.crossedBlockLayer :=
    c.blockLayer.equivMapOfInjective (MulAut.conj c.t⁻¹).toMonoidHom
      (MulAut.conj c.t⁻¹).injective
  have hb (u : c.blockLayer) : (b u).val = c.t⁻¹ * u.val * c.t := by
    change c.t⁻¹ * u.val * (c.t⁻¹)⁻¹ = _
    rw [inv_inv]
  have hbi (u : c.crossedBlockLayer) : (b.symm u).val = c.t * u.val * c.t⁻¹ := by
    have hh := congrArg Subtype.val (b.apply_symm_apply u)
    rw [hb] at hh
    rw [←hh]
    group
  let q := e.symm.toMultiplicative.toMonoidHom.comp (p.comp b.symm.toMonoidHom)
  refine ⟨q,e.symm.surjective.comp (hp.comp b.symm.surjective),?_,?_⟩
  · ext u
    let Z := c.blockLayer ⊓ centralizer (c.K.map c.H.subtype : Set G)
    change e.symm ((p (b.symm u)).toAdd) = 0 ↔
      u.val ∈ c.blockFullModule ⊔ Z.map (MulAut.conj c.t⁻¹).toMonoidHom
    rw [e.symm.map_eq_zero_iff]
    change b.symm u ∈ p.ker ↔ _
    rw [hpk]
    change (b.symm u).val ∈ c.blockFullModule ⊔ Z ↔ _
    have hX : (c.blockFullModule ⊔ Z).map (MulAut.conj c.t⁻¹).toMonoidHom =
        c.blockFullModule ⊔ Z.map (MulAut.conj c.t⁻¹).toMonoidHom := by
      rw [Subgroup.map_sup,c.crossing_fullModule D]
    have he : (MulAut.conj c.t⁻¹) (b.symm u).val = u.val := by
      simpa only [MulAut.conj_apply,inv_inv] using
        (hb (b.symm u)).symm.trans (congrArg Subtype.val (b.apply_symm_apply u))
    rw [←hX,←he]
    exact (mem_map_iff_mem (MulAut.conj c.t⁻¹).injective).symm
  · intro l u
    have hc : b.symm (blockConjugateBy L c.crossedBlockLayer
        (c.crossedBlockLayer_normalized D) l u) =
        blockConjugateBy L c.blockLayer
          ((c.le_I.trans c.I_le_H).trans c.blockLayer_normalized) (a l) (b.symm u) := by
      apply Subtype.ext
      rw [hbi]
      change c.t * (l.val * u.val * l.val⁻¹) * c.t⁻¹ =
        (c.t * l.val * c.t⁻¹) * (b.symm u).val * (c.t * l.val * c.t⁻¹)⁻¹
      rw [hbi]
      group
    apply Multiplicative.toAdd.injective
    change e.symm ((p (b.symm _)).toAdd) = _
    rw [hc,hpa]
    change e.symm ((π (a l)).val.mulVec (p (b.symm u)).toAdd) =
      (π l).val.mulVec (e.symm (p (b.symm u)).toAdd)
    apply e.injective
    rw [e.apply_symm_apply,he,e.apply_symm_apply]



/-- The crossed fixed layer dies in the original component quotient: local-core
commutators map to commutators in the abelian plane radical. -/
theorem BlockSymplecticParabolic.crossed_fixed_le_blockCore
    {V : Subgroup G} {c : SourceConfiguration T L} (m : BlockSymplecticParabolic c)
    (D : Chapter12.Section02.ChosenModule T L V) (hb : IsBlock c.K) :
    (c.blockLayer ⊓ centralizer (c.K.map c.H.subtype : Set G)).map
      (MulAut.conj c.t⁻¹).toMonoidHom ≤ c.blockCore := by
  let e := MulAut.conj c.t⁻¹
  have hL : L.map e.toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp
    (D.sylow_normalizes_component ((T : Subgroup G).inv_mem c.crossing_mem))
  have hcore : (L.pCoreIn 2).map e.toMonoidHom = L.pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 L e.toMonoidHom e.injective,hL]
  have hZ := map_mono (f := e.toMonoidHom) (m.fixed_le_core_commutator hb)
  rw [map_commutator,hcore] at hZ
  apply hZ.trans
  change ⁅c.crossedBlockLayer,L.pCoreIn 2⁆ ≤ c.blockCore
  apply commutator_le.mpr
  intro u hu a ha
  let x : c.blockLocal := inclusion (m.crossed_le_local D hb) ⟨u,hu⟩
  let y : c.blockLocal := inclusion le_sup_left ⟨a,pCoreIn_le 2 L ha⟩
  have hx : m.quotient x ∈ Plane.radical :=
    m.crossed_image_le_radical D (m.crossed_le_local D hb) ⟨⟨u,hu⟩,rfl⟩
  have hy : m.quotient y ∈ Plane.radical := by
    obtain ⟨b,hb,rfl⟩ := ha
    exact m.local_core_image ▸ mem_map_of_mem m.localMap hb
  have hc : m.quotient x * m.quotient y = m.quotient y * m.quotient x :=
    congrArg Subtype.val (Plane.radical_mul_comm ⟨m.quotient x,hx⟩ ⟨m.quotient y,hy⟩)
  have hk : ⁅x,y⁆ ∈ m.quotient.ker := by
    rw [MonoidHom.mem_ker,map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hc
  rw [m.quotient_ker] at hk
  exact hk

/-- The symplectic branch excludes itself without a fixed-layer placement premise.
Both the crossed kernel and the target radical use the original quotient. -/
theorem false_of_parabolic
    {V : Subgroup G} (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    (m : BlockSymplecticParabolic c) : False := by
  let hc := m.crossed_le_local D hb
  obtain ⟨q,hq,hqk,hqa⟩ := m.crossed_natural_quotient_modulo_fixed D hf
  let r := m.quotient.comp (inclusion hc)
  have hk : q.ker ≤ r.ker := by
    intro u hu
    rw [hqk] at hu
    have hcore := (sup_le ((c.fullModule_le_blockLayer hf).trans c.blockLayer_le_blockCore)
      (m.crossed_fixed_le_blockCore D hb)) hu
    change inclusion hc u ∈ m.quotient.ker
    rw [m.quotient_ker]
    exact hcore
  let f := q.liftOfSurjective hq ⟨r,hk⟩
  have hfq (u : c.crossedBlockLayer) : f (q u) = r u := by simp [f]
  have hR : f.range ≤ Plane.radical := by
    rintro x ⟨v,rfl⟩
    obtain ⟨u,rfl⟩ := hq v
    rw [hfq]
    exact m.crossed_image_le_radical D hc ⟨u,rfl⟩
  have he (g : planeLocal (F := m.F)) (v : Multiplicative (Fin 2 → m.F)) :
      f (Multiplicative.ofAdd (Matrix.mulVec (Plane.quotientMap g).val v.toAdd)) =
        g * f v * g⁻¹ := by
    obtain ⟨l,rfl⟩ := m.local_surjective g
    obtain ⟨u,rfl⟩ := hq v
    rw [←hqa,hfq,hfq]
    change m.quotient ⟨l.val * u.val * l.val⁻¹, _⟩ = _
    have hh : (⟨l.val * u.val * l.val⁻¹, _⟩ : c.blockLocal) =
        inclusion le_sup_left l * inclusion hc u * (inclusion le_sup_left l)⁻¹ := rfl
    rw [hh,map_mul,map_mul,map_inv]
    rfl
  have hz := Plane.natural_hom_into_radical_eq_one
    m.card m.large f hR he
  apply c.crossedBlockLayer_not_le_blockCore hb
  intro u hu
  have hr : r ⟨u,hu⟩ = 1 := by rw [←hfq ⟨u,hu⟩,hz]; rfl
  have hh : inclusion hc ⟨u,hu⟩ ∈ m.quotient.ker := hr
  rw [m.quotient_ker] at hh
  exact hh


/-- The natural symplectic block action is impossible in the original crossed
configuration, over every nonbinary field. All local markings are constructed. -/
theorem false_of_natural
    {V : Subgroup G} (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    (F : ChapterB.QuasisimpleSource.BinaryField) (hF : 1 < F.degree)
    (hm : IsLinearBlockModel c.K (ChapterB.QuasisimpleSource.binarySymplectic F)) : False := by
  obtain ⟨m⟩ := parabolic_of_natural c hf hb F hF hm
  exact false_of_parabolic c D hf hb m

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonbinarySymplectic
