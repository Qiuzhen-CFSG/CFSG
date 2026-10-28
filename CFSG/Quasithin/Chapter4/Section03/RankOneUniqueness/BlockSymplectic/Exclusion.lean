module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockSymplectic.CrossedModule
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SymplecticRootModule

/-!
# Exclusion of the Sp₄(4) block in original4.3.7

Root commutators first show [U(K),L]=U(K). Since U(K) normalizes L, this
places U(K) and its crossed copy inside the original L. The crossed image
in L O₂(K)/O₂(K) therefore lies in the abelian plane radical. I.2.3 puts
the crossed fixed layer in [U(K)ᵗ,O₂(L)], which that quotient kills.

The exact crossed natural quotient has kernel W C_U(K)(K)ᵗ. Its two factors
now lie in O₂(K), so the original quotient factors through a natural SL₂
module. The nonsplitting theorem makes this image trivial, contradicting
the crossed-layer obstruction. Thus the source branch has no fixed-layer,
placement or module callback. The separate C.4.1 classification remains
with qt-d-1222-rankone-uniqueness-block. Throughout W is the actual full
module [Ω₁Z(O₂(LT)),L], not the chosen Chapter12 module.
Source: Aschbacher–Smith I.2.3(3) and original4.3.7, printed pp.413,615–616.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

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
    (SymplecticRootModule.commutator_eq hb.short m.card m.model m.linear
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
    (SymplecticRootModule.fixed_le_core_commutator hb.short m.card m.model m.linear
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
theorem SourceConfiguration.false_of_symplectic_parabolic
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
    (by simpa using m.card : Nat.card m.F = 2 ^ 2) (by decide) f hR he
  apply c.crossedBlockLayer_not_le_blockCore hb
  intro u hu
  have hr : r ⟨u,hu⟩ = 1 := by rw [←hfq ⟨u,hu⟩,hz]; rfl
  have hh : inclusion hc ⟨u,hu⟩ ∈ m.quotient.ker := hr
  rw [m.quotient_ker] at hh
  exact hh

/-- The original Sp₄(4) block branch, with every marking and kernel premise discharged. -/
theorem SourceConfiguration.false_of_sp4Four_block
    {V : Subgroup G} (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    (hsp : IsSp4FourBlock c.K) : False := by
  obtain ⟨m⟩ := c.block_symplectic_parabolic hf hb hsp
  exact c.false_of_symplectic_parabolic D hf hb m

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
