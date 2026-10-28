module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockSymplectic.ModuleGeometry
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockSymplectic.Parabolic
public import Theory.Representation.SL2NaturalTransport

/-!
# The crossed natural module in the Sp₄ block branch

The original L maps onto SL₂(F₄) with kernel O₂(L). Conjugation by the
crossing element descends through that characteristic kernel. Its
semilinear natural coordinates correct the action on U(K)ᵗ/W, retaining
the original parabolic quotient and the literal full module
W = [Ω₁Z(O₂(LT)),L] as kernel.

Natural transvection displacements also place U(K) inside L: its kernel
is in L, and U(K) normalizes L because it lies in the original radical.
Crossing preserves L, so U(K)ᵗ lies in L O₂(K). Together these results
construct every field of BlockSymplecticGeometry once C_U(K) ≤ W is given.
The final theorem constructs the parabolic marking from the block type and
applies the nonsplit radical obstruction.

The fixed-layer containment, cited as I.2.3(3) in the source, is still an
explicit premise. Its proof and the C.4.1 alternatives remain obligations
of qt-d-1222-rankone-uniqueness-block. No identification of W with the
chosen Chapter12 module is made.
Source: Aschbacher–Smith, original 4.3.7, printed p.616, and I.2.3, p.413.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The literal natural actor quotient kills precisely the original O₂(L). -/
theorem BlockSymplecticParabolic.rankOneMap_ker
    {c : SourceConfiguration T L} (m : BlockSymplecticParabolic c) :
    (Plane.quotientMap.comp m.localMap).ker = pCore 2 L := by
  rw [←MonoidHom.comap_ker,Plane.quotientMap_ker,
    ←planeLocal_core_eq (n := 2) m.card (by decide)]
  exact m.localMap.comap_pCore_of_ker_isPGroup m.local_surjective m.local_kernel_two

/-- Natural displacements and the full-module kernel place U(K) inside the original L. -/
theorem BlockSymplecticParabolic.blockLayer_le_local_of_fixed
    {c : SourceConfiguration T L} (m : BlockSymplecticParabolic c)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (hfixed : c.blockLayer ⊓ centralizer (c.K.map c.H.subtype : Set G) ≤ c.blockFullModule) :
    c.blockLayer ≤ L := by
  obtain ⟨p,hp,hpk,hpa⟩ := m.natural_quotient hf hfixed
  have hπ := Plane.quotientMap_surjective.comp m.local_surjective
  have hWL : c.blockFullModule ≤ L := by
    have hs : conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)) = L :=
      le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy _ _)
    simpa only [hs] using c.c28.module_le
  have hUR : c.blockLayer ≤ c.I.pCoreIn 2 :=
    c.blockLayer_le_blockCore.trans
      ((map_mono (pCoreIn_le_of_subnormal 2 c.component.subnormal)).trans
        c.c28.ambient_core_le_radical)
  have hUL : c.blockLayer ≤ normalizer (L : Set G) :=
    hUR.trans (c.c28.radical_le.trans inf_le_right)
  have hcomm : ⁅L,c.blockLayer⁆ ≤ L := le_normalizer_iff_commutator_le_left.mp hUL
  let Q := ((L.subgroupOf c.blockLayer).map p).toAddSubgroup'
  have hQ : Q = ⊤ := by
    apply Representation.SL2NaturalTransport.natural_displacements_span
    intro g v
    obtain ⟨l,hl⟩ := hπ g
    change Plane.quotientMap (m.localMap l) = g at hl
    obtain ⟨u,hu⟩ := hp (Multiplicative.ofAdd v)
    let d := blockConjugateBy L c.blockLayer
      ((c.le_I.trans c.I_le_H).trans c.blockLayer_normalized) l u * u⁻¹
    have hd : d.val ∈ L := hcomm (commutator_mem_commutator l.property u.property)
    refine ⟨d,hd,?_⟩
    change p d = Multiplicative.ofAdd (g.val.mulVec v - v)
    dsimp only [d]
    rw [map_mul,map_inv,hpa,hu]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul,toAdd_inv,toAdd_ofAdd]
    rw [hl]
    exact (sub_eq_add_neg _ _).symm
  intro x hx
  let u : c.blockLayer := ⟨x,hx⟩
  have hu : (p u).toAdd ∈ Q := hQ ▸ AddSubgroup.mem_top _
  obtain ⟨d,hd,he⟩ := hu
  change p d = p u at he
  have hz : u * d⁻¹ ∈ p.ker := by
    change p (u*d⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hw : (u*d⁻¹).val ∈ c.blockFullModule := by
    rwa [hpk] at hz
  have hh := L.mul_mem (hWL hw) hd
  change x * d.val⁻¹ * d.val ∈ L at hh
  simpa only [inv_mul_cancel_right] using hh

/-- Crossing preserves L, placing the entire crossed layer in L O₂(K). -/
theorem BlockSymplecticParabolic.crossed_le_local_of_fixed
    {V : Subgroup G} {c : SourceConfiguration T L} (m : BlockSymplecticParabolic c)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (hfixed : c.blockLayer ⊓ centralizer (c.K.map c.H.subtype : Set G) ≤ c.blockFullModule) :
    c.crossedBlockLayer ≤ c.blockLocal := by
  have hL : L.map (MulAut.conj c.t⁻¹).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp
      (D.sylow_normalizes_component ((T : Subgroup G).inv_mem c.crossing_mem))
  exact ((map_mono (f := (MulAut.conj c.t⁻¹).toMonoidHom)
    (m.blockLayer_le_local_of_fixed hf hfixed)).trans_eq hL).trans le_sup_left

/-- Correct the crossed natural action by the actual induced SL₂ automorphism. -/
theorem BlockSymplecticParabolic.crossed_natural_quotient
    {V : Subgroup G} {c : SourceConfiguration T L} (m : BlockSymplecticParabolic c)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (hfixed : c.blockLayer ⊓ centralizer (c.K.map c.H.subtype : Set G) ≤ c.blockFullModule) :
    ∃ q : c.crossedBlockLayer →* Multiplicative (Fin 2 → m.F), Function.Surjective q ∧
      q.ker = c.blockFullModule.subgroupOf c.crossedBlockLayer ∧
      ∀ (l : L) (u : c.crossedBlockLayer),
        q (blockConjugateBy L c.crossedBlockLayer (c.crossedBlockLayer_normalized D) l u) =
          Multiplicative.ofAdd ((Plane.quotientMap (m.localMap l)).val.mulVec (q u).toAdd) := by
  obtain ⟨p,hp,hpk,hpa⟩ := m.natural_quotient hf hfixed
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
    change e.symm ((p (b.symm u)).toAdd) = 0 ↔ u.val ∈ c.blockFullModule
    rw [e.symm.map_eq_zero_iff]
    change b.symm u ∈ p.ker ↔ _
    rw [hpk]
    change (b.symm u).val ∈ c.blockFullModule ↔ _
    have hw : c.blockFullModule.map (MulAut.conj c.t⁻¹).toMonoidHom = c.blockFullModule :=
      c.crossing_fullModule D
    have hn : c.t⁻¹ ∈ normalizer (c.blockFullModule : Set G) :=
      mem_normalizer_iff_map_conj_eq.mpr hw
    rw [hbi]
    exact mem_normalizer_iff.mp (by simpa only [inv_inv] using
      (normalizer (c.blockFullModule : Set G)).inv_mem hn) u.val |>.symm
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

/-- Both marked natural quotients and the crossed placement follow from the fixed-layer premise. -/
theorem BlockSymplecticParabolic.geometry_of_fixed_layer
    {V : Subgroup G} {c : SourceConfiguration T L} (m : BlockSymplecticParabolic c)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (hfixed : c.blockLayer ⊓ centralizer (c.K.map c.H.subtype : Set G) ≤ c.blockFullModule) :
    Nonempty (BlockSymplecticGeometry D c m) := by
  obtain ⟨p,hp,hpk,hpa⟩ := m.natural_quotient hf hfixed
  obtain ⟨q,hq,hqk,hqa⟩ := m.crossed_natural_quotient D hf hfixed
  exact ⟨{
    full_le := c.fullModule_le_blockLayer hf
    fixed_le := hfixed
    crossed_le := m.crossed_le_local_of_fixed D hf hfixed
    natural := p
    natural_surjective := hp
    natural_kernel := hpk
    natural_action := hpa
    crossed := q
    crossed_surjective := hq
    crossed_kernel := hqk
    crossed_action := hqa }⟩

/-- The crossed geometry is constructed before applying the nonsplit radical obstruction. -/
theorem SourceConfiguration.false_of_symplectic_fixed_layer
    {V : Subgroup G} (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : ChapterC.IsBlock c.K)
    (m : BlockSymplecticParabolic c)
    (hfixed : c.blockLayer ⊓ centralizer (c.K.map c.H.subtype : Set G) ≤ c.blockFullModule) :
    False := by
  obtain ⟨d⟩ := m.geometry_of_fixed_layer D hf hfixed
  exact c.false_of_symplectic_geometry D hb m d

/-- Source application: only the containment from I.2.3(3) remains explicit.
The original block type supplies the actual parabolic marking internally. -/
theorem SourceConfiguration.false_of_sp4Four_block_of_fixed_layer
    {V : Subgroup G} (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : ChapterC.IsBlock c.K)
    (hsp : ChapterC.IsSp4FourBlock c.K)
    (hfixed : c.blockLayer ⊓ centralizer (c.K.map c.H.subtype : Set G) ≤ c.blockFullModule) :
    False := by
  obtain ⟨m⟩ := c.block_symplectic_parabolic hf hb hsp
  exact c.false_of_symplectic_fixed_layer D hf hb m hfixed

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
