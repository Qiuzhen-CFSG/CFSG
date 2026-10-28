module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction.Kernel
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.FlagTypes.Preparation
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.Representation.SymplecticNaturalNormalizer.Centralizers
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.SpecificGroups.SymplecticFour.Sylow.Normalizer

/-!
# From a marked symplectic section to the literal parabolic action

The actual Tᵥ conjugation on K⁺ preserves the image of Tᵥ ∩ K. The local
Sylow condition turns its containment marking into equality with the standard
unipotent subgroup. Natural coordinates on the canonical moved quotient then
make each induced automorphism diagram-preserving: transport the whole quotient
action into the natural normalizer and use its proved semilinear description.
The diagram kernel is normal, so the coordinates may use an arbitrary group
marking, including one with exceptional graph orientation.

A diagram-preserving automorphism stabilizing the unipotent subgroup fixes
both standard parabolics. Equivariance of the literal quotient map therefore
normalizes both published preimages. The extra natural-section premise is
explicit here. Its extraction from the complete adequate B.5 alternatives
remains required; no natural-module assertion is made about the full W_K.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the paragraph
preceding 13.6.14 and Lemma 13.6.19, printed pp.929–931; B.5.1 and B.5.6.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction
open ComponentSelection ChapterB.QuasisimpleSource

private theorem diagram_of_natural_intertwiner
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (hF : 2 < Nat.card F) (a : MulAut (Sp F))
    (b : Vector F ≃ₗ[ZMod 2] Vector F)
    (hb : ∀ g w, b (symplecticNatural 2 g w) = symplecticNatural 2 (a g) (b w)) :
    PreservesDiagram a := by
  open SymplecticNaturalNormalizer in
  have hconj (g : Sp F) : b * naturalHom g * b⁻¹ = naturalHom (a g) := by
    apply LinearEquiv.ext
    intro w
    change b (symplecticNatural 2 g (b.symm w)) = symplecticNatural 2 (a g) w
    rw [hb, b.apply_symm_apply]
  open SymplecticNaturalNormalizer SymplecticConjugatePair.Ambient.Normalizer in
  have hn : b ∈ naturalNormalizer (F := F) := by
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      obtain ⟨g, hg⟩ := (naturalEquiv hF).surjective ⟨x, hx⟩
      have he : naturalHom g = x := congrArg Subtype.val hg
      rw [← he, hconj]
      exact naturalHom_mem hF _
    · intro hx
      obtain ⟨g, hg⟩ := (naturalEquiv hF).surjective ⟨b * x * b⁻¹, hx⟩
      have he : naturalHom g = b * x * b⁻¹ := congrArg Subtype.val hg
      have hh : b * naturalHom (a.symm g) * b⁻¹ = b * x * b⁻¹ := by
        rw [hconj, a.apply_symm_apply, he]
      have he' : naturalHom (a.symm g) = x := (MulAut.conj b).injective hh
      rw [← he']
      exact naturalHom_mem hF _
  have he := SymplecticNaturalNormalizer.conjugation_eq_of_intertwines hF ⟨b, hn⟩ a hb
  rw [← he]
  exact SymplecticNaturalNormalizer.conjugation_preservesDiagram hF _

private theorem normal_action_diagram
    {H V F : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
    [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (hF : 2 < Nat.card F)
    (C : Subgroup H) [C.Normal] (ρ : Representation (ZMod 2) H V)
    (e : C ≃* Sp F) (h : H)
    (c : ActionEquiv (ρ.comp C.subtype)
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2))) :
    PreservesDiagram (MulAut.congr e (MulAut.conjNormal h)) := by
  let d := c.linearEquiv
  let A := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom h)
  let b := d.symm.trans (A.trans d)
  let a := MulAut.congr c.groupEquiv (MulAut.conjNormal h)
  have hnat (k : C) (w : V) :
      d (ρ (k : H) w) = symplecticNatural 2 (c.groupEquiv k) (d w) := c.intertwines k w
  have hA (w : V) : A w = ρ h w := rfl
  have ha : PreservesDiagram a := by
    apply diagram_of_natural_intertwiner hF a b
    intro g w
    let k := c.groupEquiv.symm g
    have hg : c.groupEquiv k = g := c.groupEquiv.apply_symm_apply g
    calc
      b (symplecticNatural 2 g w) = d (ρ h (ρ (k : H) (d.symm w))) := by
        change d (A (d.symm (symplecticNatural 2 g w))) = _
        rw [hA]
        congr 2
        apply d.injective
        rw [d.apply_symm_apply, hnat, d.apply_symm_apply, hg]
      _ = d (ρ (((MulAut.conjNormal h) k : C) : H) (ρ h (d.symm w))) := by
        congr 1
        rw [MulAut.conjNormal_apply]
        simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]
      _ = symplecticNatural 2 (a g) (b w) := by
        rw [hnat]
        rfl
  let f : MulAut (Sp F) := e.symm.trans c.groupEquiv
  have hk : a ∈ (parabolicClassAction hF).ker :=
    (mem_parabolicClassAction_ker_iff hF a).mpr ha
  have hc := (inferInstance : (parabolicClassAction hF).ker.Normal).conj_mem a hk f⁻¹
  have he : f⁻¹ * a * (f⁻¹)⁻¹ = MulAut.congr e (MulAut.conjNormal h) := by
    ext x : 1
    change e (c.groupEquiv.symm (c.groupEquiv ((MulAut.conjNormal h)
      (c.groupEquiv.symm (c.groupEquiv (e.symm x)))))) = _
    simp only [MulEquiv.symm_apply_apply]
    rfl
  rw [he] at hc
  exact (mem_parabolicClassAction_ker_iff hF _).mp hc

private theorem field_map_unipotent {F : Type*} [Field F]
    (σ : F ≃+* F) : unipotent.map (fieldAutomorphism σ).toMonoidHom = unipotent := by
  have hm (x : Sp F) : fieldAutomorphism σ x ∈ unipotent ↔ x ∈ unipotent := by
    simp [mem_unipotent_iff, fieldAutomorphism]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hm y).mpr hy
  · intro hx
    obtain ⟨y, rfl⟩ := (fieldAutomorphism σ).surjective x
    exact ⟨y, (hm y).mp hx, rfl⟩

private theorem flags_of_diagram {F : Type*} [Field F] [Finite F] [CharP F 2]
    (a : MulAut (Sp F)) (ha : PreservesDiagram a)
    (hU : unipotent.map a.toMonoidHom = unipotent) :
    pointParabolic.map a.toMonoidHom = pointParabolic ∧
      planeParabolic.map a.toMonoidHom = planeParabolic := by
  obtain ⟨g, σ, rfl⟩ := SemilinearClassification.inner_field_of_preservesDiagram a ha
  have hu : unipotent.map (MulAut.conj g).toMonoidHom = unipotent := by
    change unipotent.map ((MulAut.conj g).toMonoidHom.comp
      (fieldAutomorphism σ).toMonoidHom) = unipotent at hU
    rwa [← Subgroup.map_map, field_map_unipotent] at hU
  have hg := normalizer_unipotent_le_borel (mem_normalizer_iff_map_conj_eq.mpr hu)
  constructor
  · change pointParabolic.map ((MulAut.conj g).toMonoidHom.comp
      (fieldAutomorphism σ).toMonoidHom) = _
    rw [← Subgroup.map_map, field_map_pointParabolic]
    exact mem_normalizer_iff_map_conj_eq.mp (le_normalizer hg.1)
  · change planeParabolic.map ((MulAut.conj g).toMonoidHom.comp
      (fieldAutomorphism σ).toMonoidHom) = _
    rw [← Subgroup.map_map, field_map_planeParabolic]
    exact mem_normalizer_iff_map_conj_eq.mp (le_normalizer hg.2)


universe u
variable {G : Type u} [Group G] [Finite G]
variable (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))

/-- A containment marking of the source Sylow intersection is already equality. -/
theorem marked_intersection_eq_unipotent
    {F : Type*} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 0 < m)
    (hK : K ∈ Yz L T z v)
    (e : plusImage K L T z v hL hz K ≃* Sp F)
    (hmark : ((Tv T v).subgroupOf K).map (modelMap K L T z v hL hz e) ≤ unipotent) :
    ((Tv T v).subgroupOf K).map (modelMap K L T z v hL hz e) = unipotent := by
  have hs := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    hK.1.2.2.1 le_sup_left hK.1.2.1.subnormal
  obtain ⟨S, hS⟩ := hs
  have heS : (S : Subgroup K) = (Tv T v).subgroupOf K := by
    have hh := congrArg (comap K.subtype) hS
    simpa only [comap_map_eq_self_of_injective K.subtype_injective,
      comap_inf, comap_subtype, subgroupOf_self, inf_top_eq] using hh
  let f := modelMap K L T z v hL hz e
  let S' := S.mapSurjective (f := f) (modelMap_surjective K L T z v hL hz e)
  have heS' : (S' : Subgroup (Sp F)) = ((Tv T v).subgroupOf K).map f := by
    change (S : Subgroup K).map f = _
    rw [heS]
  have hu := (unipotentSylow hF hm).isPGroup'
  exact (S'.is_maximal' hu (heS' ▸ hmark)).trans heS' |>.symm

/-- The actual quotient conjugation preserves the standard unipotent subgroup. -/
theorem modelAction_unipotent
    {F : Type*} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 0 < m)
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* Sp F)
    (hmark : ((Tv T v).subgroupOf K).map (modelMap K L T z v hL hz e) ≤ unipotent)
    (t : Tv T v) :
    unipotent.map (LinearThree.MarkedAction.modelAction K L T z v hL hz hn e t).toMonoidHom =
      unipotent := by
  rw [← marked_intersection_eq_unipotent K L T z v hL hz hF hm hK e hmark]
  exact LinearThree.MarkedAction.modelAction_marked_subgroup K L T z v hL hz hn e t

omit [Finite G] in
/-- Natural coordinates on the canonical moved quotient exclude exceptional
diagram automorphisms. The marking of the group may have either orientation. -/
theorem modelAction_preservesDiagram_of_natural
    [IsElementaryAbelian 2 (WK K L T z v)]
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (hF : 2 < Nat.card F)
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* Sp F)
    (hmodule : Nonempty (ActionEquiv
      ((LinearThree.MarkedAction.plusComponentSection K L T z v hL hz hK hn).action.comp
        (plusImage K L T z v hL hz K).subtype)
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2))))
    (t : Tv T v) :
    PreservesDiagram (LinearThree.MarkedAction.modelAction K L T z v hL hz hn e t) := by
  let := LinearThree.MarkedAction.plus_component_normal K L T z v hL hz hK hn
  obtain ⟨c⟩ := hmodule
  rw [LinearThree.MarkedAction.modelAction_eq_conjugation K L T z v hL hz hK hn e t]
  exact normal_action_diagram hF _
    (LinearThree.MarkedAction.plusComponentSection K L T z v hL hz hK hn).action e
    (LinearThree.MarkedAction.plusTvMap K L T z v hL hz t) c

/-- Apply the natural moved-quotient action to both literal published preimages.
The whole W_K is unrestricted; only its canonical moved quotient is marked.
Extraction of these coordinates from B.5 remains an independent source input. -/
theorem flagPreimages_normalized_of_natural
    [IsElementaryAbelian 2 (WK K L T z v)]
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    {m : ℕ} (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* Sp F)
    (hmark : ((Tv T v).subgroupOf K).map (modelMap K L T z v hL hz e) ≤ unipotent)
    (hmodule : Nonempty (ActionEquiv
      ((LinearThree.MarkedAction.plusComponentSection K L T z v hL hz hK hn).action.comp
        (plusImage K L T z v hL hz K).subtype)
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)))) :
    Tv T v ≤ normalizer (pointPreimage K L T z v hL hz e : Set G) ∧
      Tv T v ≤ normalizer (planePreimage K L T z v hL hz e : Set G) := by
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (show 2 = (2 : ℕ) ^ 1 by decide).trans_lt
      (Nat.pow_lt_pow_right (by decide) hm)
  have hflags (t : Tv T v) := flags_of_diagram
    (LinearThree.MarkedAction.modelAction K L T z v hL hz hn e t)
    (modelAction_preservesDiagram_of_natural K L T z v hL hz hlarge hK hn e hmodule t)
    (modelAction_unipotent K L T z v hL hz hF (by omega) hK hn e hmark t)
  exact ⟨LinearThree.MarkedAction.preimage_normalized_of_modelAction K L T z v hL hz hn e _
      (fun t => (hflags t).1),
    LinearThree.MarkedAction.preimage_normalized_of_modelAction K L T z v hL hz hn e _
      (fun t => (hflags t).2)⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction
