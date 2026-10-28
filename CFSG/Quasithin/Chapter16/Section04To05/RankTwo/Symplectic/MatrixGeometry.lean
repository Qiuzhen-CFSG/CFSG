module

public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.Symplectic.Orbit
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry
public import Theory.GroupTheory.EmbeddedCenterMap
public import Theory.Frattini.OmegaProducts
public import Theory.GroupTheory.CharacteristicCentralizerFusion
/-!
# Matrix construction of the symplectic central plane and Cartan action

A model equivalence carrying the marked Sylow subgroup to the standard
unipotent subgroup transports its embedded center, Frattini subgroup and
maximum-elementary Thompson subgroup. The two-root parametrization constructs
the published `RootPlane`; the actual diagonal matrices construct `CartanAction`
and normalize the marked Sylow subgroup in the ambient group.

For an arbitrary Sylow marking, genuine Sylow conjugacy first adjusts the model
by an inner automorphism. The root predicate is invariant under this adjustment,
so uniform root-exclusion hypotheses can be transported without changing their
meaning. Ambient Thompson configuration and final exclusion remain separate.

Source: Aschbacher–Smith, Lemma 16.5.13, printed p.1202.
-/

@[expose] public section
open Subgroup
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter16.Intersections.RankTwo.Symplectic.MatrixGeometry
variable {G : Type*} [Group G] {F : Type*} [Field F] [CharP F 2] [Finite F]
variable {L TL W : Subgroup G} (eL : L ≃* Sp F)

/-- The actual matrix model included in the ambient group. -/
noncomputable def modelEmbedding : Sp F →* G := L.subtype.comp eL.symm.toMonoidHom

omit [CharP F 2] [Finite F] in
theorem modelEmbedding_injective : Function.Injective (modelEmbedding eL) :=
  Subtype.val_injective.comp eL.symm.injective

variable (hTL : TL ≤ L) (hmark : (TL.subgroupOf L).map eL.toMonoidHom = unipotent)

/-- The marking preserves the actual Sylow inclusion. -/
noncomputable def markedSylowEquiv : TL ≃* unipotent (F := F) :=
  (subgroupOfEquivOfLe hTL).symm.trans
    ((eL.subgroupMap (TL.subgroupOf L)).trans (MulEquiv.subgroupCongr hmark))

omit [CharP F 2] [Finite F] in
include hTL hmark in
theorem unipotent_map : (unipotent (F := F)).map (modelEmbedding eL) = TL := by
  have h : (unipotent (F := F)).map eL.symm.toMonoidHom = TL.subgroupOf L := by
    rw [← hmark, map_map]
    simp
  rw [modelEmbedding, ← map_map, h, map_subgroupOf_eq_of_le hTL]

variable (hW : W = (center TL).map TL.subtype)

omit [CharP F 2] [Finite F] in
include hTL hmark hW in
theorem embedded_center_map :
    ((center (unipotent (F := F))).map (unipotent (F := F)).subtype).map
      (modelEmbedding eL) = W := by
  rw [map_embeddedCenter _ _ (modelEmbedding_injective eL), unipotent_map eL hTL hmark, ← hW]

noncomputable def planeParameter : (Multiplicative F × Multiplicative F) →* G :=
  (modelEmbedding eL).comp CentralRootGeometry.parameter

omit [Finite F] in
theorem planeParameter_injective : Function.Injective (planeParameter eL) :=
  (modelEmbedding_injective eL).comp CentralRootGeometry.parameter_injective

include hTL hmark hW in
theorem planeParameter_range : (planeParameter eL).range = W := by
  rw [planeParameter, MonoidHom.range_comp, CentralRootGeometry.parameter_range,
    embedded_center_map eL hTL hmark hW]

noncomputable def planeEquiv : (Multiplicative F × Multiplicative F) ≃* W :=
  (MonoidHom.ofInjective (planeParameter_injective eL)).trans
    (MulEquiv.subgroupCongr (planeParameter_range eL hTL hmark hW))

theorem planeEquiv_val (x : Multiplicative F × Multiplicative F) :
    (planeEquiv eL hTL hmark hW x : G) = planeParameter eL x := rfl

include hTL hW in
theorem center_le_component : W ≤ L := by
  rw [hW]
  rintro _ ⟨x,_,rfl⟩
  exact hTL x.property

/-- The published root-plane coordinates, for a genuinely standard marking. -/
noncomputable def rootPlane : RootPlane L W eL where
  le_component := center_le_component hTL hW
  coordinates := (planeEquiv eL hTL hmark hW).symm
  model_eq w := by
    rw [← CentralRootGeometry.parameter_apply]
    apply eL.symm.injective
    rw [eL.symm_apply_apply]
    apply Subtype.ext
    exact (congrArg Subtype.val ((planeEquiv eL hTL hmark hW).apply_symm_apply w)).symm

/-- The actual diagonal Cartan lifted into the component. -/
noncomputable def cartanHom : (Fˣ × Fˣ) →* L :=
  eL.symm.toMonoidHom.comp CentralRootGeometry.diagonalTorusHom

omit [CharP F 2] [Finite F] in
theorem cartanHom_model (a : Fˣ × Fˣ) :
    eL (cartanHom eL a) = diagonalTorus a.1 a.2 := eL.apply_symm_apply _

omit [CharP F 2] [Finite F] in
include hTL hmark in
theorem cartan_normalizes_sylow (a : Fˣ × Fˣ) :
    (cartanHom eL a : G) ∈ normalizer (TL : Set G) := by
  rw [← unipotent_map eL hTL hmark]
  exact (unipotent (F := F)).le_normalizer_map (modelEmbedding eL)
    ⟨CentralRootGeometry.diagonalTorusHom a, CentralRootGeometry.diagonalTorus_normalizes a,rfl⟩

omit [CharP F 2] [Finite F] in
include hTL hmark hW in
theorem cartan_normalizes_center (a : Fˣ × Fˣ) :
    (cartanHom eL a : G) ∈ normalizer (W : Set G) := by
  rw [hW]
  exact normalizer_le_normalizer_characteristic_image TL (center TL)
    (cartan_normalizes_sylow eL hTL hmark a)

/-- The published Cartan action retains the diagonal model and exact root weights. -/
noncomputable def cartanAction : CartanAction (rootPlane eL hTL hmark hW) where
  hom := cartanHom eL
  model_eq := cartanHom_model eL
  normalizes_right := cartan_normalizes_center eL hTL hmark hW
  weights a w := by
    apply (planeEquiv eL hTL hmark hW).injective
    change (planeEquiv eL hTL hmark hW)
      ((planeEquiv eL hTL hmark hW).symm _) = _
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [planeEquiv_val]
    let x := (planeEquiv eL hTL hmark hW).symm w
    have hw : (w : G) = planeParameter eL x :=
      (congrArg Subtype.val ((planeEquiv eL hTL hmark hW).apply_symm_apply w)).symm
    change (cartanHom eL a : G) * (w : G) * (cartanHom eL a : G)⁻¹ = _
    rw [hw]
    change modelEmbedding eL (CentralRootGeometry.diagonalTorusHom a) *
      modelEmbedding eL (CentralRootGeometry.parameter x) *
      (modelEmbedding eL (CentralRootGeometry.diagonalTorusHom a))⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg (modelEmbedding eL)
      (CentralRootGeometry.diagonalTorus_weights a x.1.toAdd x.2.toAdd)

/-- This is the normalization input used by the ambient Thompson configuration. -/
theorem cartanAction_normalizes_sylow (a : Fˣ × Fˣ) :
    ((cartanAction eL hTL hmark hW).hom a : G) ∈ normalizer (TL : Set G) :=
  cartan_normalizes_sylow eL hTL hmark a

include hTL hmark hW in
theorem center_elementary : IsElementaryAbelian 2 W := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := CentralRootGeometry.center_elementary (F := F)
  let := IsElementaryAbelian.map (p := 2) (A := center (unipotent (F := F)))
    (unipotent (F := F)).subtype
  rw [← embedded_center_map eL hTL hmark hW]
  exact IsElementaryAbelian.map (modelEmbedding eL)

include hTL hmark in
theorem frattini_eq_center {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n) :
    frattini TL = center TL := by
  let e := markedSylowEquiv eL hTL hmark
  have hc : (center TL).map e.toMonoidHom = center (unipotent (F := F)) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (centerCongr e ⟨y,hy⟩).property
    · intro hx
      exact ⟨e.symm x, (centerCongr e.symm ⟨x,hx⟩).property, e.apply_symm_apply x⟩
  apply (Subgroup.map_injective (f := e.toMonoidHom) e.injective)
  rw [Subgroup.frattini_map_equiv, hc, CentralRootGeometry.frattini_eq_center hF hn]

include hTL hmark hW in
theorem embedded_frattini {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n) :
    (frattini TL).map TL.subtype = W := by
  rw [frattini_eq_center eL hTL hmark hF hn, ← hW]

include hTL hmark in
theorem elementaryAbelianMaxJ_eq : Stellmacher.elementaryAbelianMaxJ TL = TL := by
  rw [← unipotent_map eL hTL hmark,
    Stellmacher.elementaryAbelianMaxJ_map_injective _ (modelEmbedding_injective eL),
    CentralRootGeometry.elementaryAbelianMaxJ_unipotent]
omit [CharP F 2] in
/-- Sylow conjugacy supplies a standard marking by changing the model equivalence. -/
theorem exists_standard_marking {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 ≤ n)
    (P : Sylow 2 L) (hP : (P : Subgroup L) = TL.subgroupOf L) :
    ∃ g : Sp F, (TL.subgroupOf L).map (eL.trans (MulAut.conj g)).toMonoidHom = unipotent := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Finite L := Finite.of_injective eL eL.injective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Sp F)
    (P.mapSurjective (f := eL.toMonoidHom) eL.surjective) (unipotentSylow hF hn)
  refine ⟨g,?_⟩
  have he := congrArg Sylow.toSubgroup hg
  change ((P : Subgroup L).map eL.toMonoidHom).map (MulAut.conj g).toMonoidHom = unipotent at he
  rw [hP, map_map] at he
  exact he

omit [CharP F 2] [Finite F] in
/-- Changing the model by inner conjugation preserves the genuine root predicate. -/
theorem isModelRoot_conjugate_iff (g : Sp F) (w : G) :
    IsModelRoot (eL.trans (MulAut.conj g)) w ↔ IsModelRoot eL w := by
  constructor
  · rintro ⟨hw,h,r,t,ht,he⟩
    refine ⟨hw,g⁻¹*h,r,t,ht,?_⟩
    have hh := congrArg (MulAut.conj g⁻¹) he
    simpa only [MulEquiv.trans_apply, MulAut.conj_apply, mul_inv_rev, inv_inv,
      mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh
  · rintro ⟨hw,h,r,t,ht,he⟩
    refine ⟨hw,g*h,r,t,ht,?_⟩
    change g * eL ⟨w,hw⟩ * g⁻¹ = _
    rw [he]
    simp only [mul_inv_rev, mul_assoc]

end CFSG.Quasithin.Chapter16.Intersections.RankTwo.Symplectic.MatrixGeometry
