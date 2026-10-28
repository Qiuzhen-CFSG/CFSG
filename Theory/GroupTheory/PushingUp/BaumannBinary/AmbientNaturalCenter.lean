module
public import Theory.Representation.BinaryConjugationSection.TwoGroupScalarCommutant
public import Theory.Representation.SL2NaturalOffenders.Semilinear
public import Theory.GroupTheory.ConjugateSpanNormalClosure
public import Theory.GroupTheory.SylowCenterFixedSpan
public import Theory.GroupTheory.PushingUp.BaumannBinary.NaturalAll
public import Theory.Representation.NormalElementaryQuotient.NaturalMovedFixed

/-!
# Ambient Sylow centers detect a natural Baumann module

For a normal Baumann closure X, its Sylow-center module V is characteristic
under the ambient conjugation action. The ambient two-core commutes with X
on V modulo the X-core. Its action on the natural central quotient is scalar
and therefore trivial. The three-subgroup lemma makes it centralize [V,X].

If an ambient Sylow T lies in X O₂(G), the natural moved fixed-vector theorem
now gives a noncentral vector fixed by T. It lies in Ω₁(Z(T)), contradicting
centralization of X by that omega-center. This works over every finite field
of characteristic two and retains nonsplit central attachments.

Source: DGS, Groups and Graphs (1985), (6.5), pp.121--122. The literal
adjacent-core application is LocalStructure.LinearCenterExclusion.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative Pointwise
public noncomputable section
namespace Theory.GroupTheory.BaumannBinary
open Representation
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
local instance ambientNaturalAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

theorem ambient_core_centralizes_movement
    (X : Subgroup G) [X.Normal] (P : Sylow 2 X)
    (hc : centralizer (pCore 2 X : Set X) ≤ pCore 2 X)
    (hP : NoCharacteristicNormal (P : Subgroup X))
    (q : X →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 X) :
    pCore 2 G ≤ centralizer (↑(⁅(centerClosure (P : Subgroup X)).map X.subtype,X⁆ : Subgroup G) : Set G) := by
  let Vi := centerClosure (P : Subgroup X)
  let : IsElementaryAbelian 2 Vi := (centerClosure_reduced P hc).elementary
  let V := Vi.map X.subtype
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  have hV : V = AmalgamGraph.sylowCenterSpan X := by
    rw [AmalgamGraph.sylowCenterSpan_eq_conjugateSpan X X le_rfl
      (fun _ => map_subtype_le _) P]
    change (normalClosure (omegaCenterIn (P : Subgroup X) : Set X)).map X.subtype = _
    rw [map_normalClosure_eq_conjugateSpanBy_range,
      NilesRankOneKernel.omegaCenterIn_map_injective _ X.subtype_injective,range_subtype]
  let : V.Normal := by
    rw [hV]
    apply normalizer_eq_top_iff.mp
    apply top_unique
    intro g _
    rw [mem_normalizer_iff_map_conj_eq]
    change (AmalgamGraph.sylowCenterSpan X).map (MulAut.conj g).toMonoidHom = _
    rw [←AmalgamGraph.sylowCenterSpan_map]
    congr 1
    exact mem_normalizer_iff_map_conj_eq.mp (show g ∈ normalizer (X : Set G) from
      X.normalizer_eq_top.symm ▸ mem_top g)
  let := Fintype.ofFinite F
  obtain ⟨n,_,hF⟩ := FiniteField.card F 2
  have hcard : Nat.card F = 2^n.val := (Nat.card_eq_fintype_card (α := F)).trans hF
  obtain ⟨f,hf,hfker,hfe⟩ := centerClosure_natural_projection_all P hc hP q hq hk n.property hcard
  have hker (v : Additive Vi) : f v = 0 ↔ (v.toMul : X) ∈ center X := by
    change v ∈ LinearMap.ker f ↔ _
    rw [hfker]
    change ((v.toMul : X) ∈ Vi ∧ (v.toMul : X) ∈ center X) ↔ _
    exact and_iff_right v.toMul.property
  let e : Vi ≃* V := Vi.equivMapOfInjective X.subtype X.subtype_injective
  let π : V →* Multiplicative (Fin 2 → F) := {
    toFun v := Multiplicative.ofAdd (f (Additive.ofMul (e.symm v)))
    map_one' := by simp
    map_mul' a b := by simp only [map_mul]; exact f.map_add _ _ }
  let σ : Representation (ZMod 2) X (Fin 2 → F) :=
    (specialLinearNatural 2 (k := F)).restrictScalars.comp q
  have he (v : Vi) : ((e v : V) : G) = ((v : X) : G) := rfl
  have he' (v : V) : (((e.symm v : Vi) : X) : G) = v := by
    rw [←he,e.apply_symm_apply]
  have hcX (v : Vi) : (v : X) ∈ center X ↔ ((v : X) : G) ∈ centralizer (X : Set G) := by
    rw [mem_center_iff]
    constructor
    · intro hv x hx
      exact congrArg Subtype.val (hv ⟨x,hx⟩)
    · intro hv x
      exact Subtype.ext (hv x x.property)
  let d : BinaryConjugationSection X V (V ⊓ centralizer (X : Set G)) σ := {
    section_le := map_subtype_le _
    kernel_le := inf_le_left
    normalized := le_normalizer_of_normal
    coordinates := π
    onto := by
      intro u
      obtain ⟨v,hv⟩ := hf u.toAdd
      refine ⟨e v.toMul, ?_⟩
      change Multiplicative.ofAdd (f (Additive.ofMul (e.symm (e v.toMul)))) = u
      rw [e.symm_apply_apply]
      exact congrArg Multiplicative.ofAdd hv
    kernel_eq := by
      ext v
      change f (Additive.ofMul (e.symm v)) = 0 ↔ (v : G) ∈ V ⊓ centralizer (X : Set G)
      rw [hker]
      change (e.symm v : X) ∈ center X ↔ _
      rw [hcX,he']
      exact (and_iff_right v.property).symm
    equivariant := by
      intro x v
      change f (Additive.ofMul (e.symm _)) = Matrix.mulVec (q x).val (f (Additive.ofMul (e.symm v)))
      rw [←hfe]
      congr 2
      apply e.injective
      apply Subtype.ext
      change ((e (e.symm _) : V) : G) = ((e (MulAut.conjNormal x (e.symm v)) : V) : G)
      rw [e.apply_symm_apply,he]
      change (x : G)*(v : G)*(x : G)⁻¹ = (x : G)*(((e.symm v : Vi) : X) : G)*(x : G)⁻¹
      rw [he'] }
  have hs : ∀ a : (Fin 2 → F) →ₗ[ZMod 2] (Fin 2 → F),
      (∀ x v, a (σ x v) = σ x (a v)) → ∃ c : F, ∀ v, a v = c • v := by
    intro a ha
    apply SL2NaturalOffenders.centralizer_scalar a.toAddMonoidHom
    intro g v
    obtain ⟨x,rfl⟩ := hq g
    exact ha x v
  have hcomm : ⁅pCore 2 G,X⁆ ≤ centralizer (V : Set G) := by
    have hi : ⁅pCore 2 G,X⁆ ≤ X.pCoreIn 2 := by
      apply le_pCoreIn_of_normalizes
        (pCore_isPGroup.to_le (commutator_le_left _ _)) (commutator_le_right _ _)
      exact le_normalizer_of_normal
    apply hi.trans
    rintro _ ⟨a,ha,rfl⟩ v hv
    obtain ⟨w,hw,rfl⟩ := hv
    exact congrArg Subtype.val ((le_centralizer_iff.mp (centerClosure_reduced P hc).le_centralizer_pCore) ha w hw)
  exact d.centralizes_movement_of_twoGroup_scalar_commutant hs (pCore 2 G) pCore_isPGroup
    le_normalizer_of_normal le_normalizer_of_normal hcomm

/-- The ambient Sylow detects the natural Baumann layer whenever its core and X cover that Sylow. -/
theorem ambient_sylow_omega_noncentral_of_core_cover
    (X : Subgroup G) [X.Normal] (P : Sylow 2 X) (T : Sylow 2 G)
    (hc : centralizer (pCore 2 X : Set X) ≤ pCore 2 X)
    (hP : NoCharacteristicNormal (P : Subgroup X))
    (q : X →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 X)
    (hcover : (T : Subgroup G) ≤ X ⊔ pCore 2 G) :
    ¬ omegaCenterIn (T : Subgroup G) ≤ centralizer (X : Set G) := by
  let Vi := centerClosure (P : Subgroup X)
  let : IsElementaryAbelian 2 Vi := (centerClosure_reduced P hc).elementary
  let := Fintype.ofFinite F
  obtain ⟨n,_,hF⟩ := FiniteField.card F 2
  have hcard : Nat.card F = 2^n.val := (Nat.card_eq_fintype_card (α := F)).trans hF
  obtain ⟨f,hf,hfker,hfe⟩ := centerClosure_natural_projection_all P hc hP q hq hk n.property hcard
  have hker (v : Additive Vi) : f v = 0 ↔ (v.toMul : X) ∈ center X := by
    change v ∈ LinearMap.ker f ↔ _
    rw [hfker]
    change ((v.toMul : X) ∈ Vi ∧ (v.toMul : X) ∈ center X) ↔ _
    exact and_iff_right v.toMul.property
  have hkV : q.ker = centralizer (Vi : Set X) :=
    hk.trans (centerClosure_centralizer P hc hP q hq hk n.property hcard).symm
  obtain ⟨v,hv,hvfix,hvne⟩ := NormalElementaryQuotient.natural_projection_movement_fixed_nonzero
    Vi q hq hkV f hf hker hfe ((T : Subgroup G).subgroupOf X) T.isPGroup'.comap_subtype
  have hvW : ((v.toMul : X) : G) ∈ ⁅Vi.map X.subtype,X⁆ := by
    have hh := mem_map_of_mem X.subtype hv
    rwa [map_commutator,←MonoidHom.range_eq_map,range_subtype] at hh
  have hQT : pCore 2 G ≤ (T : Subgroup G) := pCore_isPGroup.le_sylow_of_normal T
  have hvT : ((v.toMul : X) : G) ∈ (T : Subgroup G) :=
    (pCore_isPGroup.map X.subtype).le_sylow_of_normal T
      (mem_map_of_mem X.subtype ((centerClosure_reduced P hc).le_pCore v.toMul.property))
  have hQ := ambient_core_centralizes_movement X P hc hP q hq hk
  have hcent : ((v.toMul : X) : G) ∈ centralizer (T : Set G) := by
    intro t ht
    have htprod : t ∈ (X : Set G) * (pCore 2 G : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right X (pCore 2 G) le_normalizer_of_normal]
      exact hcover ht
    obtain ⟨x,hx,r,hr,rfl⟩ := htprod
    have hxT : x ∈ (T : Subgroup G) := by
      simpa only [mul_inv_cancel_right] using
        (T : Subgroup G).mul_mem ht ((T : Subgroup G).inv_mem (hQT hr))
    have hxc : x * ((v.toMul : X) : G) = ((v.toMul : X) : G) * x :=
      congrArg Subtype.val (hvfix ⟨x,hx⟩ hxT)
    have hrc : r * ((v.toMul : X) : G) = ((v.toMul : X) : G) * r :=
      (hQ hr _ hvW).symm
    rw [mul_assoc,hrc,←mul_assoc,hxc,mul_assoc]
  have hvΩ : ((v.toMul : X) : G) ∈ omegaCenterIn (T : Subgroup G) := by
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨hvT,hcent,?_⟩
    exact congrArg Subtype.val
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) (v.toMul : X) v.toMul.property)
  intro hz
  apply hvne
  apply (hker v).mpr
  rw [mem_center_iff]
  intro x
  exact Subtype.ext (hz hvΩ x x.property)

end Theory.GroupTheory.BaumannBinary
