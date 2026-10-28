module
public import Theory.Representation.BinaryConjugationSection.NaturalExtension
public import Theory.Representation.SL2.NaturalCentralCommutator
public import Theory.Representation.SL2.NaturalAbelianExponent
public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.FirstCohomologyLinearTransport
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Algebra.ZMod

/-!
# Elementary quotients from two marked natural layers

Suppose V/Z and Q/V are natural binary SL₂ modules for the same covering
actor, and [Q,V] lies in Z. On the literal Q/Z quotient, the commutator
pairing vanishes by natural equivariance over a nonbinary field. The action
then descends through the actor's core, and the two-root exponent obstruction
makes every quotient element an involution.

Both coordinate maps and the actual quotient conjugation action are retained.
This proves the elementary-abelian step of DGS, *Groups and Graphs* (1985),
5.17, used in 9.10(6), pp.117,149. The direct-sum splitting is a further step.
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups commutatorElement IsMulCommutative
namespace Representation.BinaryConjugationSection
variable {G F : Type*} [Group G] [Field F] [Finite F] [CharP F 2]
local instance naturalCentralExtensionZModAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- Two natural layers with a central commutator give an elementary literal quotient. -/
theorem natural_central_extension_elementary
    (H Q V Z : Subgroup G) (hVQ : V ≤ Q) (hZV : Z ≤ V)
    (hNZ : H ≤ normalizer (Z : Set G)) [(Z.subgroupOf Q).Normal]
    (π : H →* SL(2,F)) (hπ : Function.Surjective π) (hk : π.ker = Q.subgroupOf H)
    (cV : BinaryConjugationSection H V Z
      (((specialLinearNatural 2).restrictScalars (k := ZMod 2)).comp π))
    (cQ : BinaryConjugationSection H Q V
      (((specialLinearNatural 2).restrictScalars (k := ZMod 2)).comp π))
    (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1) (hc : ⁅Q,V⁆ ≤ Z) :
    ⁅Q,Q⁆ ≤ Z ∧ IsElementaryAbelian 2 (Q ⧸ Z.subgroupOf Q) := by
  let R := Q ⧸ Z.subgroupOf Q
  let q : Q →* R := QuotientGroup.mk' (Z.subgroupOf Q)
  let e : Multiplicative (Fin 2 → F) ≃* Multiplicative (Fin 1 → Fin 2 → F) :=
    (LinearEquiv.funUnique (Fin 1) (ZMod 2) (Fin 2 → F)).symm.toAddEquiv.toMultiplicative
  let c := e.toMonoidHom.comp cQ.coordinates
  have hZc : Z.subgroupOf Q ≤ c.ker := by
    intro x hx
    change e (cQ.coordinates x) = 1
    rw [(cQ.coordinates_eq_one_iff x).mpr (hZV hx), map_one]
  let f : R →* Multiplicative (Fin 1 → Fin 2 → F) :=
    QuotientGroup.lift (Z.subgroupOf Q) c hZc
  have hfq (x : Q) : f (q x) = e (cQ.coordinates x) := rfl
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x,hx⟩ := cQ.onto (e.symm y)
    exact ⟨q x,by rw [hfq,hx,e.apply_symm_apply]⟩
  have hfker (x : Q) : q x ∈ f.ker ↔ (x : G) ∈ V := by
    change e (cQ.coordinates x) = 1 ↔ _
    rw [←e.map_one,e.injective.eq_iff,cQ.coordinates_eq_one_iff]
  let r : V →* f.ker := {
    toFun v := ⟨q (inclusion hVQ v),(hfker _).mpr v.property⟩
    map_one' := Subtype.ext q.map_one
    map_mul' v w := by
      apply Subtype.ext
      change q (inclusion hVQ (v*w)) = _
      rw [map_mul, map_mul]
      rfl }
  have hr : Function.Surjective r := by
    intro y
    obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf Q) (y : R)
    have hxV : (x : G) ∈ V := (hfker x).mp (hx ▸ y.property)
    exact ⟨⟨x,hxV⟩,Subtype.ext hx⟩
  have hrc : r.ker ≤ cV.coordinates.ker := by
    intro v hv
    apply (cV.coordinates_eq_one_iff v).mpr
    have hvq : q (inclusion hVQ v) = 1 := congrArg Subtype.val hv
    exact (QuotientGroup.eq_one_iff (N := Z.subgroupOf Q) (inclusion hVQ v)).mp hvq
  let z : f.ker →* Multiplicative (Fin 2 → F) :=
    r.liftOfSurjective hr ⟨cV.coordinates,hrc⟩
  have hzr (v : V) : z (r v) = cV.coordinates v :=
    r.liftOfRightInverse_comp_apply _ _ _ v
  have hzi : Function.Injective z := by
    apply (MonoidHom.ker_eq_bot_iff z).mp
    apply bot_unique
    intro y hy
    obtain ⟨v,rfl⟩ := hr y
    have hvZ : (v : G) ∈ Z := (cV.coordinates_eq_one_iff v).mp (by
      simpa only [MonoidHom.mem_ker,hzr] using hy)
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr hvZ
  have hzs : Function.Surjective z := by
    intro y
    obtain ⟨v,hv⟩ := cV.onto y
    exact ⟨r v,(hzr v).trans hv⟩
  have hcentral : f.ker ≤ center R := by
    intro y hy
    obtain ⟨v,hv⟩ := hr ⟨y,hy⟩
    have hvr : q (inclusion hVQ v) = y := congrArg Subtype.val hv
    rw [←hvr]
    apply mem_center_iff.mpr
    intro x
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf Q) x
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact hc (commutator_mem_commutator u.property v.property)
  obtain ⟨φ,hφ⟩ := exists_quotient_conjugation_action H Q Z cQ.normalized hNZ inferInstance
  have he (g : H) (x : R) :
      (f (φ g x)).toAdd = fun i => (π g).val *ᵥ (f x).toAdd i := by
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf Q) x
    rw [hφ,hfq,hfq]
    funext i
    exact cQ.equivariant g u
  have heZ (g : H) (x y : f.ker) (hxy : φ g x = y) :
      (z y).toAdd = (π g).val *ᵥ (z x).toAdd := by
    obtain ⟨v,rfl⟩ := hr x
    let v' : V := ⟨(g : G) * v * (g : G)⁻¹,
      (mem_normalizer_iff.mp (cV.normalized g.property) v).mp v.property⟩
    have hy : y = r v' := by
      apply Subtype.ext
      rw [←hxy]
      exact hφ g (inclusion hVQ v)
    rw [hy,hzr,hzr]
    exact cV.equivariant g v
  let hcomm := SL2.commutative_of_natural_central_extension a ha0 ha1 f hf hcentral z hzi π hπ φ he heZ
  let := hcomm
  have hQQ : ⁅Q,Q⁆ ≤ Z := by
    apply commutator_le.mpr
    intro x hx y hy
    have hz : q ⁅(⟨x,hx⟩ : Q),⟨y,hy⟩⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
    exact (QuotientGroup.eq_one_iff (N := Z.subgroupOf Q) ⁅(⟨x,hx⟩ : Q),⟨y,hy⟩⁆).mp hz
  have hkill : π.ker ≤ φ.ker := by
    rw [hk]
    exact quotient_conjugation_action_kills_commutator_layer H Q Z Q inferInstance
      cQ.normalized hQQ φ hφ
  have hs := SL2.square_eq_one_of_natural_abelian_extension a ha0 ha1 f hf z ⟨hzi,hzs⟩
    π hπ φ hkill he heZ
  exact ⟨hQQ,{ exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }⟩

/-- The elementary quotient carries its literal conjugation representation and
both natural factors; its distinguished submodule is exactly the image of V. -/
theorem natural_central_extension_factors
    (H Q V Z : Subgroup G) (hVQ : V ≤ Q) (hZV : Z ≤ V)
    (hNZ : H ≤ normalizer (Z : Set G)) [(Z.subgroupOf Q).Normal]
    (π : H →* SL(2,F)) (hπ : Function.Surjective π) (hk : π.ker = Q.subgroupOf H)
    (cV : BinaryConjugationSection H V Z
      (((specialLinearNatural 2).restrictScalars (k := ZMod 2)).comp π))
    (cQ : BinaryConjugationSection H Q V
      (((specialLinearNatural 2).restrictScalars (k := ZMod 2)).comp π))
    (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1) (hc : ⁅Q,V⁆ ≤ Z) :
    ⁅Q,Q⁆ ≤ Z ∧
    ∃ hE : IsElementaryAbelian 2 (Q ⧸ Z.subgroupOf Q),
      letI := hE
      ∃ (ρ : Representation (ZMod 2) SL(2,F) (Additive (Q ⧸ Z.subgroupOf Q)))
        (c : BinaryConjugationSection H Q Z (ρ.comp π)),
        (∀ s : Q, (c.coordinates s).toAdd =
          Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf Q) s)) ∧
        ∃ (X : Subrepresentation ρ)
          (eX : X.toSubmodule ≃ₗ[ZMod 2] (Fin 2 → F))
          (eQ : (Additive (Q ⧸ Z.subgroupOf Q) ⧸ X.toSubmodule) ≃ₗ[ZMod 2] (Fin 2 → F)),
          (∀ g x, eX (X.toRepresentation g x) = Matrix.mulVec g.val (eX x)) ∧
          (∀ g x, eQ (X.quotientRepresentation g x) = Matrix.mulVec g.val (eQ x)) ∧
          X.toSubmodule = c.imageSpace V := by
  obtain ⟨hQQ,hE⟩ := natural_central_extension_elementary H Q V Z hVQ hZV
    hNZ π hπ hk cV cQ a ha0 ha1 hc
  let := hE
  obtain ⟨ρ,c,he⟩ := exists_canonical H Q Z cQ.section_le (hZV.trans hVQ)
    cQ.normalized hNZ π hπ hk
  refine ⟨hQQ,hE,ρ,c,he,?_⟩
  exact exists_natural_submodule H Q V Z hVQ hZV π hπ ρ
    ((specialLinearNatural 2).restrictScalars (k := ZMod 2)) c cV cQ

end Representation.BinaryConjugationSection
