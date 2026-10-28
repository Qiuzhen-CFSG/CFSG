module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.OrbitReduction
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.ModuleIdentifications
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.RemainingModels.Exchanged

/-!
# Compatible coordinates for an exchanged pair of central quotients

Let K₀ be the marked internal product of K and Kᵗ, where the actual
normalizer element t has Kᵗ = K^(t⁻¹). For an invariant constituent I
centralized by Kᵗ, the sum map (i,j) ↦ i + ρ(t⁻¹)j induces coordinates
on W/C_W(K₀), with W = I + Iᵗ. The key calculation proves that its
central kernel consists precisely of pairs from C_I(K). Comparing this
surjection with the two copies of a specified constituent identification
constructs the linear equivalence, its lift formula and equivariance.

The first actor map is the marked product projection followed by the
given model isomorphism. The second is its pullback by conjugation by t;
thus the exchanged-action API receives t⁻¹. Conjugating the original
constituent constructs the other identification with these same maps.
The product kernel and return identities give cross-centralization on
both coordinate axes. If t normalizes the Borel, its two model images
agree, so only the first Borel marking needs to be supplied.

These are generic linear-algebra constructions from explicit product,
return and cross-centralization premises. Their source assembly belongs
to the exchanged-case restriction argument.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
F.9.18(5iiia), printed pp.325--326; 15.3.65(i), printed p.1152.
-/

open Representation Representation.BinaryOffender Subgroup
public noncomputable section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.PairCoordinates
variable {D E V X : Type*} [Group D] [Group E]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup X] [Module (ZMod 2) X]

/-- An internal product marked by literal inclusion and right conjugation.
The return condition records that the same element exchanges the two factors. -/
structure ProductMarking (K K₀ : Subgroup D) (t : D) where
  le : K ≤ K₀
  normalizes : t ∈ normalizer (K₀ : Set D)
  product : K × K ≃* K₀
  first : ∀ k : K, (product (k, 1) : D) = k
  second : ∀ k : K, (product (1, k) : D) = t⁻¹ * k * t
  return_eq : K.conjBy t = K.conjBy t⁻¹

private def commonKernelEquiv {U Y Z : Type*}
    [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    [AddCommGroup Z] [Module (ZMod 2) Z]
    (f : U →ₗ[ZMod 2] Y) (g : U →ₗ[ZMod 2] Z)
    (hf : Function.Surjective f) (hg : Function.Surjective g) (hk : f.ker = g.ker) :
    Y ≃ₗ[ZMod 2] Z :=
  (f.quotKerEquivOfSurjective hf).symm.trans
    ((Submodule.quotEquivOfEq _ _ hk).trans (g.quotKerEquivOfSurjective hg))

private theorem commonKernelEquiv_apply {U Y Z : Type*}
    [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    [AddCommGroup Z] [Module (ZMod 2) Z]
    (f : U →ₗ[ZMod 2] Y) (g : U →ₗ[ZMod 2] Z)
    (hf : Function.Surjective f) (hg : Function.Surjective g) (hk : f.ker = g.ker) (u : U) :
    commonKernelEquiv f g hf hg hk (f u) = g u := by
  simp [commonKernelEquiv]

namespace ProductMarking
variable {K K₀ : Subgroup D} {t : D} (p : ProductMarking K K₀ t)

include p

/-- Projection onto the marked first component. -/
@[expose] def firstProjection : K₀ →* K := (MonoidHom.fst K K).comp p.product.symm.toMonoidHom

/-- The element passed to the left-action exchanged model is the inverse
of the source's right-conjugating element. -/
@[expose] def exchanger : normalizer (K₀ : Set D) := ⟨t⁻¹, (normalizer _).inv_mem p.normalizes⟩

/-- Pullback for the action on the second coordinate: g maps to tgt⁻¹. -/
@[expose] def pullback : MulAut K₀ := (K₀.normalizerMonoidHom p.exchanger).symm

@[simp] theorem pullback_coe (g : K₀) : (p.pullback g : D) = t * g * t⁻¹ := by
  simp [pullback, ← MulAut.inv_def, ← map_inv,
    Subgroup.normalizerMonoidHom_apply_apply_coe, exchanger]

@[simp] theorem firstProjection_product (a b : K) :
    p.firstProjection (p.product (a, b)) = a := by
  simp [firstProjection]

theorem product_coe (a b : K) : (p.product (a, b) : D) = a * (t⁻¹ * b * t) := by
  have h : (a, b) = (a, (1 : K)) * (1, b) := by simp
  rw [h, map_mul, Subgroup.coe_mul, p.first, p.second]

theorem firstProjection_inclusion (k : K) :
    p.firstProjection ⟨k, p.le k.property⟩ = k := by
  have h : (⟨k, p.le k.property⟩ : K₀) = p.product (k, 1) := Subtype.ext (p.first k).symm
  rw [h, p.firstProjection_product]

theorem conjugate_le : K.conjBy t⁻¹ ≤ K₀ := by
  rintro _ ⟨k, hk, rfl⟩
  have h := (p.product (1, ⟨k, hk⟩)).property
  rw [p.second] at h
  simpa using h

theorem firstProjection_conjugate (k : K) :
    p.firstProjection ⟨t⁻¹ * k * t, p.conjugate_le
      (show t⁻¹ * k * t ∈ K.conjBy t⁻¹ from ⟨k, k.property, by simp⟩)⟩ = 1 := by
  have h : (⟨t⁻¹ * k * t, p.conjugate_le
      (show t⁻¹ * k * t ∈ K.conjBy t⁻¹ from ⟨k, k.property, by simp⟩)⟩ : K₀) = p.product (1, k) :=
    Subtype.ext (p.second k).symm
  rw [h, p.firstProjection_product]

/-- The kernel is exactly the other literal factor. -/
theorem firstProjection_ker : p.firstProjection.ker = (K.conjBy t⁻¹).subgroupOf K₀ := by
  ext g
  constructor
  · intro hg
    have ha : (p.product.symm g).1 = 1 := hg
    have he := p.product_coe (p.product.symm g).1 (p.product.symm g).2
    change (p.product (p.product.symm g) : D) = _ at he
    rw [p.product.apply_symm_apply, ha] at he
    simp only [OneMemClass.coe_one, one_mul] at he
    change (g : D) ∈ K.conjBy t⁻¹
    exact ⟨(p.product.symm g).2, (p.product.symm g).2.property, by simpa using he.symm⟩
  · rintro ⟨k, hk, he⟩
    have he' : t⁻¹ * k * t = (g : D) := by simpa using he
    have hg : g = p.product (1, ⟨k, hk⟩) := by
      apply Subtype.ext
      exact he'.symm.trans (p.second ⟨k, hk⟩).symm
    rw [hg]
    exact p.firstProjection_product 1 ⟨k, hk⟩

variable (ρ : Representation (ZMod 2) D V) {I : Submodule (ZMod 2) V}
    (hcross : subspaceCommutator ρ I (K.conjBy t⁻¹) = ⊥)

include hcross
omit p in
private theorem first_fixed_conjugate (i : I) (g : K.conjBy t⁻¹) : ρ g i = i :=
  ((subspaceCommutator_eq_bot_iff ρ I _).mp hcross i.property) g

/-- The return condition transports the literal cross-centralization to
its other half: K centralizes the right-conjugate space. -/
theorem conjugate_fixed_first (j : I) (k : K) : ρ k (ρ t⁻¹ j) = ρ t⁻¹ j := by
  rw [rightConjugate_action]
  have hg : t * k * t⁻¹ ∈ K.conjBy t⁻¹ := by
    rw [← p.return_eq]
    exact ⟨k, k.property, rfl⟩
  rw [first_fixed_conjugate ρ hcross j ⟨_, hg⟩]

/-- On I the full K₀-action factors through the first product projection. -/
theorem action_first (g : K₀) (i : I) : ρ g i = ρ (p.firstProjection g) i := by
  obtain ⟨⟨a, b⟩, rfl⟩ := p.product.surjective g
  rw [p.firstProjection_product, p.product_coe, map_mul, Module.End.mul_apply]
  have hb : t⁻¹ * b * t ∈ K.conjBy t⁻¹ := ⟨b, b.property, by simp⟩
  rw [first_fixed_conjugate ρ hcross i ⟨_, hb⟩]

/-- On Iᵗ the action is the same projection after conjugation by t. -/
theorem action_second (g : K₀) (j : I) :
    ρ g (ρ t⁻¹ j) = ρ t⁻¹ (ρ (p.firstProjection (p.pullback g)) j) := by
  rw [rightConjugate_action, ← p.pullback_coe]
  rw [p.action_first ρ hcross]

/-- The essential kernel calculation: a sum of constituent lifts is
K₀-fixed exactly when both original lifts are K-fixed. -/
theorem sum_fixed_iff (i j : I) :
    (i : V) + ρ t⁻¹ j ∈ fixedSpace ρ K₀ ↔
      (i : V) ∈ fixedSpace ρ K ∧ (j : V) ∈ fixedSpace ρ K := by
  constructor
  · intro h
    constructor
    · intro k
      have he := h ⟨k, p.le k.property⟩
      change ρ k ((i : V) + ρ t⁻¹ j) = (i : V) + ρ t⁻¹ j at he
      rw [map_add, p.conjugate_fixed_first ρ hcross] at he
      exact add_right_cancel he
    · intro k
      have hk : t⁻¹ * k * t ∈ K.conjBy t⁻¹ := ⟨k, k.property, by simp⟩
      have he := h ⟨_, p.conjugate_le hk⟩
      change ρ (t⁻¹ * k * t) ((i : V) + ρ t⁻¹ j) = (i : V) + ρ t⁻¹ j at he
      rw [map_add, first_fixed_conjugate ρ hcross i ⟨_, hk⟩] at he
      have he' := add_left_cancel he
      have ht : ρ (t⁻¹ * k * t) (ρ t⁻¹ j) = ρ t⁻¹ (ρ k j) := by
        simp only [← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      rw [ht] at he'
      have hi : Function.Injective (ρ t⁻¹) := by
        apply Function.LeftInverse.injective (g := ρ t)
        intro v
        simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_apply]
      exact hi he'
  · rintro ⟨hi, hj⟩ g
    change ∀ k : K, ρ k i = i at hi
    change ∀ k : K, ρ k j = j at hj
    change ρ g ((i : V) + ρ t⁻¹ j) = _
    rw [map_add, p.action_first ρ hcross, p.action_second ρ hcross, hi, hj]

omit p hcross in
/-- Sum of the original constituent and its right conjugate. -/
@[expose] def pairLift (i j : I) : ↥(I ⊔ rightConjugate ρ I t) :=
  ⟨(i : V) + ρ t⁻¹ j, Submodule.add_mem_sup i.property ⟨j, j.property, rfl⟩⟩

omit p hcross in
private def sumMap : I × I →ₗ[ZMod 2] ↥(I ⊔ rightConjugate ρ I t) where
  toFun ij := pairLift ρ ij.1 ij.2
  map_add' := by intro a b; apply Subtype.ext; simp [pairLift]; abel
  map_smul' := by intro a b; apply Subtype.ext; simp [pairLift, smul_add]

omit p hcross in
private theorem sumMap_surjective : Function.Surjective (sumMap ρ (I := I) (t := t)) := by
  rintro ⟨w, hw⟩
  obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.mp hw
  obtain ⟨j, hj, rfl⟩ := hj
  exact ⟨(⟨i, hi⟩, ⟨j, hj⟩), rfl⟩

omit hcross in
private def pairQuotientMap : I × I →ₗ[ZMod 2]
    centralQuotient ρ K₀ (I ⊔ rightConjugate ρ I t) :=
  ((fixedSpace ρ K₀).comap (I ⊔ rightConjugate ρ I t).subtype).mkQ.comp (sumMap ρ)

omit p hcross in
private theorem pairQuotientMap_surjective :
    Function.Surjective (pairQuotientMap (K₀ := K₀) ρ (I := I) (t := t)) :=
  (Submodule.mkQ_surjective _).comp (sumMap_surjective ρ)

/-- Both summands are K₀-invariant, even though T need not normalize K. -/
theorem pair_invariant (hI : K₀ ≤ subspaceStabilizer ρ I) :
    K₀ ≤ subspaceStabilizer ρ (I ⊔ rightConjugate ρ I t) := by
  apply le_subspaceStabilizer
  intro g hg w hw
  obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.mp hw
  obtain ⟨j, hj, rfl⟩ := hj
  rw [map_add, p.action_second ρ hcross ⟨g, hg⟩ ⟨j, hj⟩]
  exact Submodule.add_mem_sup ((hI hg i).2 hi)
    ⟨ρ (p.firstProjection (p.pullback ⟨g, hg⟩)) j,
      (hI (p.le (p.firstProjection (p.pullback ⟨g, hg⟩)).property) j).2 hj, rfl⟩

variable {hI : K ≤ subspaceStabilizer ρ I} {σ : Representation (ZMod 2) E X}
    (d : CentralQuotientIdentification ρ K I hI σ)

omit p hcross in
/-- The specified first identification evaluated on a literal lift. -/
@[expose] def constituentMap : I →ₗ[ZMod 2] X :=
  d.linearEquiv.toLinearMap.comp ((fixedSpace ρ K).comap I.subtype).mkQ

omit p hcross in
private theorem constituentMap_surjective : Function.Surjective (constituentMap ρ d) :=
  d.linearEquiv.surjective.comp (Submodule.mkQ_surjective _)

omit p hcross in
private theorem constituentMap_eq_zero (i : I) :
    constituentMap ρ d i = 0 ↔ (i : V) ∈ fixedSpace ρ K := by
  change d.linearEquiv (Submodule.Quotient.mk i) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]
  rfl

omit hcross in
/-- The model map uses the original constituent's group identification. -/
@[expose] def modelMap : K₀ →* E := d.groupEquiv.toMonoidHom.comp p.firstProjection

omit hcross in
@[simp] theorem modelMap_first (k : K) :
    p.modelMap ρ d ⟨k, p.le k.property⟩ = d.groupEquiv k := by
  change d.groupEquiv (p.firstProjection _) = _
  rw [p.firstProjection_inclusion]

omit hcross in
/-- No additional kernel premise is assumed: it is the conjugate factor. -/
theorem modelMap_ker : (p.modelMap ρ d).ker = (K.conjBy t⁻¹).subgroupOf K₀ := by
  rw [← p.firstProjection_ker]
  ext g
  change d.groupEquiv (p.firstProjection g) = 1 ↔ p.firstProjection g = 1
  exact map_eq_one_iff d.groupEquiv d.groupEquiv.injective

private theorem pair_common_kernel :
    (pairQuotientMap (K₀ := K₀) ρ (I := I) (t := t)).ker =
      ((constituentMap ρ d).prodMap (constituentMap ρ d)).ker := by
  ext ij
  change Submodule.Quotient.mk (pairLift ρ ij.1 ij.2) =
    (0 : centralQuotient ρ K₀ _) ↔
    (constituentMap ρ d ij.1, constituentMap ρ d ij.2) = (0, 0)
  rw [Submodule.Quotient.mk_eq_zero, Prod.mk.injEq,
    constituentMap_eq_zero, constituentMap_eq_zero]
  exact p.sum_fixed_iff ρ hcross ij.1 ij.2

omit p hcross in
private theorem constituentPair_surjective :
    Function.Surjective ((constituentMap ρ d).prodMap (constituentMap ρ d)) := by
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := constituentMap_surjective ρ d x
  obtain ⟨j, rfl⟩ := constituentMap_surjective ρ d y
  exact ⟨(i, j), rfl⟩

/-- Constructed coordinates on the literal quotient W/C_W(K₀). -/
def pairEquiv : centralQuotient ρ K₀ (I ⊔ rightConjugate ρ I t) ≃ₗ[ZMod 2] X × X :=
  commonKernelEquiv (pairQuotientMap ρ) ((constituentMap ρ d).prodMap (constituentMap ρ d))
    (pairQuotientMap_surjective ρ) (constituentPair_surjective ρ d)
    (p.pair_common_kernel ρ hcross d)

/-- The coordinate formula keeps exactly the given identification d on
both original lifts; the second lift is acted on by t⁻¹. -/
theorem pairEquiv_lift (i j : I) :
    p.pairEquiv ρ hcross d (Submodule.Quotient.mk (pairLift ρ i j)) =
      (constituentMap ρ d i, constituentMap ρ d j) :=
  commonKernelEquiv_apply _ _ _ _ _ (i, j)

omit p hcross in
private theorem constituentMap_action (k : K) (i : I) :
    constituentMap ρ d ⟨ρ k i, (hI k.property i).2 i.property⟩ =
      σ (d.groupEquiv k) (constituentMap ρ d i) :=
  d.equivariant k (Submodule.Quotient.mk i)

/-- Equivariance for the actual normalizer element, with the inverse
orientation required by `RemainingModels.exchangedAction`. -/
theorem pairEquiv_equivariant (hI₀ : K₀ ≤ subspaceStabilizer ρ I)
    (g : K₀) (v : centralQuotient ρ K₀ (I ⊔ rightConjugate ρ I t)) :
    p.pairEquiv ρ hcross d
      (centralQuotientRepresentation ρ K₀ _ (p.pair_invariant ρ hcross hI₀) g v) =
    RemainingModels.exchangedAction σ K₀ p.exchanger (p.modelMap ρ d) g
      (p.pairEquiv ρ hcross d v) := by
  obtain ⟨⟨i, j⟩, rfl⟩ := pairQuotientMap_surjective ρ v
  let i' : I := ⟨ρ (p.firstProjection g) i, (hI (p.firstProjection g).property i).2 i.property⟩
  let j' : I := ⟨ρ (p.firstProjection (p.pullback g)) j,
    (hI (p.firstProjection (p.pullback g)).property j).2 j.property⟩
  have he : centralQuotientRepresentation ρ K₀ _ (p.pair_invariant ρ hcross hI₀) g
      (pairQuotientMap ρ (i, j)) = Submodule.Quotient.mk (pairLift ρ i' j') := by
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    change ρ g ((i : V) + ρ t⁻¹ j) = ρ (p.firstProjection g) i +
      ρ t⁻¹ (ρ (p.firstProjection (p.pullback g)) j)
    rw [map_add, p.action_first ρ hcross, p.action_second ρ hcross]
  rw [he]
  change p.pairEquiv ρ hcross d (Submodule.Quotient.mk (pairLift ρ i' j')) =
    RemainingModels.exchangedAction σ K₀ p.exchanger (p.modelMap ρ d) g
      (p.pairEquiv ρ hcross d (Submodule.Quotient.mk (pairLift ρ i j)))
  rw [p.pairEquiv_lift, p.pairEquiv_lift]
  exact Prod.ext (constituentMap_action ρ d (p.firstProjection g) i)
    (constituentMap_action ρ d (p.firstProjection (p.pullback g)) j)

omit p hcross in
private theorem conjugate_action (k : D) (v : V) :
    ρ (t⁻¹ * k * t) (ρ t⁻¹ v) = ρ t⁻¹ (ρ k v) := by
  simp only [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

omit p hcross in
/-- The actual conjugation isomorphism between the two constituent actors. -/
@[expose] def conjugateActor : K ≃* K.conjBy t⁻¹ := (MulAut.conj t⁻¹).subgroupMap K

omit p hcross in
@[simp] theorem conjugateActor_coe (k : K) :
    (conjugateActor (t := t) k : D) = t⁻¹ * k * t := by
  change ((MulAut.conj t⁻¹).subgroupMap K k : D) = _
  exact (MulEquiv.coe_subgroupMap_apply (MulAut.conj t⁻¹) K k).trans (by simp)

omit p hcross in
/-- Right conjugation on the constituent space, before taking quotients. -/
@[expose] def conjugateVector : I →ₗ[ZMod 2] rightConjugate ρ I t :=
  ((ρ t⁻¹).comp I.subtype).codRestrict _ (fun i => ⟨i, i.property, rfl⟩)

omit p hcross in
private theorem conjugateVector_surjective :
    Function.Surjective (conjugateVector ρ (I := I) (t := t)) := by
  rintro ⟨_, i, hi, rfl⟩
  exact ⟨⟨i, hi⟩, rfl⟩

omit p hcross in
/-- The original invariant space transports to the literal conjugate actor. -/
theorem conjugate_invariant (hI : K ≤ subspaceStabilizer ρ I) :
    K.conjBy t⁻¹ ≤ subspaceStabilizer ρ (rightConjugate ρ I t) := by
  apply le_subspaceStabilizer
  rintro _ ⟨k, hk, rfl⟩ _ ⟨i, hi, rfl⟩
  change ρ (t⁻¹ * k * (t⁻¹)⁻¹) (ρ t⁻¹ i) ∈ rightConjugate ρ I t
  rw [inv_inv, conjugate_action]
  exact ⟨ρ k i, (hI hk i).2 hi, rfl⟩

omit p hcross in
/-- Conjugation carries C_I(K) exactly onto C_{Iᵗ}(Kᵗ). -/
theorem conjugate_fixed_iff (i : I) :
    ρ t⁻¹ i ∈ fixedSpace ρ (K.conjBy t⁻¹) ↔ (i : V) ∈ fixedSpace ρ K := by
  constructor
  · intro hi k
    have he := hi (conjugateActor (t := t) k)
    change ρ ((conjugateActor k : K.conjBy t⁻¹) : D) (ρ t⁻¹ i) = ρ t⁻¹ i at he
    rw [conjugateActor_coe, conjugate_action] at he
    have hi : Function.Injective (ρ t⁻¹) := by
      apply Function.LeftInverse.injective (g := ρ t)
      intro v
      simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]
    exact hi he
  · intro hi k
    obtain ⟨k, rfl⟩ := (conjugateActor (K := K) (t := t)).surjective k
    change ρ ((conjugateActor k : K.conjBy t⁻¹) : D) (ρ t⁻¹ i) = ρ t⁻¹ i
    rw [conjugateActor_coe, conjugate_action]
    exact congrArg (ρ t⁻¹) (hi k)

omit p hcross in
private def conjugateQuotientMap : I →ₗ[ZMod 2]
    centralQuotient ρ (K.conjBy t⁻¹) (rightConjugate ρ I t) :=
  ((fixedSpace ρ (K.conjBy t⁻¹)).comap (rightConjugate ρ I t).subtype).mkQ.comp
    (conjugateVector ρ)

omit p hcross in
private theorem conjugateQuotientMap_surjective :
    Function.Surjective (conjugateQuotientMap (K := K) ρ (I := I) (t := t)) :=
  (Submodule.mkQ_surjective _).comp (conjugateVector_surjective ρ)

omit p hcross in
private theorem conjugate_common_kernel :
    (conjugateQuotientMap (K := K) (t := t) ρ (I := I)).ker = (constituentMap ρ d).ker := by
  ext i
  change Submodule.Quotient.mk (conjugateVector ρ i) =
    (0 : centralQuotient ρ (K.conjBy t⁻¹) _) ↔ constituentMap ρ d i = 0
  rw [Submodule.Quotient.mk_eq_zero, constituentMap_eq_zero]
  exact conjugate_fixed_iff ρ i

omit p hcross in
/-- The conjugate constituent quotient is identified using the same lift
coordinates as the original d, with no new choice of model marking. -/
def conjugateEquiv : centralQuotient ρ (K.conjBy t⁻¹) (rightConjugate ρ I t) ≃ₗ[ZMod 2] X :=
  commonKernelEquiv (conjugateQuotientMap ρ) (constituentMap ρ d)
    (conjugateQuotientMap_surjective ρ) (constituentMap_surjective ρ d)
    (conjugate_common_kernel ρ d)

omit p hcross in
@[simp] theorem conjugateEquiv_lift (i : I) :
    conjugateEquiv (t := t) ρ d (Submodule.Quotient.mk (conjugateVector ρ i)) =
      constituentMap ρ d i := commonKernelEquiv_apply _ _ _ _ _ i

omit p hcross in
/-- Full conjugate identification, retaining the literal conjugation map
of actors and the original model representation. -/
@[expose] def conjugateIdentification : CentralQuotientIdentification ρ (K.conjBy t⁻¹)
    (rightConjugate ρ I t) (conjugate_invariant ρ hI) σ where
  groupEquiv := (conjugateActor (K := K) (t := t)).symm.trans d.groupEquiv
  linearEquiv := conjugateEquiv ρ d
  equivariant := by
    intro g v
    obtain ⟨k, rfl⟩ := (conjugateActor (K := K) (t := t)).surjective g
    obtain ⟨i, rfl⟩ := conjugateQuotientMap_surjective ρ v
    let i' : I := ⟨ρ k i, (hI k.property i).2 i.property⟩
    have he : centralQuotientRepresentation ρ (K.conjBy t⁻¹) _ (conjugate_invariant ρ hI)
        (conjugateActor k) (conjugateQuotientMap ρ i) =
          Submodule.Quotient.mk (conjugateVector ρ i') := by
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      change ρ ((conjugateActor k : K.conjBy t⁻¹) : D) (ρ t⁻¹ i) = ρ t⁻¹ (ρ k i)
      rw [conjugateActor_coe, conjugate_action]
    rw [he]
    change conjugateEquiv ρ d (Submodule.Quotient.mk (conjugateVector ρ i')) =
      σ (d.groupEquiv ((conjugateActor (t := t)).symm (conjugateActor k)))
        (conjugateEquiv ρ d (Submodule.Quotient.mk (conjugateVector ρ i)))
    rw [MulEquiv.symm_apply_apply, conjugateEquiv_lift, conjugateEquiv_lift]
    exact constituentMap_action ρ d k i


/-- Compatibility with both literal constituent identifications: d is
retained on I, and its constructed conjugate is used on Iᵗ. -/
theorem pairEquiv_constituents (i j : I) :
    p.pairEquiv ρ hcross d (Submodule.Quotient.mk (pairLift ρ i j)) =
      (d.linearEquiv (Submodule.Quotient.mk i),
        (conjugateIdentification (t := t) ρ d).linearEquiv
          (Submodule.Quotient.mk (conjugateVector ρ j))) := by
  rw [p.pairEquiv_lift]
  change (constituentMap ρ d i, constituentMap ρ d j) =
    (constituentMap ρ d i, conjugateEquiv ρ d (Submodule.Quotient.mk (conjugateVector ρ j)))
  rw [conjugateEquiv_lift]

omit hcross in
/-- The second action's map, restricted to Kᵗ, is exactly the group map
of the constructed conjugate constituent identification. -/
theorem modelMap_conjugate (g : K.conjBy t⁻¹) :
    p.modelMap ρ d (p.pullback ⟨g, p.conjugate_le g.property⟩) =
      (conjugateIdentification (t := t) ρ d).groupEquiv g := by
  obtain ⟨k, rfl⟩ := (conjugateActor (K := K) (t := t)).surjective g
  have he : p.pullback ⟨conjugateActor k, p.conjugate_le (conjugateActor k).property⟩ =
      (⟨k, p.le k.property⟩ : K₀) := by
    apply Subtype.ext
    rw [p.pullback_coe, conjugateActor_coe]
    simp [mul_assoc]
  rw [he, p.modelMap_first]
  change d.groupEquiv k = d.groupEquiv ((conjugateActor (t := t)).symm (conjugateActor k))
  rw [MulEquiv.symm_apply_apply]

omit ρ hcross in
private theorem map_normalizer_subgroupOf (n : normalizer (K₀ : Set D)) :
    (K.subgroupOf K₀).map (K₀.normalizerMonoidHom n).toMonoidHom =
      (K.conjBy n).subgroupOf K₀ := by
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    change ((K₀.normalizerMonoidHom n k : K₀) : D) ∈ K.conjBy n
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, he⟩
    refine ⟨⟨k, p.le hk⟩, hk, ?_⟩
    apply Subtype.ext
    exact he

omit ρ hcross in
/-- The return equality in precisely the form consumed by the exchanged
model's cross-centralization theorem. -/
theorem model_return :
    (K.subgroupOf K₀).map (K₀.normalizerMonoidHom p.exchanger).symm.toMonoidHom =
      (K.subgroupOf K₀).map (K₀.normalizerMonoidHom p.exchanger).toMonoidHom := by
  have he : (K₀.normalizerMonoidHom p.exchanger).symm =
      K₀.normalizerMonoidHom p.exchanger⁻¹ := by
    rw [map_inv]
    rfl
  rw [he, p.map_normalizer_subgroupOf, p.map_normalizer_subgroupOf]
  change (K.conjBy (t⁻¹)⁻¹).subgroupOf K₀ = (K.conjBy t⁻¹).subgroupOf K₀
  rw [inv_inv, p.return_eq]

omit hcross in
/-- Literal cross-centralization supplies exactly the model kernel clause;
in fact the marked direct product proves equality with this kernel. -/
theorem model_cross_kernel :
    (K.subgroupOf K₀).map (K₀.normalizerMonoidHom p.exchanger).toMonoidHom =
      (p.modelMap ρ d).ker := by
  rw [p.map_normalizer_subgroupOf, p.modelMap_ker]
  rfl

/-- Cross-centralization on both coordinate axes of the constructed
literal central quotient. -/
theorem pair_cross (hI₀ : K₀ ≤ subspaceStabilizer ρ I) :
    (∀ (g : K.subgroupOf K₀) (x : X),
      centralQuotientRepresentation ρ K₀ _ (p.pair_invariant ρ hcross hI₀) g.val
        ((p.pairEquiv ρ hcross d).symm (0, x)) = (p.pairEquiv ρ hcross d).symm (0, x)) ∧
    (∀ (g : (K.subgroupOf K₀).map (K₀.normalizerMonoidHom p.exchanger).toMonoidHom) (x : X),
      centralQuotientRepresentation ρ K₀ _ (p.pair_invariant ρ hcross hI₀) g.val
        ((p.pairEquiv ρ hcross d).symm (x, 0)) = (p.pairEquiv ρ hcross d).symm (x, 0)) :=
  RemainingModels.exchanged_centralQuotient_cross σ ρ K₀ _ (p.pair_invariant ρ hcross hI₀)
    p.exchanger (p.modelMap ρ d) (p.pairEquiv ρ hcross d)
    (p.pairEquiv_equivariant ρ hcross d hI₀) _ p.model_return
    (p.model_cross_kernel ρ d).le

omit ρ hcross in
/-- A subgroup normalized by the source element is preserved by the
pullback automorphism on K₀. -/
theorem borel_pullback (B : Subgroup D) (htB : t ∈ normalizer (B : Set D)) :
    (B.subgroupOf K₀).map p.pullback.toMonoidHom = B.subgroupOf K₀ := by
  ext g
  constructor
  · rintro ⟨b, hb, rfl⟩
    change (p.pullback b : D) ∈ B
    rw [p.pullback_coe]
    exact (mem_normalizer_iff.mp htB b).mp hb
  · intro hg
    refine ⟨p.pullback.symm g, ?_, p.pullback.apply_symm_apply g⟩
    have he := p.pullback_coe (p.pullback.symm g)
    rw [p.pullback.apply_symm_apply] at he
    change (p.pullback.symm g : D) ∈ B
    apply (mem_normalizer_iff.mp htB _).mpr
    rw [← he]
    exact hg

omit hcross in
/-- A single specified Borel image suffices when the actual exchanger
normalizes B. The second image uses exactly the map in the pair action. -/
theorem second_borel_image (B : Subgroup D) (htB : t ∈ normalizer (B : Set D))
    (B' : Subgroup E) (hB : (B.subgroupOf K₀).map (p.modelMap ρ d) = B') :
    (B.subgroupOf K₀).map ((p.modelMap ρ d).comp
      (K₀.normalizerMonoidHom p.exchanger).symm.toMonoidHom) = B' := by
  rw [← Subgroup.map_map]
  change ((B.subgroupOf K₀).map p.pullback.toMonoidHom).map (p.modelMap ρ d) = B'
  rw [p.borel_pullback B htB, hB]

end ProductMarking

/-- Source-family specialization: the normalizer premise comes from
Irr⁺(K₀,V,T), with no assertion that T normalizes the individual K.
The construction works in particular for finite faithful binary representations. -/
@[expose] def markingOfIrrPlusWith (ρ : Representation (ZMod 2) D V)
    {K K₀ T : Subgroup D} {I : Submodule (ZMod 2) V} {t : D}
    (hK : K ≤ K₀) (hI : IsIrrPlusWith ρ K₀ T I) (ht : t ∈ T)
    (κ : K × K ≃* K₀)
    (hfirst : ∀ k : K, (κ (k, 1) : D) = k)
    (hsecond : ∀ k : K, (κ (1, k) : D) = t⁻¹ * k * t)
    (hreturn : K.conjBy t = K.conjBy t⁻¹) : ProductMarking K K₀ t :=
  ⟨hK, hI.normalizes ht, κ, hfirst, hsecond, hreturn⟩

/-- The source-family specialization constructs both quotient identifications
and the equivariant pair coordinates, preserving the initial model marking.
Finiteness and faithfulness impose no further linear-algebra obligation. -/
theorem coordinates_of_isIrrPlusWith (ρ : Representation (ZMod 2) D V)
    {K K₀ T : Subgroup D} {I : Submodule (ZMod 2) V} {t : D}
    (hK : K ≤ K₀) (hI : IsIrrPlusWith ρ K₀ T I) (ht : t ∈ T)
    (κ : K × K ≃* K₀)
    (hfirst : ∀ k : K, (κ (k, 1) : D) = k)
    (hsecond : ∀ k : K, (κ (1, k) : D) = t⁻¹ * k * t)
    (hreturn : K.conjBy t = K.conjBy t⁻¹)
    (hcross : subspaceCommutator ρ I (K.conjBy t⁻¹) = ⊥)
    (σ : Representation (ZMod 2) E X)
    (d : CentralQuotientIdentification ρ K I (hK.trans hI.invariant) σ) :
    let p := markingOfIrrPlusWith ρ hK hI ht κ hfirst hsecond hreturn
    ∃ e : centralQuotient ρ K₀ (I ⊔ rightConjugate ρ I t) ≃ₗ[ZMod 2] X × X,
      (∀ g v, e (centralQuotientRepresentation ρ K₀ _
        (p.pair_invariant ρ hcross hI.invariant) g v) =
        RemainingModels.exchangedAction σ K₀ p.exchanger (p.modelMap ρ d) g (e v)) ∧
      (∀ i j : I, e (Submodule.Quotient.mk (ProductMarking.pairLift ρ i j)) =
        (ProductMarking.constituentMap ρ d i, ProductMarking.constituentMap ρ d j)) ∧
      Nonempty (CentralQuotientIdentification ρ (K.conjBy t⁻¹)
        (rightConjugate ρ I t) (ProductMarking.conjugate_invariant ρ (hK.trans hI.invariant)) σ) := by
  dsimp only
  let p := markingOfIrrPlusWith ρ hK hI ht κ hfirst hsecond hreturn
  exact ⟨p.pairEquiv ρ hcross d, p.pairEquiv_equivariant ρ hcross d hI.invariant,
    p.pairEquiv_lift ρ hcross d, ⟨ProductMarking.conjugateIdentification ρ d⟩⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.PairCoordinates
