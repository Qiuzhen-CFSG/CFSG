module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.PairedSection
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.CommonCenterRank

/-!
# Common-center transvections on the marked fixed spaces

The first space is the literal fixed space of τ. Commutation with τ preserves
it; commutation with the marked conjugator identifies its core action with
that on the second space. Their direct sum makes restriction faithful.
Trivial action modulo E then places every first-space displacement in
C_E(τ), the marked line. Every nonidentity actor is a transvection.

The actual sum isomorphism identifies the full action with two copies of the
restricted action. Common-center displacement duality therefore proves the
fixed-codimension doubling identity for every subgroup, including the trivial
one. The geometry inputs are direct-sum, conjugacy and center-line witnesses;
no transvection rank or numerical doubling is an input.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed pp.1153–1154, PDF pp.1170–1171.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement.Transvections
variable {K X : Type*} [Group K] [AddCommGroup X] [Module (ZMod 2) X]

/-- The first marked fixed space is the literal kernel of τ - 1. -/
noncomputable def firstSpace (ρ : Representation (ZMod 2) K X) (t : K) :
    Submodule (ZMod 2) X := (ρ t - LinearMap.id).ker

theorem mem_firstSpace (ρ : Representation (ZMod 2) K X) (t : K) (x : X) :
    x ∈ firstSpace ρ t ↔ ρ t x = x := sub_eq_zero

theorem firstSpace_eq_fixedSpace (ρ : Representation (ZMod 2) K X) (t : K) :
    firstSpace ρ t = fixedSpace ρ (zpowers t) := by
  ext x
  exact (mem_firstSpace ρ t x).trans (mem_fixedSpace_zpowers_iff ρ t x).symm

/-- Left conjugation sends C_X(t) to C_X(y t y⁻¹). For the book's right
conjugation notation, use the inverse of its marked conjugator. -/
theorem firstSpace_map (ρ : Representation (ZMod 2) K X) (t y : K) :
    (firstSpace ρ t).map (ρ y) = firstSpace ρ (y * t * y⁻¹) := by
  have hinv (x : X) : ρ y⁻¹ (ρ y x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hginv (x : X) : ρ y (ρ y⁻¹ x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' := (mem_firstSpace ρ t v).mp hv
    apply (mem_firstSpace ρ (y * t * y⁻¹) _).mpr
    rw [map_mul, map_mul]
    simp only [Module.End.mul_apply, hinv, hv']
  · intro hx
    refine ⟨ρ y⁻¹ x, ?_, hginv x⟩
    apply (mem_firstSpace ρ t _).mpr
    have h := congrArg (ρ y⁻¹) ((mem_firstSpace ρ (y * t * y⁻¹) x).mp hx)
    rw [map_mul, map_mul] at h
    simpa only [Module.End.mul_apply, hinv] using h

private theorem commute_apply (ρ : Representation (ZMod 2) K X) {a b : K}
    (h : Commute a b) (x : X) : ρ a (ρ b x) = ρ b (ρ a x) := by
  change (ρ a * ρ b) x = (ρ b * ρ a) x
  rw [← map_mul, ← map_mul, h.eq]

/-- Commutation with τ preserves its fixed space. -/
theorem preserves_firstSpace (ρ : Representation (ZMod 2) K X) (Q : Subgroup K) (t : K)
    (ht : ∀ q ∈ Q, Commute t q) (q : Q) {x : X} (hx : x ∈ firstSpace ρ t) :
    ρ q x ∈ firstSpace ρ t := by
  rw [mem_firstSpace] at hx ⊢
  rw [commute_apply ρ (ht q q.property), hx]

/-- The actual restricted action on C_X(τ). -/
noncomputable def firstRepresentation (ρ : Representation (ZMod 2) K X)
    (Q : Subgroup K) (t : K) (ht : ∀ q ∈ Q, Commute t q) :
    Representation (ZMod 2) Q (firstSpace ρ t) where
  toFun q := (ρ q).restrict (fun _ hx => preserves_firstSpace ρ Q t ht q hx)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

/-- Direct sum and conjugacy witnesses for the two actual fixed spaces. -/
structure FixedGeometry (ρ : Representation (ZMod 2) K X) (t y : K)
    (E : Submodule (ZMod 2) X) where
  spans : firstSpace ρ t ⊔ (firstSpace ρ t).map (ρ y) = ⊤
  disjoint : Disjoint (firstSpace ρ t) ((firstSpace ρ t).map (ρ y))
  center : X
  center_ne : center ≠ 0
  center_eq : E ⊓ firstSpace ρ t = Submodule.span (ZMod 2) {center}

variable (ρ : Representation (ZMod 2) K X) (Q : Subgroup K) (t y : K)
    (E : Submodule (ZMod 2) X)

/-- The second fixed space detects the same core action as the first. -/
theorem firstRepresentation_injective (ht : ∀ q ∈ Q, Commute t q)
    (hy : ∀ q ∈ Q, Commute y q) (hf : Function.Injective ρ)
    (d : FixedGeometry ρ t y E) :
    Function.Injective (firstRepresentation ρ Q t ht) := by
  apply (firstRepresentation ρ Q t ht).ker_eq_bot_iff.mp
  apply le_bot_iff.mp
  intro q hq
  apply Subtype.ext
  apply hf
  apply LinearMap.ext
  intro x
  have hx : x ∈ firstSpace ρ t ⊔ (firstSpace ρ t).map (ρ y) := by rw [d.spans]; trivial
  obtain ⟨v, hv, _, ⟨w, hw, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hx
  have hfix (u : X) (hu : u ∈ firstSpace ρ t) : ρ q u = u :=
    congrArg (fun a : Module.End (ZMod 2) (firstSpace ρ t) => (a ⟨u, hu⟩ : X)) hq
  change ρ q (v + ρ y w) = ρ 1 (v + ρ y w)
  rw [map_add, commute_apply ρ (hy q q.property).symm, hfix v hv, hfix w hw]
  simp

/-- Every displacement on the first fixed space lies in the marked center. -/
theorem first_displacement_range_le (ht : ∀ q ∈ Q, Commute t q)
    (hsection : ∀ q ∈ Q, ∀ x, ρ q x - x ∈ E) (q : Q) :
    LinearMap.range (firstRepresentation ρ Q t ht q - LinearMap.id) ≤
      E.comap (firstSpace ρ t).subtype := by
  rintro _ ⟨x, rfl⟩
  exact hsection q q.property x

/-- The marked center is fixed pointwise by the core, before any rank calculation. -/
theorem first_center_fixed (ht : ∀ q ∈ Q, Commute t q)
    (hE : ∀ q ∈ Q, ∀ x ∈ E, ρ q x = x) (q : Q)
    (x : firstSpace ρ t) (hx : x ∈ E.comap (firstSpace ρ t).subtype) :
    firstRepresentation ρ Q t ht q x = x := by
  apply Subtype.ext
  exact hE q q.property x hx

/-- The restricted common center is one-dimensional because it is the marked line. -/
theorem first_center_finrank [FiniteDimensional (ZMod 2) X]
    (d : FixedGeometry ρ t y E) :
    Module.finrank (ZMod 2) (E.comap (firstSpace ρ t).subtype) = 1 := by
  have hmap : (E.comap (firstSpace ρ t).subtype).map (firstSpace ρ t).subtype =
      E ⊓ firstSpace ρ t := by
    rw [Submodule.map_comap_eq, Submodule.range_subtype, inf_comm]
  rw [← Submodule.finrank_map_subtype_eq (firstSpace ρ t) (E.comap (firstSpace ρ t).subtype), hmap,
    d.center_eq, finrank_span_singleton d.center_ne]

/-- Nonidentity core elements are genuine transvections on the first fixed space. -/
theorem first_displacement_finrank [FiniteDimensional (ZMod 2) X]
    (ht : ∀ q ∈ Q, Commute t q) (hy : ∀ q ∈ Q, Commute y q)
    (hf : Function.Injective ρ) (d : FixedGeometry ρ t y E)
    (hsection : ∀ q ∈ Q, ∀ x, ρ q x - x ∈ E) (q : Q) (hq : q ≠ 1) :
    Module.finrank (ZMod 2) (LinearMap.range
      (firstRepresentation ρ Q t ht q - LinearMap.id)) = 1 := by
  have hle := (Submodule.finrank_mono
    (first_displacement_range_le ρ Q t E ht hsection q)).trans_eq
      (first_center_finrank ρ t y E d)
  have hne : Module.finrank (ZMod 2) (LinearMap.range
      (firstRepresentation ρ Q t ht q - LinearMap.id)) ≠ 0 := by
    intro hzero
    have hbot := Submodule.finrank_eq_zero.mp hzero
    have he := sub_eq_zero.mp (LinearMap.range_eq_bot.mp hbot)
    apply hq
    apply firstRepresentation_injective ρ Q t y E ht hy hf d
    exact he.trans (map_one (firstRepresentation ρ Q t ht)).symm
  omega

/-- Sum of a vector in the first fixed space and its marked conjugate. -/
noncomputable def pairMap : (firstSpace ρ t × firstSpace ρ t) →ₗ[ZMod 2] X :=
  (firstSpace ρ t).subtype.coprod ((ρ y).comp (firstSpace ρ t).subtype)

private theorem action_injective (a : K) : Function.Injective (ρ a) := by
  intro v w h
  have he := congrArg (ρ a⁻¹) h
  simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply] using he

/-- Complementarity makes the marked sum map an actual isomorphism. -/
theorem pairMap_bijective (d : FixedGeometry ρ t y E) :
    Function.Bijective (pairMap ρ t y) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply le_bot_iff.mp
    rintro ⟨v,w⟩ h
    have hvw : (v : X) + ρ y w = 0 := h
    have hv : (v : X) = 0 := by
      apply (Submodule.disjoint_def.mp d.disjoint) v v.property
      rw [eq_neg_of_add_eq_zero_left hvw]
      exact ((firstSpace ρ t).map (ρ y)).neg_mem ⟨w, w.property, rfl⟩
    have hw : (w : X) = 0 := by
      apply action_injective ρ y
      simpa only [hv, zero_add, map_zero] using hvw
    exact Prod.ext (Subtype.ext hv) (Subtype.ext hw)
  · intro x
    have hx : x ∈ firstSpace ρ t ⊔ (firstSpace ρ t).map (ρ y) := by rw [d.spans]; trivial
    obtain ⟨v, hv, _, ⟨w, hw, rfl⟩, he⟩ := Submodule.mem_sup.mp hx
    exact ⟨(⟨v,hv⟩, ⟨w,hw⟩), he⟩

/-- The actual marked decomposition X ≃ F ⊕ F. -/
noncomputable def pairEquiv (d : FixedGeometry ρ t y E) :
    (firstSpace ρ t × firstSpace ρ t) ≃ₗ[ZMod 2] X :=
  LinearEquiv.ofBijective (pairMap ρ t y) (pairMap_bijective ρ t y E d)

/-- Commutation of the core with the conjugator gives the diagonal action in this decomposition. -/
theorem pairEquiv_equivariant (ht : ∀ q ∈ Q, Commute t q)
    (hy : ∀ q ∈ Q, Commute y q) (d : FixedGeometry ρ t y E)
    (q : Q) (x : firstSpace ρ t × firstSpace ρ t) :
    pairEquiv ρ t y E d ((firstRepresentation ρ Q t ht).prod
      (firstRepresentation ρ Q t ht) q x) = ρ q (pairEquiv ρ t y E d x) := by
  change ρ q x.1 + ρ y (ρ q x.2) = ρ q ((x.1 : X) + ρ y x.2)
  rw [map_add, commute_apply ρ (hy q q.property)]

private noncomputable def prodFixedEquiv {A F : Type*} [Group A]
    [AddCommGroup F] [Module (ZMod 2) F] (σ : Representation (ZMod 2) A F)
    (W : Subgroup A) : fixedSpace (σ.prod σ) W ≃ₗ[ZMod 2]
      (fixedSpace σ W × fixedSpace σ W) where
  toFun v := (⟨v.val.1, fun q => congrArg Prod.fst (v.property q)⟩,
    ⟨v.val.2, fun q => congrArg Prod.snd (v.property q)⟩)
  invFun v := ⟨(v.1.val, v.2.val), fun q => Prod.ext (v.1.property q) (v.2.property q)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Fixed codimension on the two identical summands is additive, also for the trivial subgroup. -/
theorem fixedCodim_prod {A F : Type*} [Group A]
    [AddCommGroup F] [Module (ZMod 2) F] [FiniteDimensional (ZMod 2) F]
    (σ : Representation (ZMod 2) A F) (W : Subgroup A) :
    fixedCodim (σ.prod σ) W = 2 * fixedCodim σ W := by
  have he := (prodFixedEquiv σ W).finrank_eq
  rw [Module.finrank_prod] at he
  have h := fixedCodim_add_finrank (σ.prod σ) W
  rw [Module.finrank_prod, he] at h
  have h' := fixedCodim_add_finrank σ W
  omega

/-- The marked direct sum doubles the first-space codimension, with no rank premise. -/
theorem fixedCodim_eq_twice_first [FiniteDimensional (ZMod 2) X]
    (ht : ∀ q ∈ Q, Commute t q) (hy : ∀ q ∈ Q, Commute y q)
    (d : FixedGeometry ρ t y E) (W : Subgroup K) (hW : W ≤ Q) :
    fixedCodim ρ W = 2 * fixedCodim (firstRepresentation ρ Q t ht) (W.subgroupOf Q) := by
  have he := fixedCodim_map_equivariant
    ((firstRepresentation ρ Q t ht).prod (firstRepresentation ρ Q t ht)) ρ
    Q.subtype (pairEquiv ρ t y E d) (pairEquiv_equivariant ρ Q t y E ht hy d)
    (W.subgroupOf Q)
  rw [map_subgroupOf_eq_of_le hW, fixedCodim_prod] at he
  exact he.symm

/-- Common-center duality and the marked decomposition give the full core doubling identity. -/
theorem core_fixedCodim_eq_twice_rank [Finite K] [FiniteDimensional (ZMod 2) X]
    [IsElementaryAbelian 2 Q]
    (ht : ∀ q ∈ Q, Commute t q) (hy : ∀ q ∈ Q, Commute y q)
    (hf : Function.Injective ρ) (d : FixedGeometry ρ t y E)
    (hsection : ∀ q ∈ Q, ∀ x, ρ q x - x ∈ E)
    (hE : ∀ q ∈ Q, ∀ x ∈ E, ρ q x = x)
    (W : Subgroup K) (hW : W ≤ Q) :
    fixedCodim ρ W = 2 * rank W := by
  rw [fixedCodim_eq_twice_first ρ Q t y E ht hy d W hW]
  have hd (q : Q) (x : firstSpace ρ t) :
      firstRepresentation ρ Q t ht q x - x ∈ E.comap (firstSpace ρ t).subtype :=
    hsection q q.property x
  have hr := CommonCenter.fixedCodim_eq_rank (firstRepresentation ρ Q t ht)
    (E.comap (firstSpace ρ t).subtype) (first_center_finrank ρ t y E d)
    (firstRepresentation_injective ρ Q t y E ht hy hf d) hd
    (fun q x hx => first_center_fixed ρ Q t E ht hE q x hx) (W.subgroupOf Q)
  rw [hr]
  have hc : Nat.card (W.subgroupOf Q) = Nat.card W :=
    Nat.card_congr (subgroupOfEquivOfLe hW).toEquiv
  simp only [rank, hc]

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement.Transvections
