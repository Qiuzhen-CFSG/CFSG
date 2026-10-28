module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicWeights
public import Theory.AlgebraicGroup.Tori.Basic

/-!
# Named highest vectors for the exceptional basic F4 weights

The four pairs in `Fin 2 × Fin 2` specify exactly the source basic weights:
the long-simple coefficients vanish and the two short-simple coefficients
are zero or one. This extension exposes individual highest-vector witnesses
without changing `IsExceptionalBasic`.

Distinct pairs are distinguished by their actual simple-coroot eigenvalues.
Consequently every nonzero pair gives a nontrivial action. For the zero pair,
we also supply the elementary last step of the triviality argument: a nonzero
vector fixed by all root groups in an irreducible factor forces the action to
be trivial. Fixation by the negative root groups is a separate obligation.

Source: GLS3, Definition 2.8.1(b) and Chapter 1, Section 1.14.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

namespace ReeF4.BinaryDegree.ExceptionalTensor

universe u

variable {F : Type u} [Field F] [IsAlgClosed F]

/-- A specified vector realizing one of the four exceptional basic weights,
with the positive-coroot convention of `BasicWeights`. -/
@[expose] def AlgebraicFactor.IsBasicHighestWeightVector (B : AlgebraicFactor F)
    (weight : Fin 2 × Fin 2) (v : B.Space) : Prop :=
  v ≠ 0 ∧
    (∀ r : F4Chevalley.Root, typeF4RootPairing_base.IsPos r → ∀ t : F,
      (B.action.action (algebraicRootElement r t) : Module.End F B.Space) v = v) ∧
    (∀ (i : Fin 4) (t : Fˣ),
      (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
        Module.End F B.Space) v = ((t : F) ^ basicCoefficient weight i) • v)

/-- The basic highest weight is the specified pair. This includes the
nonzero highest vector and all its root and coroot equations. -/
@[expose] def AlgebraicFactor.HasBasicHighestWeight (B : AlgebraicFactor F)
    (weight : Fin 2 × Fin 2) : Prop :=
  ∃ v, B.IsBasicHighestWeightVector weight v

theorem AlgebraicFactor.isExceptionalBasic_iff (B : AlgebraicFactor F) :
    B.IsExceptionalBasic ↔ ∃ weight, B.HasBasicHighestWeight weight := Iff.rfl

theorem AlgebraicFactor.HasBasicHighestWeight.isExceptionalBasic
    {B : AlgebraicFactor F} {weight : Fin 2 × Fin 2}
    (h : B.HasBasicHighestWeight weight) : B.IsExceptionalBasic :=
  ⟨weight, h⟩

theorem basicCoefficient_injective : Function.Injective basicCoefficient := by
  intro a b h
  apply Prod.ext
  · apply Fin.ext
    simpa [basicCoefficient] using congrFun h 2
  · apply Fin.ext
    simpa [basicCoefficient] using congrFun h 3

/-- The same nonzero vector cannot have two different basic coroot weights.
No uniqueness theorem for irreducible highest weights is used here. -/
theorem AlgebraicFactor.IsBasicHighestWeightVector.weight_eq
    {B : AlgebraicFactor F} {a b : Fin 2 × Fin 2} {v : B.Space}
    (ha : B.IsBasicHighestWeightVector a v)
    (hb : B.IsBasicHighestWeightVector b v) : a = b := by
  apply basicCoefficient_injective
  funext i
  by_contra hi
  have hdiff : (basicCoefficient a i : ℤ) - basicCoefficient b i ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hi)
  obtain ⟨t, ht⟩ := exists_unit_zpow_ne_one (k := F) hdiff
  have he : (t : F) ^ basicCoefficient a i = (t : F) ^ basicCoefficient b i :=
    smul_left_injective F ha.1 ((ha.2.2 i t).symm.trans (hb.2.2 i t))
  apply ht
  rw [zpow_sub, mul_inv_eq_one]
  apply Units.ext
  simpa using he

/-- A nonzero basic coefficient forces a nonidentity coroot action. -/
theorem AlgebraicFactor.HasBasicHighestWeight.isNontrivial
    {B : AlgebraicFactor F} {weight : Fin 2 × Fin 2}
    (h : B.HasBasicHighestWeight weight) (hw : weight ≠ (0, 0)) :
    B.IsNontrivial := by
  by_contra htriv
  have haction : ∀ g, B.action.action g = 1 := by
    simpa [AlgebraicFactor.IsNontrivial] using htriv
  obtain ⟨v, hv⟩ := h
  have hz : B.IsBasicHighestWeightVector (0, 0) v := by
    refine ⟨hv.1, hv.2.1, ?_⟩
    intro i t
    rw [haction]
    simp [basicCoefficient]
  exact hw (hv.weight_eq hz)

/-- The actual root elements generate the closed F4 carrier as an abstract
group; the carrier was defined by this generated subgroup. -/
theorem algebraicRootElements_generate :
    Subgroup.closure (Set.range fun p : F4Chevalley.Root × F =>
      algebraicRootElement p.1 p.2) =
      (⊤ : Subgroup (Variety.Point (F4Chevalley.Carrier (k := F)))) := by
  let C := F4Chevalley.ambientClosedCarrier (k := F)
  apply Subgroup.map_injective C.inclusion_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map]
  have hroots :
      C.inclusion.onPoints '' (Set.range fun p : F4Chevalley.Root × F =>
        algebraicRootElement p.1 p.2) =
      ⋃ r : F4Chevalley.Root,
        (F4Chevalley.ambientRootSubgroup (k := F) r :
          Set (Variety.Point (F4Chevalley.Ambient F))) := by
    ext x
    constructor
    · rintro ⟨_, ⟨⟨r, t⟩, rfl⟩, rfl⟩
      refine Set.mem_iUnion.mpr ⟨r, ?_⟩
      exact ⟨kPlusPoint t, (F4Chevalley.rootMorphism_inclusion_apply r _).symm⟩
    · intro hx
      obtain ⟨r, y, rfl⟩ := Set.mem_iUnion.mp hx
      let t : F := (additiveGroupPointEquiv F y).toAdd
      have hy : kPlusPoint t = y := by
        apply (additiveGroupPointEquiv F).injective
        rfl
      refine ⟨algebraicRootElement r t, ⟨(r, t), rfl⟩, ?_⟩
      change C.inclusion.onPoints ((F4Chevalley.rootMorphism r).onPoints _) = _
      rw [F4Chevalley.rootMorphism_inclusion_apply, hy]
  rw [hroots]
  change F4Chevalley.ambientCarrierSubgroup = C.inclusion.onPoints.range
  apply SetLike.coe_injective
  exact C.range_inclusion.symm

/-- Root-group fixation propagates to the whole carrier. -/
theorem AlgebraicFactor.fixed_of_root_fixed (B : AlgebraicFactor F) (v : B.Space)
    (hv : ∀ r : F4Chevalley.Root, ∀ t : F,
      (B.action.action (algebraicRootElement r t) : Module.End F B.Space) v = v)
    (g : Variety.Point (F4Chevalley.Carrier (k := F))) :
    (B.action.action g : Module.End F B.Space) v = v := by
  have hg : g ∈ Subgroup.closure (Set.range fun p : F4Chevalley.Root × F =>
      algebraicRootElement p.1 p.2) := by
    rw [algebraicRootElements_generate]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨r, t⟩, rfl⟩ := hx
    exact hv r t
  | one => simp
  | mul x y hx hy hfixx hfixy =>
    simpa [map_mul, hfixy] using hfixx
  | inv x hx hfix =>
    have he := congrArg
      (fun w => (B.action.action x⁻¹ : Module.End F B.Space) w) hfix
    simpa [← Module.End.mul_apply, ← Units.val_mul, ← map_mul] using he.symm

/-- An irreducible factor with a nonzero vector fixed by all root groups has
trivial action. This is the terminal step, not the zero-highest-weight theorem. -/
theorem AlgebraicFactor.not_isNontrivial_of_root_fixed (B : AlgebraicFactor F)
    (v : B.Space) (hv : v ≠ 0)
    (hroot : ∀ r : F4Chevalley.Root, ∀ t : F,
      (B.action.action (algebraicRootElement r t) : Module.End F B.Space) v = v) :
    ¬ B.IsNontrivial := by
  have hfix := B.fixed_of_root_fixed v hroot
  have hspan : IsInvariantSubmodule B.action (Submodule.span F {v}) := by
    intro g w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul, hfix]
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton v))
  have htop : Submodule.span F {v} = ⊤ := by
    rcases B.irreducible.2 _ hspan with hbot | htop
    · have hm : v ∈ Submodule.span F {v} := Submodule.subset_span (Set.mem_singleton v)
      rw [hbot] at hm
      exact (hv (by simpa using hm)).elim
    · exact htop
  rintro ⟨g, hg⟩
  apply hg
  apply Units.ext
  ext w
  have hw : w ∈ Submodule.span F {v} := by rw [htop]; exact Submodule.mem_top
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  simp [map_smul, hfix]

end ReeF4.BinaryDegree.ExceptionalTensor
