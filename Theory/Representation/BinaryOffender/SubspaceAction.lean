module

public import Theory.Representation.BinaryOffender.Basic
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.GroupTheory.Index

/-!
# Action images on invariant subspaces

The ambient group acting on a subspace is the image of its setwise stabilizer.
We construct its faithful representation, identify fixed vectors and the actual
pointwise kernel, and prove the subgroup correspondence and first isomorphism
with the quotient by that kernel. Kernel normality is relative to the acting
subgroup and requires invariance of the subspace.

These are the action constructions used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, B.7.1, printed pp. 118–119.
-/

@[expose] public section

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (W : Submodule (ZMod 2) V)

/-- Setwise stabilizer of the subspace under the representation. -/
def subspaceStabilizer : Subgroup G where
  carrier := {g | ∀ v, ρ g v ∈ W ↔ v ∈ W}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh v
    simpa only [map_mul, Module.End.mul_apply] using (hg (ρ h v)).trans (hh v)
  inv_mem' := by
    intro g hg v
    have hv := hg (ρ g⁻¹ v)
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
      map_one, Module.End.one_apply] using hv.symm

/-- Invariance under a subgroup places it in the setwise stabilizer. -/
theorem le_subspaceStabilizer {A : Subgroup G}
    (hW : ∀ a ∈ A, ∀ w ∈ W, ρ a w ∈ W) : A ≤ subspaceStabilizer ρ W := by
  intro a ha v
  constructor
  · intro hv
    have := hW a⁻¹ (A.inv_mem ha) (ρ a v) hv
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply] using this
  · exact hW a ha v

/-- The actual restricted linear action of the stabilizer. -/
def stabilizerRepresentation : Representation (ZMod 2) (subspaceStabilizer ρ W) W where
  toFun g := (ρ g).restrict (fun {v} hv => (g.property v).2 hv)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

/-- `Aut_G(W)`: the image of the stabilizer, not the action of all of `G`. -/
def subspaceActionImage : Subgroup (Module.End (ZMod 2) W)ˣ :=
  (stabilizerRepresentation ρ W).asGroupHom.range

/-- The surjective action map from the stabilizer to `Aut_G(W)`. -/
def subspaceActionHom : subspaceStabilizer ρ W →* subspaceActionImage ρ W :=
  (stabilizerRepresentation ρ W).asGroupHom.rangeRestrict

/-- The tautological faithful representation of `Aut_G(W)`. -/
def subspaceImageRepresentation : Representation (ZMod 2) (subspaceActionImage ρ W) W :=
  (Units.coeHom _).comp (subspaceActionImage ρ W).subtype

theorem subspaceImageRepresentation_injective :
    Function.Injective (subspaceImageRepresentation ρ W) := by
  intro x y h
  apply Subtype.ext
  exact Units.ext h

/-- The image of a subgroup on `W`; in applications the subgroup stabilizes `W`. -/
def restrictedSubgroup (A : Subgroup G) : Subgroup (subspaceActionImage ρ W) :=
  (A.subgroupOf (subspaceStabilizer ρ W)).map (subspaceActionHom ρ W)

/-- The pointwise kernel in the original ambient group. -/
def subspaceKernel (A : Subgroup G) : Subgroup G where
  carrier := {a | a ∈ A ∧ ∀ w ∈ W, ρ a w = w}
  one_mem' := by simp
  mul_mem' := by
    rintro a b ⟨ha, hfa⟩ ⟨hb, hfb⟩
    refine ⟨A.mul_mem ha hb, ?_⟩
    intro w hw
    simp only [map_mul, Module.End.mul_apply, hfb w hw, hfa w hw]
  inv_mem' := by
    rintro a ⟨ha, hfa⟩
    refine ⟨A.inv_mem ha, ?_⟩
    intro w hw
    have := congrArg (ρ a⁻¹) (hfa w hw)
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply] using this.symm

@[simp] theorem mem_subspaceKernel {A : Subgroup G} {a : G} :
    a ∈ subspaceKernel ρ W A ↔ a ∈ A ∧ ∀ w ∈ W, ρ a w = w := Iff.rfl

theorem subspaceKernel_le (A : Subgroup G) : subspaceKernel ρ W A ≤ A :=
  fun _ h => h.1

theorem le_fixedSpace_subspaceKernel (A : Subgroup G) :
    W ≤ fixedSpace ρ (subspaceKernel ρ W A) := by
  intro w hw a
  exact a.property.2 w hw

end Representation.BinaryOffender

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (W : Submodule (ZMod 2) V)

@[simp] theorem imageRepresentation_actionHom_apply
    (g : subspaceStabilizer ρ W) (w : W) :
    (subspaceImageRepresentation ρ W (subspaceActionHom ρ W g) w : V) = ρ g w := rfl

/-- Restricting to the action image does not change fixed vectors on `W`. -/
def restrictedFixedSpaceEquiv (B : Subgroup G) (hB : B ≤ subspaceStabilizer ρ W) :
    fixedSpace (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W B) ≃ₗ[ZMod 2]
      (W ⊓ fixedSpace ρ B : Submodule (ZMod 2) V) where
  toFun v := ⟨v.val, v.val.property, by
    intro b
    have hv := v.property
      ⟨subspaceActionHom ρ W ⟨b, hB b.property⟩,
        ⟨⟨b, hB b.property⟩, b.property, rfl⟩⟩
    exact congrArg (fun w : W => (w : V)) hv⟩
  invFun v := ⟨⟨v, v.property.1⟩, by
    rintro ⟨x, ⟨b, hb, hbx⟩⟩
    subst x
    apply Subtype.ext
    exact v.property.2 ⟨b, hb⟩⟩
  left_inv v := rfl
  right_inv v := rfl
  map_add' v w := rfl
  map_smul' c v := rfl

/-- `C_W(Aut_B(W))` is literally the restriction of `C_V(B)` to `W`. -/
theorem fixedSpace_restrictedSubgroup (B : Subgroup G)
    (hB : B ≤ subspaceStabilizer ρ W) :
    fixedSpace (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W B) =
      (fixedSpace ρ B).comap W.subtype := by
  ext w
  constructor
  · intro hw
    exact ((restrictedFixedSpaceEquiv ρ W B hB) ⟨w, hw⟩).property.2
  · intro hw
    exact ((restrictedFixedSpaceEquiv ρ W B hB).symm ⟨w, w.property, hw⟩).property

/-- The action map with domain a subgroup of the stabilizer. -/
def subgroupActionHom (B : Subgroup G) (hB : B ≤ subspaceStabilizer ρ W) :
    B →* subspaceActionImage ρ W :=
  (subspaceActionHom ρ W).comp (Subgroup.inclusion hB)

theorem subgroupActionHom_range (B : Subgroup G) (hB : B ≤ subspaceStabilizer ρ W) :
    (subgroupActionHom ρ W B hB).range = restrictedSubgroup ρ W B := by
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨⟨b, hB b.property⟩, b.property, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hb⟩, rfl⟩

theorem subgroupActionHom_ker (B : Subgroup G) (hB : B ≤ subspaceStabilizer ρ W) :
    (subgroupActionHom ρ W B hB).ker.map B.subtype = subspaceKernel ρ W B := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a.property, ?_⟩
    intro w hw
    have h := congrArg (fun x => subspaceImageRepresentation ρ W x ⟨w, hw⟩) ha
    exact congrArg (fun w : W => (w : V)) h
  · rintro ⟨hb, hfix⟩
    refine ⟨⟨b, hb⟩, ?_, rfl⟩
    apply (subspaceImageRepresentation_injective ρ W)
    ext w
    exact hfix w w.property

instance [Finite G] : Finite (subspaceActionImage ρ W) :=
  Finite.of_surjective (subspaceActionHom ρ W)
    (stabilizerRepresentation ρ W).asGroupHom.rangeRestrict_surjective

/-- Cardinality of a subgroup factors as the actual action kernel times its image. -/
theorem card_subspaceKernel_mul_image (B : Subgroup G)
    (hB : B ≤ subspaceStabilizer ρ W) :
    Nat.card (subspaceKernel ρ W B) * Nat.card (restrictedSubgroup ρ W B) = Nat.card B := by
  rw [← subgroupActionHom_ker ρ W B hB, Subgroup.card_map_of_injective B.subtype_injective,
    ← subgroupActionHom_range ρ W B hB, ← Subgroup.index_ker]
  exact Subgroup.card_mul_index _

variable [Finite G]

/-- Binary rank factors as kernel rank plus image rank. -/
theorem rank_subspaceKernel_add_image (B : Subgroup G)
    (hB : B ≤ subspaceStabilizer ρ W) (hp : IsPGroup 2 B) :
    rank (subspaceKernel ρ W B) + rank (restrictedSubgroup ρ W B) = rank B := by
  have hk : IsPGroup 2 (subspaceKernel ρ W B) :=
    hp.of_injective (Subgroup.inclusion (subspaceKernel_le ρ W B))
      (Subgroup.inclusion_injective _)
  have hi : IsPGroup 2 (restrictedSubgroup ρ W B) := by
    rw [← subgroupActionHom_range ρ W B hB]
    exact hp.of_surjective _ (subgroupActionHom ρ W B hB).rangeRestrict_surjective
  obtain ⟨k, hk⟩ := hk.exists_card_eq
  obtain ⟨i, hi⟩ := hi.exists_card_eq
  have hc := card_subspaceKernel_mul_image ρ W B hB
  rw [hk, hi, ← pow_add] at hc
  simp only [rank, hk, hi, ← hc, Nat.log_pow (by decide : 1 < 2)]

end Representation.BinaryOffender

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (W : Submodule (ZMod 2) V)

theorem restrictedSubgroup_mono {A B : Subgroup G} (hBA : B ≤ A) :
    restrictedSubgroup ρ W B ≤ restrictedSubgroup ρ W A := by
  apply Subgroup.map_mono
  exact fun _ hb => hBA hb

@[simp] theorem restrictedSubgroup_bot : restrictedSubgroup ρ W ⊥ = ⊥ := by
  simp [restrictedSubgroup, Subgroup.subgroupOf]

theorem subspaceKernel_eq_of_le {A B : Subgroup G}
    (hBA : B ≤ A) (hKB : subspaceKernel ρ W A ≤ B) :
    subspaceKernel ρ W B = subspaceKernel ρ W A := by
  ext a
  exact ⟨fun h => ⟨hBA h.1, h.2⟩, fun h => ⟨hKB h, h.2⟩⟩

theorem restrictedSubgroup_ne_bot {A : Subgroup G}
    (hA : A ≤ subspaceStabilizer ρ W) (hn : ¬ W ≤ fixedSpace ρ A) :
    restrictedSubgroup ρ W A ≠ ⊥ := by
  intro heq
  apply hn
  intro w hw a
  have hm : subspaceActionHom ρ W ⟨a, hA a.property⟩ ∈ restrictedSubgroup ρ W A :=
    ⟨⟨a, hA a.property⟩, a.property, rfl⟩
  rw [heq, Subgroup.mem_bot] at hm
  have hv := congrArg (fun g => subspaceImageRepresentation ρ W g ⟨w, hw⟩) hm
  exact congrArg (fun x : W => (x : V)) hv

theorem IsElementaryTwo.restrictedSubgroup {A : Subgroup G}
    (hA : IsElementaryTwo A) (hW : A ≤ subspaceStabilizer ρ W)
    (hn : ¬ W ≤ fixedSpace ρ A) : IsElementaryTwo (restrictedSubgroup ρ W A) := by
  let _ : IsElementaryAbelian 2 A := hA.2
  let _ : IsElementaryAbelian 2 (A.subgroupOf (subspaceStabilizer ρ W)) :=
    IsElementaryAbelian.subgroupOf hW
  exact ⟨restrictedSubgroup_ne_bot ρ W hW hn, IsElementaryAbelian.map _⟩

/-- Every subgroup of the action image lifts to a subgroup containing the whole kernel. -/
theorem exists_subgroup_restrictedSubgroup {A : Subgroup G}
    (hA : A ≤ subspaceStabilizer ρ W)
    (D : Subgroup (subspaceActionImage ρ W)) (hD : D ≤ restrictedSubgroup ρ W A) :
    ∃ B : Subgroup G, B ≤ A ∧ subspaceKernel ρ W A ≤ B ∧ restrictedSubgroup ρ W B = D := by
  let S := subspaceStabilizer ρ W
  let f := subspaceActionHom ρ W
  let B := ((A.subgroupOf S) ⊓ D.comap f).map S.subtype
  refine ⟨B, ?_, ?_, ?_⟩
  · rintro b ⟨s, ⟨hsA, _⟩, rfl⟩
    exact hsA
  · rintro a ⟨ha, hfix⟩
    refine ⟨⟨a, hA ha⟩, ⟨ha, ?_⟩, rfl⟩
    change f ⟨a, hA ha⟩ ∈ D
    have hf : f ⟨a, hA ha⟩ = 1 := by
      apply subspaceImageRepresentation_injective ρ W
      ext w
      exact hfix w w.property
    rw [hf]
    exact D.one_mem
  · ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨t, ⟨_, htD⟩, hts⟩ := hs
      have hts' : t = s := Subtype.ext hts
      subst t
      exact htD
    · intro hx
      obtain ⟨s, hs, hsx⟩ := hD hx
      refine ⟨s, ?_, hsx⟩
      exact ⟨s, ⟨hs, by change f s ∈ D; rwa [hsx]⟩, rfl⟩

end Representation.BinaryOffender

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (W : Submodule (ZMod 2) V)

theorem subspaceKernel_eq_bot_iff (A : Subgroup G) :
    subspaceKernel ρ W A = ⊥ ↔
      ∀ a ∈ A, (∀ w ∈ W, ρ a w = w) → a = 1 := by
  rw [eq_bot_iff]
  exact ⟨fun h a ha hf => Subgroup.mem_bot.mp (h ⟨ha, hf⟩),
    fun h a ha => Subgroup.mem_bot.mpr (h a ha.1 ha.2)⟩

theorem subspaceKernel_ne_self {A : Subgroup G} (hn : ¬ W ≤ fixedSpace ρ A) :
    subspaceKernel ρ W A ≠ A := by
  intro h
  apply hn
  rw [← h]
  exact le_fixedSpace_subspaceKernel ρ W A

/-- The commutator subspace `[W,A]`, generated by the action differences. -/
def subspaceCommutator (A : Subgroup G) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) {v | ∃ a ∈ A, ∃ w ∈ W, v = ρ a w - w}

/-- Vanishing of the commutator is precisely pointwise fixation of `W`. -/
theorem subspaceCommutator_eq_bot_iff (A : Subgroup G) :
    subspaceCommutator ρ W A = ⊥ ↔ W ≤ fixedSpace ρ A := by
  constructor
  · intro h w hw a
    have hm : ρ a w - w ∈ subspaceCommutator ρ W A :=
      Submodule.subset_span ⟨a, a.property, w, hw, rfl⟩
    rw [h, Submodule.mem_bot] at hm
    exact sub_eq_zero.mp hm
  · intro h
    apply le_antisymm _ bot_le
    apply Submodule.span_le.mpr
    rintro v ⟨a, ha, w, hw, rfl⟩
    change ρ a w - w = 0
    exact sub_eq_zero.mpr (h hw ⟨a, ha⟩)

/-- Identification of the pointwise kernel inside its acting subgroup. -/
theorem subspaceKernel_subgroupOf_eq_ker (A : Subgroup G)
    (hA : A ≤ subspaceStabilizer ρ W) :
    (subspaceKernel ρ W A).subgroupOf A = (subgroupActionHom ρ W A hA).ker := by
  ext a
  constructor
  · intro ha
    apply subspaceImageRepresentation_injective ρ W
    ext w
    exact ha.2 w w.property
  · intro ha
    refine ⟨a.property, ?_⟩
    intro w hw
    have h := congrArg (fun g => subspaceImageRepresentation ρ W g ⟨w, hw⟩) ha
    exact congrArg (fun v : W => (v : V)) h

/-- The kernel is normal relative to `A` when `A` stabilizes `W`. -/
theorem subspaceKernel_normal (A : Subgroup G) (hA : A ≤ subspaceStabilizer ρ W) :
    ((subspaceKernel ρ W A).subgroupOf A).Normal := by
  rw [subspaceKernel_subgroupOf_eq_ker ρ W A hA]
  infer_instance

/-- The first isomorphism theorem identifies the actual quotient with the restricted image. -/
noncomputable def subspaceQuotientEquiv (A : Subgroup G)
    (hA : A ≤ subspaceStabilizer ρ W) :
    letI := subspaceKernel_normal ρ W A hA
    A ⧸ (subspaceKernel ρ W A).subgroupOf A ≃* restrictedSubgroup ρ W A := by
  letI := subspaceKernel_normal ρ W A hA
  exact (QuotientGroup.quotientMulEquivOfEq
    (subspaceKernel_subgroupOf_eq_ker ρ W A hA)).trans
    ((QuotientGroup.quotientKerEquivRange (subgroupActionHom ρ W A hA)).trans
      (MulEquiv.subgroupCongr (subgroupActionHom_range ρ W A hA)))

/-- The image rank used in the restriction theorem is the rank of `A/C_A(W)`. -/
theorem rank_restrictedSubgroup_eq_quotient (A : Subgroup G)
    (hA : A ≤ subspaceStabilizer ρ W) :
    letI := subspaceKernel_normal ρ W A hA
    rank (restrictedSubgroup ρ W A) =
      Nat.log 2 (Nat.card (A ⧸ (subspaceKernel ρ W A).subgroupOf A)) := by
  let _ := subspaceKernel_normal ρ W A hA
  unfold rank
  rw [Nat.card_congr (subspaceQuotientEquiv ρ W A hA).toEquiv]

end Representation.BinaryOffender
