module

public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.Geometry
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.TensorData
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.NaturalRecognition.Coordinates

/-!
# Intertwining the actual component join

Multiplication identifies the disjoint commuting components with their join.
The supplied TensorData equivalence intertwines each factor separately;
composition gives the product action. Semilinear changes in both factors
transport their common field, and restriction of scalars gives a binary
linear intertwiner on the original space V.

The final lemma constructs the two factor comparisons from their faithful
matrix images and orders. Source: Aschbacher--Smith, G.9.3, printed p.356.
-/

@[expose] public noncomputable section

open scoped MatrixGroups TensorProduct

namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents.NaturalRecognition

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

variable {F E : Type*} [Field F] [Field E] [Algebra (ZMod 2) F]
  [Algebra (ZMod 2) E]
  {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  [Module F M] [Module E N] [Module (ZMod 2) M] [Module (ZMod 2) N]
  [IsScalarTower (ZMod 2) F M] [IsScalarTower (ZMod 2) E N]

private def binaryEquiv (e : F ≃ₐ[ZMod 2] E) (f : M ≃ₛₗ[(e.toRingEquiv : F →+* E)] N) :
    M ≃ₗ[ZMod 2] N :=
  { f.toAddEquiv with
    map_smul' := fun r x => by
      change f (r • x) = r • f x
      rw [← algebraMap_smul F r x, f.map_smulₛₗ]
      change e (algebraMap (ZMod 2) F r) • f x = _
      rw [e.commutes, algebraMap_smul] }

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L L₂ H : Subgroup G}

/-- External tensor action over the common field. -/
def externalTensor {D D' : Type*} [Group D] [Group D']
    {W W' : Type*} [AddCommGroup W] [AddCommGroup W'] [Module E W] [Module E W']
    (σ : Representation E D W) (τ : Representation E D' W') :
    Representation E (D × D') (W ⊗[E] W') where
  toFun g := TensorProduct.map (σ g.1) (τ g.2)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [Module.End.mul_eq_comp, TensorProduct.map_comp]

/-- Restrict the public multiplication map to its proved range. Its evaluation
formula is needed below; the older `productEquiv` does not expose that formula. -/
private def joinEquiv (hc : ⁅L, L₂⁆ = ⊥) (hd : Disjoint L L₂) :
    L × L₂ ≃* (L ⊔ L₂ : Subgroup G) := by
  let f : L × L₂ →* (L ⊔ L₂ : Subgroup G) :=
    (productMap hc).codRestrict _ fun x => by
      rw [← productMap_range hc]
      exact ⟨x, rfl⟩
  have hi : Function.Injective (productMap hc) :=
    (MonoidHom.noncommCoprod_injective _ _ _).mpr
      ⟨L.subtype_injective, L₂.subtype_injective,
        by simpa only [Subgroup.range_subtype] using hd⟩
  refine MulEquiv.ofBijective f ⟨fun _ _ he => hi (congrArg Subtype.val he), ?_⟩
  intro x
  have hx : (x : G) ∈ (productMap hc).range := (productMap_range hc).symm ▸ x.property
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, Subtype.ext hy⟩

private theorem tensor_quasiequivalent (T : TensorData ρ L L₂)
    (hc : ⁅L, L₂⁆ = ⊥) (hd : Disjoint L L₂) (hH : H = L ⊔ L₂)
    {D D' : Type*} [Group D] [Group D']
    {W W' : Type*} [AddCommGroup W] [AddCommGroup W'] [Module E W] [Module E W']
    [Module (ZMod 2) W] [Module (ZMod 2) W']
    [IsScalarTower (ZMod 2) E W] [IsScalarTower (ZMod 2) E W']
    (σ : Representation E D W) (τ : Representation E D' W')
    (c : T.F ≃ₐ[ZMod 2] E) (e : L ≃* D) (e' : L₂ ≃* D')
    (f : T.I ≃ₛₗ[(c.toRingEquiv : T.F →+* E)] W) (f' : T.J ≃ₛₗ[(c.toRingEquiv : T.F →+* E)] W')
    (hf : ∀ g x, f (T.left g x) = σ (e g) (f x))
    (hf' : ∀ g x, f' (T.right g x) = τ (e' g) (f' x)) :
    Quasiequivalent (ρ.comp H.subtype)
      (Representation.restrictScalars (k := ZMod 2) (externalTensor σ τ)) := by
  subst H
  let p := joinEquiv hc hd
  let q := TensorProduct.congr f f'
  refine ⟨p.symm.trans (e.prodCongr e'), binaryEquiv c (T.tensor.trans q), ?_⟩
  intro g v
  obtain ⟨⟨l, j⟩, rfl⟩ := p.surjective g
  have hp : ((p (l, j) : (L ⊔ L₂ : Subgroup G)) : G) = (l : G) * (j : G) := rfl
  change q (T.tensor (ρ (p (l, j)) v)) =
    TensorProduct.map (σ (e (p.symm (p (l, j))).1))
      (τ (e' (p.symm (p (l, j))).2)) (q (T.tensor v))
  rw [hp, map_mul, Module.End.mul_apply, T.left_tensor, T.right_tensor,
    p.symm_apply_apply]
  generalize T.tensor v = z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    change f (T.left l x) ⊗ₜ[E] f' (T.right j y) =
      σ (e l) (f x) ⊗ₜ[E] τ (e' j) (f' y)
    rw [hf, hf']
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Transitivity retains both group and module intertwiners. -/
theorem quasiequivalent_trans {G D B V W U : Type*} [Group G] [Group D] [Group B]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup U] [Module (ZMod 2) U]
    {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) D W}
    {τ : Representation (ZMod 2) B U}
    (h : Quasiequivalent ρ σ) (h' : Quasiequivalent σ τ) : Quasiequivalent ρ τ := by
  obtain ⟨e, f, hf⟩ := h
  obtain ⟨e', f', hf'⟩ := h'
  exact ⟨e.trans e', f.trans f', fun g x => by
    change f' (f (ρ g x)) = τ (e' (e g)) (f' (f x))
    rw [hf, hf']⟩

/-- Recognition uses the actual matrix image of each factor, never an assumed
natural-module isomorphism. -/
theorem tensor_natural_of_order (T : TensorData ρ L L₂)
    [Group.IsPerfect L] [Group.IsPerfect L₂]
    (hc : ⁅L, L₂⁆ = ⊥) (hd : Disjoint L L₂) (hH : H = L ⊔ L₂)
    {E : Type*} [Field E] [Algebra (ZMod 2) E] [Finite E]
    (c : T.F ≃ₐ[ZMod 2] E) {d : ℕ} (hk : T.k = d)
    (ho : Nat.card L = Nat.card SL(d,E)) (ho' : Nat.card L₂ = Nat.card SL(d,E)) :
    Quasiequivalent (ρ.comp H.subtype)
      (Representation.restrictScalars (k := ZMod 2)
        (externalTensor (Representation.specialLinearNatural (k := E) d)
          (Representation.specialLinearNatural d))) := by
  obtain ⟨e, f, hf⟩ := natural_coordinates_of_order T.left T.left_faithful hk c.toRingEquiv ho
  obtain ⟨e', f', hf'⟩ := natural_coordinates_of_order T.right T.right_faithful
    (T.equal_dimension.trans hk) c.toRingEquiv ho'
  exact tensor_quasiequivalent T hc hd hH _ _ c e e' f f' hf hf'

end CFSG.Quasithin.ChapterG.Section09.TwoComponents.NaturalRecognition
