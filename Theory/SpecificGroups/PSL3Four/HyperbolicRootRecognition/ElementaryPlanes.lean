module

public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.RootRealization
public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.Reflections
public import Theory.ElementaryAbelian.Quotient

/-!
# The two elementary planes in the hyperbolic root model

In UT₃(F₄), a square is trivial precisely when xy=0. An elementary
subgroup containing an element with nonzero y has x=0 throughout, by
commutation; otherwise it lies in y=0. The two resulting root planes have
order sixteen, intersect in the literal center, and are therefore all the
elementary subgroups of order sixteen. These facts transport along the
actual word realization, retaining the marked root-coordinate equations.

Source: Aschbacher, *Sporadic Groups* (1994), 45.3, printed pp.242–243.
-/

@[expose] public section
noncomputable section
open Subgroup Matrix.PSL3Four Matrix.PSL3Four.SylowModel
namespace Theory.GroupTheory.HyperbolicRecognition

/-- The first literal root plane consists of (x,0,c). -/
def rootPlane₁ : Subgroup RootNormalizerModel.Root := axis₁.range
/-- The second literal root plane consists of (0,y,c). -/
def rootPlane₂ : Subgroup RootNormalizerModel.Root := axis₂.range

@[simp] theorem mem_rootPlane₁ (q : RootNormalizerModel.Root) : q ∈ rootPlane₁ ↔ q.y = 0 := by
  constructor
  · rintro ⟨p,rfl⟩
    rfl
  · intro hq
    exact ⟨Multiplicative.ofAdd (q.x,q.c),U.ext rfl hq.symm rfl⟩

@[simp] theorem mem_rootPlane₂ (q : RootNormalizerModel.Root) : q ∈ rootPlane₂ ↔ q.x = 0 := by
  constructor
  · rintro ⟨p,rfl⟩
    rfl
  · intro hq
    exact ⟨Multiplicative.ofAdd (q.y,q.c),U.ext hq.symm rfl rfl⟩

instance : IsElementaryAbelian 2 rootPlane₁ :=
  IsElementaryAbelian.of_surjective axis₁.rangeRestrict axis₁.rangeRestrict_surjective
instance : IsElementaryAbelian 2 rootPlane₂ :=
  IsElementaryAbelian.of_surjective axis₂.rangeRestrict axis₂.rangeRestrict_surjective

@[simp] theorem card_rootPlane₁ : Nat.card rootPlane₁ = 16 := by
  rw [rootPlane₁,← Nat.card_congr (MonoidHom.ofInjective axis₁_injective).toEquiv]
  change Nat.card (F × F) = 16
  rw [Nat.card_prod,card_F]

@[simp] theorem card_rootPlane₂ : Nat.card rootPlane₂ = 16 := by
  rw [rootPlane₂,← Nat.card_congr (MonoidHom.ofInjective axis₂_injective).toEquiv]
  change Nat.card (F × F) = 16
  rw [Nat.card_prod,card_F]

theorem rootPlanes_inf : rootPlane₁ ⊓ rootPlane₂ = center RootNormalizerModel.Root := by
  ext q
  simp only [mem_inf,mem_rootPlane₁,mem_rootPlane₂,mem_center_U,and_comm]

theorem rootPlanes_ne : rootPlane₁ ≠ rootPlane₂ := by
  intro h
  have hm : (⟨1,0,0⟩ : RootNormalizerModel.Root) ∈ rootPlane₁ := by simp
  rw [h,mem_rootPlane₂] at hm
  exact one_ne_zero hm

/-- The only possible root direction of an involution lies on one of the axes. -/
theorem root_square_eq_one (q : RootNormalizerModel.Root) : q^2 = 1 ↔ q.x*q.y = 0 := by
  constructor
  · intro h
    have hc := congrArg U.c h
    simpa only [pow_two,mul_c,one_c,CharTwo.add_self_eq_zero,zero_add] using hc
  · intro h
    rw [pow_two]
    apply U.ext <;> simp [h,CharTwo.add_self_eq_zero]

/-- Every elementary subgroup is contained in one of the two literal root planes. -/
theorem elementary_le_rootPlane (E : Subgroup RootNormalizerModel.Root)
    [IsElementaryAbelian 2 E] : E ≤ rootPlane₁ ∨ E ≤ rootPlane₂ := by
  by_cases h : E ≤ rootPlane₁
  · exact Or.inl h
  · right
    obtain ⟨g,hg,hn⟩ := SetLike.not_le_iff_exists.mp h
    have hgy : g.y ≠ 0 := by simpa only [mem_rootPlane₁] using hn
    have hgx : g.x = 0 := (mul_eq_zero.mp
      ((root_square_eq_one g).mp (elemPow_eq_one_of_isElementaryAbelian g hg))).resolve_right hgy
    intro q hq
    apply (mem_rootPlane₂ q).mpr
    have hc : g*q=q*g := congrArg Subtype.val
      (IsMulCommutative.is_comm.comm (⟨g,hg⟩ : E) ⟨q,hq⟩)
    have hh := (SylowModel.commute_iff g q).mp hc
    rw [hgx,zero_mul] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_right hgy

/-- There are exactly two elementary subgroups of order sixteen. -/
theorem elementary_sixteen_iff (E : Subgroup RootNormalizerModel.Root) :
    (IsElementaryAbelian 2 E ∧ Nat.card E = 16) ↔ E = rootPlane₁ ∨ E = rootPlane₂ := by
  constructor
  · rintro ⟨hE,hcard⟩
    let := hE
    rcases elementary_le_rootPlane E with h | h
    · exact Or.inl (eq_of_le_of_card_ge h (by rw [card_rootPlane₁,hcard]))
    · exact Or.inr (eq_of_le_of_card_ge h (by rw [card_rootPlane₂,hcard]))
  · rintro (rfl | rfl)
    · exact ⟨inferInstance,card_rootPlane₁⟩
    · exact ⟨inferInstance,card_rootPlane₂⟩

variable {K : Type*} [Group K]

/-- The first actual subgroup transported along a supplied root realization. -/
def transportedPlane₁ (e : K ≃* RootNormalizerModel.Root) : Subgroup K :=
  rootPlane₁.map e.symm.toMonoidHom
/-- The second actual subgroup transported along a supplied root realization. -/
def transportedPlane₂ (e : K ≃* RootNormalizerModel.Root) : Subgroup K :=
  rootPlane₂.map e.symm.toMonoidHom

@[simp] theorem mem_transportedPlane₁ (e : K ≃* RootNormalizerModel.Root) (x : K) :
    x ∈ transportedPlane₁ e ↔ (e x).y = 0 := by
  rw [transportedPlane₁,map_equiv_eq_comap_symm']
  exact mem_rootPlane₁ (e x)

@[simp] theorem mem_transportedPlane₂ (e : K ≃* RootNormalizerModel.Root) (x : K) :
    x ∈ transportedPlane₂ e ↔ (e x).x = 0 := by
  rw [transportedPlane₂,map_equiv_eq_comap_symm']
  exact mem_rootPlane₂ (e x)

instance (e : K ≃* RootNormalizerModel.Root) : IsElementaryAbelian 2 (transportedPlane₁ e) :=
  IsElementaryAbelian.map e.symm.toMonoidHom
instance (e : K ≃* RootNormalizerModel.Root) : IsElementaryAbelian 2 (transportedPlane₂ e) :=
  IsElementaryAbelian.map e.symm.toMonoidHom

@[simp] theorem card_transportedPlane₁ (e : K ≃* RootNormalizerModel.Root) :
    Nat.card (transportedPlane₁ e) = 16 := by
  rw [transportedPlane₁,card_map_of_injective e.symm.injective,card_rootPlane₁]

@[simp] theorem card_transportedPlane₂ (e : K ≃* RootNormalizerModel.Root) :
    Nat.card (transportedPlane₂ e) = 16 := by
  rw [transportedPlane₂,card_map_of_injective e.symm.injective,card_rootPlane₂]

private theorem equiv_mem_center (e : K ≃* RootNormalizerModel.Root) (x : K) :
    e x ∈ center RootNormalizerModel.Root ↔ x ∈ center K := by
  constructor
  · intro h
    apply mem_center_iff.mpr
    intro y
    apply e.injective
    simpa only [map_mul] using mem_center_iff.mp h (e y)
  · intro h
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z,rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp h z)

theorem transportedPlanes_inf (e : K ≃* RootNormalizerModel.Root) :
    transportedPlane₁ e ⊓ transportedPlane₂ e = center K := by
  ext x
  rw [mem_inf,mem_transportedPlane₁,mem_transportedPlane₂,← equiv_mem_center e,
    mem_center_U,and_comm]

theorem transportedPlanes_ne (e : K ≃* RootNormalizerModel.Root) :
    transportedPlane₁ e ≠ transportedPlane₂ e := by
  exact fun h => rootPlanes_ne (map_injective e.symm.injective h)

/-- The original carrier has precisely the two transported elementary sixteen-groups. -/
theorem transported_elementary_sixteen_iff (e : K ≃* RootNormalizerModel.Root)
    (E : Subgroup K) :
    (IsElementaryAbelian 2 E ∧ Nat.card E = 16) ↔
      E = transportedPlane₁ e ∨ E = transportedPlane₂ e := by
  constructor
  · rintro ⟨hE,hcard⟩
    let := hE
    have hh := (elementary_sixteen_iff (E.map e.toMonoidHom)).mp
      ⟨IsElementaryAbelian.map e.toMonoidHom,by rw [card_map_of_injective e.injective,hcard]⟩
    have heq : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id K := by
      ext x
      exact e.symm_apply_apply x
    rcases hh with h | h
    · left
      have he := congrArg (Subgroup.map e.symm.toMonoidHom) h
      simpa only [Subgroup.map_map,heq,Subgroup.map_id,transportedPlane₁] using he
    · right
      have he := congrArg (Subgroup.map e.symm.toMonoidHom) h
      simpa only [Subgroup.map_map,heq,Subgroup.map_id,transportedPlane₂] using he
  · rintro (rfl | rfl)
    · exact ⟨inferInstance,card_transportedPlane₁ e⟩
    · exact ⟨inferInstance,card_transportedPlane₂ e⟩

/-- Membership on the first root plane retains the marked binary vector. -/
theorem mem_modelPlane₁ (i : Fin 2) (w : Word (modelMatrix i)) :
    w ∈ transportedPlane₁ (modelEquiv i) ↔ modelFirstAxis i w.vector := by
  rw [mem_transportedPlane₁,modelEquiv_y_eq_zero]

/-- Membership on the second root plane retains the marked binary vector. -/
theorem mem_modelPlane₂ (i : Fin 2) (w : Word (modelMatrix i)) :
    w ∈ transportedPlane₂ (modelEquiv i) ↔ modelSecondAxis i w.vector := by
  rw [mem_transportedPlane₂,modelEquiv_x_eq_zero]

/-- The unique source frame in the respective surviving word law. -/
def modelFrame (i : Fin 2) : Frame := if i = 0 then identityFrame else exchangeFrame

/-- Both exact quotient reflections preserve both root axes separately. -/
theorem model_reflections_preserve_axes : ∀ (i : Fin 2) (v : Vector),
    (modelFirstAxis i (reflectA (modelFrame i) v) ↔ modelFirstAxis i v) ∧
    (modelSecondAxis i (reflectA (modelFrame i) v) ↔ modelSecondAxis i v) ∧
    (modelFirstAxis i (reflectB (modelFrame i) v) ↔ modelFirstAxis i v) ∧
    (modelSecondAxis i (reflectB (modelFrame i) v) ↔ modelSecondAxis i v) := by
  decide +kernel

private theorem map_eq_of_stable [Finite K] (E : Subgroup K) (α : MulAut K)
    (h : ∀ x ∈ E, α x ∈ E) : E.map α.toMonoidHom = E := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    exact h x hx
  · rw [card_map_of_injective α.injective]

/-- The first transported plane is detected by the original marked word coordinates. -/
theorem mem_realizedPlane₁ (i : Fin 2) (C : K ≃* Word (modelMatrix i)) (x : K) :
    x ∈ transportedPlane₁ (C.trans (modelEquiv i)) ↔ modelFirstAxis i (C x).vector := by
  rw [mem_transportedPlane₁]
  exact modelEquiv_y_eq_zero i (C x)

/-- The second transported plane is detected by the original marked word coordinates. -/
theorem mem_realizedPlane₂ (i : Fin 2) (C : K ≃* Word (modelMatrix i)) (x : K) :
    x ∈ transportedPlane₂ (C.trans (modelEquiv i)) ↔ modelSecondAxis i (C x).vector := by
  rw [mem_transportedPlane₂]
  exact modelEquiv_x_eq_zero i (C x)

/-- An actual first reflection fixes both original sixteen-groups individually;
no condition on its central coordinate corrections is needed. -/
theorem reflectionA_preserves_planes (i : Fin 2) (C : K ≃* Word (modelMatrix i))
    (α : MulAut K) (hα : ∀ x : K,
      (C (α x)).vector = reflectA (modelFrame i) (C x).vector) :
    (transportedPlane₁ (C.trans (modelEquiv i))).map α.toMonoidHom =
      transportedPlane₁ (C.trans (modelEquiv i)) ∧
    (transportedPlane₂ (C.trans (modelEquiv i))).map α.toMonoidHom =
      transportedPlane₂ (C.trans (modelEquiv i)) := by
  let : Finite K := Finite.of_equiv (Word (modelMatrix i)) C.symm.toEquiv
  constructor
  · apply map_eq_of_stable
    intro x hx
    rw [mem_realizedPlane₁,hα]
    exact (model_reflections_preserve_axes i (C x).vector).1.mpr
      ((mem_realizedPlane₁ i C x).mp hx)
  · apply map_eq_of_stable
    intro x hx
    rw [mem_realizedPlane₂,hα]
    exact (model_reflections_preserve_axes i (C x).vector).2.1.mpr
      ((mem_realizedPlane₂ i C x).mp hx)

/-- The actual second reflection fixes the same two original sixteen-groups. -/
theorem reflectionB_preserves_planes (i : Fin 2) (C : K ≃* Word (modelMatrix i))
    (β : MulAut K) (hβ : ∀ x : K,
      (C (β x)).vector = reflectB (modelFrame i) (C x).vector) :
    (transportedPlane₁ (C.trans (modelEquiv i))).map β.toMonoidHom =
      transportedPlane₁ (C.trans (modelEquiv i)) ∧
    (transportedPlane₂ (C.trans (modelEquiv i))).map β.toMonoidHom =
      transportedPlane₂ (C.trans (modelEquiv i)) := by
  let : Finite K := Finite.of_equiv (Word (modelMatrix i)) C.symm.toEquiv
  constructor
  · apply map_eq_of_stable
    intro x hx
    rw [mem_realizedPlane₁,hβ]
    exact (model_reflections_preserve_axes i (C x).vector).2.2.1.mpr
      ((mem_realizedPlane₁ i C x).mp hx)
  · apply map_eq_of_stable
    intro x hx
    rw [mem_realizedPlane₂,hβ]
    exact (model_reflections_preserve_axes i (C x).vector).2.2.2.mpr
      ((mem_realizedPlane₂ i C x).mp hx)

end Theory.GroupTheory.HyperbolicRecognition
