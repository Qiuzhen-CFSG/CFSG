module

public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Tauto

/-!
# Coordinates for the exceptional Sylow 2-group of PSL(3,4).2

The group is UT₃(F₄) extended by the entrywise field involution. The two root
planes and their common center remain marked as actual subgroups. We establish
their coordinate isomorphisms, orders and elementary abelianness, identify the
centralizer of the unipotent center, and specify the normal trace kernel Q.

The multiplication is (x,y,c)(x',y',c') =
(x+x',y+y',c+c'+xy'). Frobenius acts in each coordinate. Thus all calculations
reduce to field identities; the trace kernel has prime-field x,y coordinates.
The quaternion structure of that kernel and the recognition in a matrix
amalgam are separate results, not assumptions in these definitions.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, §5.3.7,
printed pp. 660--661 (PDF pp. 677--678).
-/

@[expose] public section
noncomputable section
namespace Matrix.PSL3Four.SylowModel
@[ext] structure U where
  x : F
  y : F
  c : F

instance : Mul U where
  mul a b := ⟨a.x + b.x, a.y + b.y, a.c + b.c + a.x * b.y⟩
instance : One U where
  one := ⟨0, 0, 0⟩
instance : Inv U where
  inv a := ⟨-a.x, -a.y, a.x * a.y - a.c⟩
instance : Group U where
  mul_assoc a b c := by
    refine U.ext (add_assoc _ _ _) (add_assoc _ _ _) ?_
    change (a.c + b.c + a.x * b.y) + c.c + (a.x + b.x) * c.y =
      a.c + (b.c + c.c + b.x * c.y) + a.x * (b.y + c.y)
    ring
  one_mul a := by
    refine U.ext (zero_add _) (zero_add _) ?_
    change 0 + a.c + 0 * a.y = a.c
    ring
  mul_one a := by
    refine U.ext (add_zero _) (add_zero _) ?_
    change a.c + 0 + a.x * 0 = a.c
    ring
  inv_mul_cancel a := by
    refine U.ext (neg_add_cancel _) (neg_add_cancel _) ?_
    change (a.x * a.y - a.c) + a.c + -a.x * a.y = 0
    ring

def coordinates : U ≃ F × F × F where
  toFun a := (a.x, a.y, a.c)
  invFun a := ⟨a.1, a.2.1, a.2.2⟩

instance : Finite U := Finite.of_equiv _ coordinates.symm

theorem card_U : Nat.card U = 64 := by
  rw [Nat.card_congr coordinates, Nat.card_prod, Nat.card_prod, card_F]

noncomputable def frob : MulAut U where
  toFun a := ⟨fieldFrobenius a.x, fieldFrobenius a.y, fieldFrobenius a.c⟩
  invFun a := ⟨fieldFrobenius a.x, fieldFrobenius a.y, fieldFrobenius a.c⟩
  left_inv a := by ext <;> exact fieldFrobenius_involutive _
  right_inv a := by ext <;> exact fieldFrobenius_involutive _
  map_mul' a b := by
    apply U.ext
    · exact map_add fieldFrobenius _ _
    · exact map_add fieldFrobenius _ _
    · change fieldFrobenius (a.c + b.c + a.x * b.y) = _
      rw [map_add, map_add, map_mul]
      rfl

theorem frob_sq : frob ^ 2 = 1 := by
  ext a <;> exact fieldFrobenius_involutive _

noncomputable def action : C2 →* MulAut U := involutionHom frob frob_sq
abbrev T := U ⋊[action] C2
instance : Finite T := Finite.of_equiv (U × C2) SemidirectProduct.equivProd.symm

theorem card_T : Nat.card T = 128 := by
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, card_U, card_C2]

@[simp] theorem mul_x (a b : U) : (a * b).x = a.x + b.x := rfl
@[simp] theorem mul_y (a b : U) : (a * b).y = a.y + b.y := rfl
@[simp] theorem mul_c (a b : U) : (a * b).c = a.c + b.c + a.x * b.y := rfl
@[simp] theorem one_x : (1 : U).x = 0 := rfl
@[simp] theorem one_y : (1 : U).y = 0 := rfl
@[simp] theorem one_c : (1 : U).c = 0 := rfl

/-- The embedded UT₃(F₄). -/
def inclusion : U →* T := SemidirectProduct.inl

def S : Subgroup T := inclusion.range

def linearEquiv : U ≃* S where
  toFun u := ⟨inclusion u, ⟨u, rfl⟩⟩
  invFun s := s.val.left
  left_inv u := rfl
  right_inv s := by
    rcases s with ⟨s, u, rfl⟩
    rfl
  map_mul' a b := Subtype.ext (map_mul inclusion a b)

@[simp] theorem mem_S (a : T) : a ∈ S ↔ a.right = 1 := by
  rw [S, inclusion, SemidirectProduct.range_inl_eq_ker_rightHom]
  rfl

@[simp] theorem card_S : Nat.card S = 64 := by
  rw [← Nat.card_congr linearEquiv.toEquiv, card_U]

/-- The first and second root planes, with the common highest-root direction. -/
def axis₁ : Multiplicative (F × F) →* U where
  toFun p := ⟨p.toAdd.1, 0, p.toAdd.2⟩
  map_one' := rfl
  map_mul' a b := by apply U.ext <;> simp

def axis₂ : Multiplicative (F × F) →* U where
  toFun p := ⟨0, p.toAdd.1, p.toAdd.2⟩
  map_one' := rfl
  map_mul' a b := by apply U.ext <;> simp

def central : Multiplicative F →* U where
  toFun c := ⟨0, 0, c.toAdd⟩
  map_one' := rfl
  map_mul' a b := by apply U.ext <;> simp

def V₁ : Subgroup T := (inclusion.comp axis₁).range
def V₂ : Subgroup T := (inclusion.comp axis₂).range
def Z : Subgroup T := (inclusion.comp central).range

theorem axis₁_injective : Function.Injective axis₁ := by
  intro a b h
  exact Prod.ext (congrArg U.x h) (congrArg U.c h)
theorem axis₂_injective : Function.Injective axis₂ := by
  intro a b h
  exact Prod.ext (congrArg U.y h) (congrArg U.c h)
theorem central_injective : Function.Injective central := by
  intro a b h
  exact congrArg U.c h

def plane₁Equiv : Multiplicative (F × F) ≃* V₁ :=
  MonoidHom.ofInjective (SemidirectProduct.inl_injective.comp axis₁_injective)
def plane₂Equiv : Multiplicative (F × F) ≃* V₂ :=
  MonoidHom.ofInjective (SemidirectProduct.inl_injective.comp axis₂_injective)
def centralEquiv : Multiplicative F ≃* Z :=
  MonoidHom.ofInjective (SemidirectProduct.inl_injective.comp central_injective)

@[simp] theorem card_V₁ : Nat.card V₁ = 16 := by
  rw [← Nat.card_congr plane₁Equiv.toEquiv]
  change Nat.card (F × F) = 16
  rw [Nat.card_prod, card_F]
@[simp] theorem card_V₂ : Nat.card V₂ = 16 := by
  rw [← Nat.card_congr plane₂Equiv.toEquiv]
  change Nat.card (F × F) = 16
  rw [Nat.card_prod, card_F]
@[simp] theorem card_Z : Nat.card Z = 4 := by
  rw [← Nat.card_congr centralEquiv.toEquiv]
  exact card_F

@[simp] theorem mem_V₁ (a : T) : a ∈ V₁ ↔ a.right = 1 ∧ a.left.y = 0 := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨hr, hy⟩
    refine ⟨Multiplicative.ofAdd (a.left.x, a.left.c), ?_⟩
    apply SemidirectProduct.ext
    · exact U.ext rfl hy.symm rfl
    · exact hr.symm

@[simp] theorem mem_V₂ (a : T) : a ∈ V₂ ↔ a.right = 1 ∧ a.left.x = 0 := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨hr, hx⟩
    refine ⟨Multiplicative.ofAdd (a.left.y, a.left.c), ?_⟩
    apply SemidirectProduct.ext
    · exact U.ext hx.symm rfl rfl
    · exact hr.symm

@[simp] theorem mem_Z (a : T) : a ∈ Z ↔ a.right = 1 ∧ a.left.x = 0 ∧ a.left.y = 0 := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨hr, hx, hy⟩
    refine ⟨Multiplicative.ofAdd a.left.c, ?_⟩
    apply SemidirectProduct.ext
    · exact U.ext hx.symm hy.symm rfl
    · exact hr.symm

instance : IsElementaryAbelian 2 (Multiplicative (F × F)) where
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro a
    rw [pow_two]
    change a.toAdd + a.toAdd = 0
    exact Prod.ext (CharTwo.add_self_eq_zero _) (CharTwo.add_self_eq_zero _)

instance : IsElementaryAbelian 2 V₁ where
  toIsMulCommutative := ⟨⟨fun a b => plane₁Equiv.symm.injective (by
    simp only [map_mul, mul_comm])⟩⟩
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro a
    apply plane₁Equiv.symm.injective
    rw [map_pow, map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (Multiplicative (F × F))) _

instance : IsElementaryAbelian 2 V₂ where
  toIsMulCommutative := ⟨⟨fun a b => plane₂Equiv.symm.injective (by
    simp only [map_mul, mul_comm])⟩⟩
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro a
    apply plane₂Equiv.symm.injective
    rw [map_pow, map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (Multiplicative (F × F))) _

/-- Generator of the field-automorphism complement. -/
def τ : C2 := Multiplicative.ofAdd 1

theorem c2_cases (t : C2) : t = 1 ∨ t = τ := by
  change ZMod 2 at t
  fin_cases t
  · exact Or.inl rfl
  · exact Or.inr rfl

@[simp] theorem action_τ : action τ = frob := involutionHom_generator _ _

@[simp] theorem frob_x (a : U) : (frob a).x = fieldFrobenius a.x := rfl
@[simp] theorem frob_y (a : U) : (frob a).y = fieldFrobenius a.y := rfl
@[simp] theorem frob_c (a : U) : (frob a).c = fieldFrobenius a.c := rfl

/-- In the unipotent group only the highest-root coordinate measures commutation. -/
theorem commute_iff (a b : U) : a * b = b * a ↔ a.x * b.y = b.x * a.y := by
  constructor
  · intro h
    have hc := congrArg U.c h
    simpa only [mul_c, add_comm b.c a.c, add_left_cancel_iff] using hc
  · intro h
    apply U.ext
    · exact add_comm _ _
    · exact add_comm _ _
    · simpa only [mul_c, add_comm b.c a.c] using congrArg (a.c + b.c + ·) h

@[simp] theorem mem_center_U (a : U) :
    a ∈ Subgroup.center U ↔ a.x = 0 ∧ a.y = 0 := by
  constructor
  · intro h
    have h₁ := (commute_iff ⟨0, 1, 0⟩ a).mp (Subgroup.mem_center_iff.mp h _)
    have h₂ := (commute_iff ⟨1, 0, 0⟩ a).mp (Subgroup.mem_center_iff.mp h _)
    exact ⟨by simpa using h₁.symm, by simpa using h₂⟩
  · rintro ⟨hx, hy⟩
    apply Subgroup.mem_center_iff.mpr
    intro b
    exact (commute_iff b a).mpr (by simp [hx, hy])

/-- The central involution fixed by Frobenius. -/
def z : T := inclusion (central (Multiplicative.ofAdd 1))

theorem z_ne_one : z ≠ 1 := by
  intro h
  have hc := congrArg (fun a : T => a.left.c) h
  exact one_ne_zero hc

theorem z_sq : z ^ 2 = 1 := by
  rw [z, ← map_pow, ← map_pow]
  have h : (Multiplicative.ofAdd (1 : F)) ^ 2 = 1 := by
    rw [pow_two]
    exact CharTwo.add_self_eq_zero (1 : F)
  rw [h, map_one, map_one]

theorem z_mem_Z : z ∈ Z := ⟨Multiplicative.ofAdd 1, rfl⟩

theorem V₁_le_S : V₁ ≤ S := fun a h => (mem_S a).mpr ((mem_V₁ a).mp h).1
theorem V₂_le_S : V₂ ≤ S := fun a h => (mem_S a).mpr ((mem_V₂ a).mp h).1

theorem V₁_inf_V₂ : V₁ ⊓ V₂ = Z := by
  ext a
  simp only [Subgroup.mem_inf, mem_V₁, mem_V₂, mem_Z]
  tauto

theorem center_S : (Subgroup.center S).map S.subtype = Z := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hc : linearEquiv.symm b ∈ Subgroup.center U :=
      (Subgroup.centerCongr linearEquiv.symm ⟨b, hb⟩).property
    have hc' := (mem_center_U _).mp hc
    exact (mem_Z b.val).mpr ⟨(mem_S b.val).mp b.property, hc'⟩
  · intro ha
    have hz := (mem_Z a).mp ha
    have hs : a ∈ S := (mem_S a).mpr hz.1
    refine ⟨⟨a, hs⟩, ?_, rfl⟩
    have hc : linearEquiv.symm ⟨a, hs⟩ ∈ Subgroup.center U :=
      (mem_center_U _).mpr hz.2
    have hp := (Subgroup.centerCongr linearEquiv
      ⟨linearEquiv.symm ⟨a, hs⟩, hc⟩).property
    change linearEquiv (linearEquiv.symm ⟨a, hs⟩) ∈ Subgroup.center S at hp
    rwa [linearEquiv.apply_symm_apply] at hp

theorem centralizer_Z : Subgroup.centralizer (Z : Set T) = S := by
  ext a
  rw [mem_S, Subgroup.mem_centralizer_iff]
  constructor
  · intro ha
    rcases c2_cases a.right with hr | hr
    · exact hr
    · obtain ⟨c, hc⟩ := exists_fieldFrobenius_ne
      have he := ha (inclusion (central (Multiplicative.ofAdd c))) ⟨_, rfl⟩
      have he' := congrArg (fun a : T => a.left.c) he
      change c + a.left.c + 0 * a.left.y =
        a.left.c + (action a.right (central (Multiplicative.ofAdd c))).c +
          a.left.x * (action a.right (central (Multiplicative.ofAdd c))).y at he'
      rw [hr, action_τ] at he'
      simp only [frob_c, frob_y, central, MonoidHom.coe_mk, OneHom.coe_mk,
        map_zero, mul_zero, zero_mul, add_zero, add_comm c a.left.c,
        add_right_inj] at he'
      exact False.elim (hc he'.symm)
  · intro hr b hb
    have hz := (mem_Z b).mp hb
    apply SemidirectProduct.ext
    · simp only [SemidirectProduct.mul_left, hr, hz.1, map_one, MulAut.one_apply]
      exact (commute_iff b.left a.left).mpr (by simp [hz.2.1, hz.2.2])
    · simp [hr, hz.1]

theorem z_mem_center : z ∈ Subgroup.center T := by
  apply Subgroup.mem_center_iff.mpr
  intro a
  rcases c2_cases a.right with hr | hr <;>
    apply SemidirectProduct.ext
  · apply U.ext <;> simp [z, inclusion, central, hr, add_comm]
  · simp [z, inclusion]
  · apply U.ext <;> simp [z, inclusion, central, hr, action_τ, frob, add_comm]
  · simp [z, inclusion]

/-- The trace to the prime field, viewed in F₄. -/
def trace (a : F) : F := a + fieldFrobenius a

@[simp] theorem trace_zero : trace 0 = 0 := by simp [trace]
theorem trace_add (a b : F) : trace (a + b) = trace a + trace b := by
  simp only [trace, map_add]
  ring
@[simp] theorem trace_frob (a : F) : trace (fieldFrobenius a) = trace a := by
  simp only [trace, fieldFrobenius_involutive, add_comm]

theorem trace_eq_zero (a : F) : trace a = 0 ↔ fieldFrobenius a = a := by
  rw [trace, add_eq_zero_iff_eq_neg, CharTwo.neg_eq, eq_comm]

/-- The two off-diagonal traces are additive even in the field extension. -/
def traceHom : T →* Multiplicative (F × F) where
  toFun a := Multiplicative.ofAdd (trace a.left.x, trace a.left.y)
  map_one' := by change (trace 0, trace 0) = (0, 0); simp
  map_mul' a b := by
    rcases c2_cases a.right with hr | hr
    · change (trace (a.left.x + (action a.right b.left).x),
        trace (a.left.y + (action a.right b.left).y)) = _
      simp only [hr, map_one, MulAut.one_apply, trace_add]
      rfl
    · change (trace (a.left.x + (action a.right b.left).x),
        trace (a.left.y + (action a.right b.left).y)) = _
      simp only [hr, action_τ, frob_x, frob_y, trace_add, trace_frob]
      rfl

/-- The source quaternion core, specified by prime-field off-diagonal coordinates.
Its extraspecial and quaternion-factor properties are proved separately. -/
def Q : Subgroup T := traceHom.ker
instance : Q.Normal := inferInstanceAs traceHom.ker.Normal

@[simp] theorem mem_Q (a : T) : a ∈ Q ↔
    fieldFrobenius a.left.x = a.left.x ∧ fieldFrobenius a.left.y = a.left.y := by
  change (trace a.left.x, trace a.left.y) = (0, 0) ↔ _
  rw [Prod.mk.injEq, trace_eq_zero, trace_eq_zero]

theorem Z_le_Q : Z ≤ Q := by
  intro a ha
  have hz := (mem_Z a).mp ha
  exact (mem_Q a).mpr (by simp [hz.2.1, hz.2.2])

/-- The central subgroup used in the source quotient. -/
def C : Subgroup T := Subgroup.zpowers z

theorem C_le_center : C ≤ Subgroup.center T :=
  Subgroup.zpowers_le_of_mem z_mem_center

instance : C.Normal where
  conj_mem a ha g := by
    have hc := Subgroup.mem_center_iff.mp (C_le_center ha) g
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    exact ha

theorem C_le_Z : C ≤ Z := Subgroup.zpowers_le_of_mem z_mem_Z
theorem C_le_Q : C ≤ Q := C_le_Z.trans Z_le_Q

/-- T modulo its marked central involution. -/
abbrev Tbar := T ⧸ C

def quotient : T →* Tbar := QuotientGroup.mk' C

/-- The image of the trace kernel in the marked central quotient. -/
def Qbar : Subgroup Tbar := Q.map quotient

end Matrix.PSL3Four.SylowModel
