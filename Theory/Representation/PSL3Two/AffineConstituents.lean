module

public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Residuals
public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.SubspaceQuotient
public import Theory.Representation.Quotient
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic
/-!
# Constituents of the binary affine point residual

For the actual affine subgroup `pointA` of SL₃(2), coordinate projection gives
the natural flag with a fixed point and irreducible plane quotient. The
inverse-transpose action has the annihilator plane and a central scalar
quotient. The alternating pairing in dimension two supplies the intertwiner;
translation coordinates identify the radical with this same irreducible plane.
The action descends to the literal quotient `pointA / O₂(pointA)`.

All finite checks involve only binary two-vectors and one fixed cubic matrix.
Coordinatewise flags, exact quotient maps and their dimensions include zero
multiplicity. No direct-sum decomposition of either three-space is asserted.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.2.5(8),
printed pp.335–336; 12.8.8, printed pp.851–852.
-/

@[expose] public section
set_option linter.unusedSimpArgs false
open Matrix Subgroup Representation
namespace Matrix.PSL3Two.MarkedAutomorphisms.AffineConstituents
abbrev K := ZMod 2
abbrev V := Fin 3 → K
abbrev W := Fin 2 → K
abbrev natural : Representation K pointA V := (specialLinearNatural 3).comp pointA.subtype

def tail : V →ₗ[K] W where
  toFun v := ![v 1, v 2]
  map_add' _ _ := by ext i; fin_cases i <;> simp
  map_smul' _ _ := by ext i; fin_cases i <;> simp

def insert : W →ₗ[K] V where
  toFun v := ![0, v 0, v 1]
  map_add' _ _ := by ext i; fin_cases i <;> simp
  map_smul' _ _ := by ext i; fin_cases i <;> simp

def first : V →ₗ[K] K := LinearMap.proj 0

@[simp] theorem tail_insert (v : W) : tail (insert v) = v := by ext i; fin_cases i <;> rfl

theorem tail_surjective : Function.Surjective tail := fun v => ⟨insert v, tail_insert v⟩

theorem entry00 (a : pointA) : a.val.val 0 0 = 1 := by
  have hd := a.val.property
  have ha := a.property
  change pointResidualPred a.val at ha
  rcases ha with ⟨h10, h20, h | h | h⟩ <;>
    rcases h with ⟨h11, h12, h21, h22⟩ <;>
    simpa only [Matrix.det_fin_three, h10, h20, h11, h12, h21, h22, mul_zero, zero_mul, mul_one, one_mul, sub_zero, zero_sub, add_zero, zero_add, CharTwo.neg_eq, add_comm] using hd

def block (a : pointA) : W →ₗ[K] W :=
  tail ∘ₗ natural a ∘ₗ insert

theorem tail_natural (a : pointA) (v : V) : tail (natural a v) = block a (tail v) := by
  have h10 := a.property.1
  have h20 := a.property.2.1
  ext i
  fin_cases i <;> simp [tail, natural, specialLinearNatural_apply, block, LinearMap.comp_apply, insert, mulVec, dotProduct,
    Fin.sum_univ_three, Fin.sum_univ_two, h10, h20]

def planeAction : Representation K pointA W where
  toFun := block
  map_one' := by
    apply LinearMap.ext
    intro v
    ext i
    fin_cases i <;> simp [block, LinearMap.comp_apply, insert, tail, natural, specialLinearNatural_apply, mulVec, dotProduct, Fin.sum_univ_two]
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    obtain ⟨u, rfl⟩ := tail_surjective v
    change block (a*b) (tail u) = block a (block b (tail u))
    rw [← tail_natural, ← tail_natural, ← tail_natural]
    exact congrArg tail (congrArg (fun f : Module.End K V => f u) (natural.map_mul a b))

def swap : W ≃ₗ[K] W where
  toFun v := ![v 1, v 0]
  invFun v := ![v 1, v 0]
  left_inv v := by ext i; fin_cases i <;> rfl
  right_inv v := by ext i; fin_cases i <;> rfl
  map_add' _ _ := by ext i; fin_cases i <;> simp
  map_smul' _ _ := by ext i; fin_cases i <;> simp

def dual : Representation K pointA V :=
  (specialLinearNatural 3).comp (inverseTranspose.toMonoidHom.comp pointA.subtype)

theorem inverseTranspose_val (g : SL) : (inverseTranspose g).val = g⁻¹.val.transpose := by
  change (SpecialLinearGroup.transpose g)⁻¹.val = _
  rw [SpecialLinearGroup.coe_inv, SpecialLinearGroup.coe_inv]
  exact (Matrix.adjugate_transpose g.val).symm

theorem dual_apply (a : pointA) (v : V) : dual a v = a.val⁻¹.val.transpose *ᵥ v := by
  change (inverseTranspose a.val).val *ᵥ v = _
  rw [inverseTranspose_val]

theorem first_dual (a : pointA) (v : V) : first (dual a v) = first v := by
  rw [dual_apply]
  have h10 := a⁻¹.property.1
  have h20 := a⁻¹.property.2.1
  have h00 := entry00 a⁻¹
  change _ = v 0
  simp only [first, LinearMap.proj_apply, mulVec, dotProduct, Fin.sum_univ_three, transpose_apply]
  change a.val⁻¹.val 0 0 = 1 at h00
  change a.val⁻¹.val 1 0 = 0 at h10
  change a.val⁻¹.val 2 0 = 0 at h20
  rw [h00, h10, h20]
  simp

theorem dual_insert_swap (a : pointA) (v : W) :
    dual a (insert (swap v)) = insert (swap (planeAction a v)) := by
  rw [dual_apply, SpecialLinearGroup.coe_inv, adjugate_fin_three]
  have h10 := a.property.1
  have h20 := a.property.2.1
  have h00 := entry00 a
  ext i
  fin_cases i <;>
    simp [insert, swap, planeAction, block, LinearMap.comp_apply, tail, natural, specialLinearNatural_apply, mulVec, dotProduct, Fin.sum_univ_three,
      Fin.sum_univ_two, transpose_apply, h10, h20, h00, CharTwo.neg_eq, add_comm]

def point : Subrepresentation natural where
  toSubmodule := tail.ker
  apply_mem_toSubmodule a v hv := by
    change tail (natural a v) = 0
    rw [tail_natural, show tail v = 0 from hv, map_zero]

def annihilator : Subrepresentation dual where
  toSubmodule := first.ker
  apply_mem_toSubmodule a v hv := by
    change first (dual a v) = 0
    rw [first_dual]
    exact hv

theorem mem_point (v : V) : v ∈ point ↔ v 1 = 0 ∧ v 2 = 0 := by
  change tail v = 0 ↔ _
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨h1,h2⟩
    ext i
    fin_cases i <;> simp [tail,h1,h2]

theorem point_fixed (a : pointA) (v : V) (hv : v ∈ point) : natural a v = v := by
  obtain ⟨h1,h2⟩ := (mem_point v).mp hv
  have h10 := a.property.1
  have h20 := a.property.2.1
  have h00 := entry00 a
  ext i
  fin_cases i <;>
    simp [natural, specialLinearNatural_apply, mulVec, dotProduct, Fin.sum_univ_three,
      h1,h2,h10,h20,h00]

def pointEquiv : point.toSubmodule ≃ₗ[K] K where
  toFun v := v.val 0
  invFun t := ⟨![t,0,0], (mem_point _).mpr (by simp)⟩
  left_inv v := by
    apply Subtype.ext
    obtain ⟨h1,h2⟩ := (mem_point v.val).mp v.property
    ext i
    fin_cases i <;> simp [h1,h2]
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def naturalQuotientEquiv : (V ⧸ point.toSubmodule) ≃ₗ[K] W :=
  tail.quotKerEquivOfSurjective tail_surjective

theorem naturalQuotientEquiv_mk (v : V) :
    naturalQuotientEquiv (point.toSubmodule.mkQ v) = tail v := rfl

def dualPlaneEquiv : W ≃ₗ[K] annihilator.toSubmodule where
  toFun v := ⟨insert (swap v), rfl⟩
  invFun v := swap (tail v.val)
  left_inv v := by simp [swap, tail, insert]; ext i; fin_cases i <;> rfl
  right_inv v := by
    apply Subtype.ext
    have hv : v.val 0 = 0 := v.property
    ext i
    fin_cases i <;> simp [swap,tail,insert,hv]
  map_add' x y := by apply Subtype.ext; exact map_add (insert.comp swap.toLinearMap) x y
  map_smul' x y := by apply Subtype.ext; exact map_smul (insert.comp swap.toLinearMap) x y

theorem first_surjective : Function.Surjective first := fun t => ⟨![t,0,0], rfl⟩

noncomputable def dualQuotientEquiv : (V ⧸ annihilator.toSubmodule) ≃ₗ[K] K :=
  first.quotKerEquivOfSurjective first_surjective

theorem dualQuotientEquiv_mk (v : V) :
    dualQuotientEquiv (annihilator.toSubmodule.mkQ v) = first v := rfl

noncomputable def naturalQuotientRepEquiv :
    point.quotientRepresentation.Equiv planeAction :=
  .mk naturalQuotientEquiv (fun a => by
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | _ v => exact tail_natural a v)

def dualPlaneRepEquiv : planeAction.Equiv annihilator.toRepresentation :=
  .mk dualPlaneEquiv (fun a => by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact (dual_insert_swap a v).symm)

def pointRepEquiv : point.toRepresentation.Equiv (trivial K pointA K) :=
  .mk pointEquiv (fun a => by
    apply LinearMap.ext
    intro v
    exact congrFun (point_fixed a v.val v.property) 0)

noncomputable def dualQuotientRepEquiv :
    annihilator.quotientRepresentation.Equiv (trivial K pointA K) :=
  .mk dualQuotientEquiv (fun a => by
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | _ v => exact first_dual a v)

private theorem cubic_span : ∀ x y : W, x ≠ 0 →
    y = 0 ∨ y = x ∨ y = planeAction ⟨cubic,cubic_mem⟩ x ∨
      y = x + planeAction ⟨cubic,cubic_mem⟩ x := by decide +kernel

theorem planeAction_irreducible : IsIrreducible planeAction := by
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, ?_⟩
  intro P
  by_cases hp : P.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hp)
  · right
    obtain ⟨x,hx,hx0⟩ := P.toSubmodule.ne_bot_iff.mp hp
    apply top_unique
    intro y _
    rcases cubic_span x y hx0 with rfl | rfl | rfl | rfl
    · exact P.toSubmodule.zero_mem
    · exact hx
    · exact P.apply_mem_toSubmodule _ hx
    · exact P.toSubmodule.add_mem hx (P.apply_mem_toSubmodule _ hx)

theorem planeAction_nontrivial : planeAction ⟨cubic,cubic_mem⟩ ![1,0] ≠ ![1,0] := by
  decide +kernel

theorem core_le_kernel : pCore 2 pointA ≤ planeAction.ker := by
  intro a ha
  have hv : a.val ∈ pointV := by
    rw [← point_core]
    exact ⟨a,ha,rfl⟩
  rcases hv with ⟨h00,h10,h20,h11,h12,h21,h22⟩
  apply LinearMap.ext
  intro v
  ext i
  fin_cases i <;>
    simp [planeAction,block,tail,insert,natural,specialLinearNatural_apply,
      mulVec,dotProduct,Fin.sum_univ_three,h11,h12,h21,h22]

/-- The action on the literal quotient of the affine group by its two-core. -/
def cubicAction : Representation K (pointA ⧸ pCore 2 pointA) W :=
  planeAction.quotientOfLEKer (pCore 2 pointA) core_le_kernel

@[simp] theorem cubicAction_mk (a : pointA) :
    cubicAction (QuotientGroup.mk' (pCore 2 pointA) a) = planeAction a := rfl

theorem cubicAction_irreducible : IsIrreducible cubicAction :=
  (quotientOfLEKer_irreducible_iff _ _ _).mpr planeAction_irreducible

theorem dimensions : Module.finrank K point.toSubmodule = 1 ∧
    Module.finrank K (V ⧸ point.toSubmodule) = 2 ∧
    Module.finrank K annihilator.toSubmodule = 2 ∧
    Module.finrank K (V ⧸ annihilator.toSubmodule) = 1 := by
  rw [pointEquiv.finrank_eq, naturalQuotientEquiv.finrank_eq,
    ← dualPlaneEquiv.finrank_eq, dualQuotientEquiv.finrank_eq]
  simp [W, K, Module.finrank_self]

/-- Translation coordinates, with the symplectic swap built in. -/
def radicalEquiv : pointV ≃* Multiplicative W where
  toFun t := Multiplicative.ofAdd ![t.val.val 0 2, t.val.val 0 1]
  invFun v := ⟨⟨!![1,v.toAdd 1,v.toAdd 0; 0,1,0; 0,0,1], by simp [det_fin_three]⟩,
    by exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩
  left_inv t := by
    apply Subtype.ext
    apply Subtype.ext
    rcases t.property with ⟨h00,h10,h20,h11,h12,h21,h22⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00,h10,h20,h11,h12,h21,h22]
  right_inv v := by
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> rfl
  map_mul' t u := by
    apply Multiplicative.toAdd.injective
    rcases t.property with ⟨h00,h10,h20,h11,h12,h21,h22⟩
    rcases u.property with ⟨k00,k10,k20,k11,k12,k21,k22⟩
    ext i
    fin_cases i <;>
      simp [SpecialLinearGroup.coe_mul,mul_apply,Fin.sum_univ_three,
        h00,h10,h20,h11,h12,h21,h22,k00,k10,k20,k11,k12,k21,k22,add_comm]

/-- Actual matrix conjugation on the translation radical. -/
def radicalConj (a : pointA) (t : pointV) : pointV :=
  ⟨a.val * t.val * a.val⁻¹, pointV_conj a.val a.property t.val t.property⟩

theorem radical_equivariant (a : pointA) (t : pointV) :
    (radicalEquiv (radicalConj a t)).toAdd = planeAction a (radicalEquiv t).toAdd := by
  have h00 := entry00 a
  rcases a.property with ⟨h10,h20,h | h | h⟩ <;>
    rcases h with ⟨h11,h12,h21,h22⟩ <;>
    rcases t.property with ⟨k00,k10,k20,k11,k12,k21,k22⟩ <;>
    ext i <;> fin_cases i <;>
    simp [radicalEquiv,radicalConj,SpecialLinearGroup.coe_mul,SpecialLinearGroup.coe_inv,
      adjugate_fin_three,mul_apply,Fin.sum_univ_three,
      planeAction,block,tail,insert,natural,specialLinearNatural_apply,mulVec,dotProduct,
      h00,h10,h20,h11,h12,h21,h22,k00,k10,k20,k11,k12,k21,k22,CharTwo.neg_eq] <;> ring_nf <;> simp [show (2 : K) = 0 from rfl]

/-- The radical has no proper nontrivial invariant additive subgroup. Over F₂
these are exactly its submodules. -/
theorem radical_irreducible (N : Subgroup pointV)
    (hN : ∀ a t, t ∈ N → radicalConj a t ∈ N) : N = ⊥ ∨ N = ⊤ := by
  by_cases hn : N = ⊥
  · exact Or.inl hn
  · right
    obtain ⟨u,hu⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hn
    let t : pointV := u
    have ht : t ∈ N := u.property
    have ht1 : t ≠ 1 := fun he => hu (Subtype.ext he)
    have ht0 : (radicalEquiv t).toAdd ≠ 0 := by
      intro he
      apply ht1
      apply radicalEquiv.injective
      rw [map_one]
      exact he
    apply top_unique
    intro u _
    rcases cubic_span (radicalEquiv t).toAdd (radicalEquiv u).toAdd ht0 with h | h | h | h
    · have hu : u = 1 := by
        apply radicalEquiv.injective
        rw [map_one]
        exact h
      rw [hu]
      exact N.one_mem
    · have hu : u = t := radicalEquiv.injective h
      simpa [hu] using ht
    · have hu : u = radicalConj ⟨cubic,cubic_mem⟩ t :=
        radicalEquiv.injective (h.trans (radical_equivariant _ _).symm)
      rw [hu]
      exact hN _ _ ht
    · have hu : u = t * radicalConj ⟨cubic,cubic_mem⟩ t := by
        apply radicalEquiv.injective
        change (radicalEquiv u).toAdd = (radicalEquiv (t * radicalConj _ t)).toAdd
        rw [map_mul]
        change (radicalEquiv u).toAdd = (radicalEquiv t).toAdd +
          (radicalEquiv (radicalConj _ t)).toAdd
        rw [radical_equivariant]
        exact h
      rw [hu]
      exact N.mul_mem ht (hN _ _ ht)

-- Coordinatewise versions; no positivity assumption on the multiplicity.
def tailCopies (k : ℕ) : (Fin k → V) →ₗ[K] (Fin k → W) :=
  LinearMap.pi fun i => tail.comp (LinearMap.proj i)

def firstCopies (k : ℕ) : (Fin k → V) →ₗ[K] (Fin k → K) :=
  LinearMap.pi fun i => first.comp (LinearMap.proj i)

theorem tailCopies_surjective (k : ℕ) : Function.Surjective (tailCopies k) := by
  intro v
  exact ⟨fun i => insert (v i), funext (fun i => tail_insert (v i))⟩

theorem firstCopies_surjective (k : ℕ) : Function.Surjective (firstCopies k) := by
  intro v
  exact ⟨fun i => ![v i,0,0], rfl⟩

def pointCopiesEquiv (k : ℕ) : (tailCopies k).ker ≃ₗ[K] (Fin k → K) where
  toFun v i := v.val i 0
  invFun v := ⟨fun i => ![v i,0,0], by ext i j; fin_cases j <;> rfl⟩
  left_inv v := by
    apply Subtype.ext
    have hv (i : Fin k) : tail (v.val i) = 0 := congrFun v.property i
    ext i j
    have h1 := congrFun (hv i) 0
    have h2 := congrFun (hv i) 1
    fin_cases j <;> simp_all [tail]
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def dualPlaneCopiesEquiv (k : ℕ) : (Fin k → W) ≃ₗ[K] (firstCopies k).ker where
  toFun v := ⟨fun i => insert (swap (v i)), rfl⟩
  invFun v i := swap (tail (v.val i))
  left_inv v := by ext i j; fin_cases j <;> rfl
  right_inv v := by
    apply Subtype.ext
    have hv (i : Fin k) : v.val i 0 = 0 := congrFun v.property i
    ext i j
    fin_cases j <;> simp [swap,tail,insert,hv]
  map_add' x y := by apply Subtype.ext; funext i; exact map_add (insert.comp swap.toLinearMap) _ _
  map_smul' x y := by apply Subtype.ext; funext i; exact map_smul (insert.comp swap.toLinearMap) _ _

noncomputable def naturalCopiesQuotientEquiv (k : ℕ) :
    ((Fin k → V) ⧸ (tailCopies k).ker) ≃ₗ[K] (Fin k → W) :=
  (tailCopies k).quotKerEquivOfSurjective (tailCopies_surjective k)

noncomputable def dualCopiesQuotientEquiv (k : ℕ) :
    ((Fin k → V) ⧸ (firstCopies k).ker) ≃ₗ[K] (Fin k → K) :=
  (firstCopies k).quotKerEquivOfSurjective (firstCopies_surjective k)

theorem copies_dimensions (k : ℕ) :
    Module.finrank K (tailCopies k).ker = k ∧
    Module.finrank K ((Fin k → V) ⧸ (tailCopies k).ker) = 2*k ∧
    Module.finrank K (firstCopies k).ker = 2*k ∧
    Module.finrank K ((Fin k → V) ⧸ (firstCopies k).ker) = k := by
  rw [(pointCopiesEquiv k).finrank_eq, (naturalCopiesQuotientEquiv k).finrank_eq,
    ← (dualPlaneCopiesEquiv k).finrank_eq, (dualCopiesQuotientEquiv k).finrank_eq]
  simp [W,K,Module.finrank_pi,Module.finrank_pi_fintype,mul_comm]

/-- Pullback of the invariant natural flag along any actual actor map. -/
def copies {E : Type*} [AddCommGroup E] [Module K E]
    (ρ : Representation K pointA E) (k : ℕ) : Representation K pointA (Fin k → E) where
  toFun a := LinearMap.pi fun i => (ρ a).comp (LinearMap.proj i)
  map_one' := by apply LinearMap.ext; intro v; ext i; exact congrArg (fun f => f (v i)) ρ.map_one
  map_mul' a b := by apply LinearMap.ext; intro v; ext i; exact congrArg (fun f => f (v i)) (ρ.map_mul a b)

variable {H : Type*} [Group H] (π : H →* pointA)

def naturalFlag (k : ℕ) : Subrepresentation ((copies natural k).comp π) where
  toSubmodule := (tailCopies k).ker
  apply_mem_toSubmodule a v hv := by
    change tailCopies k _ = 0
    funext i
    change tail (natural (π a) (v i)) = 0
    rw [tail_natural, show tail (v i) = 0 from congrFun hv i, map_zero]

def dualFlag (k : ℕ) : Subrepresentation ((copies dual k).comp π) where
  toSubmodule := (firstCopies k).ker
  apply_mem_toSubmodule a v hv := by
    ext i
    change first (dual (π a) (v i)) = 0
    rw [first_dual]
    exact congrFun hv i

theorem naturalFlag_fixed (k : ℕ) (a : H) (v : (naturalFlag π k).toSubmodule) :
    (copies natural k).comp π a v.val = v.val := by
  funext i
  exact point_fixed (π a) (v.val i) (congrFun v.property i)

theorem dualFlag_central_quotient (k : ℕ) (a : H) (v : Fin k → V) :
    firstCopies k ((copies dual k).comp π a v) = firstCopies k v := by
  ext i
  exact first_dual (π a) (v i)

/-- Each surviving two-space is acted on through the specified core quotient. -/
def constituent : Representation K H W :=
  cubicAction.comp ((QuotientGroup.mk' (pCore 2 pointA)).comp π)

theorem constituent_irreducible (hπ : Function.Surjective π) :
    IsIrreducible (constituent π) :=
  (irreducible_comp_surjective_iff π hπ planeAction).mpr planeAction_irreducible

theorem naturalFlag_quotient_map (k : ℕ) (a : H) (v : Fin k → V) (i : Fin k) :
    tailCopies k ((copies natural k).comp π a v) i = constituent π a (tailCopies k v i) :=
  tail_natural (π a) (v i)

theorem dualFlag_intertwines (k : ℕ) (a : H) (v : Fin k → W) :
    ((copies dual k).comp π a (dualPlaneCopiesEquiv k v).val) =
      (dualPlaneCopiesEquiv k (fun i => constituent π a (v i))).val := by
  funext i
  exact dual_insert_swap (π a) (v i)

/-- The dual flag is literally the annihilator of the fixed point. -/
theorem annihilator_iff (v : V) :
    v ∈ annihilator ↔ ∀ w ∈ point, dotProduct w v = 0 := by
  change v 0 = 0 ↔ _
  constructor
  · intro hv w hw
    obtain ⟨h1,h2⟩ := (mem_point w).mp hw
    simp [dotProduct,Fin.sum_univ_three,hv,h1,h2]
  · intro h
    simpa [dotProduct,Fin.sum_univ_three] using h ![1,0,0] ((mem_point _).mpr (by simp))

noncomputable def naturalDualConstituentEquiv :
    point.quotientRepresentation.Equiv annihilator.toRepresentation :=
  naturalQuotientRepEquiv.trans dualPlaneRepEquiv

/-- The group form of the same linear equivalence identifies the actual
translation matrices, not just an abstract group of order four. -/
noncomputable def naturalRadicalEquiv :
    Multiplicative (V ⧸ point.toSubmodule) ≃* pointV :=
  naturalQuotientEquiv.toAddEquiv.toMultiplicative.trans radicalEquiv.symm

/-- Transport a linear kernel through specified multiplicative coordinates. -/
def kernelCoordinates {A M N : Type*} [Group A]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (e : A ≃* Multiplicative M) (f : M →ₗ[K] N) :
    (f.toAddMonoidHom.toMultiplicative.comp e.toMonoidHom).ker ≃* Multiplicative f.ker where
  toFun x := Multiplicative.ofAdd ⟨(e x.val).toAdd, x.property⟩
  invFun x := ⟨e.symm (Multiplicative.ofAdd x.toAdd.val), by
    change f (e (e.symm (Multiplicative.ofAdd x.toAdd.val))).toAdd = 0
    rw [e.apply_symm_apply]
    exact x.toAdd.property⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.val
  right_inv x := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (e.apply_symm_apply _)
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (e.map_mul x.val y.val)

private theorem irreducible_of_equiv {M N : Type*}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    {ρ : Representation K pointA M} {σ : Representation K pointA N}
    (e : ρ.Equiv σ) (hσ : Representation.IsIrreducible σ) :
    Representation.IsIrreducible ρ := by
  let f := IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap
  let ef := LinearEquiv.ofBijective f (show Function.Bijective f from e.toLinearEquiv.bijective)
  rw [irreducible_iff_isSimpleModule_asModule]
  exact ef.isSimpleModule_iff.mpr ((irreducible_iff_isSimpleModule_asModule σ).mp hσ)

theorem naturalQuotient_irreducible : Representation.IsIrreducible point.quotientRepresentation :=
  irreducible_of_equiv naturalQuotientRepEquiv planeAction_irreducible

theorem dualPlane_irreducible : Representation.IsIrreducible annihilator.toRepresentation :=
  irreducible_of_equiv dualPlaneRepEquiv.symm planeAction_irreducible

theorem naturalRadicalEquiv_intertwines (a : pointA) (v : V ⧸ point.toSubmodule) :
    naturalRadicalEquiv (Multiplicative.ofAdd (point.quotientRepresentation a v)) =
      radicalConj a (naturalRadicalEquiv (Multiplicative.ofAdd v)) := by
  have hcoords (w : V ⧸ point.toSubmodule) :
      (radicalEquiv (naturalRadicalEquiv (Multiplicative.ofAdd w))).toAdd =
        naturalQuotientEquiv w :=
    congrArg Multiplicative.toAdd (radicalEquiv.apply_symm_apply _)
  apply radicalEquiv.injective
  apply Multiplicative.toAdd.injective
  rw [hcoords, radical_equivariant, hcoords]
  exact congrArg (fun f : (V ⧸ point.toSubmodule) →ₗ[K] W => f v)
    (naturalQuotientRepEquiv.isIntertwining' a)

end Matrix.PSL3Two.MarkedAutomorphisms.AffineConstituents
