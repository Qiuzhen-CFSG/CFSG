module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Construction

/-!
# Two concrete linear-five subgroups in the octad pullback

Conjugating the native F by the kernel seed gives a distinct elementary subgroup
of order 1024 in Q. The sixteen quotient coordinates and their checked kernel
actions show that the intersection is exactly F ∩ E, of order 64. This proves
existence and the intersection clause of Kleidman--Wilson (1988), Lemma 1.1.2(ii),
p.485. Exhaustiveness among all global conjugates in D is a further assertion.

The calculation uses eleven-bit actions, with no new dense matrix certificates.
-/

@[expose] public noncomputable section
namespace Janko4.LocalStructure.LinearFive.Geometry
open Cardinality KernelCount QuotientCount.Image Subgroup
open Simplicity.Max1Fusion.KernelOrbits
open scoped IsMulCommutative
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
  localX localY localKernelSeed basis lift

private theorem product_split {G : Type*} [Monoid G] {n m : ℕ}
    (a : Fin n → G) (b : Fin m → G) (v : Fin (n+m) → Bool) :
    binaryProduct (Fin.append a b) v =
      binaryProduct a (fun i => v (Fin.castAdd m i)) *
        binaryProduct b (fun i => v (Fin.natAdd n i)) := by
  simp only [binaryProduct, List.ofFn_add, List.prod_append, Fin.append_left', Fin.append_right]
  rfl

def liftProduct (v : Fin 4 → Bool) : M := binaryProduct lift v

theorem lift_mem_localF (i : Fin 4) : lift i ∈ localF := by
  simpa only [generators, Fin.append_right] using generator_mem_localF (Fin.natAdd 6 i)

theorem localF_commute (f : M) (hf : f ∈ localF) (g : M) (hg : g ∈ localF) :
    Commute f g := by
  let _ := localF_elementary
  exact congrArg (fun a : localF => (a : M)) (mul_comm (⟨f,hf⟩ : localF) ⟨g,hg⟩)

theorem liftProduct_mem (v : Fin 4 → Bool) : liftProduct v ∈ localF :=
  binaryProduct_mem lift v localF lift_mem_localF

theorem localF_decomposition (f : M) (hf : f ∈ localF) :
    ∃ e : M, e ∈ localKernel matrixA_mul_self matrixB_pow_four ∧
      ∃ v : Fin 4 → Bool, f = e * liftProduct v := by
  obtain ⟨v,rfl⟩ := (mem_closure_iff_binaryProduct generators generators_square
    generators_commute f).mp hf
  refine ⟨binaryProduct kernelGenerator (fun i => v (Fin.castAdd 4 i)), ?_,
    (fun i => v (Fin.natAdd 6 i)), ?_⟩
  · apply binaryProduct_mem
    intro i
    exact (maskValue matrixA_mul_self matrixB_pow_four (kernelMasks i)).property
  · exact product_split kernelGenerator lift v

def actionProduct : {n : ℕ} → (Fin n → ℕ → ℕ) → (Fin n → Bool) → ℕ → ℕ
  | 0, _, _, m => m
  | _n+1, a, v, m => actionProduct (fun i => a i.succ) (fun i => v i.succ)
      (if v 0 then a 0 m else m)

private theorem conjugate_binaryProduct {G : Type*} [Group G] (e : ℕ → G)
    {n : ℕ} (g : Fin n → G) (a : Fin n → ℕ → ℕ)
    (h : ∀ i m, (g i)⁻¹ * e m * g i = e (a i m)) (v : Fin n → Bool) (m : ℕ) :
    (binaryProduct g v)⁻¹ * e m * binaryProduct g v = e (actionProduct a v m) := by
  induction n generalizing m with
  | zero => simp [binaryProduct, actionProduct]
  | succ n ih =>
    rw [binaryProduct_succ]
    have he : ((if v 0 then g 0 else 1) * binaryProduct (fun i => g i.succ) (fun i => v i.succ))⁻¹ *
        e m * ((if v 0 then g 0 else 1) * binaryProduct (fun i => g i.succ) (fun i => v i.succ)) =
        (binaryProduct (fun i => g i.succ) (fun i => v i.succ))⁻¹ *
          ((if v 0 then g 0 else 1)⁻¹ * e m * (if v 0 then g 0 else 1)) *
          binaryProduct (fun i => g i.succ) (fun i => v i.succ) := by group
    rw [he]
    cases hv : v 0
    · simp only [hv, Bool.false_eq_true, ↓reduceIte, inv_one, one_mul, mul_one, actionProduct]
      exact ih _ _ (fun i => h i.succ) _ _
    · simp only [hv, ↓reduceIte, h, actionProduct]
      exact ih _ _ (fun i => h i.succ) _ _

def liftAction (v : Fin 4 → Bool) (m : ℕ) : ℕ :=
  actionProduct (fun i => maskImage (liftKernelMasks i)) v m

theorem liftProduct_conjugates_kernel (v : Fin 4 → Bool) (m : ℕ) :
    (liftProduct v)⁻¹ * kernelValue m * liftProduct v = kernelValue (liftAction v m) :=
  conjugate_binaryProduct kernelValue lift _ lift_conjugates_kernel v m

/-- No nonidentity quotient coordinate has seed displacement fixed by all four lifts. -/
theorem seed_displacement_detects (v : Fin 4 → Bool)
    (h : ∀ i : Fin 4, maskImage (liftKernelMasks i) (Nat.xor (liftAction v 1) 1) =
      Nat.xor (liftAction v 1) 1) : v = fun _ => false := by
  have hc : ∀ v : Fin 4 → Bool,
      (∀ i : Fin 4, maskImage (liftKernelMasks i) (Nat.xor (liftAction v 1) 1) =
        Nat.xor (liftAction v 1) 1) → v = fun _ => false := by decide +kernel
  exact hc v h

theorem seed_displacement_bounds (v : Fin 4 → Bool) (i : Fin 4) :
    Nat.xor (liftAction v 1) 1 < 2048 ∧
      maskImage (liftKernelMasks i) (Nat.xor (liftAction v 1) 1) < 2048 := by
  have hc : ∀ (v : Fin 4 → Bool) (i : Fin 4),
    Nat.xor (liftAction v 1) 1 < 2048 ∧
      maskImage (liftKernelMasks i) (Nat.xor (liftAction v 1) 1) < 2048 := by decide +kernel
  exact hc v i



/-- The kernel seed which exchanges the two constructed elementary groups. -/
def seed : Model := kernelValue 1

/-- A literal second global conjugate, still lying in Q. -/
def secondF : Subgroup Model := F.map (MulAut.conj seed).toMonoidHom

theorem kernel_commute (e : M) (he : e ∈ localKernel matrixA_mul_self matrixB_pow_four)
    (m : ℕ) : Commute e (kernelValue m) := by
  let _ := localKernel_elementary matrixA_mul_self matrixB_pow_four
  exact congrArg (fun a : localKernel matrixA_mul_self matrixB_pow_four => (a : M))
    (mul_comm (⟨e,he⟩ : localKernel matrixA_mul_self matrixB_pow_four)
      (maskValue matrixA_mul_self matrixB_pow_four m))

/-- The seed preserves an element of F precisely on the kernel intersection. -/
theorem seed_conjugate_mem_localF_iff (f : M) (hf : f ∈ localF) :
    kernelValue 1 * f * (kernelValue 1)⁻¹ ∈ localF ↔
      f ∈ localKernel matrixA_mul_self matrixB_pow_four := by
  constructor
  · intro hc
    obtain ⟨e,he,v,rfl⟩ := localF_decomposition f hf
    have hd : kernelValue (Nat.xor (liftAction v 1) 1) ∈ localF := by
      have hh := localF.mul_mem (localF.inv_mem hf) hc
      have heq : (e * liftProduct v)⁻¹ * (kernelValue 1 * (e * liftProduct v) * (kernelValue 1)⁻¹) =
          (liftProduct v)⁻¹ * ((e⁻¹ * kernelValue 1) * e) * liftProduct v * (kernelValue 1)⁻¹ := by group
      rw [heq, mul_assoc e⁻¹, ← (kernel_commute e he 1).eq, inv_mul_cancel_left,
        liftProduct_conjugates_kernel] at hh
      have hinv : (kernelValue 1)⁻¹ = kernelValue 1 :=
        inv_eq_of_mul_eq_one_right (kernelValue_square 1)
      rw [hinv, ← kernelValue_xor] at hh
      exact hh
    have hv : v = fun _ => false := by
      apply seed_displacement_detects
      intro i
      have hh := (localF_commute _ hd (lift i) (lift_mem_localF i)).eq
      apply kernelValue_injective (seed_displacement_bounds v i).2
        (seed_displacement_bounds v i).1
      rw [← lift_conjugates_kernel, mul_assoc, hh, inv_mul_cancel_left]
    simpa only [hv, liftProduct, binaryProduct_zero, mul_one] using he
  · intro he
    simpa only [← mul_assoc, (kernel_commute f he 1).symm.eq, mul_assoc,
      mul_inv_cancel, mul_one] using hf

theorem seed_mem_E : seed ∈ E := kernelValue_mem_E 1

theorem seed_square : seed * seed = 1 :=
  congrArg (fun x : M => (x : Model)) (kernelValue_square 1)

theorem secondF_le_Q : secondF ≤ Q := by
  rintro x ⟨f,hf,rfl⟩
  exact Q.mul_mem (Q.mul_mem (Q_contains_E seed_mem_E) (F_le_Q hf))
    (Q.inv_mem (Q_contains_E seed_mem_E))

theorem secondF_elementary : IsElementaryAbelian 2 secondF := by
  let _ := F_elementary
  exact IsElementaryAbelian.map _

theorem secondF_card : Nat.card secondF = 1024 := by
  rw [secondF, Subgroup.card_map_of_injective (MulAut.conj seed).injective, F_card]

/-- The literal intersection of the two global conjugates is F ∩ E. -/
theorem intersection_eq : F ⊓ secondF = F ⊓ E := by
  apply le_antisymm
  · rintro x ⟨hx,hx2⟩
    obtain ⟨f,hf,rfl⟩ := mem_map.mp hx2
    obtain ⟨z,hz,rfl⟩ := mem_map.mp hf
    have hconj : kernelValue 1 * z * (kernelValue 1)⁻¹ ∈ localF := by
      obtain ⟨w,hw,he⟩ := mem_map.mp hx
      have he' : w = kernelValue 1 * z * (kernelValue 1)⁻¹ := Subtype.ext he
      exact he' ▸ hw
    have hzK := (seed_conjugate_mem_localF_iff z hz).mp hconj
    refine ⟨hx,mem_map.mpr ⟨z,hzK,?_⟩⟩
    change (z : Model) = seed * (z : Model) * seed⁻¹
    have hcomm := congrArg (fun a : M => (a : Model)) (kernel_commute z hzK 1).eq
    change (z : Model) * seed = seed * (z : Model) at hcomm
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  · rintro x ⟨hx,he⟩
    refine ⟨hx,mem_map.mpr ⟨x,hx,?_⟩⟩
    obtain ⟨z,hz,rfl⟩ := mem_map.mp he
    have hcomm := congrArg (fun a : M => (a : Model)) (kernel_commute z hz 1).eq
    change (z : Model) * seed = seed * (z : Model) at hcomm
    change seed * (z : Model) * seed⁻¹ = (z : Model)
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]

theorem intersection_card : Nat.card (F ⊓ secondF : Subgroup Model) = 64 := by
  rw [intersection_eq, F_inf_E_card]

theorem intersection_le_E : F ⊓ secondF ≤ E := by
  rw [intersection_eq]
  exact inf_le_right

theorem secondF_ne : F ≠ secondF := by
  intro he
  have hh := intersection_card
  rw [← he, inf_idem, F_card] at hh
  omega

end Janko4.LocalStructure.LinearFive.Geometry
