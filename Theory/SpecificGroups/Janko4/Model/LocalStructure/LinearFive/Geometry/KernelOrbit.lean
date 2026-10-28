module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Geometry.Pair

/-!
# Exactly two conjugates under E and Q

Eleven corrected kernel basis elements normalize the actual native F, as follows
from the checked displacement matrices and the proved common fixed kernel.
The full kernel has two cosets modulo its F-normalizer. Therefore its orbit of F
is exactly the pair constructed in `Pair`. The literal factorization Q = E F
shows that Q has the same orbit.

This supplies the kernel and Q occurrence calculation for Kleidman--Wilson
(1988), Lemma 1.1.2(ii), p.485. The assertion about all global conjugates
contained in D is stronger and is not claimed here.
-/

@[expose] public noncomputable section
namespace Janko4.LocalStructure.LinearFive.Geometry
open Cardinality KernelCount QuotientCount.Image Subgroup
open Simplicity.Max1Fusion.KernelOrbits
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
  localX localY localKernelSeed basis lift

def correctedKernelMasks : Fin 11 → ℕ := ![0,2,5,8,16,33,65,129,257,513,1025]

theorem corrected_masks_spec (j : Fin 11) :
    correctedKernelMasks j = 2^j.val ∨ correctedKernelMasks j = Nat.xor (2^j.val) 1 := by
  fin_cases j <;> decide

private theorem corrected_fixed : ∀ (j : Fin 11) (i k : Fin 4),
    maskImage (liftKernelMasks k)
      (Nat.xor (maskImage (liftKernelMasks i) (correctedKernelMasks j)) (correctedKernelMasks j)) =
        Nat.xor (maskImage (liftKernelMasks i) (correctedKernelMasks j)) (correctedKernelMasks j) := by
  decide +kernel

private theorem kernelValue_commutes_lift_of_fixed (m : ℕ) (i : Fin 4)
    (h : maskImage (liftKernelMasks i) m = m) : Commute (kernelValue m) (lift i) := by
  have hc := lift_conjugates_kernel i m
  rw [h] at hc
  change kernelValue m * lift i = lift i * kernelValue m
  calc
    _ = lift i * ((lift i)⁻¹ * kernelValue m * lift i) := by group
    _ = _ := by rw [hc]

private theorem involutive_normalizes {G : Type*} [Group G]
    (H : Subgroup G) (s : G) (hs : s*s=1)
    (h : H ≤ H.comap (MulAut.conj s).toMonoidHom) : s ∈ normalizer (H : Set G) := by
  apply mem_normalizer_iff.mpr
  intro f
  constructor
  · exact fun hf => h hf
  · intro hf
    have hh := h hf
    change s*(s*f*s⁻¹)*s⁻¹ ∈ H at hh
    have he : s*(s*f*s⁻¹)*s⁻¹ = f := by
      have hi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
      rw [hi]
      calc
        _ = (s*s)*f*(s*s) := by group
        _ = _ := by rw [hs]; simp
    exact he ▸ hh

private theorem kernel_displacement_mem (m : ℕ)
    (h : ∀ i k : Fin 4,
      maskImage (liftKernelMasks k) (Nat.xor (maskImage (liftKernelMasks i) m) m) =
        Nat.xor (maskImage (liftKernelMasks i) m) m) (i : Fin 4) :
    kernelValue (Nat.xor (maskImage (liftKernelMasks i) m) m) ∈ localF := by
  apply kernel_mem_localF_of_commuting_lifts
  · exact (maskValue matrixA_mul_self matrixB_pow_four _).property
  · intro k
    exact kernelValue_commutes_lift_of_fixed _ k (h i k)

private theorem kernel_conjugate_generator_mem (m : ℕ)
    (hd : ∀ i : Fin 4, kernelValue (Nat.xor (maskImage (liftKernelMasks i) m) m) ∈ localF)
    (i : Fin 10) : kernelValue m * generators i * (kernelValue m)⁻¹ ∈ localF := by
  refine Fin.addCases (m := 6) (n := 4) ?_ ?_ i
  · intro j
    simp only [generators, Fin.append_left]
    have hc := (kernelValue_commute m (kernelMasks j)).eq
    change kernelValue m * kernelValue (kernelMasks j) * (kernelValue m)⁻¹ ∈ localF
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    simpa only [generators, Fin.append_left, kernelGenerator] using generator_mem_localF (Fin.castAdd 4 j)
  · intro j
    simp only [generators, Fin.append_right]
    have he : kernelValue m * lift j * (kernelValue m)⁻¹ =
        lift j * ((lift j)⁻¹ * kernelValue m * lift j) * (kernelValue m)⁻¹ := by group
    rw [he, lift_conjugates_kernel,
      inv_eq_of_mul_eq_one_right (kernelValue_square m), mul_assoc, ← kernelValue_xor]
    exact localF.mul_mem (lift_mem_localF j) (hd j)

private theorem localF_normalizes_of_generators (s : M) (hs : s*s=1)
    (hg : ∀ i : Fin 10, s * generators i * s⁻¹ ∈ localF) :
    s ∈ normalizer (localF : Set M) := by
  apply involutive_normalizes localF s hs
  apply (closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  exact hg i

/-- Fixed kernel displacements give actual normalization of the native F. -/
theorem kernelValue_normalizes_of_fixed (m : ℕ)
    (h : ∀ i k : Fin 4,
      maskImage (liftKernelMasks k) (Nat.xor (maskImage (liftKernelMasks i) m) m) =
        Nat.xor (maskImage (liftKernelMasks i) m) m) :
    kernelValue m ∈ normalizer (localF : Set M) :=
  localF_normalizes_of_generators (kernelValue m) (kernelValue_square m)
    (kernel_conjugate_generator_mem m (kernel_displacement_mem m h))

theorem corrected_kernel_normalizes (j : Fin 11) :
    kernelValue (correctedKernelMasks j) ∈ normalizer (localF : Set M) :=
  kernelValue_normalizes_of_fixed (correctedKernelMasks j) (corrected_fixed j)

private theorem binaryProduct_two_cosets {G : Type*} [Group G] (H : Subgroup G)
    (s : G) (hs : s * s = 1) {n : ℕ} (g : Fin n → G)
    (hc : ∀ i, Commute s (g i)) (hg : ∀ i, g i ∈ H ∨ g i * s ∈ H)
    (v : Fin n → Bool) : binaryProduct g v ∈ H ∨ binaryProduct g v * s ∈ H := by
  induction n with
  | zero => simp only [binaryProduct, List.ofFn_zero, List.prod_nil]; exact Or.inl H.one_mem
  | succ n ih =>
    rw [binaryProduct_succ]
    let a := if v 0 then g 0 else 1
    let b := binaryProduct (fun i => g i.succ) (fun i => v i.succ)
    have ha : a ∈ H ∨ a * s ∈ H := by
      dsimp only [a]
      split_ifs
      · exact hg 0
      · exact Or.inl H.one_mem
    have hb : b ∈ H ∨ b * s ∈ H := ih _ (fun i => hc i.succ) (fun i => hg i.succ) _
    have hcb : s * b = b * s := (commute_binaryProduct _ _ s (fun i => hc i.succ)).eq
    change a * b ∈ H ∨ a * b * s ∈ H
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (H.mul_mem ha hb)
    · exact Or.inr (by simpa only [mul_assoc] using H.mul_mem ha hb)
    · exact Or.inr (by simpa only [mul_assoc, hcb] using H.mul_mem ha hb)
    · left
      have he : (a*s)*(b*s) = a*b := by rw [mul_assoc, ← mul_assoc s, hcb, mul_assoc b, hs, mul_one]
      exact he ▸ H.mul_mem ha hb

/-- The entire actual kernel has only two cosets modulo its F-normalizer. -/
theorem kernel_two_cosets (z : M)
    (hz : z ∈ localKernel matrixA_mul_self matrixB_pow_four) :
    z ∈ normalizer (localF : Set M) ∨ z * kernelValue 1 ∈ normalizer (localF : Set M) := by
  obtain ⟨m,hm⟩ := maskValue_surjective matrixA_mul_self matrixB_pow_four ⟨z,hz⟩
  have hm' : kernelValue m.val = z := congrArg Subtype.val hm
  rw [← hm']
  have hg (j : Fin 11) : basis matrixA_mul_self matrixB_pow_four j ∈ normalizer (localF : Set M) ∨
      basis matrixA_mul_self matrixB_pow_four j * kernelValue 1 ∈ normalizer (localF : Set M) := by
    rw [← maskValue_basis matrixA_mul_self matrixB_pow_four j]
    rcases corrected_masks_spec j with hj | hj
    · exact Or.inl (hj ▸ corrected_kernel_normalizes j)
    · right
      have hh := corrected_kernel_normalizes j
      rw [hj, kernelValue_xor] at hh
      exact hh
  exact binaryProduct_two_cosets _ (kernelValue 1) (kernelValue_square 1)
    (basis matrixA_mul_self matrixB_pow_four)
    (fun j => by rw [← maskValue_basis matrixA_mul_self matrixB_pow_four j]; exact kernelValue_commute 1 _)
    hg (fun j => m.val.testBit j.val)



private theorem ambient_normalizes (z : M) (hz : z ∈ normalizer (localF : Set M)) :
    (z : Model) ∈ normalizer (F : Set Model) := by
  apply mem_normalizer_fintype
  rintro _ ⟨f,hf,rfl⟩
  exact mem_map.mpr ⟨z*f*z⁻¹,(mem_normalizer_iff.mp hz f).mp hf,rfl⟩

private theorem conjugate_mul (H : Subgroup Model) (a b : Model) :
    H.map (MulAut.conj (a*b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

/-- Every E-conjugate is one of the two displayed global conjugates. -/
theorem E_conjugates (z : Model) (hz : z ∈ E) :
    F.map (MulAut.conj z).toMonoidHom = F ∨
      F.map (MulAut.conj z).toMonoidHom = secondF := by
  obtain ⟨e,he,rfl⟩ := mem_map.mp hz
  rcases kernel_two_cosets e he with h | h
  · exact Or.inl (mem_normalizer_iff_map_conj_eq.mp (ambient_normalizes e h))
  · right
    have hn : F.map (MulAut.conj ((e : Model)*seed)).toMonoidHom = F :=
      mem_normalizer_iff_map_conj_eq.mp (ambient_normalizes (e * kernelValue 1) h)
    have hcomm : seed * (e : Model) = (e : Model) * seed :=
      congrArg (fun z : M => (z : Model)) (kernel_commute e he 1).symm.eq
    have heq : seed * ((e : Model)*seed) = (e : Model) := by
      rw [← mul_assoc, hcomm, mul_assoc, seed_square, mul_one]
    change F.map (MulAut.conj (e : Model)).toMonoidHom = secondF
    rw [← heq, conjugate_mul, hn]
    rfl

/-- The two kernel conjugates are attained, distinct, and contained in D. -/
theorem E_conjugates_exact :
    {H : Subgroup Model | ∃ z : Model, z ∈ E ∧ F.map (MulAut.conj z).toMonoidHom = H} =
      {F, secondF} := by
  ext H
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact (E_conjugates z hz).elim (fun h => Or.inl h) (fun h => Or.inr h)
  · rintro (rfl | rfl)
    · refine ⟨1,E.one_mem,?_⟩
      exact mem_normalizer_iff_map_conj_eq.mp (normalizer (F : Set Model)).one_mem
    · exact ⟨seed,seed_mem_E,rfl⟩

/-- Every element of Q has an actual kernel times F factorization. -/
theorem Q_factorization (q : Model) (hq : q ∈ Q) :
    ∃ e : Model, e ∈ E ∧ ∃ f : Model, f ∈ F ∧ q = e*f := by
  change q ∈ (A.comap projection).map M.subtype at hq
  obtain ⟨a,ha,rfl⟩ := mem_map.mp hq
  change projection a ∈ A at ha
  rw [← localF_image] at ha
  obtain ⟨f,hf,he⟩ := mem_map.mp ha
  have hk : a*f⁻¹ ∈ localKernel matrixA_mul_self matrixB_pow_four := by
    rw [← MathieuHallActors.projection_ker, MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
  refine ⟨a*f⁻¹,mem_map.mpr ⟨a*f⁻¹,hk,rfl⟩,f,mem_map.mpr ⟨f,hf,rfl⟩,?_⟩
  simp

/-- Q itself has precisely the same two conjugates of F. -/
theorem Q_conjugates (q : Model) (hq : q ∈ Q) :
    F.map (MulAut.conj q).toMonoidHom = F ∨
      F.map (MulAut.conj q).toMonoidHom = secondF := by
  obtain ⟨e,he,f,hf,rfl⟩ := Q_factorization q hq
  have hfn : F.map (MulAut.conj f).toMonoidHom = F :=
    mem_normalizer_iff_map_conj_eq.mp (F.le_normalizer hf)
  rw [conjugate_mul, hfn]

  exact E_conjugates e he

end Janko4.LocalStructure.LinearFive.Geometry
