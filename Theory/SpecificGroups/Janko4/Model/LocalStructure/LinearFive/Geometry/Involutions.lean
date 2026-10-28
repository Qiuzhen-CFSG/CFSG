module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Geometry.InvolutionMasks

/-!
# Square-one elements and elementary subgroups of Q

Split a Q element into a kernel mask and a literal quotient lift. Removing the
common fixed kernel leaves five bits, whose checked square equations put every
involution outside E in F or its seed conjugate. A subgroup with full octad
image centralizes only the common fixed kernel inside E; consequently an
elementary subgroup with that image lies in one member of the native pair.

Source: KW (1988), Lemma 1.1.2(ii) and the Q calculation in Proposition 2.2.2.
The intrinsic orthogonality clause of that proposition is a separate assertion.
-/
@[expose] public noncomputable section
namespace Janko4.LocalStructure.LinearFive.Geometry
open Cardinality KernelCount QuotientCount.Image Subgroup
open Simplicity.Max1Fusion.KernelOrbits
open scoped IsMulCommutative
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
  localX localY localKernelSeed basis lift

private theorem kernelValue_fold (l : List ℕ) :
    kernelValue (l.foldr Nat.xor 0) = (l.map kernelValue).prod := by
  simpa only [kernelValue, SubmonoidClass.coe_list_prod, List.map_map, Function.comp_def] using
    congrArg (fun z : localKernel matrixA_mul_self matrixB_pow_four => (z : M))
      (maskValue_fold matrixA_mul_self matrixB_pow_four l)

private theorem kernelPart_value (m : ℕ) :
    kernelValue (kernelPartMask m) = binaryProduct kernelGenerator (fun j => m.testBit (j.val + 5)) := by
  rw [kernelPartMask, kernelValue_fold]
  simp only [List.map_ofFn, binaryProduct]
  congr 1
  congr 1
  funext j
  dsimp only [Function.comp_apply]
  split_ifs
  · rfl
  · exact kernelValue_zero

private theorem kernelPart_mem (m : ℕ) : kernelValue (kernelPartMask m) ∈ localF := by
  rw [kernelPart_value]
  apply binaryProduct_mem
  intro j
  simpa only [generators, Fin.append_left] using generator_mem_localF (Fin.castAdd 4 j)

private theorem localF_square (f : M) (hf : f ∈ localF) : f * f = 1 := by
  let := localF_elementary
  simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) f hf

private theorem square_mul_commute {G : Type*} [Group G] (a b : G)
    (ha : a*a=1) (hb : b*b=1) (hab : (a*b)*(a*b)=1) : Commute a b := by
  have hai : a⁻¹=a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹=b := inv_eq_of_mul_eq_one_right hb
  have habi : (a*b)⁻¹=a*b := inv_eq_of_mul_eq_one_right hab
  rw [mul_inv_rev, hai, hbi] at habi
  exact habi.symm

private theorem reduced_product_square (m : ℕ) (v : Fin 4 → Bool)
    (h : (kernelValue m * liftProduct v) * (kernelValue m * liftProduct v) = 1) :
    (kernelValue (reducedMask m) * liftProduct v) *
      (kernelValue (reducedMask m) * liftProduct v) = 1 := by
  have hc : Commute (kernelValue m) (liftProduct v) :=
    square_mul_commute _ _ (kernelValue_square m)
      (localF_square _ (liftProduct_mem v)) h
  have hp : Commute (kernelValue (kernelPartMask m)) (liftProduct v) :=
    localF_commute _ (kernelPart_mem m) _ (liftProduct_mem v)
  have hr : Commute (kernelValue (reducedMask m)) (liftProduct v) := by
    rw [reducedMask, kernelValue_xor]
    exact hc.mul_left hp
  calc
    _ = (kernelValue (reducedMask m) * kernelValue (reducedMask m)) *
        (liftProduct v * liftProduct v) := by rw [← mul_assoc, mul_assoc (kernelValue (reducedMask m)), ← hr.eq]; group
    _ = 1 := by rw [kernelValue_square, localF_square _ (liftProduct_mem v), one_mul]

private theorem fixed_value_mem (m : ℕ)
    (h : ∀ i : Fin 4, maskImage (liftKernelMasks i) m = m) : kernelValue m ∈ localF := by
  apply kernel_mem_localF_of_commuting_lifts
  · exact (maskValue matrixA_mul_self matrixB_pow_four m).property
  · intro i
    have hc := lift_conjugates_kernel i m
    rw [h i] at hc
    change kernelValue m * lift i = lift i * kernelValue m
    calc
      _ = lift i * ((lift i)⁻¹ * kernelValue m * lift i) := by group
      _ = _ := by rw [hc]

/-- Every reduced square-one lift with nonzero quotient belongs to the native pair. -/
theorem reduced_square_one_pair (v : Fin 4 → Bool) (m : Fin 32)
    (hv : v ≠ fun _ => false)
    (hs : (kernelValue m.val * liftProduct v) * (kernelValue m.val * liftProduct v) = 1) :
    (kernelValue m.val * liftProduct v : M) ∈ localF ∨
      ((kernelValue m.val * liftProduct v : M) : Model) ∈ secondF := by
  have hl := localF_square _ (liftProduct_mem v)
  have hc := square_mul_commute _ _ (kernelValue_square m.val) hl hs
  have hfix : liftAction v m.val = m.val := by
    apply kernelValue_injective (reduced_action_lt v m) (m.isLt.trans (by decide))
    rw [← liftProduct_conjugates_kernel, mul_assoc, hc.eq, inv_mul_cancel_left]
  rcases reduced_involution_masks v m hv hfix with hm | hm
  · left
    rw [hm, kernelValue_zero, one_mul]
    exact liftProduct_mem v
  · right
    let d := Nat.xor (liftAction v 1) 1
    have hn : kernelValue (Nat.xor m.val d) ∈ localF := fixed_value_mem _ hm
    have hsi : (kernelValue 1)⁻¹ = kernelValue 1 := inv_eq_of_mul_eq_one_right (kernelValue_square 1)
    have hd : kernelValue d = (liftProduct v)⁻¹ * kernelValue 1 * liftProduct v * kernelValue 1 := by
      rw [kernelValue_xor, ← liftProduct_conjugates_kernel]
    have hdconj : kernelValue 1 * liftProduct v * (kernelValue 1)⁻¹ =
        liftProduct v * kernelValue d := by
      rw [hd, hsi]
      group
    have he : kernelValue 1 * (kernelValue (Nat.xor m.val d) * liftProduct v) *
        (kernelValue 1)⁻¹ = kernelValue m.val * liftProduct v := by
      calc
        _ = kernelValue (Nat.xor m.val d) *
            (kernelValue 1 * liftProduct v * (kernelValue 1)⁻¹) := by
          rw [← mul_assoc, (kernelValue_commute 1 _).eq]
          group
        _ = kernelValue (Nat.xor m.val d) * (liftProduct v * kernelValue d) := by rw [hdconj]
        _ = liftProduct v * (kernelValue (Nat.xor m.val d) * kernelValue d) := by
          rw [← mul_assoc, (localF_commute _ hn _ (liftProduct_mem v)).eq, mul_assoc]
        _ = liftProduct v * kernelValue m.val := by
          rw [kernelValue_xor, mul_assoc (kernelValue m.val), kernelValue_square, mul_one]
        _ = kernelValue m.val * liftProduct v := hc.eq.symm
    exact mem_map.mpr ⟨(kernelValue (Nat.xor m.val d) * liftProduct v : M),
      mem_map.mpr ⟨_,localF.mul_mem hn (liftProduct_mem v),rfl⟩,
      congrArg (fun z : M => (z : Model)) he⟩

/-- Every local Q element has a bounded kernel coordinate and a literal F lift. -/
theorem localQ_decomposition (q : M) (hq : q ∈ A.comap projection) :
    ∃ m : Fin 2048, ∃ v : Fin 4 → Bool, q = kernelValue m.val * liftProduct v := by
  change projection q ∈ A at hq
  rw [← localF_image] at hq
  obtain ⟨f,hf,he⟩ := mem_map.mp hq
  obtain ⟨e,heK,v,hfv⟩ := localF_decomposition f hf
  have hk : q*f⁻¹ ∈ localKernel matrixA_mul_self matrixB_pow_four := by
    rw [← MathieuHallActors.projection_ker, MonoidHom.mem_ker,
      map_mul, map_inv, he, mul_inv_cancel]
  have hke := (localKernel matrixA_mul_self matrixB_pow_four).mul_mem hk heK
  obtain ⟨m,hm⟩ := maskValue_surjective matrixA_mul_self matrixB_pow_four ⟨q*f⁻¹*e,hke⟩
  refine ⟨m,v,?_⟩
  have hm' : kernelValue m.val = q*f⁻¹*e := congrArg Subtype.val hm
  rw [hm', mul_assoc, mul_assoc, ← hfv, inv_mul_cancel, mul_one]

/-- Every square-one element of Q lies in E or one of the two actual F-subgroups. -/
theorem Q_square_one_occurrences (q : Model) (hq : q ∈ Q) (hs : q*q=1) :
    q ∈ E ∨ q ∈ F ∨ q ∈ secondF := by
  obtain ⟨a,ha,rfl⟩ := mem_map.mp hq
  obtain ⟨m,v,rfl⟩ := localQ_decomposition a ha
  have hsq : (kernelValue m.val * liftProduct v) * (kernelValue m.val * liftProduct v) = 1 :=
    Subtype.ext hs
  change ((kernelValue m.val * liftProduct v : M) : Model) ∈ E ∨
    ((kernelValue m.val * liftProduct v : M) : Model) ∈ F ∨
    ((kernelValue m.val * liftProduct v : M) : Model) ∈ secondF
  by_cases hv : v = fun _ => false
  · left
    simpa only [hv, liftProduct, binaryProduct_zero, mul_one] using kernelValue_mem_E m.val
  have hred := reduced_square_one_pair v ⟨reducedMask m.val,reducedMask_lt m⟩ hv
    (reduced_product_square m.val v hsq)
  have hk := kernelPart_mem m.val
  have hkE := kernelValue_mem_E (kernelPartMask m.val)
  have hkF : (kernelValue (kernelPartMask m.val) : Model) ∈ F := mem_map.mpr ⟨_,hk,rfl⟩
  have hk2 : (kernelValue (kernelPartMask m.val) : Model) ∈ secondF := by
    have hh : (kernelValue (kernelPartMask m.val) : Model) ∈ F ⊓ E := ⟨hkF,hkE⟩
    rw [← intersection_eq] at hh
    exact hh.2
  have he : (kernelValue (reducedMask m.val) * liftProduct v) * kernelValue (kernelPartMask m.val) =
      kernelValue m.val * liftProduct v := by
    rw [mul_assoc, ← (localF_commute _ hk _ (liftProduct_mem v)).eq, ← mul_assoc,
      reducedMask, kernelValue_xor, mul_assoc (kernelValue m.val), kernelValue_square, mul_one]
  right
  rcases hred with hred | hred
  · left
    exact mem_map.mpr ⟨_,he ▸ localF.mul_mem hred hk,rfl⟩
  · right
    have hh := secondF.mul_mem hred hk2
    exact congrArg (fun z : M => (z : Model)) he ▸ hh

private theorem kernel_commute_elements (x y : M)
    (hx : x ∈ localKernel matrixA_mul_self matrixB_pow_four)
    (hy : y ∈ localKernel matrixA_mul_self matrixB_pow_four) : Commute x y := by
  let := localKernel_elementary matrixA_mul_self matrixB_pow_four
  exact congrArg (fun z : localKernel matrixA_mul_self matrixB_pow_four => (z : M))
    (mul_comm (⟨x,hx⟩ : localKernel matrixA_mul_self matrixB_pow_four) ⟨y,hy⟩)

/-- Full octad image forces every centralizing kernel element into F ∩ E. -/
theorem kernel_centralizer_full_image (H : Subgroup M) (hH : H.map projection = A)
    (z : M) (hz : z ∈ localKernel matrixA_mul_self matrixB_pow_four)
    (hc : z ∈ centralizer (H : Set M)) : z ∈ localF := by
  apply kernel_mem_localF_of_commuting_lifts z hz
  intro i
  have hi : projection (lift i) ∈ H.map projection := hH ▸ lift_projection_mem_A i
  obtain ⟨h,hh,he⟩ := mem_map.mp hi
  have hk : h⁻¹ * lift i ∈ localKernel matrixA_mul_self matrixB_pow_four := by
    rw [← MathieuHallActors.projection_ker, MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
  have hzh : Commute z h := ((mem_centralizer_iff.mp hc) h hh).symm
  have hzk := kernel_commute_elements z _ hz hk
  simpa only [mul_inv_cancel_left] using hzh.mul_right hzk

/-- An elementary subgroup with full octad image lies in one member of the native pair. -/
theorem elementary_full_image_pair (H : Subgroup Model) [IsElementaryAbelian 2 H]
    (hHQ : H ≤ Q) (himage : (H.subgroupOf M).map projection = A) :
    H ≤ F ∨ H ≤ secondF := by
  apply SubgroupClass.subset_union.mp
  intro z hz
  have hs : z*z=1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) z hz
  rcases Q_square_one_occurrences z (hHQ hz) hs with he | hf | hf
  · left
    obtain ⟨k,hk,rfl⟩ := mem_map.mp he
    apply mem_map.mpr
    refine ⟨k, kernel_centralizer_full_image (H.subgroupOf M) himage k hk ?_,rfl⟩
    intro y hy
    apply Subtype.ext
    exact congrArg (fun a : H => (a : Model)) (mul_comm (⟨y,hy⟩ : H) ⟨k,hz⟩)
  · exact Or.inl hf
  · exact Or.inr hf

end Janko4.LocalStructure.LinearFive.Geometry
