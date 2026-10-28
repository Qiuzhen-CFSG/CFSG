module
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.Restriction
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Quotient
public import Theory.AtlasPort.LinearGroups.G2.LieBinaryCompatibility
public import Theory.SpecificGroups.C4SquareSignSwapPresentation

/-!
# The full binary G₂ Sylow subgroup with all three source markings

The original six positive-root coordinates give four generators satisfying
simultaneous inversion and interchange of two commuting elements of order
four. Their normal forms are distinct, so the model of order 64 maps
isomorphically to the actual common Sylow subgroup. The derived subgroup is
detected by the sum of root coordinates C, D and F; the first and second
vertex cores are detected by the vanishing of F and E respectively.

Thus the same equivalence identifies the derived Sylow subgroup with the
wreathed transfer subgroup, and the two actual parabolic cores with the
extraspecial and inversion cores. This is the full G₂(2) model calculation
used by Aschbacher–Smith 14.2.22, following 14.2.21 (printed pp.988–989).
Root-coordinate laws come from the licensed ATLAS port in the imports;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup Atlas.G2.Explicit
namespace Atlas.G2.BinaryParabolicPair.FullSignSwap
open BinaryCore

private def aP : Fin 6 → ZMod 2 := ![0,0,0,1,0,1]
private def bP : Fin 6 → ZMod 2 := ![1,1,1,0,0,1]
private def tP : Fin 6 → ZMod 2 := ![0,0,0,1,0,0]
private def uP : Fin 6 → ZMod 2 := ![0,0,0,0,1,0]
private def powP (a : Fin 6 → ZMod 2) : ℕ → Fin 6 → ZMod 2
  | 0 => 0
  | n+1 => unipotentProductParameters (powP a n) a
private theorem eval_powP (a : Fin 6 → ZMod 2) (n : ℕ) :
    unipotentProduct (powP a n) = unipotentProduct a ^ n := by
  induction n with
  | zero => exact unipotentProduct_zero
  | succ n hn => rw [powP, ← unipotentProduct_mul, hn, pow_succ]
private noncomputable def elt (a : Fin 6 → ZMod 2) : commonSylow :=
  ⟨unipotentProduct a, unipotentProduct_mem a⟩
private theorem elt_mul (a b : Fin 6 → ZMod 2) :
    elt a * elt b = elt (unipotentProductParameters a b) :=
  Subtype.ext (unipotentProduct_mul a b)
private theorem elt_pow (a : Fin 6 → ZMod 2) (n : ℕ) :
    elt a ^ n = elt (powP a n) := Subtype.ext (eval_powP a n).symm
private theorem elt_zero : elt 0 = 1 := Subtype.ext unipotentProduct_zero
private theorem relations : C4SquareSignSwap.Relations (elt aP) (elt bP) (elt tP) (elt uP) := by
  have htp : elt tP ^ 2 = 1 := by rw [elt_pow]; exact congrArg elt (by decide +kernel) |>.trans elt_zero
  have hup : elt uP ^ 2 = 1 := by rw [elt_pow]; exact congrArg elt (by decide +kernel) |>.trans elt_zero
  have hti : (elt tP)⁻¹ = elt tP := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using htp)
  have hui : (elt uP)⁻¹ = elt uP := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hup)
  have hap : elt aP ^ 4 = 1 := by rw [elt_pow]; exact congrArg elt (by decide +kernel) |>.trans elt_zero
  have hbp : elt bP ^ 4 = 1 := by rw [elt_pow]; exact congrArg elt (by decide +kernel) |>.trans elt_zero
  have hai : (elt aP)⁻¹ = elt aP ^ 3 := by
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_succ, hap]
  have hbi : (elt bP)⁻¹ = elt bP ^ 3 := by
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_succ, hbp]
  refine ⟨hap,hbp,htp,hup,?_,?_,?_,?_,?_,?_⟩
  · change elt aP * elt bP = elt bP * elt aP
    simp only [elt_mul]
    exact congrArg elt (by decide +kernel)
  · change elt tP * elt uP = elt uP * elt tP
    simp only [elt_mul]
    exact congrArg elt (by decide +kernel)
  · rw [hti,hai,elt_pow,elt_mul,elt_mul]
    exact congrArg elt (by decide +kernel)
  · rw [hti,hbi,elt_pow,elt_mul,elt_mul]
    exact congrArg elt (by decide +kernel)
  · rw [hui,elt_mul,elt_mul]
    exact congrArg elt (by decide +kernel)
  · rw [hui,elt_mul,elt_mul]
    exact congrArg elt (by decide +kernel)

private def wordP (x : C4SquareSignSwap.Model) : Fin 6 → ZMod 2 :=
  unipotentProductParameters (unipotentProductParameters
    (unipotentProductParameters (powP aP x.left.1.toAdd.val)
      (powP bP x.left.2.toAdd.val)) (powP tP x.right.1.toAdd.val))
    (powP uP x.right.2.toAdd.val)

private noncomputable def modelHom : C4SquareSignSwap.Model →* commonSylow :=
  C4SquareSignSwap.presentationHom relations

private theorem modelHom_apply (x : C4SquareSignSwap.Model) : modelHom x = elt (wordP x) := by
  conv_lhs => rw [C4SquareSignSwap.normal_form x]
  simp only [map_mul,map_pow,modelHom,C4SquareSignSwap.presentationHom_rotation₁,
    C4SquareSignSwap.presentationHom_rotation₂,C4SquareSignSwap.presentationHom_inverter,
    C4SquareSignSwap.presentationHom_swapper]
  apply Subtype.ext
  change unipotentProduct aP ^ x.left.1.toAdd.val *
    unipotentProduct bP ^ x.left.2.toAdd.val *
    unipotentProduct tP ^ x.right.1.toAdd.val *
    unipotentProduct uP ^ x.right.2.toAdd.val = unipotentProduct (wordP x)
  rw [← eval_powP, ← eval_powP, ← eval_powP, ← eval_powP]
  simp only [unipotentProduct_mul,wordP]

set_option maxRecDepth 10000 in
private theorem wordP_injective : Function.Injective wordP := by decide +kernel

private theorem modelHom_injective : Function.Injective modelHom := by
  intro x y h
  rw [modelHom_apply,modelHom_apply] at h
  exact wordP_injective (unipotentProduct_injective (congrArg Subtype.val h))

private noncomputable def modelEquiv : C4SquareSignSwap.Model ≃* commonSylow :=
  MulEquiv.ofBijective modelHom (modelHom_injective.bijective_of_nat_card_le (by
    rw [C4SquareSignSwap.card_model]
    exact card_unipotent_binary.le))


private theorem product_mem_derived_iff (p : Fin 6 → ZMod 2) :
    unipotentProduct p ∈ commutator (Model (ZMod 2)) ↔ p 2 + p 3 + p 5 = 0 := by
  rw [commutator_eq_longRootClosure, ← QuotientGroup.eq_one_iff]
  change BinaryException.projection (unipotentProduct p) = 1 ↔ _
  simp only [unipotentProduct, map_mul, BinaryException.project_A,
    BinaryException.project_B, BinaryException.project_E, one_mul, mul_one,
    BinaryException.project_C_eq_D, BinaryException.project_D_eq_F]
  rw [← map_mul, ← map_mul, rootF_add, rootF_add]
  have hb : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide +kernel
  rcases hb (p 2 + p 3 + p 5) with h | h
  · simp [h, rootF_zero]
  · rw [h]
    exact iff_of_false quotientBit_ne_one (by decide)

private theorem product_mem_firstCore_iff (p : Fin 6 → ZMod 2) :
    unipotentProduct p ∈ firstParabolic.pCoreIn 2 ↔ p 5 = 0 := by
  rw [firstParabolic_pCore]
  constructor
  · rintro ⟨q,hq⟩
    exact (congrFun (unipotentProduct_injective hq) 5).symm
  · intro hp
    refine ⟨⟨p 0,p 1,p 2,p 3,p 4⟩,?_⟩
    simp [embedding,parameters,unipotentProduct,hp]

private theorem product_mem_secondCore_iff (p : Fin 6 → ZMod 2) :
    unipotentProduct p ∈ secondParabolic.pCoreIn 2 ↔ p 4 = 0 := by
  rw [← LieParabolicSetup.local₂_binary, LieParabolicSetup.local₂_pCoreIn]
  change (∃ q : Fin 6 → ZMod 2, q 4 = 0 ∧ unipotentProduct q = unipotentProduct p) ↔ _
  constructor
  · rintro ⟨q,hq,he⟩
    exact (congrFun (unipotentProduct_injective he) 4).symm.trans hq
  · exact fun hp => ⟨p,hp,rfl⟩

private theorem word_marks : ∀ x : C4SquareSignSwap.Model,
    ((wordP x 2 + wordP x 3 + wordP x 5 = 0) ↔ x ∈ C4SquareSignSwap.transfer) ∧
    ((wordP x 5 = 0) ↔ x ∈ C4SquareSignSwap.extraspecialCore) ∧
    ((wordP x 4 = 0) ↔ x ∈ C4SquareSignSwap.inverterCore) := by decide +kernel

/-- The actual common Sylow subgroup with sign-and-swap coordinates. -/
noncomputable def equiv : commonSylow ≃* C4SquareSignSwap.Model := modelEquiv.symm

private theorem modelEquiv_apply (x : C4SquareSignSwap.Model) :
    (modelEquiv x : Model (ZMod 2)) = unipotentProduct (wordP x) :=
  congrArg Subtype.val (modelHom_apply x)

/-- The ambient derived group restricts to the marked wreathed subgroup. -/
theorem derived_mark :
    ((commutator (Model (ZMod 2))).subgroupOf (commonSylow : Subgroup _)).map
      equiv.toMonoidHom = C4SquareSignSwap.transfer := by
  ext x
  rw [Subgroup.mem_map_equiv]
  change (modelEquiv x : Model (ZMod 2)) ∈ commutator (Model (ZMod 2)) ↔ _
  rw [modelEquiv_apply,product_mem_derived_iff]
  exact (word_marks x).1

/-- The first vertex retains its actual extraspecial two-core. -/
theorem first_core_mark :
    ((firstParabolic.pCoreIn 2).subgroupOf (commonSylow : Subgroup _)).map
      equiv.toMonoidHom = C4SquareSignSwap.extraspecialCore := by
  ext x
  rw [Subgroup.mem_map_equiv]
  change (modelEquiv x : Model (ZMod 2)) ∈ firstParabolic.pCoreIn 2 ↔ _
  rw [modelEquiv_apply,product_mem_firstCore_iff]
  exact (word_marks x).2.1

/-- The second vertex retains its actual simultaneous-inversion two-core. -/
theorem second_core_mark :
    ((secondParabolic.pCoreIn 2).subgroupOf (commonSylow : Subgroup _)).map
      equiv.toMonoidHom = C4SquareSignSwap.inverterCore := by
  ext x
  rw [Subgroup.mem_map_equiv]
  change (modelEquiv x : Model (ZMod 2)) ∈ secondParabolic.pCoreIn 2 ↔ _
  rw [modelEquiv_apply,product_mem_secondCore_iff]
  exact (word_marks x).2.2


/-- The original root involution has the specified central coordinate. -/
theorem equiv_involution :
    equiv ⟨z, core_le_unipotent (elementary_le_core z_mem_elementary)⟩ =
      C4SquareSignSwap.rotation₁ ^ 2 * C4SquareSignSwap.rotation₂ ^ 2 := by
  apply modelEquiv.injective
  change modelEquiv (modelEquiv.symm _) = _
  rw [modelEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [modelEquiv_apply]
  have hword : wordP (C4SquareSignSwap.rotation₁ ^ 2 * C4SquareSignSwap.rotation₂ ^ 2) =
      ![1,0,0,0,0,0] := by decide +kernel
  rw [hword]
  simp [unipotentProduct,z]

end Atlas.G2.BinaryParabolicPair.FullSignSwap
