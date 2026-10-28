module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CoreCenter
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.A5ResidualMarked
import all Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.A5Factor

/-!
# Cubic fixed subgroups of the literal J₄ max4 two-core

The actual A₅ preimage has order 2¹⁵·60, so its order-three subgroups
are conjugate. A word in the certified max4 generators supplies one such
subgroup. On the first sixteen coordinates, the fifteen binary core words
have square-zero differences. Commutation with the cubic therefore gives
twelve linear equations; their checked invertible coefficient matrix forces
the first twelve word bits to vanish. Only three binary parameters remain.
Consequently every cubic in the same A₅ preimage fixes at most eight core
elements. No equality between the A₅ preimage and its residual is used.

Source: Aschbacher--Smith 5.1.13, printed p.637. All matrix coordinates
and ATLAS attribution are inherited from `SymmetricLinear.Model` and
`SylowTwoPart.KernelCardinality`. The coefficient data can be reproduced
with `CubicCore/source/verify.py`; only Lean kernel checks are proofs.
The internal import exposes the already marked preimage for this extension.
-/

public noncomputable section
open Subgroup
open scoped Matrix BigOperators
namespace Janko4.LocalStructure.SymmetricLinear.CubicCore
open CharacteristicTwo SylowTwoPart KernelCardinality
attribute [local irreducible] modelGroup matrixA matrixB max4Subgroup

private def word : max4Subgroup := (first * second * first * second^2)^14
private def cubic : max4Subgroup := word^(2^15)

private def rows2 : Vector ℕ 28 := ⟨#[7, 14, 1, 10, 55566, 34188, 49854, 30230, 29409, 43192, 57777, 56690, 14482, 48477, 26927, 62731, 84902629, 234282011, 197019653, 26898878, 38033544, 34012426, 154733782, 6169347, 149067910, 76084228, 187956708, 23462113], by decide⟩
private def rows3 : Vector ℕ 28 := ⟨#[6, 15, 1, 10, 30685, 49903, 56732, 56921, 36548, 63077, 5702, 56342, 40183, 18049, 33275, 6694, 204538884, 234256501, 221559355, 26884025, 228956875, 136816883, 154749650, 752687, 71924047, 130185564, 21449847, 62304264], by decide⟩
private def rows4 : Vector ℕ 28 := ⟨#[15, 2, 8, 4, 17594, 36845, 51672, 37893, 54238, 38004, 29162, 2531, 40157, 47003, 11950, 60848, 165865640, 245608362, 214444063, 105462948, 242084224, 216847319, 236535917, 170508199, 105016551, 66809017, 37859447, 3967450], by decide⟩
private def rows5 : Vector ℕ 28 := ⟨#[10, 1, 15, 6, 10956, 34139, 9383, 16087, 23576, 19444, 45201, 25466, 40939, 24378, 43245, 36525, 153000624, 15014369, 175560509, 183298961, 131090595, 123334751, 190095674, 17336747, 66269722, 225161970, 64100282, 259704041], by decide⟩
private def rows6 : Vector ℕ 28 := ⟨#[7, 10, 2, 14, 28109, 27714, 21539, 26742, 52775, 27027, 23149, 27404, 19047, 23697, 11717, 44349, 187052949, 242068203, 56561731, 261000068, 13010800, 37545746, 118511802, 153080773, 230044218, 4286594, 66146538, 65319419], by decide⟩
private def rows7 : Vector ℕ 28 := ⟨#[15, 4, 10, 6, 45644, 5148, 20864, 20476, 46151, 53705, 23895, 48608, 5940, 21375, 40839, 3950, 18678277, 42941774, 62626178, 104943793, 54342815, 241885008, 247523441, 118380403, 192193738, 204871947, 170177921, 43740835], by decide⟩
private def rows8 : Vector ℕ 28 := ⟨#[1, 2, 4, 8, 34423, 32203, 49651, 34502, 46474, 14564, 41221, 5274, 46643, 38331, 6646, 44722, 176649358, 12846187, 215470568, 260463899, 150657961, 77296368, 240902178, 213578916, 145118280, 266196116, 46557656, 56427346], by decide⟩
private def rows9 : Vector ℕ 28 := ⟨#[10, 1, 15, 6, 65276, 64946, 53172, 28598, 39973, 15503, 36234, 15206, 6789, 27778, 5472, 55497, 9719214, 2813644, 44670355, 162236152, 262590537, 102574173, 240131288, 119602679, 62443767, 104368315, 228895920, 194565867], by decide⟩
private def rows10 : Vector ℕ 28 := ⟨#[7, 10, 2, 14, 37512, 64926, 46872, 850, 35095, 44895, 40369, 57283, 29407, 41145, 14636, 19524, 170859912, 261933866, 238743427, 539818, 171126, 262980648, 32689376, 238677646, 45133619, 193779133, 101747914, 255139445], by decide⟩
private def rows11 : Vector ℕ 28 := ⟨#[15, 4, 10, 6, 37528, 64951, 46941, 978, 34839, 44374, 39357, 55242, 25302, 32944, 31008, 52292, 9744525, 1063065, 43211368, 545398, 261910469, 264111351, 222912743, 119539158, 169575601, 100804098, 228491129, 195167645], by decide⟩
private theorem prod2 : decode firstRows * decode secondRows = decode rows2 :=
  product _ _ _ (by decide +kernel)
private theorem prod3 : decode rows2 * decode firstRows = decode rows3 :=
  product _ _ _ (by decide +kernel)
private theorem prod4 : decode secondRows * decode secondRows = decode rows4 :=
  product _ _ _ (by decide +kernel)
private theorem prod5 : decode rows3 * decode rows4 = decode rows5 :=
  product _ _ _ (by decide +kernel)
private theorem prod6 : decode rows5 * decode rows5 = decode rows6 :=
  product _ _ _ (by decide +kernel)
private theorem prod7 : decode rows6 * decode rows6 = decode rows7 :=
  product _ _ _ (by decide +kernel)
private theorem prod8 : decode rows7 * decode rows6 = decode rows8 :=
  product _ _ _ (by decide +kernel)
private theorem prod9 : decode rows8 * decode rows5 = decode rows9 :=
  product _ _ _ (by decide +kernel)
private theorem prod10 : decode rows9 * decode rows9 = decode rows10 :=
  product _ _ _ (by decide +kernel)
private theorem prod11 : decode rows10 * decode rows10 = decode rows11 :=
  product _ _ _ (by decide +kernel)

private theorem image_word : representation word = decode rows10 := by
  have h2 : (decode rows5)^2 = decode rows6 := by rw [pow_two,prod6]
  have h4 : (decode rows5)^4 = decode rows7 := by
    rw [show (4 : ℕ) = 2+2 from rfl,pow_add,h2,prod7]
  have h7 : (decode rows5)^7 = decode rows9 := by
    rw [show (7 : ℕ) = 4+2+1 from rfl,pow_add,pow_add,pow_one,h4,h2,prod8,prod9]
  simp only [word, map_mul, map_pow, image_first, image_second]
  rw [pow_two,prod4,prod2,prod3,prod5,
    show (14 : ℕ) = 7+7 from rfl,pow_add,h7,prod10]

private theorem matrix_word_cube : (decode rows10)^3 = 1 := by
  rw [show (3 : ℕ) = 2+1 from rfl,pow_add,pow_two,pow_one,prod11]
  exact (product rows11 rows10 (⟨#[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608, 16777216, 33554432, 67108864, 134217728], by decide⟩)
    (by decide +kernel)).trans (by decide +kernel)

attribute [local irreducible] word cubic

private theorem image_cubic : representation cubic = decode rows11 := by
  have hp := pow_eq_pow_mod (2^15) matrix_word_cube
  have hm : (2^15)%3 = 2 := by decide
  rw [hm] at hp
  unfold cubic
  exact (map_pow representation word (2^15)).trans
    ((congrArg (fun A : SmallMatrix => A^(2^15)) image_word).trans
      (hp.trans ((pow_two _).trans prod11)))

private theorem word_projection : max4Projection word =
    (Projection.firstImage * Projection.secondImage * Projection.firstImage *
      Projection.secondImage^2)^14 := by
  simp only [word,map_pow,map_mul]
  change (max4Projection Projection.first * max4Projection Projection.second *
    max4Projection Projection.first * (max4Projection Projection.second)^2)^14 = _
  rw [max4Projection_first,max4Projection_second]

private theorem word_projection_cube : (max4Projection word)^3 = 1 := by
  rw [word_projection]
  decide +kernel

private theorem word_mem : word ∈ a5Preimage := by
  change max4Projection word ∈ (alternatingGroup (Fin 5)).prod ⊥
  rw [word_projection]
  constructor
  · change Equiv.Perm.sign _ = 1
    decide +kernel
  · change _ = 1
    decide +kernel

/-- The specified element is a genuine cubic in the literal A₅ preimage. -/
private theorem cubic_mem_order : cubic ∈ a5Preimage ∧ orderOf cubic = 3 := by
  have hk : word^3 ∈ pCore 2 max4Subgroup := by
    rw [←max4Projection_kernel_eq_twoCore,MonoidHom.mem_ker,map_pow,word_projection_cube]
  have h3 : cubic^3 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨word^3,hk⟩ : pCore 2 max4Subgroup))
    have hc : (⟨word^3,hk⟩ : pCore 2 max4Subgroup)^(2^15) = 1 := by
      simpa only [twoCore_card] using hh
    have he := congrArg (pCore 2 max4Subgroup).subtype hc
    simpa only [map_pow,map_one,coe_subtype,cubic,←pow_mul,Nat.mul_comm] using he
  refine ⟨by unfold cubic; exact a5Preimage.pow_mem word_mem _,orderOf_eq_prime h3 ?_⟩
  intro he
  have hh := congrArg max4Projection he
  rw [cubic,map_pow,pow_eq_pow_mod _ word_projection_cube,word_projection] at hh
  have hn : ((Projection.firstImage * Projection.secondImage * Projection.firstImage *
      Projection.secondImage^2)^14)^2 ≠ 1 := by decide +kernel
  exact hn (by simpa only [map_one,show 2^15 % 3 = 2 by decide] using hh)

private abbrev Mat16 := Matrix (Fin 16) (Fin 16) (ZMod 2)
private def cut (A : SmallMatrix) : Mat16 :=
  A.submatrix (Fin.castAdd 12) (Fin.castAdd 12)

private theorem cut_mul (A B : SmallMatrix)
    (hA : ∀ (i : Fin 16) (j : Fin 12), A (Fin.castAdd 12 i) (Fin.natAdd 16 j) = 0) :
    cut (A*B) = cut A * cut B := by
  ext i j
  simp only [cut,Matrix.submatrix_apply,Matrix.mul_apply]
  rw [Fin.sum_univ_add (a := 16) (b := 12)]
  simp only [hA,zero_mul,Finset.sum_const_zero,add_zero]

set_option maxRecDepth 2000 in
private def smallRepresentation : max4Subgroup →* Mat16 where
  toFun g := cut (representation g)
  map_one' := by ext i j; simp [cut,Matrix.one_apply,Fin.ext_iff]
  map_mul' g h := by
    rw [map_mul]
    apply cut_mul
    intro i j
    change OrderBound.representation g (Fin.castAdd 84 (Fin.castAdd 12 i))
      (Fin.castAdd 84 (Fin.natAdd 16 j)) = 0
    exact OrderBound.representation_triangular g (by
      change OrderBound.blockIndex (Fin.castAdd 84 (Fin.castAdd 12 i)) <
        OrderBound.blockIndex (Fin.castAdd 84 (Fin.natAdd 16 j))
      have h1 : ∀ i : Fin 16, OrderBound.blockIndex (Fin.castAdd 84 (Fin.castAdd 12 i)) ≤ 1 := by decide +kernel
      have h2 : ∀ j : Fin 12, 2 ≤ OrderBound.blockIndex (Fin.castAdd 84 (Fin.natAdd 16 j)) := by decide +kernel
      exact lt_of_le_of_lt (h1 i) (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) (h2 j)))

private def diff (i : Fin 15) : Mat16 := cut (decode (pivotRows.get i)) - 1

private theorem shape (k : Fin 15) (i j : Fin 16) :
    i.val < 4 ∨ 4 ≤ j.val → diff k i j = 0 := by
  simp only [diff,cut,Matrix.submatrix_apply,Matrix.sub_apply]
  revert k i j
  decide +kernel

private theorem diff_mul (i j : Fin 15) : diff i * diff j = 0 := by
  ext r c
  simp only [Matrix.mul_apply,Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k.val < 4
  · rw [shape j k c (Or.inl hk),mul_zero]
  · rw [shape i r k (Or.inr (by omega)),zero_mul]

private def coeff : Matrix (Fin 12) (Fin 12) (ZMod 2) := ![![0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1],
    ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0],
    ![0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1],
    ![1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0],
    ![1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0],
    ![1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1],
    ![0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0],
    ![1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1],
    ![1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0]]
private def inverse : Matrix (Fin 12) (Fin 12) (ZMod 2) := ![![0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 1],
    ![0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 1],
    ![1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1],
    ![1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1],
    ![0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1],
    ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0],
    ![1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1],
    ![0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1],
    ![1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1],
    ![1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1],
    ![1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0],
    ![0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1]]
private def row : Fin 12 → Fin 16 := ![4, 4, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7]
private def column : Fin 12 → Fin 16 := ![0, 1, 2, 3, 0, 1, 2, 0, 1, 2, 0, 1]

private theorem inverse_mul : inverse * coeff = 1 := by decide +kernel

private theorem coefficient (k : Fin 12) (i : Fin 15) :
    (diff i * cut (decode rows11) - cut (decode rows11) * diff i)
      (row k) (column k) = if h : i.val < 12 then coeff k ⟨i.val,h⟩ else 0 := by
  revert k i
  decide +kernel

private theorem image_product (bits : Fin 15 → Fin 2) :
    smallRepresentation (binaryProduct bits) =
      (List.ofFn (fun i => 1 + ((bits i).val : ZMod 2) • diff i)).prod := by
  change (smallRepresentation.comp seedNormalClosure.subtype) (binaryProduct bits) = _
  rw [binaryProduct,map_list_prod,List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  change smallRepresentation ((pivotWord i : max4Subgroup) ^ (bits i).val) = _
  rw [map_pow]
  have him : smallRepresentation (pivotWord i) = 1 + diff i := by
    change cut (seedRepresentation (pivotWord i)) = _
    rw [image_pivotWord seedConjugate_coordinates,diff]
    abel
  rw [him]
  generalize bits i = b
  fin_cases b <;> simp

private theorem fixed_bits_zero (bits : Fin 15 → Fin 2)
    (hc : Commute (binaryProduct bits : max4Subgroup) cubic) :
    ∀ i : Fin 12, bits (Fin.castAdd 3 i) = 0 := by
  let v : Fin 12 → ZMod 2 := fun i => (bits (Fin.castAdd 3 i)).val
  let L := List.ofFn (fun i => ((bits i).val : ZMod 2) • diff i)
  have hzero : ∀ a ∈ L, ∀ b ∈ L, a*b = 0 := by
    intro a ha b hb
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
    rw [smul_mul_smul_comm,diff_mul,smul_zero]
  have hcomm : Commute (L.map (1+·)).prod (cut (decode rows11)) := by
    have hh := hc.map smallRepresentation
    rw [image_product] at hh
    change Commute _ (cut (representation cubic)) at hh
    rw [image_cubic] at hh
    simpa only [L,List.map_ofFn,Function.comp_def] using hh
  have he := Theory.LinearAlgebra.ThreeBlockProduct.prod_commutation L (cut (decode rows11))
    (fun a ha b hb => by rw [hzero a ha b hb,zero_mul])
    (fun a ha b hb => by rw [mul_assoc,hzero a ha b hb,mul_zero]) hcomm
  have hv : coeff *ᵥ v = 0 := by
    funext k
    have hh := congrArg (fun A : Mat16 => A (row k) (column k)) he
    simp only [L,List.map_ofFn,List.sum_ofFn,Matrix.sum_apply,Function.comp_def,
      smul_mul_assoc,mul_smul_comm,←smul_sub,Matrix.smul_apply,smul_eq_mul,
      coefficient,Matrix.zero_apply] at hh
    rw [Fin.sum_univ_add (a := 12) (b := 3)] at hh
    have hfirst (i : Fin 12) : (Fin.castAdd 3 i).val < 12 := i.isLt
    have hlast (i : Fin 3) : ¬(Fin.natAdd 12 i).val < 12 := by simp
    simp only [hfirst,dif_pos,hlast,dite_false,mul_zero,Finset.sum_const_zero,add_zero] at hh
    have hcast (i : Fin 12) : (⟨(Fin.castAdd 3 i).val,hfirst i⟩ : Fin 12) = i := Fin.ext rfl
    simpa only [hcast,Matrix.mulVec,dotProduct,v,mul_comm,Pi.zero_apply] using hh
  have hv0 : v = 0 := by
    have hh := congrArg (fun v => inverse *ᵥ v) hv
    rw [Matrix.mulVec_mulVec,inverse_mul,Matrix.one_mulVec,Matrix.mulVec_zero] at hh
    exact hh
  intro i
  have hh := congrArg ZMod.val (congrFun hv0 i)
  apply Fin.ext
  simpa only [v,ZMod.val_natCast,Nat.mod_eq_of_lt (bits (Fin.castAdd 3 i)).isLt,
    ZMod.val_zero,Fin.val_zero,Pi.zero_apply] using hh

/-- At most eight elements of the actual max4 two-core commute with the marked cubic. -/
private theorem marked_core_centralizer_card :
    Nat.card (pCore 2 max4Subgroup ⊓ centralizer ({cubic} : Set max4Subgroup) :
      Subgroup max4Subgroup) ≤ 8 := by
  rw [←seedNormalClosure_eq_twoCore]
  let C := seedNormalClosure ⊓ centralizer ({cubic} : Set max4Subgroup)
  let e : (Fin 15 → Fin 2) ≃ seedNormalClosure :=
    Equiv.ofBijective binaryProduct binaryProduct_bijective
  let f : C → (Fin 3 → Fin 2) := fun z i => e.symm ⟨z,z.property.1⟩ (Fin.natAdd 12 i)
  have fixed (z : C) : ∀ i : Fin 12, e.symm ⟨z,z.property.1⟩ (Fin.castAdd 3 i) = 0 := by
    apply fixed_bits_zero
    rw [show binaryProduct (e.symm ⟨z,z.property.1⟩) = ⟨z,z.property.1⟩ from e.apply_symm_apply _]
    exact mem_centralizer_singleton_iff.mp z.property.2
  have hf : Function.Injective f := by
    intro x y hh
    have he : e.symm ⟨x,x.property.1⟩ = e.symm ⟨y,y.property.1⟩ := by
      funext i
      refine Fin.addCases (m := 12) (n := 3) (fun j => ?_) (fun j => ?_) i
      · rw [fixed x j,fixed y j]
      · exact congrFun hh j
    exact Subtype.ext (congrArg seedNormalClosure.subtype (e.symm.injective he))
  have hh := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_fun,Nat.card_fin,show 2^3 = 8 by decide] using hh

private theorem preimage_card : Nat.card a5Preimage = 1966080 := by
  let f : a5Preimage →* a5Factor := max4Projection.subgroupComap a5Factor
  have hf : Function.Surjective f :=
    max4Projection.subgroupComap_surjective_of_surjective a5Factor max4Projection_surjective
  have hk : f.ker = (pCore 2 max4Subgroup).subgroupOf a5Preimage := by
    ext x
    change f x = 1 ↔ _
    rw [←a5Factor.subtype_injective.eq_iff]
    change max4Projection x = 1 ↔ _
    rw [←max4Projection_kernel_eq_twoCore]
    rfl
  have hc := f.ker.card_mul_index
  rw [index_ker,f.range_eq_top_of_surjective hf,card_top,hk,
    Nat.card_congr (subgroupOfEquivOfLe twoCore_le_a5Preimage).toEquiv,
    twoCore_card,Nat.card_congr a5FactorEquiv.toEquiv,
    nat_card_alternatingGroup] at hc
  norm_num [Nat.factorial] at hc
  exact hc.symm

private theorem cubic_subgroups_conjugate (x : max4Subgroup)
    (hx : x ∈ a5Preimage) (ho : orderOf x = 3) :
    ∃ g : a5Preimage, (zpowers x).map (MulAut.conj (g : max4Subgroup)).toMonoidHom =
      zpowers cubic := by
  let u : a5Preimage := ⟨x,hx⟩
  let t : a5Preimage := ⟨cubic,cubic_mem_order.1⟩
  have hu : Nat.card (zpowers u) = 3 := by
    rw [Nat.card_zpowers,←orderOf_coe,ho]
  have ht : Nat.card (zpowers t) = 3 := by
    rw [Nat.card_zpowers,←orderOf_coe,cubic_mem_order.2]
  have syl (D : Subgroup a5Preimage) (hd : Nat.card D = 3) : ¬3 ∣ D.index := by
    have hh := D.card_mul_index
    rw [hd,preimage_card] at hh
    have hi : D.index = 655360 := by omega
    rw [hi]
    decide
  let P := (IsPGroup.of_card (p := 3) (n := 1) hu).toSylow (syl _ hu)
  let Q := (IsPGroup.of_card (p := 3) (n := 1) ht).toSylow (syl _ ht)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq a5Preimage P Q
  have he : (zpowers u).map (MulAut.conj g).toMonoidHom = zpowers t :=
    congrArg Sylow.toSubgroup hg
  have hh := congrArg (map a5Preimage.subtype) he
  simp only [MonoidHom.map_zpowers] at hh
  refine ⟨g,?_⟩
  change zpowers ((g : max4Subgroup) * x * (g : max4Subgroup)⁻¹) = zpowers cubic at hh
  exact (MonoidHom.map_zpowers _ _).trans hh

/-- Every cubic in the actual A₅ preimage fixes at most eight elements of the same two-core. -/
theorem core_centralizer_card (x : max4Subgroup)
    (hx : x ∈ a5Preimage) (ho : orderOf x = 3) :
    Nat.card (pCore 2 max4Subgroup ⊓ centralizer ({x} : Set max4Subgroup) :
      Subgroup max4Subgroup) ≤ 8 := by
  obtain ⟨g,hg⟩ := cubic_subgroups_conjugate x hx ho
  let a := MulAut.conj (g : max4Subgroup)
  have hz : (centralizer ({x} : Set max4Subgroup)).map a.toMonoidHom ≤
      centralizer ({cubic} : Set max4Subgroup) := by
    have hh := map_centralizer_le_centralizer_image (zpowers x : Set max4Subgroup) a.toMonoidHom
    change _ ≤ centralizer ((zpowers x).map a.toMonoidHom : Set max4Subgroup) at hh
    rw [hg] at hh
    simpa only [zpowers_eq_closure,centralizer_closure] using hh
  rw [←card_map_of_injective (f := a.toMonoidHom) a.injective,
    map_inf _ _ _ a.injective,pCore_map_iso 2 a]
  exact (Nat.le_of_dvd Nat.card_pos (card_dvd_of_le (inf_le_inf_left _ hz))).trans marked_core_centralizer_card

/-- Subgroup form retaining the original cubic, its inclusion and the literal two-core. -/
theorem subgroup_core_centralizer_card (E : Subgroup max4Subgroup)
    (hE : Nat.card E = 3) (hEA : E ≤ a5Preimage) :
    Nat.card (pCore 2 max4Subgroup ⊓ centralizer (E : Set max4Subgroup) :
      Subgroup max4Subgroup) ≤ 8 := by
  let : IsCyclic E := isCyclic_of_prime_card hE
  obtain ⟨x,hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have ho : orderOf (x : max4Subgroup) = 3 := (orderOf_coe x).trans (hx.trans hE)
  have he : zpowers (x : max4Subgroup) = E :=
    eq_of_le_of_card_ge (zpowers_le.mpr x.property) (by rw [Nat.card_zpowers,ho,hE])
  rw [←he,zpowers_eq_closure,centralizer_closure]
  exact core_centralizer_card x (hEA x.property) ho

end Janko4.LocalStructure.SymmetricLinear.CubicCore
