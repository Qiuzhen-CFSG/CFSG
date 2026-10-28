module
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.NoFF
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.OverlapExtensions.Coordinates
public import Theory.Representation.BinaryOffender.PermutationConjugacy
-- Intentional internal certificate split: only the proved native implementer
-- and its original-generator characterization are accessed through these imports.
import all CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient.Native
import all CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient.NativeMatrices

/-!
# Fixed vectors of elementary sixteens on the native Aut(M₁₂) heart

The three checked Sylow-generator matrices implement the actual automorphisms
on the binary ten-space. The eight outer involutions have a common elementary
centralizer of order sixteen in this Sylow group, and two displayed independent
vectors are fixed by it. The inner rank bound and Sylow conjugacy therefore
supply at least two fixed dimensions for every elementary sixteen.

Only two fixed vectors are needed; no exhaustive vector-rank computation is
used. The finite identities use the existing ATLAS degree-24 coordinates and
are checked by the kernel. The internal imports above keep the native
implementer certificate coupled to its owning implementation without widening
that module's public API.

Source: Aschbacher–Smith G.11.7, printed p.367, and H.11.1, pp.392–393;
ATLAS M12d2G1-p24B0 attribution is retained in Extension.Seeds.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient.ElementaryFixed
open Subgroup Representation Representation.BinaryOffender Sporadic.Mathieu
open M12ExceptionalExtension OverlapExtensions
open scoped IsMulCommutative

private theorem embedding_block (x : M12) (i : Fin 12) :
    (innerModel.embedding x).val (blockLabel i) = blockLabel (x.val i) := by
  let f := blockRestriction.comp innerModel.equiv.toMonoidHom
  have hA : originalA ∈ f.eqLocus (MonoidHom.id M12) := by
    change blockRestriction (innerModel.equiv originalA) = originalA
    have he : innerModel.equiv originalA = ⟨innerA,subset_closure (by simp)⟩ :=
      Subtype.ext innerModel.embedding_originalA
    rw [he,blockRestriction_innerA]
  have hB : originalB ∈ f.eqLocus (MonoidHom.id M12) := by
    change blockRestriction (innerModel.equiv originalB) = originalB
    have he : innerModel.equiv originalB = ⟨innerB,subset_closure (by simp)⟩ :=
      Subtype.ext innerModel.embedding_originalB
    rw [he,blockRestriction_innerB]
  have ht := original_pair_generates (f.eqLocus (MonoidHom.id M12)) hA hB
  have hx : f x = x := show x ∈ f.eqLocus (MonoidHom.id M12) from ht.symm ▸ mem_top x
  have he := blockRestriction_spec (innerModel.equiv x) i
  change (innerModel.embedding x).val (blockLabel i) = _ at he
  exact he.trans (congrArg (fun y : M12 => blockLabel (y.val i)) hx)

private def perm00 : Equiv.Perm (Fin 12) where
  toFun := ![0, 3, 2, 1, 8, 6, 5, 11, 4, 9, 10, 7]
  invFun := ![0, 3, 2, 1, 8, 6, 5, 11, 4, 9, 10, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def perm01 : Equiv.Perm (Fin 12) where
  toFun := ![11, 9, 3, 10, 7, 1, 0, 8, 4, 5, 2, 6]
  invFun := ![6, 5, 10, 2, 8, 9, 11, 4, 7, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def perm10 : Equiv.Perm (Fin 12) where
  toFun := ![1, 0, 2, 3, 7, 5, 8, 4, 6, 10, 9, 11]
  invFun := ![1, 0, 2, 3, 7, 5, 8, 4, 6, 10, 9, 11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def perm11 : Equiv.Perm (Fin 12) where
  toFun := ![1, 8, 4, 9, 5, 2, 3, 10, 0, 6, 11, 7]
  invFun := ![8, 0, 5, 6, 2, 4, 9, 11, 1, 3, 7, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def perm20 : Equiv.Perm (Fin 12) where
  toFun := ![6, 4, 2, 10, 1, 11, 0, 7, 8, 9, 3, 5]
  invFun := ![6, 4, 2, 10, 1, 11, 0, 7, 8, 9, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def perm21 : Equiv.Perm (Fin 12) where
  toFun := ![4, 0, 10, 9, 1, 8, 3, 5, 7, 6, 11, 2]
  invFun := ![1, 4, 11, 6, 0, 7, 9, 8, 5, 3, 2, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def conjugatePerm (i : Fin 3) (j : Fin 2) : Equiv.Perm (Fin 12) :=
  ![![perm00,perm01],![perm10,perm11],![perm20,perm21]] i j

private theorem conjugate_block : ∀ i : Fin 3, ∀ j : Fin 2, ∀ k : Fin 12,
    (Overlap.generatorPerm i * (if j=0 then innerAPerm else innerBPerm) *
      (Overlap.generatorPerm i)⁻¹) (blockLabel k) = blockLabel (conjugatePerm i j k) := by
  decide +kernel

private theorem original_action (i : Fin 3) (j : Fin 2) :
    (automorphismEquiv (Overlap.generator i).val (NativeMatrices.original j)).val =
      conjugatePerm i j := by
  apply Equiv.ext
  intro k
  apply blockLabel_injective
  rw [←embedding_block]
  have he := NativeMatrices.embedding_action (Overlap.generator i).val (NativeMatrices.original j)
  have hg : innerModel.embedding (NativeMatrices.original j) =
      if j=0 then innerA else innerB := by
    simp only [NativeMatrices.original]
    split_ifs <;> simp only [innerModel.embedding_originalA,innerModel.embedding_originalB]
  rw [he,hg]
  have hp := Overlap.generator_val i
  change ((Overlap.generator i).val.val *
    (if j=0 then innerA else innerB).val * ((Overlap.generator i).val.val)⁻¹) (blockLabel k) = _
  rw [hp]
  convert conjugate_block i j k using 1
  split_ifs <;> rfl

private def rows : Fin 3 → Fin 10 → ℕ := ![![384, 272, 768, 258, 288, 264, 256, 257, 767, 260],
  ![613, 489, 391, 976, 682, 846, 246, 316, 819, 91],
  ![9, 40, 12, 8, 1015, 10, 72, 520, 264, 136]]
private def inverseRows : Fin 3 → Fin 10 → ℕ := ![![192, 72, 576, 96, 66, 80, 959, 65, 64, 68],
  ![613, 489, 391, 976, 682, 846, 246, 316, 819, 91],
  ![9, 40, 12, 8, 1015, 10, 72, 520, 264, 136]]
private def matrix (i : Fin 3) : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  fun j k => if (rows i j).testBit k.val then 1 else 0
private def inverseMatrix (i : Fin 3) : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  fun j k => if (inverseRows i j).testBit k.val then 1 else 0
private theorem inverse_left : ∀ i, inverseMatrix i * matrix i = 1 := by decide +kernel
private theorem inverse_right : ∀ i, matrix i * inverseMatrix i = 1 := by decide +kernel
private def coordinateEquiv (i : Fin 3) : Coordinates ≃ₗ[ZMod 2] Coordinates :=
  LinearEquiv.ofLinearMap (matrix i).mulVecLin (inverseMatrix i).mulVecLin
    (by rw [← Matrix.mulVecLin_mul,inverse_right,Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul,inverse_left,Matrix.mulVecLin_one])
private theorem intertwines_basis : ∀ i j, ∀ k : Fin 10,
    (matrix i).mulVecLin (action (if j=0 then m12GeneratorA else m12GeneratorB) (Pi.single k 1)) =
    action (conjugatePerm i j) ((matrix i).mulVecLin (Pi.single k 1)) := by decide +kernel
private theorem coordinate_intertwines (i : Fin 3) (j : Fin 2) (v : Coordinates) :
    coordinateEquiv i (coordinateRepresentation (NativeMatrices.original j) v) =
      action (conjugatePerm i j) (coordinateEquiv i v) := by
  have he : (matrix i).mulVecLin.comp
      (action (if j=0 then m12GeneratorA else m12GeneratorB)) =
      (action (conjugatePerm i j)).comp (matrix i).mulVecLin := by
    apply LinearMap.pi_ext
    intro k x
    have hx : (Pi.single k x : Coordinates) = x • Pi.single k 1 := by
      ext l
      simp [Pi.single_apply]
    rw [hx]
    simp only [map_smul,LinearMap.comp_apply,intertwines_basis]
  have hp : (NativeMatrices.original j).val = if j=0 then m12GeneratorA else m12GeneratorB := by
    simp only [NativeMatrices.original]
    split_ifs <;> rfl
  change (matrix i).mulVecLin (action (NativeMatrices.original j).val v) = _
  rw [hp]
  exact congrArg (fun f : Module.End (ZMod 2) Coordinates => f v) he
private def heart (i : Fin 3) : M12Heart ≃ₗ[ZMod 2] M12Heart :=
  M12Calculations.heartEquiv.symm.trans ((coordinateEquiv i).trans M12Calculations.heartEquiv)
private theorem heart_intertwines (i : Fin 3) (j : Fin 2) (v : M12Heart) :
    heart i (m12HeartRepresentation (NativeMatrices.original j) v) =
      m12HeartRepresentation (automorphismEquiv (Overlap.generator i).val (NativeMatrices.original j))
        (heart i v) := by
  obtain ⟨u,rfl⟩ := M12Calculations.heartEquiv.surjective v
  have hh (g : M12) (w : Coordinates) : m12HeartRepresentation g (M12Calculations.heartEquiv w) =
      M12Calculations.heartEquiv (coordinateRepresentation g w) :=
    (M12Calculations.heartEquiv_action g.val w).symm
  simp only [hh,heart,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]
  rw [coordinate_intertwines]
  change M12Calculations.heartEquiv (action (conjugatePerm i j) (coordinateEquiv i u)) =
    M12Calculations.heartEquiv
      (action (automorphismEquiv (Overlap.generator i).val (NativeMatrices.original j)).val (coordinateEquiv i u))
  rw [original_action]

private def carrierAction : Representation (ZMod 2) Carrier M12Heart :=
  automorphismRepresentation.comp automorphismEquiv.toMonoidHom
private theorem generator_action (i : Fin 3) (u : Coordinates) :
    carrierAction (Overlap.generator i).val (M12Calculations.heartEquiv u) =
      M12Calculations.heartEquiv ((matrix i).mulVecLin u) := by
  have he := heart_intertwiner_unique (automorphismEquiv (Overlap.generator i).val)
    (implementer _) (heart i) (implementer_spec _)
    (intertwines_of_original _ _ (heart_intertwines i))
  change implementer (automorphismEquiv (Overlap.generator i).val) (M12Calculations.heartEquiv u) = _
  rw [he]
  simp only [heart,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]
  rfl

private def vector (i : Fin 2) : Coordinates :=
  fun j => if (![63,349] i).testBit j.val then 1 else 0
private def wordAction : List (Fin 3) → Coordinates → Coordinates
  | [],v => v
  | j::w,v => (matrix j).mulVecLin (wordAction w v)
set_option maxRecDepth 1000 in
private theorem element_action (i : Fin 128) (u : Coordinates) :
    carrierAction (Overlap.element i).val (M12Calculations.heartEquiv u) =
      M12Calculations.heartEquiv (wordAction (Data.overlapWords i) u) := by
  change carrierAction (overlap.subtype (FiniteWords.evaluate Overlap.generator (Data.overlapWords i))) _ = _
  generalize Data.overlapWords i = w
  induction w with
  | nil => simp only [FiniteWords.evaluate,map_one,Module.End.one_apply,wordAction]
  | cons j w ih =>
    simp only [FiniteWords.evaluate,map_mul,Module.End.mul_apply,wordAction]
    rw [ih]
    exact generator_action j (wordAction w u)

private def perm (i : Fin 128) : Equiv.Perm (Fin 24) :=
  FiniteWords.evaluate Overlap.generatorPerm (Data.overlapWords i)
private def outerIndices : Fin 8 → Fin 128 := ![2,12,14,45,70,103,113,127]
private def centralIndices : Fin 16 → Fin 128 := ![0,2,4,12,14,28,45,70,73,97,98,103,113,124,125,127]
private theorem outer_coverage : ∀ i : Fin 128,
    perm i ^ 2 = 1 →
    (∃ j : Fin 12, generatorA (perm i (blockLabel 0)) = blockLabel j) →
      ∃ k : Fin 8, i = outerIndices k := by decide +kernel
private theorem commuting_coverage : ∀ k : Fin 8, ∀ j : Fin 128,
    perm j * perm (outerIndices k) = perm (outerIndices k) * perm j →
      ∃ l : Fin 16, j = centralIndices l := by decide +kernel
private theorem vectors_fixed : ∀ k : Fin 16, ∀ j : Fin 2,
    wordAction (Data.overlapWords (centralIndices k)) (vector j) = vector j := by decide +kernel
private theorem vectors_nonzero : ∀ j : Fin 2, vector j ≠ 0 := by decide +kernel
private theorem vectors_distinct : vector 0 ≠ vector 1 := by decide +kernel

private theorem outer_marker (x : Carrier) (hx : x ∉ M12ExceptionalExtension.inner) :
    ∃ j : Fin 12, generatorA (x.val (blockLabel 0)) = blockLabel j := by
  have hp : OuterInvolutions.seed * x ∈ M12ExceptionalExtension.inner :=
    (mul_mem_iff_of_index_two (H := M12ExceptionalExtension.inner) (a := OuterInvolutions.seed) (b := x)
      inner_index).mpr (iff_of_false OuterInvolutions.seed_not_mem_inner hx)
  let y : M12ExceptionalExtension.inner := ⟨OuterInvolutions.seed*x,hp⟩
  refine ⟨(blockRestriction y).val 0,?_⟩
  have hb := blockRestriction_spec y 0
  have hval : y.val.val = generatorA*x.val := rfl
  rw [hval,Equiv.Perm.mul_apply] at hb
  exact hb

private theorem fixed_vectors_of_overlap (A : Subgroup Carrier)
    [IsElementaryAbelian 2 A] (hA : A ≤ overlap) (hx : ¬ A ≤ M12ExceptionalExtension.inner) :
    ∀ j : Fin 2, M12Calculations.heartEquiv (vector j) ∈ fixedSpace carrierAction A := by
  obtain ⟨x,hxA,hxo⟩ := SetLike.not_le_iff_exists.mp hx
  obtain ⟨i,hi⟩ := Overlap.element_surjective ⟨x,hA hxA⟩
  have he : (Overlap.element i : Carrier) = x := congrArg Subtype.val hi
  have hp : perm i ^ 2 = 1 := by
    have hh := elemPow_eq_one_of_isElementaryAbelian (p := 2) x hxA
    rw [←he] at hh
    simpa only [Subgroup.coe_pow,Subgroup.coe_one,Overlap.element_val,perm]
      using congrArg Subtype.val hh
  have hm : ∃ j : Fin 12, generatorA (perm i (blockLabel 0)) = blockLabel j := by
    simpa only [←he,Overlap.element_val,perm] using outer_marker x hxo
  obtain ⟨k,rfl⟩ := outer_coverage i hp hm
  intro j y
  obtain ⟨l,hl⟩ := Overlap.element_surjective ⟨y,hA y.property⟩
  have hey : (Overlap.element l : Carrier) = y := congrArg Subtype.val hl
  have hc : perm l * perm (outerIndices k) = perm (outerIndices k) * perm l := by
    have hh : (y : Carrier)*x = x*(y : Carrier) := congrArg Subtype.val
      (mul_comm y (⟨x,hxA⟩ : A))
    rw [←he,←hey] at hh
    simpa only [Subgroup.coe_mul,Overlap.element_val,perm] using congrArg Subtype.val hh
  obtain ⟨q,rfl⟩ := commuting_coverage k l hc
  change carrierAction (y : Carrier) (M12Calculations.heartEquiv (vector j)) = _
  rw [←hey,element_action,vectors_fixed]

private theorem inner_rank : primeRank 2 M12ExceptionalExtension.inner ≤ 3 := by
  rw [←Theory.GroupTheory.primeRank_equiv 2 innerModel.equiv]
  exact m12_twoRank_le_three

private theorem not_le_inner (A : Subgroup Carrier) [IsElementaryAbelian 2 A]
    (hc : Nat.card A = 16) : ¬ A ≤ M12ExceptionalExtension.inner := by
  intro hi
  have hE : IsElementaryAbelian 2 (A.subgroupOf M12ExceptionalExtension.inner) := IsElementaryAbelian.subgroupOf hi
  have hcard := (primeRank_le_iff_elementary_card_le M12ExceptionalExtension.inner).mp inner_rank (A.subgroupOf M12ExceptionalExtension.inner) hE
  rw [Nat.card_congr (subgroupOfEquivOfLe hi).toEquiv,hc] at hcard
  norm_num at hcard

private theorem two_le_fixed_of_overlap (A : Subgroup Carrier)
    [IsElementaryAbelian 2 A] (hA : A ≤ overlap) (hc : Nat.card A = 16) :
    2 ≤ Module.finrank (ZMod 2) (fixedSpace carrierAction A) := by
  have hfix := fixed_vectors_of_overlap A hA (not_le_inner A hc)
  let vec : Fin 3 → Coordinates := ![0,vector 0,vector 1]
  have hi : Function.Injective vec := by decide +kernel
  have hf (i : Fin 3) : M12Calculations.heartEquiv (vec i) ∈ fixedSpace carrierAction A := by
    fin_cases i
    · change M12Calculations.heartEquiv (0 : Coordinates) ∈ _
      rw [map_zero]
      exact (fixedSpace carrierAction A).zero_mem
    · exact hfix 0
    · exact hfix 1
  let f : Fin 3 → fixedSpace carrierAction A := fun i => ⟨_,hf i⟩
  have hfi : Function.Injective f := fun i j he =>
    hi (M12Calculations.heartEquiv.injective (congrArg (fun z : fixedSpace carrierAction A => z.val) he))
  have hcard := Nat.card_le_card_of_injective f hfi
  rw [Nat.card_fin,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hcard
  by_contra hn
  have hh := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show Module.finrank (ZMod 2) (fixedSpace carrierAction A) ≤ 1 by omega)
  norm_num at hh
  omega

private theorem two_le_fixed_carrier (A : Subgroup Carrier)
    [IsElementaryAbelian 2 A] (hc : Nat.card A = 16) :
    2 ≤ Module.finrank (ZMod 2) (fixedSpace carrierAction A) := by
  obtain ⟨P,hP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Carrier P VerifiedPair.commonSylow
  let C := A.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map _
  have hC : C ≤ overlap := by
    rintro _ ⟨a,ha,rfl⟩
    have hh := (P.equivSMul g ⟨a,hP ha⟩).property
    change MulAut.conj g a ∈ (g • P : Sylow 2 Carrier) at hh
    rw [hg] at hh
    exact hh
  have hcC : Nat.card C = 16 :=
    (Nat.card_congr ((MulAut.conj g).subgroupMap A).toEquiv).symm.trans hc
  rw [(fixedSpaceConjEquiv carrierAction A g).finrank_eq]
  exact two_le_fixed_of_overlap C hC hcC

/-- Every elementary sixteen in the genuine full automorphism group fixes
at least two dimensions of the binary ten-dimensional heart. -/
theorem two_le_fixed_of_sixteen (A : Subgroup (MulAut M12))
    [IsElementaryAbelian 2 A] (hc : Nat.card A = 16) :
    2 ≤ Module.finrank (ZMod 2) (fixedSpace automorphismRepresentation A) := by
  let C := A.map automorphismEquiv.symm.toMonoidHom
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map _
  have hcC : Nat.card C = 16 :=
    (Nat.card_congr (automorphismEquiv.symm.subgroupMap A).toEquiv).symm.trans hc
  have he : fixedSpace automorphismRepresentation A = fixedSpace carrierAction C := by
    rw [←fixedSpace_comp_map]
    congr 1
    apply MonoidHom.ext
    intro a
    apply LinearMap.ext
    intro w
    change automorphismRepresentation a w = automorphismRepresentation
      (automorphismEquiv (automorphismEquiv.symm a)) w
    rw [automorphismEquiv.apply_symm_apply]
  rw [he]
  exact two_le_fixed_carrier C hcC

end CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient.ElementaryFixed
