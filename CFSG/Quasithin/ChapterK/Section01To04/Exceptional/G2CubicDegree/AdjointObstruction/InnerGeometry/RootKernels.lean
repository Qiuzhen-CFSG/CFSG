module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.AdjointObstruction.Inputs

/-!
# Pointwise kernels on the two root fixed spaces

Eight explicit fixed derivations constrain every element fixing the root's
fixed space pointwise. Their commutation equations force a three-parameter
matrix on the split octonions. Preserving trace and one basis product fixes
two parameters, so the remaining field entry injects the kernel into F.
The argument uses the actual derivation action and the actual octonion product;
the subgroup remains the pointwise kernel inside the involution centralizer.

The entry equations and short elimination certificates below are checked over
an arbitrary characteristic-two field. No finite enumeration is used in the
proof. Separating the sparse derivation formulas from the entry equations
avoids repeated expansion of the fourteen-parameter derivation formula.

Source: Guralnick–Malle, Classification of 2F-modules II, Proposition 8.2,
manuscript pp.53–54. These coordinate calculations supply its bound q for
root fixed-space kernels. The underlying Wilson root and octonion formulas
are the attributed ATLAS ports; see LICENSES/ATLAS.txt.
-/

public section
open Atlas.G2 Atlas.SplitOctonion
open Atlas.G2.Restricted.Adjoint.Coordinates
open Representation Representation.BinaryOffender Subgroup
open CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree
attribute [local instance] ZMod.algebra
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.AdjointObstruction.InnerGeometry
variable {F : Type*} [Field F] [CharP F 2]
private def paramsA (k : Fin 8) : Fin 14 → F :=
  ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, Pi.single 3 1,
    Pi.single 4 1, Pi.single 7 1, Pi.single 12 1, Pi.single 6 1 + Pi.single 13 1] k

omit [CharP F 2] in
private theorem paramsA_constraints (k : Fin 8) :
    paramsA (F := F) k 5 = 0 ∧ paramsA (F := F) k 8 = 0 ∧ paramsA (F := F) k 9 = 0 ∧
      paramsA (F := F) k 10 = 0 ∧ paramsA (F := F) k 11 = 0 ∧ paramsA (F := F) k 6 = paramsA (F := F) k 13 := by
  fin_cases k <;> simp [paramsA]

private theorem paramsA_fixed (k : Fin 8) :
    action F (rootA 1) (paramsA k) = paramsA (F := F) k := by
  rw [action_rootA]
  obtain ⟨h5, h8, h9, h10, h11, h6⟩ := paramsA_constraints (F := F) k
  ext i
  fin_cases i <;> simp [h5, h8, h9, h10, h11, h6, CharTwo.add_self_eq_zero,
    add_assoc]

private theorem fixed_commutes (t g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) t)
    (p : Fin 14 → F) (hp : action F t p = p) (x : Carrier F) :
    g.val (endomorphism p x) = endomorphism p (g.val x) := by
  have hf : fromParams F p ∈ fixedSpace (adjointBinary F) (zpowers t) := by
    rw [mem_fixedSpace_zpowers_iff]
    apply (equiv F).injective
    change equiv F (Restricted.Adjoint.action F t (fromParams F p)) = equiv F (fromParams F p)
    have he := (repEquiv F).isIntertwining t (fromParams F p)
    change equiv F (Restricted.Adjoint.action F t (fromParams F p)) =
      action F t (equiv F (fromParams F p)) at he
    rw [he]
    simpa only [equiv_apply, params_fromParams] using hp
  have he := hg.2 _ hf
  have hh := congrArg (fun D : Restricted.Adjoint.Space F => D.val (g.val x)) he
  change g.val (endomorphism p ((g⁻¹).val (g.val x))) = endomorphism p (g.val x) at hh
  simpa only [show (g⁻¹).val (g.val x) = x from g.val.symm_apply_apply x] using hh

private def entries (g : Model F) (i j : Fin 8) : F := g.val (basisVector j) i

omit [CharP F 2] in
private theorem linear_apply (g : Model F) (v : Carrier F) (i : Fin 8) :
    g.val v i = ∑ j : Fin 8, v j * entries g i j := by
  have he : v = ∑ j : Fin 8, v j • basisVector j := by
    ext k
    simp [basisVector, Pi.single_apply]
  conv_lhs => rw [he]
  simp [map_sum, entries]

omit [CharP F 2] in
private theorem commute_entries (g : Model F) (p : Fin 14 → F)
    (hg : ∀ x, g.val (endomorphism p x) = endomorphism p (g.val x)) (i j : Fin 8) :
    (∑ l : Fin 8, endomorphism p (basisVector j) l * entries g i l) =
      endomorphism p (fun l => entries g l j) i := by
  rw [← linear_apply]
  exact congrFun (hg (basisVector j)) i

private def paramsC (k : Fin 8) : Fin 14 → F :=
  ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, Pi.single 3 1,
    Pi.single 5 1, Pi.single 6 1, Pi.single 4 1 + Pi.single 12 1,
    Pi.single 7 1 + Pi.single 11 1] k

omit [CharP F 2] in
private theorem paramsC_constraints (k : Fin 8) :
    paramsC (F := F) k 8 = 0 ∧ paramsC (F := F) k 9 = 0 ∧
      paramsC (F := F) k 10 = 0 ∧ paramsC (F := F) k 13 = 0 ∧
      paramsC (F := F) k 4 = paramsC (F := F) k 12 ∧
      paramsC (F := F) k 7 = paramsC (F := F) k 11 := by
  fin_cases k <;> simp [paramsC]

private theorem paramsC_fixed (k : Fin 8) :
    action F (rootC 1) (paramsC k) = paramsC k := by
  rw [action_rootC]
  obtain ⟨h8,h9,h10,h13,h4,h7⟩ := paramsC_constraints (F := F) k
  ext i
  fin_cases i <;> simp [h8,h9,h10,h13,h4,h7,CharTwo.add_self_eq_zero, add_assoc]
omit [CharP F 2] in
private theorem derivationA_0 (x : Carrier F) :
    endomorphism (paramsA (0 : Fin 8)) x = ![x 6, x 7, 0, 0, 0, 0, 0, 0] := by
  ext i
  fin_cases i <;> simp [paramsA, endomorphism]

omit [CharP F 2] in
private theorem derivationA_1 (x : Carrier F) :
    endomorphism (paramsA (1 : Fin 8)) x = ![x 5, 0, x 7, 0, 0, 0, 0, 0] := by
  ext i
  fin_cases i <;> simp [paramsA, endomorphism]

omit [CharP F 2] in
private theorem derivationA_2 (x : Carrier F) :
    endomorphism (paramsA (2 : Fin 8)) x = ![x 3 + x 4, x 5, x 6, x 7, x 7, 0, 0, 0] := by
  ext i
  fin_cases i <;> simp [paramsA, endomorphism]

omit [CharP F 2] in
private theorem derivationA_3 (x : Carrier F) :
    endomorphism (paramsA (3 : Fin 8)) x = ![0, x 2, 0, 0, 0, x 6, 0, 0] := by
  ext i
  fin_cases i <;> simp [paramsA, endomorphism]

omit [CharP F 2] in
private theorem derivationA_4 (x : Carrier F) :
    endomorphism (paramsA (4 : Fin 8)) x = ![x 2, x 3 + x 4, 0, x 6, x 6, x 7, 0, 0] := by
  ext i
  fin_cases i <;> simp [paramsA, endomorphism]

omit [CharP F 2] in
private theorem derivationA_5 (x : Carrier F) :
    endomorphism (paramsA (5 : Fin 8)) x = ![x 1, 0, x 3 + x 4, x 5, x 5, 0, x 7, 0] := by
  ext i
  fin_cases i <;> simp [paramsA, endomorphism]

omit [CharP F 2] in
private theorem derivationA_6 (x : Carrier F) :
    endomorphism (paramsA (6 : Fin 8)) x = ![0, x 0, 0, x 2, x 2, x 3 + x 4, 0, x 6] := by
  ext i
  fin_cases i <;> simp [paramsA, endomorphism]

private theorem derivationA_7 (x : Carrier F) :
    endomorphism (paramsA (7 : Fin 8)) x = ![x 0, x 1, 0, 0, 0, 0, x 6, x 7] := by
  ext i
  fin_cases i <;> simp [paramsA, endomorphism, CharTwo.add_self_eq_zero]

private theorem equationA_0 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    0 = entries g 6 0 := by
  have h := commute_entries g (paramsA (0 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 0)) 0 0
  simp only [derivationA_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_1 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    0 = entries g 6 1 := by
  have h := commute_entries g (paramsA (0 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 0)) 0 1
  simp only [derivationA_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_2 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    0 = entries g 6 2 := by
  have h := commute_entries g (paramsA (0 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 0)) 0 2
  simp only [derivationA_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_3 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    0 = entries g 6 3 := by
  have h := commute_entries g (paramsA (0 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 0)) 0 3
  simp only [derivationA_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_4 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    0 = entries g 6 4 := by
  have h := commute_entries g (paramsA (0 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 0)) 0 4
  simp only [derivationA_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_5 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    0 = entries g 6 5 := by
  have h := commute_entries g (paramsA (0 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 0)) 0 5
  simp only [derivationA_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_6 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 0 0 = entries g 6 6 := by
  have h := commute_entries g (paramsA (0 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 0)) 0 6
  simp only [derivationA_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_7 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 0 1 = entries g 6 7 := by
  have h := commute_entries g (paramsA (0 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 0)) 0 7
  simp only [derivationA_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_8 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    0 = entries g 7 0 := by
  have h := commute_entries g (paramsA (0 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 0)) 1 0
  simp only [derivationA_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_9 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    0 = entries g 7 1 := by
  have h := commute_entries g (paramsA (0 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 0)) 1 1
  simp only [derivationA_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_10 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    0 = entries g 7 2 := by
  have h := commute_entries g (paramsA (0 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 0)) 1 2
  simp only [derivationA_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_11 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    0 = entries g 7 3 := by
  have h := commute_entries g (paramsA (0 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 0)) 1 3
  simp only [derivationA_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_12 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    0 = entries g 7 4 := by
  have h := commute_entries g (paramsA (0 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 0)) 1 4
  simp only [derivationA_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_13 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    0 = entries g 7 5 := by
  have h := commute_entries g (paramsA (0 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 0)) 1 5
  simp only [derivationA_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_14 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 1 0 = entries g 7 6 := by
  have h := commute_entries g (paramsA (0 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 0)) 1 6
  simp only [derivationA_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_15 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 1 1 = entries g 7 7 := by
  have h := commute_entries g (paramsA (0 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 0)) 1 7
  simp only [derivationA_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_16 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 2 0 = 0 := by
  have h := commute_entries g (paramsA (0 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 0)) 2 6
  simp only [derivationA_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_17 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 2 1 = 0 := by
  have h := commute_entries g (paramsA (0 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 0)) 2 7
  simp only [derivationA_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_18 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 3 0 = 0 := by
  have h := commute_entries g (paramsA (0 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 0)) 3 6
  simp only [derivationA_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_19 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 3 1 = 0 := by
  have h := commute_entries g (paramsA (0 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 0)) 3 7
  simp only [derivationA_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_20 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 4 0 = 0 := by
  have h := commute_entries g (paramsA (0 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 0)) 4 6
  simp only [derivationA_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_21 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 4 1 = 0 := by
  have h := commute_entries g (paramsA (0 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 0)) 4 7
  simp only [derivationA_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_22 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 5 0 = 0 := by
  have h := commute_entries g (paramsA (0 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 0)) 5 6
  simp only [derivationA_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_23 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 5 1 = 0 := by
  have h := commute_entries g (paramsA (0 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 0)) 5 7
  simp only [derivationA_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_30 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    0 = entries g 5 2 := by
  have h := commute_entries g (paramsA (1 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 1)) 0 2
  simp only [derivationA_1] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_31 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    0 = entries g 5 3 := by
  have h := commute_entries g (paramsA (1 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 1)) 0 3
  simp only [derivationA_1] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_32 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    0 = entries g 5 4 := by
  have h := commute_entries g (paramsA (1 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 1)) 0 4
  simp only [derivationA_1] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_33 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 0 0 = entries g 5 5 := by
  have h := commute_entries g (paramsA (1 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 1)) 0 5
  simp only [derivationA_1] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_34 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    0 = entries g 5 6 := by
  have h := commute_entries g (paramsA (1 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 1)) 0 6
  simp only [derivationA_1] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_35 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 0 2 = entries g 5 7 := by
  have h := commute_entries g (paramsA (1 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 1)) 0 7
  simp only [derivationA_1] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_36 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 1 0 = 0 := by
  have h := commute_entries g (paramsA (1 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 1)) 1 5
  simp only [derivationA_1] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_37 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 1 2 = 0 := by
  have h := commute_entries g (paramsA (1 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 1)) 1 7
  simp only [derivationA_1] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_45 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 2 2 = entries g 7 7 := by
  have h := commute_entries g (paramsA (1 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 1)) 2 7
  simp only [derivationA_1] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_47 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 3 2 = 0 := by
  have h := commute_entries g (paramsA (1 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 1)) 3 7
  simp only [derivationA_1] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_49 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 4 2 = 0 := by
  have h := commute_entries g (paramsA (1 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 1)) 4 7
  simp only [derivationA_1] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_59 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 0 0 = entries g 3 3 + entries g 4 3 := by
  have h := commute_entries g (paramsA (2 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 2)) 0 3
  simp only [derivationA_2] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_60 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 0 0 = entries g 3 4 + entries g 4 4 := by
  have h := commute_entries g (paramsA (2 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 2)) 0 4
  simp only [derivationA_2] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_61 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 0 1 = entries g 3 5 + entries g 4 5 := by
  have h := commute_entries g (paramsA (2 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 2)) 0 5
  simp only [derivationA_2] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_62 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 0 2 = entries g 3 6 + entries g 4 6 := by
  have h := commute_entries g (paramsA (2 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 2)) 0 6
  simp only [derivationA_2] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_63 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 0 3 + entries g 0 4 = entries g 3 7 + entries g 4 7 := by
  have h := commute_entries g (paramsA (2 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 2)) 0 7
  simp only [derivationA_2] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_69 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 1 1 = entries g 5 5 := by
  have h := commute_entries g (paramsA (2 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 2)) 1 5
  simp only [derivationA_2] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_71 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 1 3 + entries g 1 4 = entries g 5 7 := by
  have h := commute_entries g (paramsA (2 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 2)) 1 7
  simp only [derivationA_2] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_79 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 2 3 + entries g 2 4 = entries g 6 7 := by
  have h := commute_entries g (paramsA (2 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 2)) 2 7
  simp only [derivationA_2] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_87 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 3 3 + entries g 3 4 = entries g 7 7 := by
  have h := commute_entries g (paramsA (2 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 2)) 3 7
  simp only [derivationA_2] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_111 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 0 1 = 0 := by
  have h := commute_entries g (paramsA (3 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 3)) 0 2
  simp only [derivationA_3] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_112 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 0 5 = 0 := by
  have h := commute_entries g (paramsA (3 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 3)) 0 6
  simp only [derivationA_3] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_116 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    0 = entries g 2 3 := by
  have h := commute_entries g (paramsA (3 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 3)) 1 3
  simp only [derivationA_3] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_118 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    0 = entries g 2 5 := by
  have h := commute_entries g (paramsA (3 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 3)) 1 5
  simp only [derivationA_3] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_119 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 1 5 = entries g 2 6 := by
  have h := commute_entries g (paramsA (3 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 3)) 1 6
  simp only [derivationA_3] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_120 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    0 = entries g 2 7 := by
  have h := commute_entries g (paramsA (3 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 3)) 1 7
  simp only [derivationA_3] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_124 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 3 5 = 0 := by
  have h := commute_entries g (paramsA (3 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 3)) 3 6
  simp only [derivationA_3] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_145 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 0 3 + entries g 0 4 = entries g 2 6 := by
  have h := commute_entries g (paramsA (4 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 4)) 0 6
  simp only [derivationA_4] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_197 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 0 2 = entries g 1 3 := by
  have h := commute_entries g (paramsA (5 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 5)) 0 3
  simp only [derivationA_5] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_198 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 0 2 = entries g 1 4 := by
  have h := commute_entries g (paramsA (5 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 5)) 0 4
  simp only [derivationA_5] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_200 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    0 = entries g 1 6 := by
  have h := commute_entries g (paramsA (5 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 5)) 0 6
  simp only [derivationA_5] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_201 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 0 6 = entries g 1 7 := by
  have h := commute_entries g (paramsA (5 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 5)) 0 7
  simp only [derivationA_5] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_222 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 3 6 = entries g 5 7 := by
  have h := commute_entries g (paramsA (5 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 5)) 3 7
  simp only [derivationA_5] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_250 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 0 3 + entries g 0 4 = 0 := by
  have h := commute_entries g (paramsA (6 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 6)) 0 2
  simp only [derivationA_6] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_253 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 0 7 = 0 := by
  have h := commute_entries g (paramsA (6 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 6)) 0 6
  simp only [derivationA_6] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_257 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 1 5 = entries g 0 3 := by
  have h := commute_entries g (paramsA (6 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 6)) 1 3
  simp only [derivationA_6] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationA_273 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) :
    entries g 3 7 = entries g 2 6 := by
  have h := commute_entries g (paramsA (6 : Fin 8))
    (fixed_commutes (rootA 1) g hg _ (paramsA_fixed 6)) 3 6
  simp only [derivationA_6] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

set_option linter.unusedSimpArgs false in
private theorem commutantA_row0 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) (j : Fin 8) :
    entries g 0 j = (![entries g 0 0, 0, 0, 0, 0, 0, entries g 0 6, 0] : Fin 8 → F) j := by
  fin_cases j
  · rfl
  · change entries g 0 1 = 0
    linear_combination (norm := ring_nf) (equationA_111 g hg)
  · change entries g 0 2 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_35 g hg) + (equationA_71 g hg) + (equationA_197 g hg) + (equationA_198 g hg)
  · change entries g 0 3 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_119 g hg) + (equationA_145 g hg) + (equationA_250 g hg) + (equationA_257 g hg)
  · change entries g 0 4 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_119 g hg) + (equationA_145 g hg) + (equationA_257 g hg)
  · change entries g 0 5 = 0
    linear_combination (norm := ring_nf) (equationA_112 g hg)
  · rfl
  · change entries g 0 7 = 0
    linear_combination (norm := ring_nf) (equationA_253 g hg)

set_option linter.unusedSimpArgs false in
private theorem commutantA_row1 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) (j : Fin 8) :
    entries g 1 j = (![0, entries g 0 0, 0, 0, 0, 0, 0, entries g 0 6] : Fin 8 → F) j := by
  fin_cases j
  · change entries g 1 0 = 0
    linear_combination (norm := ring_nf) (equationA_36 g hg)
  · change entries g 1 1 = entries g 0 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_33 g hg) + (equationA_69 g hg)
  · change entries g 1 2 = 0
    linear_combination (norm := ring_nf) (equationA_37 g hg)
  · change entries g 1 3 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_35 g hg) + (equationA_71 g hg) + (equationA_198 g hg)
  · change entries g 1 4 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_35 g hg) + (equationA_71 g hg) + (equationA_197 g hg)
  · change entries g 1 5 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_119 g hg) + (equationA_145 g hg) + (equationA_250 g hg)
  · change entries g 1 6 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_200 g hg)
  · change entries g 1 7 = entries g 0 6
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_201 g hg)

set_option linter.unusedSimpArgs false in
private theorem commutantA_row2 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) (j : Fin 8) :
    entries g 2 j = (![0, 0, entries g 0 0, 0, 0, 0, 0, 0] : Fin 8 → F) j := by
  fin_cases j
  · change entries g 2 0 = 0
    linear_combination (norm := ring_nf) (equationA_16 g hg)
  · change entries g 2 1 = 0
    linear_combination (norm := ring_nf) (equationA_17 g hg)
  · change entries g 2 2 = entries g 0 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_15 g hg) + (equationA_33 g hg) + (equationA_45 g hg) + (equationA_69 g hg)
  · change entries g 2 3 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_116 g hg)
  · change entries g 2 4 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_7 g hg) + (equationA_79 g hg) + (equationA_111 g hg) + (equationA_116 g hg)
  · change entries g 2 5 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_118 g hg)
  · change entries g 2 6 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_145 g hg) + (equationA_250 g hg)
  · change entries g 2 7 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_120 g hg)

set_option linter.unusedSimpArgs false in
private theorem commutantA_row3 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) (j : Fin 8) :
    entries g 3 j = (![0, 0, 0, entries g 3 3, entries g 0 0 + entries g 3 3, 0, 0, 0] : Fin 8 → F) j := by
  fin_cases j
  · change entries g 3 0 = 0
    linear_combination (norm := ring_nf) (equationA_18 g hg)
  · change entries g 3 1 = 0
    linear_combination (norm := ring_nf) (equationA_19 g hg)
  · change entries g 3 2 = 0
    linear_combination (norm := ring_nf) (equationA_47 g hg)
  · rfl
  · change entries g 3 4 = entries g 0 0 + entries g 3 3
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_15 g hg) + (equationA_33 g hg) + (equationA_69 g hg) + (equationA_87 g hg)
  · change entries g 3 5 = 0
    linear_combination (norm := ring_nf) (equationA_124 g hg)
  · change entries g 3 6 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_71 g hg) + (equationA_197 g hg) + (equationA_198 g hg) + (equationA_222 g hg)
  · change entries g 3 7 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_145 g hg) + (equationA_250 g hg) + (equationA_273 g hg)

set_option linter.unusedSimpArgs false in
private theorem commutantA_row4 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) (j : Fin 8) :
    entries g 4 j = (![0, 0, 0, entries g 0 0 + entries g 3 3, entries g 3 3, 0, 0, 0] : Fin 8 → F) j := by
  fin_cases j
  · change entries g 4 0 = 0
    linear_combination (norm := ring_nf) (equationA_20 g hg)
  · change entries g 4 1 = 0
    linear_combination (norm := ring_nf) (equationA_21 g hg)
  · change entries g 4 2 = 0
    linear_combination (norm := ring_nf) (equationA_49 g hg)
  · change entries g 4 3 = entries g 0 0 + entries g 3 3
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_59 g hg)
  · change entries g 4 4 = entries g 3 3
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_15 g hg) + (equationA_33 g hg) + (equationA_60 g hg) + (equationA_69 g hg) + (equationA_87 g hg)
  · change entries g 4 5 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_61 g hg) + (equationA_111 g hg) + (equationA_124 g hg)
  · change entries g 4 6 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_35 g hg) + (equationA_62 g hg) + (equationA_222 g hg)
  · change entries g 4 7 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_63 g hg) + (equationA_145 g hg) + (equationA_273 g hg)

set_option linter.unusedSimpArgs false in
private theorem commutantA_row5 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) (j : Fin 8) :
    entries g 5 j = (![0, 0, 0, 0, 0, entries g 0 0, 0, 0] : Fin 8 → F) j := by
  fin_cases j
  · change entries g 5 0 = 0
    linear_combination (norm := ring_nf) (equationA_22 g hg)
  · change entries g 5 1 = 0
    linear_combination (norm := ring_nf) (equationA_23 g hg)
  · change entries g 5 2 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_30 g hg)
  · change entries g 5 3 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_31 g hg)
  · change entries g 5 4 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_32 g hg)
  · change entries g 5 5 = entries g 0 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_33 g hg)
  · change entries g 5 6 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_34 g hg)
  · change entries g 5 7 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_71 g hg) + (equationA_197 g hg) + (equationA_198 g hg)

set_option linter.unusedSimpArgs false in
private theorem commutantA_row6 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) (j : Fin 8) :
    entries g 6 j = (![0, 0, 0, 0, 0, 0, entries g 0 0, 0] : Fin 8 → F) j := by
  fin_cases j
  · change entries g 6 0 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_0 g hg)
  · change entries g 6 1 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_1 g hg)
  · change entries g 6 2 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_2 g hg)
  · change entries g 6 3 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_3 g hg)
  · change entries g 6 4 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_4 g hg)
  · change entries g 6 5 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_5 g hg)
  · change entries g 6 6 = entries g 0 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_6 g hg)
  · change entries g 6 7 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_7 g hg) + (equationA_111 g hg)

set_option linter.unusedSimpArgs false in
private theorem commutantA_row7 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) (j : Fin 8) :
    entries g 7 j = (![0, 0, 0, 0, 0, 0, 0, entries g 0 0] : Fin 8 → F) j := by
  fin_cases j
  · change entries g 7 0 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_8 g hg)
  · change entries g 7 1 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_9 g hg)
  · change entries g 7 2 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_10 g hg)
  · change entries g 7 3 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_11 g hg)
  · change entries g 7 4 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_12 g hg)
  · change entries g 7 5 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_13 g hg)
  · change entries g 7 6 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_14 g hg) + (equationA_36 g hg)
  · change entries g 7 7 = entries g 0 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationA_15 g hg) + (equationA_33 g hg) + (equationA_69 g hg)

private theorem commutantA_entries (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) (i j : Fin 8) :
    entries g i j = (![
    ![entries g 0 0, 0, 0, 0, 0, 0, entries g 0 6, 0],
    ![0, entries g 0 0, 0, 0, 0, 0, 0, entries g 0 6],
    ![0, 0, entries g 0 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, entries g 3 3, entries g 0 0 + entries g 3 3, 0, 0, 0],
    ![0, 0, 0, entries g 0 0 + entries g 3 3, entries g 3 3, 0, 0, 0],
    ![0, 0, 0, 0, 0, entries g 0 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, entries g 0 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, entries g 0 0]
  ] : Fin 8 → Fin 8 → F) i j := by
  fin_cases i
  · exact commutantA_row0 g hg j
  · exact commutantA_row1 g hg j
  · exact commutantA_row2 g hg j
  · exact commutantA_row3 g hg j
  · exact commutantA_row4 g hg j
  · exact commutantA_row5 g hg j
  · exact commutantA_row6 g hg j
  · exact commutantA_row7 g hg j
omit [CharP F 2] in
private theorem derivationC_0 (x : Carrier F) :
    endomorphism (paramsC (0 : Fin 8)) x = ![x 6, x 7, 0, 0, 0, 0, 0, 0] := by
  ext i
  fin_cases i <;> simp [paramsC, endomorphism]

omit [CharP F 2] in
private theorem derivationC_1 (x : Carrier F) :
    endomorphism (paramsC (1 : Fin 8)) x = ![x 5, 0, x 7, 0, 0, 0, 0, 0] := by
  ext i
  fin_cases i <;> simp [paramsC, endomorphism]

omit [CharP F 2] in
private theorem derivationC_2 (x : Carrier F) :
    endomorphism (paramsC (2 : Fin 8)) x = ![x 3 + x 4, x 5, x 6, x 7, x 7, 0, 0, 0] := by
  ext i
  fin_cases i <;> simp [paramsC, endomorphism]

omit [CharP F 2] in
private theorem derivationC_3 (x : Carrier F) :
    endomorphism (paramsC (3 : Fin 8)) x = ![0, x 2, 0, 0, 0, x 6, 0, 0] := by
  ext i
  fin_cases i <;> simp [paramsC, endomorphism]

omit [CharP F 2] in
private theorem derivationC_4 (x : Carrier F) :
    endomorphism (paramsC (4 : Fin 8)) x = ![0, 0, x 1, 0, 0, 0, x 5, 0] := by
  ext i
  fin_cases i <;> simp [paramsC, endomorphism]

omit [CharP F 2] in
private theorem derivationC_5 (x : Carrier F) :
    endomorphism (paramsC (5 : Fin 8)) x = ![0, x 1, x 2, 0, 0, x 5, x 6, 0] := by
  ext i
  fin_cases i <;> simp [paramsC, endomorphism]

omit [CharP F 2] in
private theorem derivationC_6 (x : Carrier F) :
    endomorphism (paramsC (6 : Fin 8)) x = ![x 2, x 0 + x 3 + x 4, 0, x 2 + x 6, x 2 + x 6, x 3 + x 4 + x 7, 0, x 6] := by
  ext i
  fin_cases i <;> simp [paramsC, endomorphism]

omit [CharP F 2] in
private theorem derivationC_7 (x : Carrier F) :
    endomorphism (paramsC (7 : Fin 8)) x = ![x 1, 0, x 0 + x 3 + x 4, x 1 + x 5, x 1 + x 5, 0, x 3 + x 4 + x 7, x 5] := by
  ext i
  fin_cases i <;> simp [paramsC, endomorphism]

private theorem equationC_0 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    0 = entries g 6 0 := by
  have h := commute_entries g (paramsC (0 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 0)) 0 0
  simp only [derivationC_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_1 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    0 = entries g 6 1 := by
  have h := commute_entries g (paramsC (0 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 0)) 0 1
  simp only [derivationC_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_2 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    0 = entries g 6 2 := by
  have h := commute_entries g (paramsC (0 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 0)) 0 2
  simp only [derivationC_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_3 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    0 = entries g 6 3 := by
  have h := commute_entries g (paramsC (0 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 0)) 0 3
  simp only [derivationC_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_4 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    0 = entries g 6 4 := by
  have h := commute_entries g (paramsC (0 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 0)) 0 4
  simp only [derivationC_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_5 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    0 = entries g 6 5 := by
  have h := commute_entries g (paramsC (0 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 0)) 0 5
  simp only [derivationC_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_6 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 0 0 = entries g 6 6 := by
  have h := commute_entries g (paramsC (0 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 0)) 0 6
  simp only [derivationC_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_7 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 0 1 = entries g 6 7 := by
  have h := commute_entries g (paramsC (0 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 0)) 0 7
  simp only [derivationC_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_8 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    0 = entries g 7 0 := by
  have h := commute_entries g (paramsC (0 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 0)) 1 0
  simp only [derivationC_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_9 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    0 = entries g 7 1 := by
  have h := commute_entries g (paramsC (0 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 0)) 1 1
  simp only [derivationC_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_10 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    0 = entries g 7 2 := by
  have h := commute_entries g (paramsC (0 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 0)) 1 2
  simp only [derivationC_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_11 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    0 = entries g 7 3 := by
  have h := commute_entries g (paramsC (0 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 0)) 1 3
  simp only [derivationC_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_12 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    0 = entries g 7 4 := by
  have h := commute_entries g (paramsC (0 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 0)) 1 4
  simp only [derivationC_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_13 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    0 = entries g 7 5 := by
  have h := commute_entries g (paramsC (0 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 0)) 1 5
  simp only [derivationC_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_14 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 1 0 = entries g 7 6 := by
  have h := commute_entries g (paramsC (0 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 0)) 1 6
  simp only [derivationC_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_15 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 1 1 = entries g 7 7 := by
  have h := commute_entries g (paramsC (0 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 0)) 1 7
  simp only [derivationC_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_16 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 2 0 = 0 := by
  have h := commute_entries g (paramsC (0 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 0)) 2 6
  simp only [derivationC_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_17 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 2 1 = 0 := by
  have h := commute_entries g (paramsC (0 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 0)) 2 7
  simp only [derivationC_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_18 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 3 0 = 0 := by
  have h := commute_entries g (paramsC (0 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 0)) 3 6
  simp only [derivationC_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_19 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 3 1 = 0 := by
  have h := commute_entries g (paramsC (0 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 0)) 3 7
  simp only [derivationC_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_20 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 4 0 = 0 := by
  have h := commute_entries g (paramsC (0 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 0)) 4 6
  simp only [derivationC_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_21 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 4 1 = 0 := by
  have h := commute_entries g (paramsC (0 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 0)) 4 7
  simp only [derivationC_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_22 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 5 0 = 0 := by
  have h := commute_entries g (paramsC (0 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 0)) 5 6
  simp only [derivationC_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_23 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 5 1 = 0 := by
  have h := commute_entries g (paramsC (0 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 0)) 5 7
  simp only [derivationC_0] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_30 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    0 = entries g 5 2 := by
  have h := commute_entries g (paramsC (1 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 1)) 0 2
  simp only [derivationC_1] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_31 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    0 = entries g 5 3 := by
  have h := commute_entries g (paramsC (1 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 1)) 0 3
  simp only [derivationC_1] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_32 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    0 = entries g 5 4 := by
  have h := commute_entries g (paramsC (1 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 1)) 0 4
  simp only [derivationC_1] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_33 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 0 0 = entries g 5 5 := by
  have h := commute_entries g (paramsC (1 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 1)) 0 5
  simp only [derivationC_1] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_34 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    0 = entries g 5 6 := by
  have h := commute_entries g (paramsC (1 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 1)) 0 6
  simp only [derivationC_1] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_35 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 0 2 = entries g 5 7 := by
  have h := commute_entries g (paramsC (1 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 1)) 0 7
  simp only [derivationC_1] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_36 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 1 0 = 0 := by
  have h := commute_entries g (paramsC (1 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 1)) 1 5
  simp only [derivationC_1] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_37 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 1 2 = 0 := by
  have h := commute_entries g (paramsC (1 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 1)) 1 7
  simp only [derivationC_1] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_45 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 2 2 = entries g 7 7 := by
  have h := commute_entries g (paramsC (1 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 1)) 2 7
  simp only [derivationC_1] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_47 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 3 2 = 0 := by
  have h := commute_entries g (paramsC (1 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 1)) 3 7
  simp only [derivationC_1] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_49 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 4 2 = 0 := by
  have h := commute_entries g (paramsC (1 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 1)) 4 7
  simp only [derivationC_1] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_59 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 0 0 = entries g 3 3 + entries g 4 3 := by
  have h := commute_entries g (paramsC (2 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 2)) 0 3
  simp only [derivationC_2] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_60 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 0 0 = entries g 3 4 + entries g 4 4 := by
  have h := commute_entries g (paramsC (2 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 2)) 0 4
  simp only [derivationC_2] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_61 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 0 1 = entries g 3 5 + entries g 4 5 := by
  have h := commute_entries g (paramsC (2 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 2)) 0 5
  simp only [derivationC_2] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_62 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 0 2 = entries g 3 6 + entries g 4 6 := by
  have h := commute_entries g (paramsC (2 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 2)) 0 6
  simp only [derivationC_2] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_63 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 0 3 + entries g 0 4 = entries g 3 7 + entries g 4 7 := by
  have h := commute_entries g (paramsC (2 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 2)) 0 7
  simp only [derivationC_2] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_69 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 1 1 = entries g 5 5 := by
  have h := commute_entries g (paramsC (2 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 2)) 1 5
  simp only [derivationC_2] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_71 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 1 3 + entries g 1 4 = entries g 5 7 := by
  have h := commute_entries g (paramsC (2 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 2)) 1 7
  simp only [derivationC_2] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_79 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 2 3 + entries g 2 4 = entries g 6 7 := by
  have h := commute_entries g (paramsC (2 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 2)) 2 7
  simp only [derivationC_2] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_87 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 3 3 + entries g 3 4 = entries g 7 7 := by
  have h := commute_entries g (paramsC (2 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 2)) 3 7
  simp only [derivationC_2] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_111 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 0 1 = 0 := by
  have h := commute_entries g (paramsC (3 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 3)) 0 2
  simp only [derivationC_3] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_112 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 0 5 = 0 := by
  have h := commute_entries g (paramsC (3 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 3)) 0 6
  simp only [derivationC_3] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_116 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    0 = entries g 2 3 := by
  have h := commute_entries g (paramsC (3 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 3)) 1 3
  simp only [derivationC_3] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_118 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    0 = entries g 2 5 := by
  have h := commute_entries g (paramsC (3 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 3)) 1 5
  simp only [derivationC_3] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_119 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 1 5 = entries g 2 6 := by
  have h := commute_entries g (paramsC (3 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 3)) 1 6
  simp only [derivationC_3] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_120 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    0 = entries g 2 7 := by
  have h := commute_entries g (paramsC (3 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 3)) 1 7
  simp only [derivationC_3] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_124 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 3 5 = 0 := by
  have h := commute_entries g (paramsC (3 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 3)) 3 6
  simp only [derivationC_3] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_139 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 0 2 = 0 := by
  have h := commute_entries g (paramsC (4 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 4)) 0 1
  simp only [derivationC_4] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_140 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 0 6 = 0 := by
  have h := commute_entries g (paramsC (4 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 4)) 0 5
  simp only [derivationC_4] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_142 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 1 6 = 0 := by
  have h := commute_entries g (paramsC (4 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 4)) 1 5
  simp only [derivationC_4] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_146 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    0 = entries g 1 3 := by
  have h := commute_entries g (paramsC (4 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 4)) 2 3
  simp only [derivationC_4] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_150 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    0 = entries g 1 7 := by
  have h := commute_entries g (paramsC (4 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 4)) 2 7
  simp only [derivationC_4] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_152 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 3 6 = 0 := by
  have h := commute_entries g (paramsC (4 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 4)) 3 5
  simp only [derivationC_4] at h
  simpa [basisVector, Fin.sum_univ_succ] using h

private theorem equationC_201 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 0 0 + entries g 0 3 + entries g 0 4 = entries g 2 2 := by
  have h := commute_entries g (paramsC (6 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 6)) 0 2
  simp only [derivationC_6] at h
  simpa [basisVector, Fin.sum_univ_succ, add_assoc] using h

private theorem equationC_205 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 0 3 + entries g 0 4 + entries g 0 7 = entries g 2 6 := by
  have h := commute_entries g (paramsC (6 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 6)) 0 6
  simp only [derivationC_6] at h
  simpa [basisVector, Fin.sum_univ_succ, add_assoc] using h

private theorem equationC_210 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 1 1 + entries g 1 5 = entries g 0 3 + entries g 3 3 + entries g 4 3 := by
  have h := commute_entries g (paramsC (6 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 6)) 1 3
  simp only [derivationC_6] at h
  simpa [basisVector, Fin.sum_univ_succ, add_assoc] using h

private theorem equationC_227 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) :
    entries g 3 3 + entries g 3 4 + entries g 3 7 = entries g 2 6 + entries g 6 6 := by
  have h := commute_entries g (paramsC (6 : Fin 8))
    (fixed_commutes (rootC 1) g hg _ (paramsC_fixed 6)) 3 6
  simp only [derivationC_6] at h
  simpa [basisVector, Fin.sum_univ_succ, add_assoc] using h

set_option linter.unusedSimpArgs false in
private theorem commutantC_row0 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) (j : Fin 8) :
    entries g 0 j = (![entries g 0 0, 0, 0, entries g 0 3, entries g 0 3, 0, 0, entries g 0 3] : Fin 8 → F) j := by
  fin_cases j
  · rfl
  · change entries g 0 1 = 0
    linear_combination (norm := ring_nf) (equationC_111 g hg)
  · change entries g 0 2 = 0
    linear_combination (norm := ring_nf) (equationC_139 g hg)
  · rfl
  · change entries g 0 4 = entries g 0 3
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_15 g hg) + (equationC_33 g hg) + (equationC_45 g hg) + (equationC_69 g hg) + (equationC_201 g hg)
  · change entries g 0 5 = 0
    linear_combination (norm := ring_nf) (equationC_112 g hg)
  · change entries g 0 6 = 0
    linear_combination (norm := ring_nf) (equationC_140 g hg)
  · change entries g 0 7 = entries g 0 3
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_15 g hg) + (equationC_45 g hg) + (equationC_59 g hg) + (equationC_119 g hg) + (equationC_201 g hg) + (equationC_205 g hg) + (equationC_210 g hg)

set_option linter.unusedSimpArgs false in
private theorem commutantC_row1 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) (j : Fin 8) :
    entries g 1 j = (![0, entries g 0 0, 0, 0, 0, entries g 0 3, 0, 0] : Fin 8 → F) j := by
  fin_cases j
  · change entries g 1 0 = 0
    linear_combination (norm := ring_nf) (equationC_36 g hg)
  · change entries g 1 1 = entries g 0 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_33 g hg) + (equationC_69 g hg)
  · change entries g 1 2 = 0
    linear_combination (norm := ring_nf) (equationC_37 g hg)
  · change entries g 1 3 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_146 g hg)
  · change entries g 1 4 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_35 g hg) + (equationC_71 g hg) + (equationC_139 g hg) + (equationC_146 g hg)
  · change entries g 1 5 = entries g 0 3
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_33 g hg) + (equationC_59 g hg) + (equationC_69 g hg) + (equationC_210 g hg)
  · change entries g 1 6 = 0
    linear_combination (norm := ring_nf) (equationC_142 g hg)
  · change entries g 1 7 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_150 g hg)

set_option linter.unusedSimpArgs false in
private theorem commutantC_row2 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) (j : Fin 8) :
    entries g 2 j = (![0, 0, entries g 0 0, 0, 0, 0, entries g 0 3, 0] : Fin 8 → F) j := by
  fin_cases j
  · change entries g 2 0 = 0
    linear_combination (norm := ring_nf) (equationC_16 g hg)
  · change entries g 2 1 = 0
    linear_combination (norm := ring_nf) (equationC_17 g hg)
  · change entries g 2 2 = entries g 0 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_15 g hg) + (equationC_33 g hg) + (equationC_45 g hg) + (equationC_69 g hg)
  · change entries g 2 3 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_116 g hg)
  · change entries g 2 4 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_7 g hg) + (equationC_79 g hg) + (equationC_111 g hg) + (equationC_116 g hg)
  · change entries g 2 5 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_118 g hg)
  · change entries g 2 6 = entries g 0 3
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_33 g hg) + (equationC_59 g hg) + (equationC_69 g hg) + (equationC_119 g hg) + (equationC_210 g hg)
  · change entries g 2 7 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_120 g hg)

set_option linter.unusedSimpArgs false in
private theorem commutantC_row3 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) (j : Fin 8) :
    entries g 3 j = (![0, 0, 0, entries g 3 3, entries g 0 0 + entries g 3 3, 0, 0, entries g 0 3] : Fin 8 → F) j := by
  fin_cases j
  · change entries g 3 0 = 0
    linear_combination (norm := ring_nf) (equationC_18 g hg)
  · change entries g 3 1 = 0
    linear_combination (norm := ring_nf) (equationC_19 g hg)
  · change entries g 3 2 = 0
    linear_combination (norm := ring_nf) (equationC_47 g hg)
  · rfl
  · change entries g 3 4 = entries g 0 0 + entries g 3 3
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_15 g hg) + (equationC_33 g hg) + (equationC_69 g hg) + (equationC_87 g hg)
  · change entries g 3 5 = 0
    linear_combination (norm := ring_nf) (equationC_124 g hg)
  · change entries g 3 6 = 0
    linear_combination (norm := ring_nf) (equationC_152 g hg)
  · change entries g 3 7 = entries g 0 3
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_6 g hg) + (equationC_15 g hg) + (equationC_59 g hg) + (equationC_87 g hg) + (equationC_119 g hg) + (equationC_210 g hg) + (equationC_227 g hg)

set_option linter.unusedSimpArgs false in
private theorem commutantC_row4 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) (j : Fin 8) :
    entries g 4 j = (![0, 0, 0, entries g 0 0 + entries g 3 3, entries g 3 3, 0, 0, entries g 0 3] : Fin 8 → F) j := by
  fin_cases j
  · change entries g 4 0 = 0
    linear_combination (norm := ring_nf) (equationC_20 g hg)
  · change entries g 4 1 = 0
    linear_combination (norm := ring_nf) (equationC_21 g hg)
  · change entries g 4 2 = 0
    linear_combination (norm := ring_nf) (equationC_49 g hg)
  · change entries g 4 3 = entries g 0 0 + entries g 3 3
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_59 g hg)
  · change entries g 4 4 = entries g 3 3
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_15 g hg) + (equationC_33 g hg) + (equationC_60 g hg) + (equationC_69 g hg) + (equationC_87 g hg)
  · change entries g 4 5 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_61 g hg) + (equationC_111 g hg) + (equationC_124 g hg)
  · change entries g 4 6 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_62 g hg) + (equationC_139 g hg) + (equationC_152 g hg)
  · change entries g 4 7 = entries g 0 3
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_6 g hg) + (equationC_33 g hg) + (equationC_45 g hg) + (equationC_59 g hg) + (equationC_63 g hg) + (equationC_69 g hg) + (equationC_87 g hg) + (equationC_119 g hg) + (equationC_201 g hg) + (equationC_210 g hg) + (equationC_227 g hg)

set_option linter.unusedSimpArgs false in
private theorem commutantC_row5 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) (j : Fin 8) :
    entries g 5 j = (![0, 0, 0, 0, 0, entries g 0 0, 0, 0] : Fin 8 → F) j := by
  fin_cases j
  · change entries g 5 0 = 0
    linear_combination (norm := ring_nf) (equationC_22 g hg)
  · change entries g 5 1 = 0
    linear_combination (norm := ring_nf) (equationC_23 g hg)
  · change entries g 5 2 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_30 g hg)
  · change entries g 5 3 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_31 g hg)
  · change entries g 5 4 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_32 g hg)
  · change entries g 5 5 = entries g 0 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_33 g hg)
  · change entries g 5 6 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_34 g hg)
  · change entries g 5 7 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_35 g hg) + (equationC_139 g hg)

set_option linter.unusedSimpArgs false in
private theorem commutantC_row6 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) (j : Fin 8) :
    entries g 6 j = (![0, 0, 0, 0, 0, 0, entries g 0 0, 0] : Fin 8 → F) j := by
  fin_cases j
  · change entries g 6 0 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_0 g hg)
  · change entries g 6 1 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_1 g hg)
  · change entries g 6 2 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_2 g hg)
  · change entries g 6 3 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_3 g hg)
  · change entries g 6 4 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_4 g hg)
  · change entries g 6 5 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_5 g hg)
  · change entries g 6 6 = entries g 0 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_6 g hg)
  · change entries g 6 7 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_7 g hg) + (equationC_111 g hg)

set_option linter.unusedSimpArgs false in
private theorem commutantC_row7 (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) (j : Fin 8) :
    entries g 7 j = (![0, 0, 0, 0, 0, 0, 0, entries g 0 0] : Fin 8 → F) j := by
  fin_cases j
  · change entries g 7 0 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_8 g hg)
  · change entries g 7 1 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_9 g hg)
  · change entries g 7 2 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_10 g hg)
  · change entries g 7 3 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_11 g hg)
  · change entries g 7 4 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_12 g hg)
  · change entries g 7 5 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_13 g hg)
  · change entries g 7 6 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_14 g hg) + (equationC_36 g hg)
  · change entries g 7 7 = entries g 0 0
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) (equationC_15 g hg) + (equationC_33 g hg) + (equationC_69 g hg)

private theorem commutantC_entries (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) (i j : Fin 8) :
    entries g i j = (![
    ![entries g 0 0, 0, 0, entries g 0 3, entries g 0 3, 0, 0, entries g 0 3],
    ![0, entries g 0 0, 0, 0, 0, entries g 0 3, 0, 0],
    ![0, 0, entries g 0 0, 0, 0, 0, entries g 0 3, 0],
    ![0, 0, 0, entries g 3 3, entries g 0 0 + entries g 3 3, 0, 0, entries g 0 3],
    ![0, 0, 0, entries g 0 0 + entries g 3 3, entries g 3 3, 0, 0, entries g 0 3],
    ![0, 0, 0, 0, 0, entries g 0 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, entries g 0 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, entries g 0 0]
  ] : Fin 8 → Fin 8 → F) i j := by
  fin_cases i
  · exact commutantC_row0 g hg j
  · exact commutantC_row1 g hg j
  · exact commutantC_row2 g hg j
  · exact commutantC_row3 g hg j
  · exact commutantC_row4 g hg j
  · exact commutantC_row5 g hg j
  · exact commutantC_row6 g hg j
  · exact commutantC_row7 g hg j
private def formA (d b e : F) : Fin 8 → Fin 8 → F := ![
  ![d,0,0,0,0,0,b,0], ![0,d,0,0,0,0,0,b], ![0,0,d,0,0,0,0,0],
  ![0,0,0,e,d+e,0,0,0], ![0,0,0,d+e,e,0,0,0],
  ![0,0,0,0,0,d,0,0], ![0,0,0,0,0,0,d,0], ![0,0,0,0,0,0,0,d]]

private def formC (d b e : F) : Fin 8 → Fin 8 → F := ![
  ![d,0,0,b,b,0,0,b], ![0,d,0,0,0,b,0,0], ![0,0,d,0,0,0,b,0],
  ![0,0,0,e,d+e,0,0,b], ![0,0,0,d+e,e,0,0,b],
  ![0,0,0,0,0,d,0,0], ![0,0,0,0,0,0,d,0], ![0,0,0,0,0,0,0,d]]
private theorem normal_entriesA (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootA 1)) (i j : Fin 8) :
    entries g i j = formA 1 (entries g 0 6) 1 i j := by
  let d := entries g 0 0
  let b := entries g 0 6
  let e := entries g 3 3
  have he (i j : Fin 8) : entries g i j = formA d b e i j :=
    commutantA_entries g hg i j
  have ht := automorphism_trace g (basisVector 3)
  change entries g 3 3 + entries g 4 3 = trace (basisVector 3) at ht
  rw [he 3 3, he 4 3] at ht
  simp [formA, trace, basisVector] at ht
  have hd : d = 1 := by
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) ht
  have hp : mul (basisVector (F := F) 0) (basisVector 7) = basisVector 3 := by
    ext k
    fin_cases k <;> simp [Atlas.SplitOctonion.mul, basisVector, CharTwo.neg_eq]
  have hm := congrFun (automorphism_mul g (basisVector 0) (basisVector 7)) 3
  rw [hp] at hm
  change entries g 3 3 = mul (fun k => entries g k 0) (fun k => entries g k 7) 3 at hm
  simp [Atlas.SplitOctonion.mul, he, formA, hd, CharTwo.neg_eq] at hm
  simpa only [hd, hm] using he i j

/-- Commuting with the eight fixed derivations determines a kernel element
from one field entry. This bounds the actual kernel in the root centralizer. -/
theorem rootA_one_fixedKernel_card [Finite F] :
    Nat.card (involutionFixedKernel (adjointBinary F) (rootA 1)) ≤ Nat.card F := by
  let f : involutionFixedKernel (adjointBinary F) (rootA 1) → F :=
    fun g => entries g 0 6
  apply Nat.card_le_card_of_injective f
  intro g h hgh
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply Atlas.SplitOctonion.linearMap_ext
  intro j
  ext i
  change entries (g : Model F) i j = entries (h : Model F) i j
  rw [normal_entriesA (g : Model F) g.property, normal_entriesA (h : Model F) h.property]
  change entries (g : Model F) 0 6 = entries (h : Model F) 0 6 at hgh
  rw [hgh]
private theorem normal_entriesC (g : Model F)
    (hg : g ∈ involutionFixedKernel (adjointBinary F) (rootC 1)) (i j : Fin 8) :
    entries g i j = formC 1 (entries g 0 3) 1 i j := by
  let d := entries g 0 0
  let b := entries g 0 3
  let e := entries g 3 3
  have he (i j : Fin 8) : entries g i j = formC d b e i j :=
    commutantC_entries g hg i j
  have ht := automorphism_trace g (basisVector 3)
  change entries g 3 3 + entries g 4 3 = trace (basisVector 3) at ht
  rw [he 3 3, he 4 3] at ht
  simp [formC, trace, basisVector] at ht
  have hd : d = 1 := by
    linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)])) ht
  have hp : mul (basisVector (F := F) 0) (basisVector 7) = basisVector 3 := by
    ext k
    fin_cases k <;> simp [Atlas.SplitOctonion.mul, basisVector, CharTwo.neg_eq]
  have hm := congrFun (automorphism_mul g (basisVector 0) (basisVector 7)) 3
  rw [hp] at hm
  change entries g 3 3 = mul (fun k => entries g k 0) (fun k => entries g k 7) 3 at hm
  simp [Atlas.SplitOctonion.mul, he, formC, hd, CharTwo.neg_eq] at hm
  simpa only [hd, hm] using he i j

/-- Commuting with the eight fixed derivations determines a kernel element
from one field entry. This bounds the actual kernel in the root centralizer. -/
theorem rootC_one_fixedKernel_card [Finite F] :
    Nat.card (involutionFixedKernel (adjointBinary F) (rootC 1)) ≤ Nat.card F := by
  let f : involutionFixedKernel (adjointBinary F) (rootC 1) → F :=
    fun g => entries g 0 3
  apply Nat.card_le_card_of_injective f
  intro g h hgh
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply Atlas.SplitOctonion.linearMap_ext
  intro j
  ext i
  change entries (g : Model F) i j = entries (h : Model F) i j
  rw [normal_entriesC (g : Model F) g.property, normal_entriesC (h : Model F) h.property]
  change entries (g : Model F) 0 3 = entries (h : Model F) 0 3 at hgh
  rw [hgh]

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.AdjointObstruction.InnerGeometry
