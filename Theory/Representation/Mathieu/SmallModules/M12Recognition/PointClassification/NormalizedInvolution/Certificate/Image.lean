module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.NormIdeal
public import Theory.Representation.JacobsonDensity
/-!
# The full endomorphism image of the binary M₁₁ point module

The actual elements B and ABABBABA fix the augmentation vector which is zero
at point zero and one elsewhere. Their permutations are transitive together
on the remaining ten points, so their common fixed space in the augmentation
module is exactly this line. An equivariant endomorphism therefore has a
binary eigenvalue. Irreducibility makes it scalar, and Jacobson density gives
surjectivity of the actual point representation's group-algebra map.

The augmentation-to-point equivalence preserves the marked group elements
and the inverse-permutation convention. Only small permutation tables are
checked; no character table or classification premise is used.
Source application: the James input to Aschbacher–Smith G.7.3(2), printed
p.348/PDF p.359; James, J. Algebra 27 (1973), 57–111.
-/

public section
open Sporadic.Mathieu BinaryPermutation
open Sporadic.Mathieu.M11OrderCertificate
open scoped MonoidAlgebra
namespace Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution
private def abPerm : _root_.Equiv.Perm (Fin 11) where
  toFun := ![4, 0, 7, 9, 3, 6, 8, 5, 1, 10, 2]
  invFun := ![1, 8, 10, 4, 0, 7, 5, 2, 6, 3, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def baPerm : _root_.Equiv.Perm (Fin 11) where
  toFun := ![3, 4, 10, 8, 0, 7, 9, 6, 2, 1, 5]
  invFun := ![4, 9, 8, 0, 1, 10, 7, 5, 3, 6, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def dPerm : _root_.Equiv.Perm (Fin 11) where
  toFun := ![0, 3, 8, 5, 10, 1, 4, 2, 7, 9, 6]
  invFun := ![0, 5, 7, 1, 6, 3, 10, 8, 2, 9, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private theorem abPerm_eq : m11L0G0 * m11L0G1 = abPerm := by
  ext i; fin_cases i <;> rfl
private theorem baPerm_eq : m11L0G1 * m11L0G0 = baPerm := by
  ext i; fin_cases i <;> rfl
private theorem dPerm_eq : (abPerm * abPerm) * (baPerm * baPerm) = dPerm := by
  ext i; fin_cases i <;> rfl
private theorem dPerm_mem : dPerm ∈ M11 := by
  have hA : m11L0G0 ∈ M11 := m11GeneratorA_eq_m11L0G0 ▸ m11GeneratorA_mem
  have hB : m11L0G1 ∈ M11 := m11GeneratorB_eq_m11L0G1 ▸ m11GeneratorB_mem
  have hab : abPerm ∈ M11 := abPerm_eq ▸ M11.mul_mem hA hB
  have hba : baPerm ∈ M11 := baPerm_eq ▸ M11.mul_mem hB hA
  exact dPerm_eq ▸ M11.mul_mem (M11.mul_mem hab hab) (M11.mul_mem hba hba)
private noncomputable def dGroup : M11 := ⟨dPerm, dPerm_mem⟩
private theorem dGroup_val : dGroup.val = dPerm := rfl
private theorem dPerm_apply (i : Fin 11) : dPerm i =
    ![0, 3, 8, 5, 10, 1, 4, 2, 7, 9, 6] i := rfl
private theorem augmentation_apply (g : M11) (v : core (Fin 11)) (i : Fin 11) :
    (augmentationRepresentation g v).val i = v.val (g.val.symm i) := rfl
private theorem fixed_forward (g : M11) (v : core (Fin 11))
    (h : augmentationRepresentation g v = v) (i : Fin 11) :
    v.val (g.val i) = v.val i := by
  have he := congrArg (fun x : core (Fin 11) => x.val (g.val i)) h
  rw [augmentation_apply, _root_.Equiv.symm_apply_apply] at he
  exact he.symm
private def pointVector : Full (Fin 11) := fun i => if i = 0 then 0 else 1
private theorem pointVector_mem : pointVector ∈ core (Fin 11) := by
  change ∑ i, pointVector i = 0
  decide +kernel
private def u : core (Fin 11) := ⟨pointVector, pointVector_mem⟩
private theorem u_ne_zero : u ≠ 0 := by
  intro h
  have h1 := congrArg (fun x : core (Fin 11) => x.val 1) h
  change (1 : ZMod 2) = 0 at h1
  exact one_ne_zero h1
private theorem fixes_pointVector (g : _root_.Equiv.Perm (Fin 11)) (hg : g 0 = 0) :
    representation (Fin 11) g pointVector = pointVector := by
  ext i
  simp only [representation_apply, pointVector, _root_.Equiv.symm_apply_eq, hg]
private theorem fix_u : augmentationRepresentation m11GeneratorBInM11 u = u ∧
    augmentationRepresentation dGroup u = u := by
  constructor <;> apply Subtype.ext
  · change representation (Fin 11) m11GeneratorB pointVector = pointVector
    apply fixes_pointVector
    rw [m11GeneratorB_eq_m11L0G1]
    rfl
  · change representation (Fin 11) dGroup.val pointVector = pointVector
    rw [dGroup_val]
    exact fixes_pointVector dPerm (dPerm_apply 0)
private theorem ten_nsmul (c : ZMod 2) : 10 • c = 0 := by
  rw [show 10 = 5 * 2 from rfl, mul_nsmul, two_nsmul, CharTwo.add_self_eq_zero]
private theorem fixed_scalar (v : core (Fin 11))
    (hb : augmentationRepresentation m11GeneratorBInM11 v = v)
    (hd : augmentationRepresentation dGroup v = v) :
    ∃ c : ZMod 2, v = c • u := by
  have hB (i : Fin 11) : v.val (m11L0G1 i) = v.val i := by
    have h := fixed_forward m11GeneratorBInM11 v hb i
    change v.val (m11GeneratorB i) = v.val i at h
    rwa [m11GeneratorB_eq_m11L0G1] at h
  have hD (i : Fin 11) : v.val (![0, 3, 8, 5, 10, 1, 4, 2, 7, 9, 6] i) = v.val i := by
    have h := fixed_forward dGroup v hd i
    rwa [dGroup_val, dPerm_apply] at h
  have b1 : v.val 4 = v.val 1 := hB 1
  have b4 : v.val 3 = v.val 4 := hB 4
  have b3 : v.val 8 = v.val 3 := hB 3
  have b2 : v.val 5 = v.val 2 := hB 2
  have b5 : v.val 6 = v.val 5 := hB 5
  have b6 : v.val 9 = v.val 6 := hB 6
  have d3 : v.val 5 = v.val 3 := hD 3
  have d8 : v.val 7 = v.val 8 := hD 8
  have d4 : v.val 10 = v.val 4 := hD 4
  have hc (i : Fin 11) (hi : i ≠ 0) : v.val i = v.val 1 := by
    fin_cases i <;> simp_all
  have h0 : v.val 0 = 0 := by
    have hv := v.property
    change (∑ i : Fin 11, v.val i) = 0 at hv
    have hsum : (∑ i : Fin 11, v.val i) = v.val 0 := by
      rw [Fin.sum_univ_succ]
      have hs : ∀ i : Fin 10, v.val i.succ = v.val 1 := fun i => hc i.succ (by simp)
      simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [ten_nsmul, add_zero]
    rwa [hsum] at hv
  refine ⟨v.val 1, ?_⟩
  apply Subtype.ext
  ext i
  change v.val i = v.val 1 * pointVector i
  by_cases hi : i = 0
  · subst i; simp [pointVector, h0]
  · simp [pointVector, hi, hc i hi]
private theorem end_scalar : Function.Surjective (algebraMap (ZMod 2) (End pointRepresentation)) := by
  let : pointRepresentation.IsIrreducible := pointRepresentation_isIrreducible
  intro f
  let e := augmentationEquivPoint
  let f' : augmentationRepresentation.IntertwiningMap augmentationRepresentation :=
    e.symm.toIntertwiningMap.comp (f.comp e.toIntertwiningMap)
  have hfix (g : M11) (hg : augmentationRepresentation g u = u) :
      augmentationRepresentation g (f' u) = f' u := by
    have he := LinearMap.congr_fun (f'.isIntertwining' g) u
    change f' (augmentationRepresentation g u) = augmentationRepresentation g (f' u) at he
    rw [hg] at he
    exact he.symm
  obtain ⟨c, hc⟩ := fixed_scalar (f' u) (hfix _ fix_u.1) (hfix _ fix_u.2)
  have he : f (e u) = c • e u := by
    have hh := congrArg e hc
    change e (e.symm (f (e u))) = e (c • u) at hh
    simpa only [Representation.Equiv.apply_symm_apply, map_smul] using hh
  have hn : e u ≠ 0 := by
    intro h
    exact u_ne_zero (e.injective (h.trans (map_zero e).symm))
  have hz : f - algebraMap (ZMod 2) (End pointRepresentation) c = 0 := by
    apply (Representation.IsIrreducible.injective_or_eq_zero _).resolve_left
    intro hinj
    apply hn
    apply hinj
    change f (e u) - c • e u = f 0 - c • (0 : M12Heart)
    rw [he, sub_self, map_zero, smul_zero, sub_self]
  exact ⟨c, (sub_eq_zero.mp hz).symm⟩
/-- The actual binary M₁₁ point representation spans its full endomorphism algebra. -/
theorem pointRepresentation_asAlgebraHom_surjective :
    Function.Surjective pointRepresentation.asAlgebraHom := by
  let : pointRepresentation.IsIrreducible := pointRepresentation_isIrreducible
  have ht := jacobson_density_surjective_rep pointRepresentation end_scalar
  apply (AlgHom.range_eq_top _).mp
  apply top_unique
  rw [← ht]
  apply Algebra.adjoin_le
  rintro _ ⟨g, rfl⟩
  exact ⟨MonoidAlgebra.single g 1, Representation.asAlgebraHom_single_one _ _⟩
end Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution
