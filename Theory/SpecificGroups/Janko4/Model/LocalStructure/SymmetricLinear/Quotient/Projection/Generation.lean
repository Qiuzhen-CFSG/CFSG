module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.Projection.Generators
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Mathlib.GroupTheory.Perm.Closure

/-!
# Joint generation of the symmetric-linear quotient

The displayed images of the literal ATLAS max4 generators generate the actual
product S₅ × SL₃(2). A fifth power of their product has trivial permutation
component. Together with its conjugate by the first image, it gives the three
cyclic elementary transvections; elementary generation then supplies the whole
linear factor. Removing the linear components of the original generators
leaves a five-cycle and a transposition, which generate S₅.

Only small matrix and permutation identities are checked by kernel reduction;
there is no enumeration of the product group or reliance on exploratory counts.
Source: ATLAS `J4G1-max4W1`, with the literal images and multiplication
conventions in `Projection.Generators`. This supplies the joint-generation
premise of `Projection.projectionOfLinearHom_surjective` for the local quotient
used in Aschbacher–Smith, Proposition 1.3.4, printed p.511/PDF p.528.
-/

namespace Janko4.LocalStructure.SymmetricLinear.Projection

private abbrev Linear := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

private def c : Linear := ⟨!![1,0,1;0,0,1;1,1,1], by decide +kernel⟩
private def d : Linear := ⟨!![0,1,1;1,1,0;1,1,1], by decide +kernel⟩
private def x : Linear := ⟨!![1,1,0;0,1,0;0,0,1], by decide +kernel⟩
private def y : Linear := ⟨!![1,0,0;0,1,1;0,0,1], by decide +kernel⟩
private def z : Linear := ⟨!![1,0,0;0,1,0;1,0,1], by decide +kernel⟩

private theorem c_word : (firstImage * secondImage)^5 = (1, c) := by decide +kernel
private theorem d_word : firstImage * (1, c) * firstImage = (1, d) := by decide +kernel
private theorem x_word : x = c * c * d := by decide +kernel
private theorem y_word : y = c * c * d * d * c⁻¹ := by decide +kernel
private theorem z_word : z = c * d⁻¹ * c * c * d⁻¹ * c := by decide +kernel

private theorem elementary_words :
    ∀ (i j : Fin 3) (hij : i ≠ j) (a : ZMod 2),
      Matrix.SpecialLinearGroup.transvection hij a = 1 ∨
      Matrix.SpecialLinearGroup.transvection hij a = x ∨
      Matrix.SpecialLinearGroup.transvection hij a = y ∨
      Matrix.SpecialLinearGroup.transvection hij a = z ∨
      Matrix.SpecialLinearGroup.transvection hij a = x * y * x * y ∨
      Matrix.SpecialLinearGroup.transvection hij a = y * z * y * z ∨
      Matrix.SpecialLinearGroup.transvection hij a = z * x * z * x := by decide +kernel

private theorem linear_factor_mem (H : Subgroup QuotientModel)
    (ha : firstImage ∈ H) (hb : secondImage ∈ H) (g : Linear) : (1, g) ∈ H := by
  let K := H.comap (MonoidHom.inr (Equiv.Perm (Fin 5)) Linear)
  have hc : c ∈ K := by
    change (1, c) ∈ H
    rw [← c_word]
    exact H.pow_mem (H.mul_mem ha hb) 5
  have hd : d ∈ K := by
    change (1, d) ∈ H
    rw [← d_word]
    exact H.mul_mem (H.mul_mem ha hc) ha
  have hx : x ∈ K := by
    rw [x_word]
    exact K.mul_mem (K.mul_mem hc hc) hd
  have hy : y ∈ K := by
    rw [y_word]
    exact K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem hc hc) hd) hd) (K.inv_mem hc)
  have hz : z ∈ K := by
    rw [z_word]
    exact K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem hc
      (K.inv_mem hd)) hc) hc) (K.inv_mem hd)) hc
  change g ∈ K
  apply Atlas.sl_elementary_induction (fun g => g ∈ K) ?_ (fun _ _ => K.mul_mem) g
  intro i j hij a
  rcases elementary_words i j hij a with h | h | h | h | h | h | h <;> rw [h]
  · exact K.one_mem
  · exact hx
  · exact hy
  · exact hz
  · exact K.mul_mem (K.mul_mem (K.mul_mem hx hy) hx) hy
  · exact K.mul_mem (K.mul_mem (K.mul_mem hy hz) hy) hz
  · exact K.mul_mem (K.mul_mem (K.mul_mem hz hx) hz) hx

private theorem perm_product_isCycle : (firstPerm * secondPerm).IsCycle := by
  refine ⟨0, by decide +kernel, ?_⟩
  intro i _
  have h : ∀ i : Fin 5, ∃ n : Fin 5, ((firstPerm * secondPerm) ^ (n : ℕ)) 0 = i := by
    decide +kernel
  obtain ⟨n, hn⟩ := h i
  exact ⟨(n : ℤ), by simpa only [zpow_natCast] using hn⟩

private theorem perm_pair_generates :
    Subgroup.closure ({firstPerm, secondPerm} : Set (Equiv.Perm (Fin 5))) = ⊤ := by
  have h := Equiv.Perm.closure_prime_cycle_swap (by decide : (Fintype.card (Fin 5)).Prime)
    perm_product_isCycle (by decide +kernel : (firstPerm * secondPerm).support = Finset.univ)
    (show firstPerm.IsSwap from ⟨3, 4, by decide, by decide +kernel⟩)
  apply top_unique
  rw [← h]
  apply (Subgroup.closure_le _).mpr
  intro g hg
  have ha : firstPerm ∈ Subgroup.closure ({firstPerm, secondPerm} : Set _) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : secondPerm ∈ Subgroup.closure ({firstPerm, secondPerm} : Set _) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  rcases hg with rfl | rfl
  · exact Subgroup.mul_mem _ ha hb
  · exact ha

/-- The two literal proposed images jointly generate the genuine product S₅ × SL₃(2). -/
public theorem imagePair_generates :
    Subgroup.closure ({firstImage, secondImage} : Set QuotientModel) = ⊤ := by
  let H := Subgroup.closure ({firstImage, secondImage} : Set QuotientModel)
  have ha : firstImage ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : secondImage ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hlin := linear_factor_mem H ha hb
  let K := H.comap (MonoidHom.inl (Equiv.Perm (Fin 5)) Linear)
  have hpa : firstPerm ∈ K := by
    change (firstPerm, 1) ∈ H
    have h := H.mul_mem ha (hlin firstLinear⁻¹)
    simpa only [firstImage, Prod.mk_mul_mk, mul_one, mul_inv_cancel] using h
  have hpb : secondPerm ∈ K := by
    change (secondPerm, 1) ∈ H
    have h := H.mul_mem hb (hlin secondLinear⁻¹)
    simpa only [secondImage, Prod.mk_mul_mk, mul_one, mul_inv_cancel] using h
  have hperm : ∀ p : Equiv.Perm (Fin 5), (p, 1) ∈ H := by
    have hK : (⊤ : Subgroup (Equiv.Perm (Fin 5))) ≤ K := by
      rw [← perm_pair_generates]
      apply (Subgroup.closure_le _).mpr
      intro p hp
      rcases hp with rfl | rfl
      · exact hpa
      · exact hpb
    intro p
    exact hK (Subgroup.mem_top p)
  apply top_unique
  rintro ⟨p, g⟩ _
  simpa only [Prod.mk_mul_mk, mul_one, one_mul] using H.mul_mem (hperm p) (hlin g)

end Janko4.LocalStructure.SymmetricLinear.Projection
