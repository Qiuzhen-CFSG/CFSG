module
public import Theory.GroupTheory.CyclicSL23AbelianConjugates
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Cubic conjugation in C₄∗SL₂(3)

An element of SL₂(3) commuting with its conjugate under an element of
order dividing three is fixed by that element. The calculation is checked
on the 24-element binary tetrahedral model. In a central product with a
factor of exponent four, every cubic element is already in SL₂(3), so
the same assertion holds. The moving Klein four in A₄ therefore excludes
an embedding of A₄ in this central product.

The actual opposite-centralizer application is in Chapter14's
RecognitionAlternating. Source: Aschbacher--Smith 14.3.22, printed p.999.
-/

public section
open Subgroup
namespace Subgroup
private abbrev BT := QuaternionGroup 2 ⋊[GLS3.Chapter5.SchurPresentation.q8C3Action] Multiplicative (ZMod 3)
private instance : DecidableEq BT := SemidirectProduct.equivProd.injective.decidableEq
private instance : Fintype BT := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

private theorem bt_cubic : ∀ x c : BT, c ^ 3 = 1 →
    x * (c*x*c⁻¹) = (c*x*c⁻¹)*x → c*x*c⁻¹ = x := by decide +kernel

variable {G : Type*} [Group G]

theorem sl23_cubic_commuting_conjugate (B : Subgroup G)
    (eB : B ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (x c : G) (hx : x ∈ B) (hc : c ∈ B) (hc3 : c ^ 3 = 1)
    (hcomm : x * (c*x*c⁻¹) = (c*x*c⁻¹)*x) : c*x*c⁻¹ = x := by
  let f := eB.trans GLS3.Chapter5.SchurPresentation.binaryTetrahedralEquivSL.symm
  let xx : B := ⟨x,hx⟩
  let cc : B := ⟨c,hc⟩
  have h3 : (f cc) ^ 3 = 1 := by
    rw [←map_pow,show cc^3=1 from Subtype.ext hc3,map_one]
  have hcom : f xx * (f cc * f xx * (f cc)⁻¹) =
      (f cc * f xx * (f cc)⁻¹) * f xx := by
    simpa only [map_mul,map_inv] using congrArg f (show xx*(cc*xx*cc⁻¹)=(cc*xx*cc⁻¹)*xx from
      Subtype.ext hcomm)
  exact congrArg Subtype.val (f.injective (show f (cc*xx*cc⁻¹) = f xx by
    simpa only [map_mul,map_inv] using bt_cubic (f xx) (f cc) h3 hcom))

theorem cyclic_sl23_cubic_commuting_conjugate (E B : Subgroup G)
    (hE : ∀ u ∈ E, u ^ 4 = 1)
    (eB : B ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (hEB : E ≤ centralizer (B : Set G))
    (x c : G) (hx : x ∈ E ⊔ B) (hc : c ∈ E ⊔ B) (hc3 : c ^ 3 = 1)
    (hcomm : x * (c*x*c⁻¹) = (c*x*c⁻¹)*x) : c*x*c⁻¹ = x := by
  have decomp {y : G} (hy : y ∈ E ⊔ B) : ∃ u ∈ E, ∃ b ∈ B, u*b=y := by
    change y ∈ (↑(E ⊔ B) : Set G) at hy
    rw [coe_mul_of_right_le_normalizer_left E B
      ((le_centralizer_iff.mp hEB).trans (Subgroup.centralizer_le_normalizer _))] at hy
    exact hy
  have hcB : c ∈ B := by
    obtain ⟨u,hu,b,hb,rfl⟩ := decomp hc
    have hub : Commute u b := (hEB hu b hb).symm
    rw [hub.mul_pow] at hc3
    have hu4 := hE u hu
    have he : u = b^3 := by
      calc
        u = u^4 * (u^3)⁻¹ := by group
        _ = (u^3)⁻¹ := by rw [hu4,one_mul]
        _ = b^3 := by rw [mul_eq_one_iff_eq_inv.mp hc3,inv_inv]
    exact B.mul_mem (he.symm ▸ B.pow_mem hb 3) hb
  obtain ⟨u,hu,b,hb,rfl⟩ := decomp hx
  let v := c*b*c⁻¹
  have hvB : v ∈ B := B.mul_mem (B.mul_mem hcB hb) (B.inv_mem hcB)
  have hub : b*u=u*b := hEB hu b hb
  have huc : c*u=u*c := hEB hu c hcB
  have huv : v*u=u*v := hEB hu v hvB
  have he : c*(u*b)*c⁻¹=u*v := by
    dsimp only [v]
    rw [←mul_assoc c u b,huc]
    simp only [mul_assoc]
  have hbcomm : b*v=v*b := by
    rw [he] at hcomm
    have hl : (u*b)*(u*v)=(u*u)*(b*v) := by
      calc
        _ = u*(b*u)*v := by group
        _ = u*(u*b)*v := by rw [hub]
        _ = _ := by group
    have hr : (u*v)*(u*b)=(u*u)*(v*b) := by
      calc
        _ = u*(v*u)*b := by group
        _ = u*(u*v)*b := by rw [huv]
        _ = _ := by group
    rw [hl,hr] at hcomm
    exact mul_left_cancel hcomm
  have hv : v=b := sl23_cubic_commuting_conjugate B eB b c hb hcB hc3 hbcomm
  rw [he,hv]

private def ax : alternatingGroup (Fin 4) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
private def ac : alternatingGroup (Fin 4) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
private theorem ac_cube : ac^3=1 := by decide +kernel
private theorem ax_comm : ax*(ac*ax*ac⁻¹)=(ac*ax*ac⁻¹)*ax := by decide +kernel
private theorem ax_moved : ac*ax*ac⁻¹≠ax := by decide +kernel

theorem no_alternatingFour_embedding_cyclic_sl23 (E B : Subgroup G)
    (hE : ∀ u ∈ E, u ^ 4 = 1)
    (eB : B ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (hEB : E ≤ centralizer (B : Set G))
    (f : alternatingGroup (Fin 4) →* G) (hf : Function.Injective f)
    (hr : f.range ≤ E ⊔ B) : False := by
  have hh := cyclic_sl23_cubic_commuting_conjugate E B hE eB hEB (f ax) (f ac)
    (hr ⟨ax,rfl⟩) (hr ⟨ac,rfl⟩)
    (by rw [←map_pow,ac_cube,map_one])
    (by simpa only [map_mul,map_inv] using congrArg f ax_comm)
  apply ax_moved
  apply hf
  simpa only [map_mul,map_inv] using hh

end Subgroup

