module
public import Theory.GroupTheory.CommutatorPreimage.Membership
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The center of the original pair of seeds

Two abelian modules contain the two generating seeds. Separation of their
cross actions modulo Z and the two source centralizer bounds force the center
of the seed join to be exactly Z. Decompose a central element into its seed
factors; the first bound puts its second factor in Z, and the second bound
then puts the element itself in Z.
Source: Aschbacher–Smith F.9.5(6.i), printed p.319.
-/
public section
open scoped IsMulCommutative commutatorElement Pointwise
namespace Subgroup
variable {G : Type*} [Group G]

/-- A center calculation retaining both original seed embeddings. -/
theorem center_seed_sup_eq
    (H A B C E Z : Subgroup G)
    (hCA : C ≤ A) (hEB : E ≤ B) (hAH : A ≤ H) (hBH : B ≤ H)
    (hZC : Z ≤ C)
    (hA : IsMulCommutative A) (hEC : E ≤ normalizer (C : Set G))
    (hHZ : H ≤ centralizer (Z : Set G))
    (hfirst : commutatorPreimage C B Z = Z)
    (hsecond : commutatorPreimage E A Z = Z)
    (hc : ⁅A,H ⊓ centralizer (C : Set G)⁆ ≤ Z)
    (he : ⁅B,H ⊓ centralizer (E : Set G)⁆ ≤ Z) :
    (center (C ⊔ E : Subgroup G)).map (C ⊔ E).subtype = Z := by
  let P := C ⊔ E
  have hCP : C ≤ P := le_sup_left
  have hEP : E ≤ P := le_sup_right
  have hPH : P ≤ H := sup_le (hCA.trans hAH) (hEB.trans hBH)
  have hZN : H ≤ normalizer (Z : Set G) := hHZ.trans (centralizer_le_normalizer _)
  apply le_antisymm
  · rintro x ⟨xP,hx,rfl⟩
    have hxC : (xP : G) ∈ centralizer (C : Set G) := by
      intro c hc'
      exact congrArg Subtype.val (mem_center_iff.mp hx ⟨c,hCP hc'⟩)
    have hxE : (xP : G) ∈ centralizer (E : Set G) := by
      intro e he'
      exact congrArg Subtype.val (mem_center_iff.mp hx ⟨e,hEP he'⟩)
    have hprod : (xP : G) ∈ (C : Set G) * (E : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left C E hEC]
      exact xP.property
    obtain ⟨c,hc',e,he',hprod⟩ := hprod
    have heZ : e ∈ Z := by
      rw [←hsecond]
      apply (mem_commutatorPreimage_iff E A Z (hEB.trans (hBH.trans hZN)) e).mpr
      refine ⟨he', fun a ha => ?_⟩
      have hcA : a*c=c*a := by
        let := hA
        exact congrArg Subtype.val (mul_comm (⟨a,ha⟩ : A) ⟨c,hCA hc'⟩)
      have hh : ⁅a,(xP:G)⁆ ∈ Z := hc (commutator_mem_commutator ha ⟨hPH xP.property,hxC⟩)
      rw [←hprod,commutatorElement_mul_right_eq_mul_conj,
        commutatorElement_eq_one_iff_mul_comm.mpr hcA,one_mul] at hh
      have hh' : ⁅a,e⁆ ∈ Z := (mem_normalizer_iff.mp (hZN (hAH (hCA hc'))) _).mpr hh
      rw [←commutatorElement_inv]
      exact Z.inv_mem hh'
    have hxC' : (xP:G) ∈ C := by
      rw [←hprod]
      exact C.mul_mem hc' (hZC heZ)
    rw [←hfirst]
    apply (mem_commutatorPreimage_iff C B Z (hCA.trans (hAH.trans hZN)) _).mpr
    refine ⟨hxC', fun b hb => ?_⟩
    rw [←commutatorElement_inv]
    exact Z.inv_mem (he (commutator_mem_commutator hb ⟨hPH xP.property,hxE⟩))
  · intro z hz
    refine ⟨⟨z,hCP (hZC hz)⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro p
    apply Subtype.ext
    exact (hHZ (hPH p.property) z hz).symm
end Subgroup
