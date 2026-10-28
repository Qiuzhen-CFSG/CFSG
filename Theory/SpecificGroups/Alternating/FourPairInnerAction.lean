module

public import Theory.SpecificGroups.Alternating.FourPairMarkedAction
public import Theory.SpecificGroups.Alternating.FourPairThompson.Definitions

/-!
# Inner automorphisms in the literal symmetric wreath model

The inner automorphism of (a,b) is the base word with coordinates a,b.
Consequently the image of Inn(A₄²) is exactly the alternating base, and
every nonswapping wreath word preserves the first coordinate factor.
These identities match the original marked conjugation action, rather
than just the isomorphism types of its subgroup images.

Source: Aschbacher--Smith 14.1.10, printed p.978.
-/

@[expose] public section
open Subgroup
namespace AlternatingFourPair

private noncomputable def innerWord (v : Model) : W := ⟨fun i => (pairFunction v i : D),1⟩

private theorem wreathAut_innerWord (v : Model) : wreathAut (innerWord v) = MulAut.conj v := by
  apply MulEquiv.ext
  intro x
  apply pairFunction.injective
  funext i
  rw [wreathAut_pair]
  simp only [innerWord,inv_one,one_mul,MulAut.conj_apply,map_mul,map_inv,
    Pi.mul_apply,Pi.inv_apply]
  rfl

private theorem pairAut_inner (v : Model) : pairAutEquiv' (MulAut.conj v) = innerWord v := by
  apply pairAutEquiv.injective
  exact (pairAutEquiv.apply_symm_apply _).trans (wreathAut_innerWord v).symm

/-- The actual inner automorphisms are exactly the alternating base. -/
theorem map_inner_eq_alternatingBase :
    (MulAut.innerSubgroup Model).map pairAutEquiv'.toMonoidHom = Thompson.alternatingBase := by
  ext w
  constructor
  · rintro ⟨a,⟨v,rfl⟩,rfl⟩
    change pairAutEquiv' (MulAut.conj v) ∈ Thompson.alternatingBase
    rw [pairAut_inner,Thompson.mem_alternatingBase]
    exact ⟨rfl,fun i => (pairFunction v i).property⟩
  · intro hw
    obtain ⟨hr,hl⟩ := (Thompson.mem_alternatingBase w).mp hw
    let v : Model := (⟨w.left 1,hl 1⟩,⟨w.left (Multiplicative.ofAdd 1),hl _⟩)
    have he : innerWord v = w := by
      apply RegularWreathProduct.ext
      · funext i
        have hi : ∀ i : Q, i = 1 ∨ i = Multiplicative.ofAdd 1 := by decide
        rcases hi i with rfl | rfl <;> simp [innerWord,pairFunction,v]
      · exact hr.symm
    exact ⟨MulAut.conj v,⟨v,rfl⟩,(pairAut_inner v).trans he⟩

/-- A nonswapping actor preserves the literal first A₄ factor. -/
theorem map_axis0_of_mem_base (w : W) (hw : w ∈ Thompson.base) :
    axis0.map (wreathAut w).toMonoidHom = axis0 := by
  have hr := (Thompson.mem_base w).mp hw
  have hle : axis0.map (wreathAut w).toMonoidHom ≤ axis0 := by
    rintro y ⟨x,hx,rfl⟩
    have hx2 : x.2 = 1 := hx.2
    have hh := wreathAut_pair w x (Multiplicative.ofAdd 1)
    have hy2 : (wreathAut w x).2 = 1 := by
      simpa [pairFunction,hr,hx2] using hh
    exact ⟨mem_top _,hy2⟩
  exact eq_of_le_of_card_ge hle (by
    rw [card_map_of_injective (wreathAut w).injective])

/-- The two literal A₄ factors are distinct. -/
theorem axis0_ne_axis1 : axis0 ≠ axis1 := by
  intro he
  have h : (c3,1) ∈ axis0 := ⟨mem_top _,by simp⟩
  rw [he] at h
  exact c_order_ne h.1

end AlternatingFourPair
