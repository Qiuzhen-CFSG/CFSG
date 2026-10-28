module
public import Theory.GroupTheory.WreathTwoElementaryRank
public import Theory.Frattini.PGroupMap

/-!
# Frattini kernels in binary wreath products

A homomorphism of the base groups induces the literal coordinate map of
regular wreath products. If its kernel lies in the Frattini subgroup of a
finite two-group, the binary wreath map also has Frattini kernel: embed
each coordinate and use functoriality of the Frattini subgroup. Therefore
surjectivity after this reduction forces the original wreath image to be full.

The PSL₂(16) application uses the field action on cube roots of unity.
Source: the outer-action step in Aschbacher--Smith 14.6.14(4), printed p.1033.
-/

public section
open Subgroup
namespace RegularWreathProduct
variable {D E Q : Type*} [Group D] [Group E] [Group Q]

@[expose] def mapBase (f : D →* E) : RegularWreathProduct D Q →* RegularWreathProduct E Q where
  toFun w := ⟨fun i => f (w.left i), w.right⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp

theorem mapBase_surjective (f : D →* E) (hf : Function.Surjective f) :
    Function.Surjective (mapBase (Q := Q) f) := by
  classical
  intro w
  choose g hg using hf
  exact ⟨⟨fun i => g (w.left i),w.right⟩,by ext <;> simp [mapBase,hg]⟩

theorem mapBase_comp {A : Type*} [Group A] (f : D →* E) (g : E →* A) :
    (mapBase (Q := Q) g).comp (mapBase f) = mapBase (g.comp f) := rfl

end RegularWreathProduct

namespace Theory.GroupTheory.WreathTwoElementaryRank
variable {D E : Type*} [Group D] [Group E]

/-- A wreath base map whose factor kernel is Frattini has a Frattini kernel. -/
theorem wreath_map_ker_le_frattini [Finite D]
    (hD : IsPGroup 2 D) (f : D →* E) (hk : f.ker ≤ frattini D) :
    (RegularWreathProduct.mapBase (Q := C2) f).ker ≤ frattini (W D) := by
  let : Fact (IsPGroup 2 D) := ⟨hD⟩
  have hW : IsPGroup 2 (W D) := by
    obtain ⟨n,hn⟩ := hD.exists_card_eq
    apply IsPGroup.of_card (n := n*2+1)
    rw [RegularWreathProduct.card,show Nat.card C2 = 2 from Nat.card_zmod 2,hn]
    simp only [pow_succ,pow_mul]
  let : Fact (IsPGroup 2 (W D)) := ⟨hW⟩
  let l : D →* W D := baseHom.comp (MonoidHom.inl D D)
  let r : D →* W D := baseHom.comp (MonoidHom.inr D D)
  intro w hw
  have hr : w.right = 1 := congrArg RegularWreathProduct.right hw
  have hc (i : C2) : w.left i ∈ frattini D :=
    hk (show f (w.left i) = 1 from congrArg (fun v => v.left i) hw)
  have hleft := frattini_map_le_of_isPGroup (p := 2) l (mem_map_of_mem l (hc 1))
  have hright := frattini_map_le_of_isPGroup (p := 2) r (mem_map_of_mem r (hc turn))
  have he : l (w.left 1) * r (w.left turn) = w := by
    apply RegularWreathProduct.ext
    · funext i
      rcases index_cases i with rfl | rfl <;>
        simp [l,r,baseHom,turn_ne_one]
    · exact hr.symm
  exact he ▸ (frattini (W D)).mul_mem hleft hright

/-- Full image after the factor Frattini reduction forces full wreath image. -/
theorem wreath_surjective_of_frattini_reduction [Finite D]
    (hD : IsPGroup 2 D) (f : D →* E)
    (hk : f.ker ≤ frattini D)
    {A : Type*} [Group A] (ρ : A →* W D)
    (hρ : Function.Surjective ((RegularWreathProduct.mapBase f).comp ρ)) :
    Function.Surjective ρ := by
  let q := RegularWreathProduct.mapBase (Q := C2) f
  have hi : ρ.range.map q = ⊤ := by
    rw [←MonoidHom.range_comp]
    exact MonoidHom.range_eq_top.mpr hρ
  have hgen : ρ.range ⊔ q.ker = ⊤ := by
    have hh := congrArg (comap q) hi
    simpa only [comap_map_eq,comap_top] using hh
  apply MonoidHom.range_eq_top.mp
  apply frattini_nongenerating
  exact top_unique (hgen ▸ sup_le_sup_left (wreath_map_ker_le_frattini hD f hk) ρ.range)

end Theory.GroupTheory.WreathTwoElementaryRank
