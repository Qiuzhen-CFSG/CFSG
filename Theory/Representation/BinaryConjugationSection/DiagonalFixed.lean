module

public import Theory.GroupTheory.IndexTwoOmegaDiagonal
public import Theory.Representation.BinaryConjugationSection

/-!
# Fixed coordinates from an index-two diagonal

An involution central in an index-two subgroup gives a central diagonal in
its overgroup. An actor preserving the two factors and centralizing this
diagonal fixes the first factor modulo their intersection. A binary
conjugation section turns this into equality of coordinates whenever its
kernel contains that intersection.

This separates the group-theoretic diagonal argument from the subsequent
natural, Hermitian or Suzuki module calculation.
Source: Aschbacher--Smith, 10.1.2(5), printed p.742.
-/

public noncomputable section

open Subgroup Stellmacher Representation

namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] {R S T W Z : Subgroup G}
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) R V}

/-- An actor centralizing the central diagonal fixes the retained coordinates
of each involution central in the index-two subgroup. -/
theorem coordinates_conj_eq_of_centralizes_diagonal
    (d : BinaryConjugationSection R W Z ρ)
    (hST : S ≤ T) (hi : S.relIndex T = 2)
    (t : G) (ht : t ∈ T) (htS : t ∉ S)
    (hinter : W ⊓ W.map (MulAut.conj t).toMonoidHom ≤ Z)
    (w : W) (hwS : (w : G) ∈ omegaOneCenterAmbient S)
    (hc : Commute (w : G) (t*w*t⁻¹))
    (b : G) (hbW : b ∈ normalizer (W : Set G))
    (hbWt : b ∈ normalizer (W.map (MulAut.conj t).toMonoidHom : Set G))
    (hbZ : b ∈ centralizer (omegaOneCenterAmbient T : Set G)) :
    d.coordinates ⟨b*w*b⁻¹,(mem_normalizer_iff.mp hbW w).mp w.property⟩ =
      d.coordinates w := by
  let v := t*(w:G)*t⁻¹
  have hv : v ∈ W.map (MulAut.conj t).toMonoidHom := mem_map_of_mem _ w.property
  have hz : (w:G)*v ∈ omegaOneCenterAmbient T :=
    indexTwo_diagonal_mem_omegaCenter S T hST hi t ht htS w hwS hc
  have hfixed : b*((w:G)*v)*b⁻¹ = (w:G)*v := by
    rw [←hbZ _ hz,mul_inv_cancel_right]
  let wb : W := ⟨b*w*b⁻¹,(mem_normalizer_iff.mp hbW w).mp w.property⟩
  have hvb : b*v*b⁻¹ ∈ W.map (MulAut.conj t).toMonoidHom :=
    (mem_normalizer_iff.mp hbWt v).mp hv
  have hdiff : ((w⁻¹*wb : W):G) = v*(b*v*b⁻¹)⁻¹ := by
    have he : (wb:G)*(b*v*b⁻¹) = (w:G)*v := by
      calc
        (wb:G)*(b*v*b⁻¹) = b*((w:G)*v)*b⁻¹ := by dsimp [wb]; group
        _ = _ := hfixed
    calc
      ((w⁻¹*wb : W):G) = (w:G)⁻¹*((wb:G)*(b*v*b⁻¹))*(b*v*b⁻¹)⁻¹ := by
        change (w:G)⁻¹*(wb:G) = _
        group
      _ = v*(b*v*b⁻¹)⁻¹ := by rw [he]; group
  have hker : ((w⁻¹*wb : W):G) ∈ Z := by
    apply hinter
    refine ⟨(w⁻¹*wb).property,?_⟩
    rw [hdiff]
    exact (W.map (MulAut.conj t).toMonoidHom).mul_mem hv
      ((W.map (MulAut.conj t).toMonoidHom).inv_mem hvb)
  have he := (d.coordinates_eq_one_iff (w⁻¹*wb)).mpr hker
  rw [map_mul,map_inv,inv_mul_eq_one] at he
  exact he.symm

end Representation.BinaryConjugationSection
