module
public import Theory.Representation.SL5ExteriorSquare.RadicalFixed.Endpoint
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.NormalPerfect

/-!
# Perfect normal subgroups of a radical normalizer with six fixed dimensions

The retained endpoint conjugation identifies the original radical normalizer
with the literal hyperplane parabolic. Transporting the same perfect normal
subgroup preserves its order and nontriviality, so the simple SL4(2) Levi
quotient forces a factor five. No replacement subgroup or parabolic premise
is assumed.
Source: Aschbacher--Smith C.4.8 and 12.1.11, pp.154,794.
-/
public noncomputable section
open Subgroup
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

/-- A nontrivial perfect normal subgroup of the actual radical normalizer
has order divisible by five when the radical fixes at least six dimensions. -/
theorem five_dvd_card_of_normal_perfect_radical_normalizer
    (P : Subgroup Group) (hP : P.IsPRadical 2)
    (hd : 6 ≤ Module.finrank (ZMod 2) (BinaryOffender.fixedSpace (exteriorAction 2) P))
    (B : Subgroup (normalizer (P : Set Group))) [B.Normal] [Group.IsPerfect B]
    (hB : B ≠ ⊥) : 5 ∣ Nat.card B := by
  obtain ⟨g,_,hN,_,_⟩ := radical_six_fixed_hyperplane P hP hd
  let e : normalizer (P : Set Group) ≃* parabolic 4 :=
    ((MulAut.conj g).subgroupMap (normalizer (P : Set Group))).trans
      (MulEquiv.subgroupCongr ((map_equiv_normalizer_eq P (MulAut.conj g)).trans hN))
  let C := B.map e.toMonoidHom
  let t : B ≃* C := B.equivMapOfInjective e.toMonoidHom e.injective
  let : C.Normal := Normal.map inferInstance e.toMonoidHom e.surjective
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective (f := t.toMonoidHom) t.surjective
  have hC : C ≠ ⊥ := fun he =>
    hB ((B.map_eq_bot_iff_of_injective (f := e.toMonoidHom) e.injective).mp he)
  have hdiv := LocalGeometry.ParabolicStructure.five_dvd_card_of_normal_perfect C hC
  rwa [←Nat.card_congr t.toEquiv] at hdiv

end Representation.SL5ExteriorSquare
