module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFiveSylowFixed
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedFive.ActionCore
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction
import all CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction


/-!
# The actual action on a normal alternating-five block

The fixed layer vanishes, so the defining natural quotient identifies the
whole block module with the four-dimensional binary core. The normalizer
theorem extends its inner action to the ambient group, retaining the chosen
O₂ quotient map and identifying the kernel with the literal centralizer.

Source: Aschbacher--Smith C.1.13(c) and preliminary 15.2.23, printed
pp.124--125 and1115, refs/quasithin.pdf.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
open RankOne.ChiProduct.SelectedRankOne.PairedFive
variable {G : Type*} [Group G]

theorem IsAlternatingBlock.five_normal_action (X : Subgroup G) [X.Normal]
    (hb : IsAlternatingBlock X 5) :
    ∃ q : (X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5),
    ∃ E : blockU X ≃* Multiplicative (BinaryPermutation.core (Fin 5)),
    ∃ f : G →* Equiv.Perm (Fin 5),
      (∀ x : X, f x = (q (QuotientGroup.mk' (pCore 2 X) x)).val) ∧
      (∀ g u, (E (MulAut.characteristic (blockU X) (MulAut.conjNormal g) u)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 5) (f g) (E u).toAdd) ∧
      X.map f = alternatingGroup (Fin 5) ∧
      (f.comp X.subtype).ker = pCore 2 X ∧
      f.ker = centralizer ((blockU X).map X.subtype : Set G) := by
  obtain ⟨r,⟨m⟩,hm⟩ := hb.2.2
  let t := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  let p : blockU X ≃* BlockModule X := MulEquiv.ofBijective
    (QuotientGroup.mk' (blockFixed X))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by
      rw [QuotientGroup.ker_mk', hb.blockFixed_eq_bot]), QuotientGroup.mk'_surjective _⟩
  let E : blockU X ≃* Multiplicative (BinaryPermutation.core (Fin 5)) :=
    (p.trans m.moduleIso).trans t.symm.toAddEquiv.toMultiplicative
  let W := (blockU X).map X.subtype
  let : IsElementaryAbelian 2 (blockU X) := hb.2.1.elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map X.subtype
  let j : blockU X ≃* W := (blockU X).equivMapOfInjective X.subtype X.subtype_injective
  let F : W ≃* Multiplicative (BinaryPermutation.core (Fin 5)) := j.symm.trans E
  let e : Additive W ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 5) :=
    LinearEquiv.ofBijective (F.toMonoidHom.toAdditiveLeft.toZModLinearMap 2) F.bijective
  have hq (u : blockU X) : t (E u).toAdd =
      (m.moduleIso (QuotientGroup.mk' (blockFixed X) u)).toAdd := t.apply_symm_apply _
  have hE (x : X) (u : blockU X) : (E (blockConjugate X x u)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 5) (m.actor x).val (E u).toAdd := by
    apply t.injective
    rw [hq, BinaryPermutation.coreEquivNatural_equivariant, hq, m.intertwining, hm]
    rfl
  have hc (g : G) (u : blockU X) :
      j (MulAut.characteristic (blockU X) (MulAut.conjNormal g) u) =
        MulAut.conjNormal g (j u) := by
    apply Subtype.ext
    rfl
  have hj (x : X) (v : Additive W) :
      j.symm (conjugationAction W x.val v).toMul = blockConjugate X x (j.symm v.toMul) := by
    apply j.injective
    rw [j.apply_symm_apply]
    apply Subtype.ext
    change (x : G) * (v.toMul : G) * (x : G)⁻¹ =
      (x : G) * (((j.symm v.toMul : blockU X) : X) : G) * (x : G)⁻¹
    congr 2
    exact (congrArg Subtype.val (j.apply_symm_apply v.toMul)).symm
  obtain ⟨f,hker,himage,hf⟩ := ambient_five_action W X m.actor m.actor_surjective e (by
    intro x v
    change (E (j.symm _)).toAdd = _
    rw [hj]
    exact hE x (j.symm v.toMul))
  have hfE (g : G) (u : blockU X) :
      (E (MulAut.characteristic (blockU X) (MulAut.conjNormal g) u)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 5) (f g) (E u).toAdd := by
    have hh := hf g (Additive.ofMul (j u))
    change (E (j.symm (MulAut.conjNormal g (j u)))).toAdd =
      BinaryPermutation.coreRepresentation (Fin 5) (f g) (E (j.symm (j u))).toAdd at hh
    rw [←hc,j.symm_apply_apply,j.symm_apply_apply] at hh
    exact hh
  have hmark (x : X) : f x = (m.actor x).val := by
    apply coreRepresentation_injective
    ext v
    obtain ⟨u,hu⟩ := E.surjective (Multiplicative.ofAdd v)
    have hv : (E u).toAdd = v := congrArg Multiplicative.toAdd hu
    rw [←hv,←hfE,←hE]
    rfl
  refine ⟨m.quotientIso,E,f,hmark,hfE,himage,?_,hker⟩
  ext x
  change f x = 1 ↔ x ∈ pCore 2 X
  rw [hmark]
  constructor
  · intro hx
    apply (QuotientGroup.eq_one_iff (N := pCore 2 X) x).mp
    apply m.quotientIso.injective
    rw [map_one]
    exact Subtype.ext hx
  · intro hx
    have he : QuotientGroup.mk' (pCore 2 X) x = 1 :=
      (QuotientGroup.eq_one_iff (N := pCore 2 X) x).mpr hx
    change (m.quotientIso (QuotientGroup.mk' (pCore 2 X) x)).val = 1
    rw [he,map_one]
    rfl
end CFSG.Quasithin.ChapterC

