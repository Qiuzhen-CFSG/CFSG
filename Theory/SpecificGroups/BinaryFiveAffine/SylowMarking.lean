module
public import Theory.Representation.BinaryAlternatingFiveExtension.MarkedSylow
public import Theory.SpecificGroups.BinaryFiveAffine.Marking
public import Theory.SpecificGroups.SymmetricFive.AutomorphismRank
public import Theory.GroupTheory.PCoreSurjective
/-!
# Marking the natural module and Sylow subgroup in the binary affine model

The binary vector subgroup is the full two-core of the affine extension by
S5. Therefore every group isomorphism preserves this subgroup. Composing an
isomorphism with conjugation aligns any chosen Sylow subgroup with the literal
four-coordinate dihedral wreath model, retaining the natural-module marking.

Source: Aschbacher--Smith, 2.4.29, printed p.545.
-/

@[expose] public section
open Subgroup
namespace BinaryFiveAffine
noncomputable abbrev standardSylow : Sylow 2 W := BinaryPermutation.AlternatingFiveExtension.SylowModel.standardSylow

theorem pCore_eq_vectorGroup : pCore 2 W = vectorGroup := by
  let q : W →* S := SemidirectProduct.rightHom
  have hq : Function.Surjective q := fun g=>⟨SemidirectProduct.inr g,rfl⟩
  have hk : q.ker=vectorGroup := by ext w; exact (mem_vectorGroup w).symm
  have hc : Nat.card q.ker=16 := by
    rw [hk,vectorGroup,←Nat.card_congr (MonoidHom.ofInjective (f:=(SemidirectProduct.inl:V→*W)) SemidirectProduct.inl_injective).toEquiv]
    exact card_vectors
  have hp : IsPGroup 2 q.ker := IsPGroup.of_card (n:=4) hc
  have hh := q.comap_pCore_of_ker_isPGroup hq hp
  rw [Theory.SpecificGroups.SymmetricFive.pCore_two_eq_bot,MonoidHom.comap_bot,hk] at hh
  exact hh.symm

theorem exists_sylow_marked_equiv {H : Type*} [Group H] [Finite H]
    (e : H ≃* W) (U : Subgroup H) (hU : pCore 2 H=U) (T : Sylow 2 H) :
    ∃ f : H ≃* W, U.map f.toMonoidHom=vectorGroup ∧
      (T:Subgroup H).map f.toMonoidHom=(standardSylow:Subgroup W) := by
  let T' := T.mapSurjective (f:=e.toMonoidHom) e.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq W T' standardSylow
  let f := e.trans (MulAut.conj g)
  refine ⟨f,?_,?_⟩
  · rw [←hU,pCore_map_iso,pCore_eq_vectorGroup]
  · have hh := congrArg Sylow.toSubgroup hg
    change ((T:Subgroup H).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = _ at hh
    have hf : f.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      rfl
    rwa [hf, ←map_map]
end BinaryFiveAffine