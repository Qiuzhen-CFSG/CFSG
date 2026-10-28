module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Recognition.Coordinates
public import Theory.Representation.PSL3Two.NaturalDualCentralizer
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.Assembly

/-!
# Faithful conjugation on the recognized normal actor

The literal U/Z is natural plus dual for K*. Its concrete invertible
commutant is trivial, so the ambient quotient embeds into Aut(K*) by
conjugation. The irreducibility from 15.3.57 excludes an entirely inner
image; the checked index two of Inn(PSL3(2)) then makes the embedding onto.
Source: Aschbacher–Smith 15.3.58, printed p.1149.
-/

@[expose] public section

open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
open NormalReduction
universe u
variable {G : Type u} [Group G] [Finite G] {Z ZS V M : Subgroup G}
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)] [IsElementaryAbelian 2 V]
  {C : GroupClass.{u}} {v : ActorQuotient Z} {s : ℕ}
  {d : EarlierSourceInputs Z ZS V M C v s} {a : EarlierActionInputs d}

namespace NaturalPair
variable (p : NaturalPair d a)

/-- The same faithful action expressed in natural–dual coordinates. -/
noncomputable def coordinateActor (h : ActorQuotient Z) :
    BinaryLinearThree.NaturalDual.Space ≃ₗ[ZMod 2] BinaryLinearThree.NaturalDual.Space :=
  p.linearCoordinates.symm.trans
    ((LinearMap.GeneralLinearGroup.toLinearEquiv
      ((actorRepresentation Z ZS d.kernel).asGroupHom h)).trans p.linearCoordinates)

omit [Finite G] in
theorem coordinateActor_apply (h : ActorQuotient Z)
    (x : BinaryLinearThree.NaturalDual.Space) :
    p.coordinateActor h x = p.linearCoordinates
      (actorRepresentation Z ZS d.kernel h (p.linearCoordinates.symm x)) := rfl

omit [Finite G] in
theorem coordinateActor_K (k : p.K) (x : BinaryLinearThree.NaturalDual.Space) :
    p.coordinateActor k x = BinaryLinearThree.NaturalDual.action
      (Matrix.PSL3Two.equiv.symm (p.first_model.actor k)) x := by
  rw [p.coordinateActor_apply, p.linearCoordinates_equivariant,
    p.linearCoordinates.apply_symm_apply]
  rfl

omit [Finite G] in
/-- Faithfulness of the original quotient identifies its K*-centralizer. -/
theorem centralizer_eq_bot : centralizer (p.K : Set (ActorQuotient Z)) = ⊥ := by
  apply le_bot_iff.mp
  intro c hc
  have hf : ∀ g x, p.coordinateActor c (BinaryLinearThree.NaturalDual.action g x) =
      BinaryLinearThree.NaturalDual.action g (p.coordinateActor c x) := by
    intro g x
    obtain ⟨k, rfl⟩ := (p.first_model.actor.trans Matrix.PSL3Two.equiv.symm).surjective g
    simp only [MulEquiv.trans_apply]
    rw [← p.coordinateActor_K, ← p.coordinateActor_K]
    simp only [p.coordinateActor_apply, p.linearCoordinates.symm_apply_apply]
    congr 1
    have hcomm := (mem_centralizer_iff.mp hc) k k.property
    have h := congrArg (fun g : ActorQuotient Z =>
      actorRepresentation Z ZS d.kernel g (p.linearCoordinates.symm x)) hcomm
    simpa only [map_mul, Module.End.mul_apply] using h.symm
  have he := BinaryLinearThree.NaturalDual.centralizer_eq_one (p.coordinateActor c) hf
  apply mem_bot.mpr
  apply actorRepresentation_injective Z ZS d.kernel
  apply LinearMap.ext
  intro w
  have h := congrArg (fun f : BinaryLinearThree.NaturalDual.Space ≃ₗ[ZMod 2]
    BinaryLinearThree.NaturalDual.Space => f (p.linearCoordinates w)) he
  simp only [p.coordinateActor_apply, p.linearCoordinates.symm_apply_apply,
    LinearEquiv.refl_apply] at h
  have hw := p.linearCoordinates.injective h
  simpa only [map_one, Module.End.one_apply] using hw

omit [Finite G] in
theorem first_ne_bot : p.pair.first.toSubmodule ≠ ⊥ := by
  intro h
  have hd := p.first_model.finrank_eq_three
  rw [h, finrank_bot] at hd
  omega

omit [Finite G] in
theorem first_ne_top : p.pair.first.toSubmodule ≠ ⊤ := by
  intro h
  have hb : p.pair.second.toSubmodule = ⊥ := by
    apply bot_unique
    intro w hw
    exact p.pair.complement.disjoint.le_bot ⟨by rw [h]; trivial, hw⟩
  have hd := p.second_model.finrank_eq_three
  rw [hb, finrank_bot] at hd
  omega

/-- The normal actor cannot be the entire irreducible ambient actor. -/
theorem K_ne_top : p.K ≠ ⊤ := by
  intro hK
  let J : Subrepresentation (actorRepresentation Z ZS d.kernel) := {
    toSubmodule := p.pair.first.toSubmodule
    apply_mem_toSubmodule := by
      intro g w hw
      exact p.pair.first.apply_mem_toSubmodule ⟨g, by rw [hK]; trivial⟩ hw }
  have hi := (normal_reduction_of_earlier_source d).irreducible
  rw [Representation.IsIrreducible, isSimpleOrder_iff] at hi
  rcases hi.2 J with hb | ht
  · exact p.first_ne_bot (congrArg Subrepresentation.toSubmodule hb)
  · exact p.first_ne_top (congrArg Subrepresentation.toSubmodule ht)

/-- The actor is identified by actual conjugation on the recognized K*. -/
noncomputable def actorEquiv : ActorQuotient Z ≃* MulAut Matrix.PSL3Two.PSL := by
  let := p.minimal.minimal.1
  let φ := SplitBranch.actorConjugation p.K p.first_model.actor
  have hi : Function.Injective φ :=
    SplitBranch.actorConjugation_injective p.K p.first_model.actor p.centralizer_eq_bot
  have ht : ∃ t : ActorQuotient Z, φ t ∉ MulAut.innerSubgroup Matrix.PSL3Two.PSL := by
    by_contra hn
    push Not at hn
    apply p.K_ne_top
    apply top_unique
    intro t _
    obtain ⟨x, hx⟩ := hn t
    obtain ⟨k, rfl⟩ := p.first_model.actor.surjective x
    have he : φ k = φ t :=
      (SplitBranch.actorConjugation_on_normal p.K p.first_model.actor k).trans hx
    exact hi he ▸ k.property
  have hr : φ.range = ⊤ := by
    obtain ⟨t, ht⟩ := ht
    exact SplitBranch.actorConjugation_range_top_of_outer
      p.K p.first_model.actor t
      (SplitBranch.inner_le_actorConjugation_range p.K p.first_model.actor) ht
      SplitBranch.psl_inner_index
  exact MulEquiv.ofBijective φ ⟨hi, by
    intro x
    have hx : x ∈ φ.range := by rw [hr]; trivial
    exact hx⟩

theorem actorEquiv_apply (h : ActorQuotient Z) :
    p.actorEquiv h =
      @SplitBranch.actorConjugation _ _ _ _ p.K p.minimal.minimal.1
        p.first_model.actor h := rfl

/-- The selected minimal normal subgroup is exactly the inner actor. -/
theorem actorEquiv_K : p.K.map p.actorEquiv.toMonoidHom =
    MulAut.innerSubgroup Matrix.PSL3Two.PSL := by
  let := p.minimal.minimal.1
  apply le_antisymm
  · rintro x ⟨k, hk, rfl⟩
    refine ⟨p.first_model.actor ⟨k, hk⟩, ?_⟩
    exact (SplitBranch.actorConjugation_on_normal p.K p.first_model.actor ⟨k, hk⟩).symm
  · rintro x ⟨g, rfl⟩
    obtain ⟨k, rfl⟩ := p.first_model.actor.surjective g
    exact ⟨k, k.property,
      SplitBranch.actorConjugation_on_normal p.K p.first_model.actor k⟩

/-- The recognized normal subgroup is the genuine two-residual. -/
theorem residual_eq_K : pResidual 2 (ActorQuotient Z) = p.K := by
  let := p.minimal.minimal.1
  have hi : p.K.index = 2 := by
    rw [← index_map_equiv p.K p.actorEquiv]
    change (p.K.map p.actorEquiv.toMonoidHom).index = 2
    rw [p.actorEquiv_K]
    exact SplitBranch.psl_inner_index
  have hq : IsPGroup 2 (ActorQuotient Z ⧸ p.K) :=
    IsPGroup.of_card (n := 1) (by simpa only [index_eq_card, pow_one] using hi)
  apply le_antisymm
  · exact sInf_le ⟨inferInstance, hq⟩
  · rw [← p.minimal.two_residual_image]
    exact map_pResidual_le 2 p.K.subtype

end NaturalPair
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
