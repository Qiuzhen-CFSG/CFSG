module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Recognition.Actor
public import Theory.Representation.PSL3Two.NaturalDualNormalizer

/-!
# The outer coset interchanges the actual recognized constituents

Transporting conjugation on K* through its natural coordinates gives the
literal covariance equation. The concrete natural–dual normalizer calculation
then identifies the constituent stabilizer with K*, without a new block
permutation assumption. This completes the actor conclusion used in 15.3.58.
Source: Aschbacher–Smith, printed p.1149.
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

/-- Linear-group coordinates for the same automorphism actor. -/
noncomputable def actorEquivSL : ActorQuotient Z ≃* MulAut Matrix.PSL3Two.SL :=
  p.actorEquiv.trans (MulAut.congr Matrix.PSL3Two.equiv.symm)

theorem actorEquivSL_on_K (k : p.K) : p.actorEquivSL k =
    MulAut.conj (Matrix.PSL3Two.equiv.symm (p.first_model.actor k)) := by
  let := p.minimal.minimal.1
  change MulAut.congr Matrix.PSL3Two.equiv.symm (p.actorEquiv k) = _
  rw [p.actorEquiv_apply, SplitBranch.actorConjugation_on_normal]
  ext g : 1
  change Matrix.PSL3Two.equiv.symm
    (p.first_model.actor k * Matrix.PSL3Two.equiv g * (p.first_model.actor k)⁻¹) = _
  simp only [map_mul, map_inv, MulEquiv.symm_apply_apply, MulAut.conj_apply]

theorem actorEquivSL_K : p.K.map p.actorEquivSL.toMonoidHom =
    MulAut.innerSubgroup Matrix.PSL3Two.SL := by
  apply le_antisymm
  · rintro x ⟨k, hk, rfl⟩
    exact ⟨Matrix.PSL3Two.equiv.symm (p.first_model.actor ⟨k, hk⟩),
      (p.actorEquivSL_on_K ⟨k, hk⟩).symm⟩
  · rintro x ⟨g, rfl⟩
    obtain ⟨k, rfl⟩ :=
      (p.first_model.actor.trans Matrix.PSL3Two.equiv.symm).surjective g
    exact ⟨k, k.property, p.actorEquivSL_on_K k⟩

theorem actor_inner_iff (h : ActorQuotient Z) :
    p.actorEquivSL h ∈ MulAut.innerSubgroup Matrix.PSL3Two.SL ↔ h ∈ p.K := by
  rw [← p.actorEquivSL_K]
  exact mem_map_iff_mem p.actorEquivSL.injective

/-- The group conjugation map and the representation use the same marking. -/
theorem coordinateActor_covariance (h : ActorQuotient Z)
    (g : BinaryLinearThree.Group) (x : BinaryLinearThree.NaturalDual.Space) :
    p.coordinateActor h (BinaryLinearThree.NaturalDual.action g x) =
      BinaryLinearThree.NaturalDual.action (p.actorEquivSL h g) (p.coordinateActor h x) := by
  let := p.minimal.minimal.1
  obtain ⟨k, rfl⟩ :=
    (p.first_model.actor.trans Matrix.PSL3Two.equiv.symm).surjective g
  let l : p.K := MulAut.conjNormal h k
  have he : p.actorEquivSL h (Matrix.PSL3Two.equiv.symm (p.first_model.actor k)) =
      Matrix.PSL3Two.equiv.symm (p.first_model.actor l) := by
    simp [actorEquivSL, p.actorEquiv_apply, SplitBranch.actorConjugation,
      MulAut.congr_apply, l]
  simp only [MulEquiv.trans_apply]
  rw [he, ← p.coordinateActor_K, ← p.coordinateActor_K]
  simp only [p.coordinateActor_apply, p.linearCoordinates.symm_apply_apply]
  congr 1
  change actorRepresentation Z ZS d.kernel h
      (actorRepresentation Z ZS d.kernel k (p.linearCoordinates.symm x)) =
    actorRepresentation Z ZS d.kernel (h * (k : ActorQuotient Z) * h⁻¹)
      (actorRepresentation Z ZS d.kernel h (p.linearCoordinates.symm x))
  simp only [← Module.End.mul_apply, ← map_mul]
  simp [mul_assoc]

theorem outer_swaps (h : ActorQuotient Z) (hh : h ∉ p.K) :
    (∀ x : BinaryLinearThree.Vector, (p.coordinateActor h (x, 0)).1 = 0) ∧
    ∀ x : Module.Dual (ZMod 2) BinaryLinearThree.Vector,
      (p.coordinateActor h (0, x)).2 = 0 :=
  BinaryLinearThree.NaturalDual.outer_swaps (p.actorEquivSL h) (p.coordinateActor h)
    (p.coordinateActor_covariance h) (fun hinner => hh ((p.actor_inner_iff h).mp hinner))

theorem map_first_of_inner (h : ActorQuotient Z) (hh : h ∈ p.K) :
    p.pair.first.toSubmodule.map (actorRepresentation Z ZS d.kernel h) =
      p.pair.first.toSubmodule := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.map_le_iff_le_comap.mpr
    intro w hw
    exact p.pair.first.apply_mem_toSubmodule ⟨h, hh⟩ hw
  · exact LinearEquiv.finrank_map_eq
      (LinearMap.GeneralLinearGroup.toLinearEquiv
        ((actorRepresentation Z ZS d.kernel).asGroupHom h)) _

theorem map_first_of_outer (h : ActorQuotient Z) (hh : h ∉ p.K) :
    p.pair.first.toSubmodule.map (actorRepresentation Z ZS d.kernel h) =
      p.pair.second.toSubmodule := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.map_le_iff_le_comap.mpr
    intro w hw
    apply (p.mem_second_iff _).mpr
    have hw0 := (p.mem_first_iff w).mp hw
    have he : p.linearCoordinates w = ((p.linearCoordinates w).1, 0) :=
      Prod.ext rfl hw0
    have hs := (p.outer_swaps h hh).1 (p.linearCoordinates w).1
    rw [← he, p.coordinateActor_apply, p.linearCoordinates.symm_apply_apply] at hs
    exact hs
  · exact (LinearEquiv.finrank_map_eq
      (LinearMap.GeneralLinearGroup.toLinearEquiv
        ((actorRepresentation Z ZS d.kernel).asGroupHom h)) _).trans
      (p.first_model.finrank_eq_three.trans p.second_model.finrank_eq_three.symm)

/-- The earlier actor-recognition interface is now a proved conclusion. -/
noncomputable def actorRecognition : ActorRecognition p where
  equiv := p.actorEquiv
  inner := p.actorEquiv_K
  residual := p.residual_eq_K
  centralizer := p.centralizer_eq_bot
  permutes h := by
    by_cases hh : h ∈ p.K
    · exact Or.inl (p.map_first_of_inner h hh)
    · exact Or.inr (p.map_first_of_outer h hh)
  stabilizer h := by
    constructor
    · intro he
      by_contra hh
      have hsame : p.pair.first.toSubmodule = p.pair.second.toSubmodule :=
        he.symm.trans (p.map_first_of_outer h hh)
      have hdisj := p.pair.complement.disjoint
      rw [← hsame] at hdisj
      exact p.first_ne_bot (disjoint_self.mp hdisj)
    · exact p.map_first_of_inner h

end NaturalPair
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
