module
public import Theory.Representation.BinaryTransvectionGroups.RootForms.Generation
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Mathlib.RepresentationTheory.Irreducible
/-!
# A full center and an irreducible normal action

Let H act irreducibly on a binary space of dimension at least three, and let
an abelian group Y normalize H. If Y contains every transvection with one
fixed nonzero center, then H is the full general linear group.

Indeed, the full transvection directions of HY form an H-invariant subspace
containing that center. Irreducibility makes it the whole space, so generation
by transvections gives HY = GL. Perfectness of binary GL then gives H = GL,
since its quotient by H is abelian.

This supplies the irreducible full-center case used in Aschbacher--Smith
G.3.1 and G.10.15(1)(ii), printed pp.337--338 and 361--362. It uses the actual
full-center hypothesis and does not use the unguarded legacy G.3.1 interface.
-/

@[expose] public noncomputable section
open Subgroup Module BinaryLinear BinaryLinear.FourCentralizerOvergroups
namespace BinaryTransvectionGroups
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A normal irreducible subgroup supplemented by an abelian full center is GL. -/
theorem normal_eq_top_of_irreducible_full_center
    (H Y : Subgroup (BinaryLinear.GL V)) [IsMulCommutative Y]
    (hY : Y ≤ normalizer (H : Set (BinaryLinear.GL V)))
    (hi : ∀ U : Submodule (ZMod 2) V, H ≤ parabolic U → U = ⊥ ∨ U = ⊤)
    (hd : 3 ≤ finrank (ZMod 2) V) (v : V) (hv : v ≠ 0)
    (hfull : ∀ f : Module.Dual (ZMod 2) V, ∀ hf : f v = 0,
      transvection v f hf ∈ Y) : H = ⊤ := by
  let K := H ⊔ Y
  have hvD : v ∈ directions K := fun f hf => (le_sup_right : Y ≤ K) (hfull f hf)
  have hdir : directions K = ⊤ := by
    rcases hi (directions K) ((le_sup_left : H ≤ K).trans (le_parabolic_directions K)) with hz | ht
    · rw [hz] at hvD
      exact (hv hvD).elim
    · exact ht
  have hK : H ⊔ Y = ⊤ := eq_top_of_directions_eq_top K hdir
  let : H.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [← hK]
    exact sup_le H.le_normalizer hY))
  let n := finrank (ZMod 2) V
  let e : V ≃ₗ[ZMod 2] OuterCyclic.Space n := LinearEquiv.ofFinrankEq _ _ (by
    simp only [OuterCyclic.Space,Module.finrank_pi,Fintype.card_fin]
    rfl)
  let E : BinaryLinear.GL V ≃* OuterCyclic.LinearGroup n :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm.trans
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv e).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (OuterCyclic.Space n)))
  let : Group.IsPerfect (OuterCyclic.LinearGroup n) := linearGroup_isPerfect n hd
  let : Group.IsPerfect (BinaryLinear.GL V) := Group.IsPerfect.ofSurjective (f:=E.symm.toMonoidHom) E.symm.surjective
  have hc := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hK inferInstance
  rw [Group.IsPerfect.commutator_eq_top] at hc
  exact top_unique hc
end BinaryTransvectionGroups

namespace Representation
variable {G A V : Type*} [Group G] [Group A] [IsMulCommutative A]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Representation form of the full-center recognition result, with literal action maps. -/
theorem normalAction_surjective_of_full_center
    (ρ : Representation (ZMod 2) G V) (H : Subgroup G) [H.Normal]
    (α : A →* G) (hi : IsIrreducible (ρ.comp H.subtype))
    (hd : 3 ≤ finrank (ZMod 2) V) (v : V) (hv : v ≠ 0)
    (hfull : ∀ f : Module.Dual (ZMod 2) V, f v = 0 →
      ∃ a : A, ∀ w : V, ρ (α a) w = w + f w • v) :
    Function.Surjective (Representation.asGroupHom (ρ.comp H.subtype)) := by
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V
  let π : G →* BinaryLinear.GL V := e.toMonoidHom.comp ρ.asGroupHom
  have htop : H.map π = ⊤ := by
    refine BinaryTransvectionGroups.normal_eq_top_of_irreducible_full_center
      (H.map π) (α.range.map π) ?_ ?_ hd v hv ?_
    · exact (Subgroup.map_mono (show α.range ≤ normalizer (H : Set G) from le_top.trans H.normalizer_eq_top.ge)).trans
        (Subgroup.le_normalizer_map π)
    · intro U hU
      let R : Subrepresentation (ρ.comp H.subtype) := ⟨U,fun g w hw =>
        (hU (Subgroup.mem_map_of_mem π g.property) w).2 hw⟩
      rcases hi.eq_bot_or_eq_top R with hb | ht
      · exact Or.inl (congrArg Subrepresentation.toSubmodule hb)
      · exact Or.inr (congrArg Subrepresentation.toSubmodule ht)
    · intro f hf
      obtain ⟨a,ha⟩ := hfull f hf
      refine ⟨α a,⟨a,rfl⟩,?_⟩
      exact LinearEquiv.ext (fun w => ha w)
  intro a
  obtain ⟨g,hg,he⟩ := htop.ge (Subgroup.mem_top (e a))
  exact ⟨⟨g,hg⟩,e.injective he⟩
end Representation

