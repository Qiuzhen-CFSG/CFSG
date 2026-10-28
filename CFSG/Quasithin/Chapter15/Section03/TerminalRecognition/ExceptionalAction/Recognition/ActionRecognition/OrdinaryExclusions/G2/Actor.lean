module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.Reduction
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
public import Theory.GroupTheory.PPerfectHom

/-!
# The actual offender actor in the binary G₂ branch

Every nontrivial normal subgroup of G₂(2) contains its long-root normal
closure, already identified with the actual derived group. That group has
index two. Transport through the supplied quotient isomorphism therefore
leaves exactly the derived and full groups as possible offender actors.
The two-perfect first local factor lies in the derived group in either case.

These are group identifications, not a recognition of the FF action.
Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, final
proof of 15.3.1, printed p.1155. The imported G₂ proofs use the licensed
ATLAS octonion model; no additional ATLAS source is copied here.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2

variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- The nontrivial normal offender actor contains the actual derived group
under the supplied full-quotient identification. -/
theorem derived_le_offenderImage (e : coreQuotient H ≃* Atlas.G2.Model (ZMod 2)) :
    commutator (Atlas.G2.Model (ZMod 2)) ≤ d.offenderGroup.map e.toMonoidHom := by
  let : (d.offenderGroup.map e.toMonoidHom).Normal :=
    (inferInstance : d.offenderGroup.Normal).map e.toMonoidHom e.surjective
  rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
  exact Atlas.G2.BinaryException.H_le_normal _ (fun hb => d.offenderGroup_ne_bot
    ((d.offenderGroup.map_eq_bot_iff_of_injective e.injective).mp hb))

/-- Index two leaves exactly the derived and full offender actors. This does
not identify the offender actor with the full quotient. -/
theorem offenderImage_eq_derived_or_top (e : coreQuotient H ≃* Atlas.G2.Model (ZMod 2)) :
    d.offenderGroup.map e.toMonoidHom = commutator (Atlas.G2.Model (ZMod 2)) ∨
      d.offenderGroup.map e.toMonoidHom = ⊤ := by
  have hl := derived_le_offenderImage d e
  have hm := relIndex_mul_index hl
  rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure,
    Atlas.G2.BinaryException.index_H] at hm
  have hp : ((Atlas.G2.BinaryException.H).relIndex (d.offenderGroup.map e.toMonoidHom) *
      (d.offenderGroup.map e.toMonoidHom).index).Prime := hm.symm ▸ (by decide : Nat.Prime 2)
  rcases Nat.prime_mul_iff.mp hp with ⟨_, hi⟩ | ⟨_, hr⟩
  · exact Or.inr (index_eq_one.mp hi)
  · exact Or.inl (le_antisymm (by
      rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
      exact relIndex_eq_one.mp hr) hl)

/-- Actual multiplicative equivalences for the two possible offender actors. -/
theorem offenderGroup_models (e : coreQuotient H ≃* Atlas.G2.Model (ZMod 2)) :
    Nonempty (d.offenderGroup ≃* commutator (Atlas.G2.Model (ZMod 2))) ∨
      Nonempty (d.offenderGroup ≃* Atlas.G2.Model (ZMod 2)) := by
  let f := d.offenderGroup.equivMapOfInjective e.toMonoidHom e.injective
  rcases offenderImage_eq_derived_or_top d e with h | h
  · exact Or.inl ⟨f.trans (MulEquiv.subgroupCongr h)⟩
  · exact Or.inr ⟨(f.trans (MulEquiv.subgroupCongr h)).trans Subgroup.topEquiv⟩

omit [Finite H] [IsElementaryAbelian 2 (moduleClosure V)] in
/-- The two-perfect first local factor maps into the actual derived group;
the quotient by that group has order two. -/
theorem firstImage_le_derived (e : coreQuotient H ≃* Atlas.G2.Model (ZMod 2)) :
    (d.YF.map coreProjection).map e.toMonoidHom ≤
      commutator (Atlas.G2.Model (ZMod 2)) := by
  let D := commutator (Atlas.G2.Model (ZMod 2))
  have hp : IsPGroup 2 (Atlas.G2.Model (ZMod 2) ⧸ D) := by
    apply IsPGroup.of_card (n := 1)
    change Nat.card (Atlas.G2.Model (ZMod 2) ⧸ commutator (Atlas.G2.Model (ZMod 2))) = 2 ^ 1
    rw [← Subgroup.index_eq_card,
      Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure,
      Atlas.G2.BinaryException.index_H]
    rfl
  let f : d.YF →* (Atlas.G2.Model (ZMod 2) ⧸ D) :=
    (QuotientGroup.mk' D).comp (e.toMonoidHom.comp (coreProjection.comp d.YF.subtype))
  have hf : f = 1 := d.first_perfect.hom_eq_one_of_isPGroup hp f
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  apply (QuotientGroup.eq_one_iff _).mp
  exact DFunLike.congr_fun hf ⟨y, hy⟩

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2
