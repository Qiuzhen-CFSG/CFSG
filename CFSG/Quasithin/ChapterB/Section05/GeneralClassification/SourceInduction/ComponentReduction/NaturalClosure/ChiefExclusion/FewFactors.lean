module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.Flags
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.FewFactors.SmallDegree
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.FewFactors.MovedHead
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.FewFactors.HeadCount
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.FewFactors.HeadKernel

/-!
# Excluding at most two noncentral factors

The original chief flag bounds every noncentral dual multiplicity of
W = [V,L]. If its noncentral count is at most two, the actual second
natural component acts trivially on these multiplicity spaces, by its
characteristic-two small-degree obstruction. Hence it centralizes the
literal L-head of W. The perfect-action head detection theorem lifts this
to centralization of W, contradicting the supplied cross action.

Thus the exact `InvariantChiefFlag.noncentral` count is greater than two,
including exclusion of zero and one. No invariance of the flag under the
second component or semisimplicity of W is assumed. The original zero-factor
argument remains available without finiteness hypotheses. Construction of
the flag and second component belongs to the surrounding source assembly.

Source: Aschbacher–Smith, B.5.9, printed p.108, the c = 2 assertion
(1 March 2004 manuscript).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure.FewFactors
open QuasisimpleSource
set_option backward.isDefEq.respectTransparency false

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- An exhaustive all-central flag would kill the perfect L-action and hence its cross action. -/
theorem noncentral_pos {A L : Subgroup G} (hL : IsComponent G L)
    (d : SecondComponent ρ A L) (f : InvariantChiefFlag ρ A L ⊤) :
    0 < f.noncentral.card := by
  classical
  by_contra hn
  have he : f.noncentral = ∅ := Finset.card_eq_zero.mp (by omega)
  have ht : ∀ i < f.length, ∀ l v,
      sectionRepresentation (ρ.comp L.subtype) (f.term i) (f.term (i + 1)) l v = v := by
    intro i hi
    by_contra hh
    have hm := f.noncentral_mem.mpr ⟨hi, hh⟩
    rw [he] at hm
    exact Finset.notMem_empty i hm
  let : IsQuasisimple L := hL.2
  let : Group.IsPerfect (⊤ : Subgroup L) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := L)).symm.toMonoidHom)
      Subgroup.topEquiv.symm.surjective
  have hfix := le_fixedSpace_of_central_flag (ρ.comp L.subtype) ⊤ f.term f.start
    f.length (fun i hi l _ => ht i hi l)
  have hmove : moved ρ L = ⊥ := by
    apply (subspaceCommutator_eq_bot_iff ρ ⊤ L).mpr
    intro v _ l
    exact hfix (f.stop.symm ▸ Submodule.mem_top) ⟨l, Subgroup.mem_top l⟩
  apply d.cross_action
  rw [hmove]
  apply bot_unique
  apply Submodule.span_le.mpr
  rintro _ ⟨g, hg, v, hv, rfl⟩
  have hv0 : v = 0 := hv
  simp [hv0]

/-- At most two literal noncentral factors make the second component centralize W = [V,L].
The proof uses its actual natural model and perfectness, without using its cross action. -/
theorem commutator_eq_bot_of_noncentral_card_le_two [Finite G] [Module.Finite (ZMod 2) V]
    {A L : Subgroup G} (hL : IsComponent G L)
    (d : SecondComponent ρ A L) (f : InvariantChiefFlag ρ A L ⊤)
    (hcount : f.noncentral.card ≤ 2) :
    subspaceCommutator ρ (moved ρ L) d.second = ⊥ := by
  let : Group.IsPerfect d.second := d.isComponent.2.toIsPerfect
  have hhead := HeadCount.secondHead_eq_one_of_noncentral_card_le_two ρ hL d f hcount
  have haction := Head.eq_one_of_action_eq_one
    (componentAction ρ L) (secondAction ρ hL d) (moved_commute ρ hL d) hhead
  apply (subspaceCommutator_eq_bot_iff ρ (moved ρ L) d.second).mpr
  intro v hv m
  exact congrArg Subtype.val
    (DFunLike.congr_fun (DFunLike.congr_fun haction m) (⟨v, hv⟩ : moved ρ L))

/-- The nontrivial cross action forces more than two noncentral factors in the original flag.
This is the small-factor exclusion in B.5.9, with no additional source premises. -/
theorem two_lt_noncentral_card [Finite G] [Module.Finite (ZMod 2) V]
    {A L : Subgroup G} (hL : IsComponent G L)
    (d : SecondComponent ρ A L) (f : InvariantChiefFlag ρ A L ⊤) :
    2 < f.noncentral.card := by
  apply Nat.lt_of_not_ge
  intro hcount
  exact d.cross_action (commutator_eq_bot_of_noncentral_card_le_two ρ hL d f hcount)

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure.FewFactors
