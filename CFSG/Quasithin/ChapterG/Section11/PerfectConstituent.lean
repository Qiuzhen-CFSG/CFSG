module
public import CFSG.Quasithin.ChapterG.Section06.Source
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.FullLinearSelfDual
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Perfect irreducible constituents exclude the two-factor G.6.4 row

In the two-factor alternative the normal closure of the marked involution
has a cyclic supplement. Every perfect subgroup lies in that normal closure,
so it normalizes each commuting factor and preserves each moved subspace.
An irreducible perfect restriction and a faithful whole action then contradict
the two nontrivial factors. No identification of an abstract constituent
image is substituted for its actual restriction.

Source: Aschbacher--Smith G.10.16(4), printed pp.363--364.
-/

public section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11

private theorem moved_ne_bot {D U : Type*} [Group D] [AddCommGroup U]
    [Module (ZMod 2) U] (σ : Representation (ZMod 2) D U)
    (hf : Function.Injective σ) (K : Subgroup D) (hk : K ≠ ⊥) :
    subspaceCommutator σ ⊤ K ≠ ⊥ := by
  intro hz
  apply hk
  apply bot_unique
  intro k hk
  apply mem_bot.mpr
  apply hf
  apply LinearMap.ext
  intro u
  have hh := (subspaceCommutator_eq_bot_iff σ ⊤ K).mp hz (Submodule.mem_top (x := u)) ⟨k,hk⟩
  change σ k u = u at hh
  simpa only [map_one,Module.End.one_apply] using hh

/-- A faithful action with an irreducible perfect restriction cannot have
the two-factor G.6.4 decomposition. -/
theorem not_twoFactors_of_perfect_irreducible {D A U : Type*} [Group D] [Group A] [Group.IsPerfect A]
    [AddCommGroup U] [Module (ZMod 2) U]
    (σ : Representation (ZMod 2) D U) (hf : Function.Injective σ)
    (r : A →* D) (hi : IsIrreducible (σ.comp r)) (a : D)
    (d : Section06.TwoFactors σ a) : False := by
  let K := normalClosure ({a} : Set D)
  obtain ⟨t,_,_,hgen,ht⟩ := d.extension
  have hcom : commutator D ≤ K :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hgen inferInstance
  let : Group.IsPerfect r.range := Group.IsPerfect.range r
  have hrK : r.range ≤ K := by
    calc
      r.range = ⁅r.range,r.range⁆ := r.range.commutator_eq_self.symm
      _ ≤ commutator D := commutator_mono le_top le_top
      _ ≤ K := hcom
  have hKn : K ≤ normalizer (d.first : Set D) := by
    change normalClosure ({a} : Set D) ≤ _
    rw [← d.join_eq]
    exact sup_le d.first.le_normalizer ((commutator_eq_bot_iff_le_centralizer.mp
      (by rw [commutator_comm]; exact d.commute)).trans (Subgroup.centralizer_le_normalizer _))
  have hstable := subspaceCommutator_invariant_normalizer σ
    (le_subspaceStabilizer σ ⊤ (by intros; trivial) : r.range ≤ subspaceStabilizer σ ⊤)
    (hrK.trans hKn)
  let R : Subrepresentation (σ.comp r) :=
    ⟨subspaceCommutator σ ⊤ d.first,fun g u hu => (hstable ⟨g,rfl⟩ u).2 hu⟩
  have hfirst : d.first ≠ ⊥ := by
    intro he
    apply d.second_nontrivial
    rw [he,Subgroup.map_bot] at ht
    exact ht.symm
  rcases hi.eq_bot_or_eq_top R with hz | htop
  · exact moved_ne_bot σ hf d.first hfirst (congrArg Subrepresentation.toSubmodule hz)
  · have he : subspaceCommutator σ ⊤ d.first = ⊤ :=
      congrArg Subrepresentation.toSubmodule htop
    have hz := d.cross_second
    rw [he] at hz
    exact moved_ne_bot σ hf d.second d.second_nontrivial hz
end CFSG.Quasithin.ChapterG.Section11
