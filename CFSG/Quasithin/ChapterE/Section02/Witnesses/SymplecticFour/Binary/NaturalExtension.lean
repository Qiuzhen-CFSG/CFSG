module
public import CFSG.Quasithin.ChapterE.Section02.Structure.Sporadic.Reduction
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic
public import Theory.SpecificGroups.SymmetricSix.Parabolics
/-!
# Natural A6 and S6 extensions are not minimal parabolic

Each six-letter group has two distinct proper Sylow overgroups generating
the whole group. A faithful extension of A6 inside its natural S6 is one
of these two groups, by index two. This gives the original source escape
from the natural automorphism subgroup in the binary case of E.2.7, p.219.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour.Binary
open Theory.SpecificGroups.SymmetricSix
open AlternatingSix.ShadowLocal

theorem not_minimal_alternating (T : Sylow 2 (alternatingGroup (Fin 6))) :
    ¬ ChapterB.IsMinimalParabolicOver T ⊤ := by
  apply Structure.Sporadic.not_minimal_of_marked_pair T (MulEquiv.refl _) a6BorelSylow
    a6DuadStabilizer a6SynthemeStabilizer a6DuadStabilizer_ne_top a6SynthemeStabilizer_ne_top
  · exact a6Borel_le_duadStabilizer
  · exact a6Borel_le_synthemeStabilizer
  · exact a6_parabolics_sup

theorem not_minimal_symmetric (T : Sylow 2 (Equiv.Perm (Fin 6))) :
    ¬ ChapterB.IsMinimalParabolicOver T ⊤ := by
  apply Structure.Sporadic.not_minimal_of_marked_pair T (MulEquiv.refl _) borelSylow
    duadStabilizer synthemeStabilizer duadStabilizer_ne_top synthemeStabilizer_ne_top
  · exact borel_le_duadStabilizer
  · exact borel_le_synthemeStabilizer
  · exact parabolics_sup

variable {G : Type*} [Group G] [Finite G]
/-- A faithful extension of A6 contained in its natural S6 cannot satisfy
original minimal parabolicity. Both proper Sylow overgroups are retained. -/
theorem not_minimal_of_natural_extension (T : Sylow 2 G)
    (a : G →* AutA6) (ha : Function.Injective a) (hi : AlternatingSix.ShadowLocal.inner ≤ a.range)
    (hn : a.range ≤ natural) : ¬ ChapterB.IsMinimalParabolicOver T ⊤ := by
  let e := MonoidHom.ofInjective permutationAction_injective
  let b : G →* Equiv.Perm (Fin 6) := e.symm.toMonoidHom.comp
    (a.codRestrict natural (fun x => hn ⟨x,rfl⟩))
  have hab (x:G) : permutationAction (b x) = a x := by
    exact congrArg Subtype.val (e.apply_symm_apply ⟨a x,hn ⟨x,rfl⟩⟩)
  have hb : Function.Injective b := by
    intro x y hh
    apply ha
    rw [←hab x,←hab y,hh]
  have hB : alternatingGroup (Fin 6) ≤ b.range := by
    intro x hx
    obtain ⟨y,hy⟩ := hi (show MulAut.conj (⟨x,hx⟩ : alternatingGroup (Fin 6)) ∈ AlternatingSix.ShadowLocal.inner from ⟨_,rfl⟩)
    refine ⟨y,permutationAction_injective ?_⟩
    rw [hab,hy]
    exact (permutationAction_coe ⟨x,hx⟩).symm
  have hd : b.range.index ∣ 2 := (alternatingGroup.index_eq_two (α := Fin 6)) ▸ index_dvd_of_le hB
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · have ht : b.range = ⊤ := index_eq_one.mp h1
    let f : G ≃* Equiv.Perm (Fin 6) :=
      (MonoidHom.ofInjective hb).trans ((MulEquiv.subgroupCongr ht).trans topEquiv)
    exact Structure.Sporadic.not_minimal_of_model T f not_minimal_symmetric
  · have ht : b.range = alternatingGroup (Fin 6) := Equiv.Perm.eq_alternatingGroup_of_index_eq_two h2
    let f : G ≃* alternatingGroup (Fin 6) := (MonoidHom.ofInjective hb).trans (MulEquiv.subgroupCongr ht)
    exact Structure.Sporadic.not_minimal_of_model T f not_minimal_alternating
end CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour.Binary
