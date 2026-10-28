module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SymplecticAction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions

/-!
# Cubic movement through a marked symplectic natural action

An actual group equivalence and binary-linear intertwiner transport the
full Sylow, local C-component and specified nonzero fixed vector to the
natural symplectic model. The moving cubic is carried back through the
same group equivalence. Normalizer membership, each commutator in the
original two-core and movement under the original representation are
retained explicitly.

This is the marked-module consumer of the natural action step in
Aschbacher–Smith 10.2.9, printed pp.751–752. Its `ActionEquiv` is supplied
by source assembly; no representation identification or lift through a
nontrivial group kernel is inferred here.
-/

public section
noncomputable section
open Subgroup Theory.SpecificGroups.SymplecticFour Representation
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF
open ChapterB.QuasisimpleSource
variable {D V F : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- Transport natural-module cubic movement through the actual group and
binary-linear marking, retaining the original subgroup and vector. -/
theorem marked_symplectic_local_moving_cubic
    (ρ : Representation (ZMod 2) D V) (hF : Nat.card F = 4)
    (e : ActionEquiv ρ (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)))
    (S : Sylow 2 D) (B : Subgroup D)
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (v : V) (hv : v ≠ 0) (hfix : ∀ s ∈ (S : Subgroup D), ρ s v = v) :
    ∃ x : D, orderOf x = 3 ∧ x ∈ normalizer (B : Set D) ∧
      (∀ b ∈ B, ⁅x,b⁆ ∈ B.pCoreIn 2) ∧ ρ x v ≠ v := by
  let a := e.groupEquiv
  let S' := S.mapSurjective (f := a.toMonoidHom) a.surjective
  let : Group.IsSolvable a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot_iff.mpr a.injective]
    infer_instance
  have hB' : B.map a.toMonoidHom ∈ localCComponents (S' : Subgroup (Sp F)) :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hB a.toMonoidHom
  have hp : B.map a.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hproper
    apply Subgroup.map_injective (f := a.toMonoidHom) a.injective
    rwa [map_top_of_surjective a.toMonoidHom a.surjective]
  have hv' : e.linearEquiv v ≠ 0 := by
    intro h
    exact hv (e.linearEquiv.injective (h.trans e.linearEquiv.map_zero.symm))
  have hf : ∀ s ∈ (S' : Subgroup (Sp F)), s • e.linearEquiv v = e.linearEquiv v := by
    rintro s ⟨r, hr, rfl⟩
    change restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)
      (e.groupEquiv r) (e.linearEquiv v) = e.linearEquiv v
    rw [← e.intertwines, hfix r hr]
  obtain ⟨x, ho, hn, hc, hm⟩ := symplectic_local_moving_cubic hF S'
    (B.map a.toMonoidHom) hB' hp (e.linearEquiv v) hv' hf
  refine ⟨a.symm x, (orderOf_injective a.symm.toMonoidHom a.symm.injective x).trans ho,
    ?_, ?_, ?_⟩
  · apply (mem_map_iff_mem (f := a.toMonoidHom) a.injective).mp
    rw [map_normalizer_eq_of_bijective B a.bijective]
    change a (a.symm x) ∈ normalizer (B.map a.toMonoidHom : Set (Sp F))
    rw [a.apply_symm_apply]
    exact hn
  · intro b hb
    apply (mem_map_iff_mem (f := a.toMonoidHom) a.injective).mp
    rw [map_pCoreIn_of_injective 2 _ _ a.injective]
    change a ⁅a.symm x,b⁆ ∈ (B.map a.toMonoidHom).pCoreIn 2
    rw [map_commutatorElement, a.apply_symm_apply]
    exact hc (a b) (mem_map_of_mem a.toMonoidHom hb)
  · intro h
    apply hm
    have ht := e.intertwines (a.symm x) v
    rw [h] at ht
    change e.linearEquiv v = a (a.symm x) • e.linearEquiv v at ht
    rw [a.apply_symm_apply] at ht
    exact ht.symm

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF
