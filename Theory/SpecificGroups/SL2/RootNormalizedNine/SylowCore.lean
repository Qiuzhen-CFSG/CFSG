module
public import Theory.SpecificGroups.SL2.RootNormalizedNine
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.PCoreSurjective.OddExtension

/-!
# The two-core of a marked subgroup of a binary rank-one pair

A Sylow-normalized subgroup of SL₂(F)² with intrinsic quotient E₉
contains the full product Sylow. The existing root commutator calculation
proves this in upper-root coordinates. Conjugation moves the result to
any prescribed Sylow, and relative normality identifies its two-core.

Source application: Aschbacher--Smith 12.6.31, printed p.836, the
containment T ∩ K₀ ≤ O₂(L₁T). All quotients here use intrinsic two-cores.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup.RootNormalizedNine
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local notation "E" => SL(2,F) × SL(2,F)
local notation "U" => Subgroup.prod (upperUnipotent F) (upperUnipotent F)

private theorem root_two : IsPGroup 2 U := by
  obtain ⟨a,ha⟩ := (upperUnipotentSylow F 2).isPGroup'.exists_card_eq
  apply IsPGroup.of_card (n := a+a)
  rw [Nat.card_congr (prodEquiv (upperUnipotent F) (upperUnipotent F)).toEquiv,
    Nat.card_prod,show Nat.card (upperUnipotent F) = 2^a from ha,pow_add]

private theorem root_core (C : Subgroup E) (hq : 2 < Nat.card F)
    (hn : U ≤ normalizer (C : Set E))
    (e : (C ⧸ pCore 2 C) ≃* Multiplicative (ZMod 3 × ZMod 3)) :
    C.pCoreIn 2 = U := by
  have hB := subgroup_le_borel C hq hn e
  obtain ⟨h₁,h₂⟩ := exists_diagonal_ne_one C hB hn e
  have hUC := root_le_of_diagonal_nontrivial C hB hn h₁ h₂
  apply le_antisymm (core_le_root C hn)
  apply le_pCoreIn_of_normalizes
  · exact root_two
  · exact hUC
  · intro c hc
    apply mem_normalizer_iff.mpr
    intro x
    exact (mem_normalizer_iff.mp (hB hc).1 x.1).and
      (mem_normalizer_iff.mp (hB hc).2 x.2)

/-- The entire prescribed Sylow is the intrinsic two-core image of C.
Neither a Borel containment nor a full unipotent containment is assumed. -/
theorem sylow_eq_core (S : Sylow 2 E) (C : Subgroup E)
    (hq : 2 < Nat.card F) (hn : (S : Subgroup E) ≤ normalizer (C : Set E))
    (e : (C ⧸ pCore 2 C) ≃* Multiplicative (ZMod 3 × ZMod 3)) :
    C.pCoreIn 2 = (S : Subgroup E) := by
  have hp : IsPGroup 2 U := root_two
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  have hPU : (P : Subgroup E) = U := by
    apply le_antisymm _ hP
    have hfst : (P : Subgroup E).map (MonoidHom.fst _ _) = upperUnipotent F :=
      (upperUnipotentSylow F 2).is_maximal' (P.isPGroup'.map _) (by
        intro x hx
        exact ⟨(x,1),hP ⟨hx,one_mem _⟩,rfl⟩)
    have hsnd : (P : Subgroup E).map (MonoidHom.snd _ _) = upperUnipotent F :=
      (upperUnipotentSylow F 2).is_maximal' (P.isPGroup'.map _) (by
        intro x hx
        exact ⟨(1,x),hP ⟨one_mem _,hx⟩,rfl⟩)
    intro x hx
    exact ⟨hfst ▸ mem_map_of_mem (MonoidHom.fst _ _) hx,
      hsnd ▸ mem_map_of_mem (MonoidHom.snd _ _) hx⟩
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq E S P
  let a := MulAut.conj g
  have hSU : (S : Subgroup E).map a.toMonoidHom = U := by
    change ((g • S : Sylow 2 E) : Subgroup E) = U
    rw [hg,hPU]
  let C' := C.map a.toMonoidHom
  let c := C.equivMapOfInjective a.toMonoidHom a.injective
  let e' := (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).symm.trans e
  have hn' : U ≤ normalizer (C' : Set E) := by
    rw [←hSU]
    exact (map_mono hn).trans (le_normalizer_map a.toMonoidHom)
  have hc := root_core C' hq hn' e'
  apply Subgroup.map_injective (f := a.toMonoidHom) a.injective
  rw [map_pCoreIn_of_injective 2 C a.toMonoidHom a.injective,hSU]
  exact hc

/-- Transport to a paired model without changing the prescribed Sylow or C. -/
theorem sylow_eq_core_of_equiv {A : Type*} [Group A] [Finite A]
    (a : A ≃* E) (S : Sylow 2 A) (C : Subgroup A)
    (hq : 2 < Nat.card F) (hn : (S : Subgroup A) ≤ normalizer (C : Set A))
    (e : (C ⧸ pCore 2 C) ≃* Multiplicative (ZMod 3 × ZMod 3)) :
    C.pCoreIn 2 = (S : Subgroup A) := by
  let c := C.equivMapOfInjective a.toMonoidHom a.injective
  let e' := (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).symm.trans e
  have h := sylow_eq_core (S.mapSurjective a.surjective) (C.map a.toMonoidHom)
    hq ((map_mono hn).trans (le_normalizer_map a.toMonoidHom)) e'
  apply Subgroup.map_injective (f := a.toMonoidHom) a.injective
  rw [map_pCoreIn_of_injective 2 C a.toMonoidHom a.injective]
  exact h

end Matrix.SpecialLinearGroup.RootNormalizedNine
