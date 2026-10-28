module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Levi.Irreducibility.Curtis.RootCollection
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap.Basic
public import Theory.Representation.SubrepresentationLattice

/-!
# Opposite-unipotent cyclicity over the binary field

A local highest vector has opposite-unipotent orbit span stable under the
adjacent exchanges: collect the selected lower root to the right, then use
its inactive or active rank-one relation. Lower roots and exchanges generate
SL₅(2), so an irreducible module equals this nonzero invariant span.

The existing zero-Hecke highest-vector theorem supplies the vector without
absolute irreducibility or a dimension cutoff. Empty support is permitted.
This proves the spanning part needed for the binary version of GLS,
Volume 3, Theorem 2.8.9, `refs/KGroup/GLS3/chapter2.tex`, printed p.94.
-/

public section

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Levi.Irreducibility.Curtis
open Representation Representation.SL5TenDimensional Representation.SL5TenDimensional.Classification
open HeckeAction
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- A local highest vector generates an irreducible module under the opposite unipotent. -/
theorem lower_orbit_eq_top (σ : Representation (ZMod 2) SL5TenDimensional.Group V)
    [IsIrreducible σ] {J : Finset (Fin 4)} {v : V} (hv : v ≠ 0)
    (hJ : LocalHighestVector σ J v) :
    Submodule.span (ZMod 2) (Set.range fun u : lower => σ u v) = ⊤ := by
  let W := Submodule.span (ZMod 2) (Set.range fun u : lower => σ u v)
  have hmem (u : lower) : σ u v ∈ W := Submodule.subset_span ⟨u,rfl⟩
  have hvW : v ∈ W := by simpa only [Subgroup.coe_one, map_one, Module.End.one_apply] using hmem 1
  have hlower (g : SL5TenDimensional.Group) (hg : g ∈ lower) : ∀ x ∈ W, σ g x ∈ W := by
    apply show W ≤ W.comap (σ g) from ?_
    apply Submodule.span_le.mpr
    rintro _ ⟨u,rfl⟩
    change σ g (σ u v) ∈ W
    simpa only [map_mul, Module.End.mul_apply] using hmem ⟨g*u,lower.mul_mem hg u.property⟩
  have hswapv (i : Fin 4) : σ (simpleSwap i) v ∈ W := by
    by_cases hi : i ∈ J
    · have hr := hJ.active_relation i hi
      have he : σ (simpleSwap i) v = -(v + σ (simpleLower i) v) := by
        apply eq_neg_of_add_eq_zero_right
        calc
          (v + σ (simpleLower i) v) + σ (simpleSwap i) v =
              v + σ (simpleSwap i) v + σ (simpleLower i) v := by abel
          _ = 0 := hr
      rw [he]
      exact W.neg_mem (W.add_mem hvW (hmem ⟨_,simpleLower_mem i⟩))
    · rw [hJ.inactive_fixed i hi]
      exact hvW
  have hswap (i : Fin 4) : ∀ x ∈ W, σ (simpleSwap i) x ∈ W := by
    apply show W ≤ W.comap (σ (simpleSwap i)) from ?_
    apply Submodule.span_le.mpr
    rintro _ ⟨u,rfl⟩
    obtain ⟨h,hh,hs,he⟩ := lower_collection i u.property
    have hcollect : simpleSwap i * h = (simpleSwap i * h * simpleSwap i) * simpleSwap i := by
      simp only [mul_assoc, swap_sq, mul_one]
    change σ (simpleSwap i) (σ u.val v) ∈ W
    rcases he with he | he
    · rw [he]
      rw [← Module.End.mul_apply, ← map_mul]
      rw [hcollect, map_mul]
      exact hlower _ hs _ (hswapv i)
    · rw [he]
      rw [← Module.End.mul_apply, ← map_mul]
      rw [← mul_assoc, hcollect, mul_assoc, swap_mul_lower]
      have hu : σ (simpleUpper i) v = v := hJ.upper_fixed i.castSucc i.succ (by simp)
      simpa only [map_mul, Module.End.mul_apply, hu] using
        hlower _ hs _ (hmem ⟨_,simpleLower_mem i⟩)
  have hall (g : SL5TenDimensional.Group) : ∀ x ∈ W, σ g x ∈ W := by
    apply lower_swap_induction (fun g => ∀ x ∈ W, σ g x ∈ W)
      (by intro x hx; simpa only [map_one, Module.End.one_apply] using hx)
      (fun g h hg hh x hx => by
        simpa only [map_mul, Module.End.mul_apply] using hg _ (hh x hx)) hlower hswap
  let S : Subrepresentation σ := ⟨W, hall⟩
  have hS : S = ⊤ := (eq_bot_or_eq_top S).resolve_left (by
    intro hS
    have hm : v ∈ S := hvW
    rw [hS] at hm
    exact hv hm)
  exact congrArg Subrepresentation.toSubmodule hS

/-- Every binary simple module has an upper-fixed, lower-cyclic vector. -/
theorem exists_upper_fixed_lower_cyclic [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) [IsIrreducible σ] :
    ∃ v : V, v ≠ 0 ∧ v ∈ invariants (σ.comp upper.subtype) ∧
      Submodule.span (ZMod 2) (Set.range fun u : lower => σ u v) = ⊤ := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial σ
  obtain ⟨J,v,hv,hJ⟩ :=
    CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap.exists_localHighestVector σ
  refine ⟨v,hv,?_,lower_orbit_eq_top σ hv hJ⟩
  intro u
  exact (upperFixed_iff_fixed_subgroup σ v).mp hJ.upper_fixed u u.property

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Levi.Irreducibility.Curtis
