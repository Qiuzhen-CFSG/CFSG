module
public import Theory.Representation.BinaryConjugationSection
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Module.ZMod

/-!
# Finite generators of a binary group section

A spanning family in a finite binary section contains a basis. Choosing
preimages of those basis vectors gives generators of the original group
modulo the literal kernel. No action or splitting of the kernel is needed.

Source application: Aschbacher--Smith, proof of 13.8.33, printed pp.967--968,
where the spanning family consists of conjugates of the original seed.
-/

public section
open Subgroup
namespace Subgroup
variable {G W ι : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  [Finite W] (U V : Subgroup G) (f : U →* Multiplicative W)

/-- A spanning family in a binary section contains exactly its dimension
many generators modulo the original kernel. -/
theorem exists_generators_of_spanning_binary_section
    (hV : V ≤ U) (hk : f.ker = V.subgroupOf U)
    (x : ι → U) (hs : Submodule.span (ZMod 2) (Set.range fun i => (f (x i)).toAdd) = ⊤)
    (n : ℕ) (hd : Module.finrank (ZMod 2) W = n) :
    ∃ j : Fin n → ι, U = V ⊔ closure (Set.range fun k => (x (j k) : G)) := by
  classical
  let S := Set.range fun i => (f (x i)).toAdd
  let I := (linearIndepOn_empty (ZMod 2) (id : W → W)).extend (Set.empty_subset S)
  let b : Module.Basis I (ZMod 2) W := Module.Basis.ofSpan (show ⊤ ≤ Submodule.span (ZMod 2) S from hs.ge)
  let := Fintype.ofFinite I
  have hc : Fintype.card I = n := (Module.finrank_eq_card_basis b).symm.trans hd
  let e : Fin n ≃ I := (Fintype.equivFinOfCardEq hc).symm
  have hb (k : Fin n) : ∃ i, (f (x i)).toAdd = b (e k) :=
    (Module.Basis.ofSpan_subset (show ⊤ ≤ Submodule.span (ZMod 2) S from hs.ge)) ⟨e k,rfl⟩
  choose j hj using hb
  let C := V ⊔ closure (Set.range fun k => (x (j k) : G))
  have hCU : C ≤ U := sup_le hV ((closure_le _).mpr (by rintro _ ⟨k,rfl⟩; exact (x (j k)).property))
  let E : Submodule (ZMod 2) W :=
    AddSubgroup.toZModSubmodule 2 (((C.subgroupOf U).map f).toAddSubgroup')
  have hE : E = ⊤ := by
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    obtain ⟨k,rfl⟩ := e.surjective i
    rw [← hj k]
    exact ⟨x (j k), mem_sup_right (subset_closure ⟨k,rfl⟩),rfl⟩
  refine ⟨j,le_antisymm ?_ hCU⟩
  intro u hu
  have hv : (f ⟨u,hu⟩).toAdd ∈ E := hE ▸ Submodule.mem_top
  change f ⟨u,hu⟩ ∈ (C.subgroupOf U).map f at hv
  obtain ⟨v,hvC,hvu⟩ := hv
  have hkvu : (⟨u,hu⟩ : U) / v ∈ f.ker := by
    change f (⟨u,hu⟩ / v) = 1
    rw [map_div,hvu]
    exact div_self' _
  rw [hk] at hkvu
  have hkV : u / (v : G) ∈ V := hkvu
  have hm := C.mul_mem (mem_sup_left hkV) (show (v : G) ∈ C from hvC)
  simpa only [div_mul_cancel] using hm

end Subgroup
