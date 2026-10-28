module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.Placement
public import Theory.GroupTheory.SylowKernelCore

/-!
# Transport of the complete graph-centralizer placement

Ambient conjugation takes each marked local group K_c to K_(sc). It also
preserves centralizers, the literal Sylow intersection, its cardinality,
the intrinsic two-core and generation. Actor conjugation and Sylow
conjugacy therefore reduce placement to one reference configuration.

These are transport lemmas for E.1.2 and E.1.5 in the PSL₃(3) branch of
Aschbacher–Smith E.1.14(7), printed pp.209–210, 214 (Asc82a 4.11).
The reference configuration itself is not assumed to exist by this module.
-/

public section
open Subgroup Theory.GroupTheory
open Matrix.PSL3Three.GraphLocalQuotients
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.InnerActors

private theorem map_conj_comp (A : Subgroup G) (s t : G) :
    (A.map (MulAut.conj t).toMonoidHom).map (MulAut.conj s).toMonoidHom =
      A.map (MulAut.conj (s * t)).toMonoidHom := by
  rw [map_map]
  apply congrArg (fun f : G →* G => A.map f)
  apply MonoidHom.ext
  intro x
  change s * (t * x * t⁻¹) * s⁻¹ = (s * t) * x * (s * t)⁻¹
  group

private theorem map_localSubgroup (s c : G) :
    (localSubgroup c).map (MulAut.conj s).toMonoidHom = localSubgroup (s * c) :=
  map_conj_comp baseCentralizer s c

private theorem map_centralizer (e : G ≃* G) (A : Subgroup G) :
    (centralizer (A : Set G)).map e.toMonoidHom =
      centralizer (A.map e.toMonoidHom : Set G) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  intro y hy
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using
    hx (e y) (mem_map_of_mem e.toMonoidHom hy)

private theorem card_subgroupOf (S K : Subgroup G) :
    Nat.card (S.subgroupOf K) = Nat.card (S ⊓ K : Subgroup G) := by
  rw [← subgroupOf_map_subtype, card_map_of_injective K.subtype_injective]

private theorem subgroupOf_le_core_iff (B K : Subgroup G) (hBK : B ≤ K) :
    B.subgroupOf K ≤ pCore 2 K ↔ B ≤ K.pCoreIn 2 := by
  constructor
  · intro h
    have hm := map_mono (f := K.subtype) h
    simpa only [pCoreIn, map_subgroupOf_eq_of_le hBK] using hm
  · intro h x hx
    obtain ⟨y, hy, he⟩ := h hx
    have hxy : y = x := Subtype.ext he
    exact hxy ▸ hy

/-- Changing only the representative of an actor preserves placement of the
whole original actor. -/
theorem placement_of_actor_conjugate (T : Sylow 2 G) (A B : Subgroup G) (s : G)
    (hs : A.map (MulAut.conj s).toMonoidHom = B)
    (hB : CentralizerPlacement T B) : CentralizerPlacement T A := by
  obtain ⟨g, c, h⟩ := hB
  refine ⟨g * s, c, ?_⟩
  simpa only [← map_conj_comp A g s, hs] using h

/-- Simultaneous conjugation preserves every clause of concrete placement,
including the intrinsic two-core and the literal local intersection. -/
theorem placement_conjugate (T : Sylow 2 G) (A : Subgroup G) (s : G)
    (hA : CentralizerPlacement T A) :
    CentralizerPlacement (s • T) (A.map (MulAut.conj s).toMonoidHom) := by
  obtain ⟨g, c, hBT, hBK, hcent, hcard, hcore, hgen⟩ := hA
  let f := (MulAut.conj s).toMonoidHom
  let B := A.map (MulAut.conj g).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj s).injective
  have hT : ((s • T : Sylow 2 G) : Subgroup G) = (T : Subgroup G).map f := rfl
  have hB : (A.map f).map (MulAut.conj (s * g * s⁻¹)).toMonoidHom = B.map f := by
    rw [map_conj_comp, map_conj_comp]
    apply congrArg (fun x : G => A.map (MulAut.conj x).toMonoidHom)
    group
  refine ⟨s * g * s⁻¹, s * c, ?_⟩
  change (A.map f).map _ ≤ _ ∧ _
  rw [hB, hT, ← map_localSubgroup]
  refine ⟨map_mono hBT, map_mono hBK, ?_, ?_, ?_, ?_⟩
  · rw [← map_centralizer, ← map_inf _ _ _ hf]
    exact map_mono hcent
  · rw [card_subgroupOf, ← map_inf _ _ _ hf, card_map_of_injective hf,
      ← card_subgroupOf]
    exact hcard
  · intro h
    apply hcore
    apply (subgroupOf_le_core_iff B (localSubgroup c) hBK).mpr
    have hh := (subgroupOf_le_core_iff (B.map f) ((localSubgroup c).map f)
      (map_mono hBK)).mp h
    rw [← map_pCoreIn_of_injective 2 (localSubgroup c) f hf] at hh
    exact (map_le_map_iff_of_injective hf).mp hh
  · rw [← Subgroup.map_sup, hgen, map_top_of_surjective _ (MulAut.conj s).surjective]

/-- One Sylow calculation suffices for every Sylow subgroup, once actors can
be conjugated to the transported reference actor. -/
theorem placement_at_any_sylow (R : Sylow 2 G) (D : Subgroup G)
    (hD : CentralizerPlacement R D) (T : Sylow 2 G) (A : Subgroup G)
    (hconj : ∀ s : G, ∃ g : G,
      A.map (MulAut.conj g).toMonoidHom = D.map (MulAut.conj s).toMonoidHom) :
    CentralizerPlacement T A := by
  obtain ⟨s, hs⟩ := MulAction.exists_smul_eq G R T
  obtain ⟨g, hg⟩ := hconj s
  exact placement_of_actor_conjugate T A _ g hg
    (hs ▸ placement_conjugate R D s hD)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.InnerActors
