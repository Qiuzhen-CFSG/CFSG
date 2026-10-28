module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.Placement
public import Theory.GroupTheory.SylowKernelCore

/-!
# Transport of concrete graph-centralizer placement

Conjugate both the Sylow subgroup and the whole elementary actor. The local
marker changes from `c` to `u*c`, the intersection order is preserved by the
induced subgroup equivalence, and the intrinsic two-core is preserved by the
local isomorphism. Sylow conjugacy consequently reduces the outer branch to
one chosen Sylow, including actors of order eight.

Source: the literal E0 and E1 placement obligations in Aschbacher–Smith
E.1.2/E.1.5, printed pp.209–210, applied to E.1.14(7), p.214.
-/

public section
open Subgroup Theory.GroupTheory
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
open Matrix.PSL3Three.GraphLocalQuotients
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry

private theorem map_conj_comp (A : Subgroup G) (u v : G) :
    (A.map (MulAut.conj u).toMonoidHom).map (MulAut.conj v).toMonoidHom =
      A.map (MulAut.conj (v * u)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

private theorem map_localSubgroup (u c : G) :
    (localSubgroup c).map (MulAut.conj u).toMonoidHom = localSubgroup (u * c) :=
  map_conj_comp baseCentralizer c u

private theorem card_subgroupOf_eq_inf (S K : Subgroup G) :
    Nat.card (S.subgroupOf K) = Nat.card (S ⊓ K : Subgroup G) := by
  rw [← subgroupOf_map_subtype S K, card_map_of_injective K.subtype_injective]

private theorem subgroupOf_le_core_iff {A K : Subgroup G} (h : A ≤ K) :
    A.subgroupOf K ≤ pCore 2 K ↔ A ≤ K.pCoreIn 2 := by
  rw [← map_le_map_iff_of_injective K.subtype_injective,
    map_subgroupOf_eq_of_le h]
  rfl

private theorem centralizer_map (e : G ≃* G) (A : Subgroup G) :
    centralizer (A.map e.toMonoidHom : Set G) =
      (centralizer (A : Set G)).map e.toMonoidHom := by
  apply le_antisymm
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply mem_centralizer_iff.mpr
    intro a ha
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      mem_centralizer_iff.mp hx (e a) (mem_map_of_mem e.toMonoidHom ha)
  · exact map_centralizer_le_centralizer_image _ _

/-- Conjugating the ambient Sylow and the whole actor preserves all six
literal placement clauses, including the intrinsic local two-core. -/
theorem centralizerPlacement_conj (T : Sylow 2 G) (A : Subgroup G) (u : G)
    (h : CentralizerPlacement T A) :
    CentralizerPlacement (u • T) (A.map (MulAut.conj u).toMonoidHom) := by
  obtain ⟨g,c,hBT,hBK,hcent,hcard,hcore,hgen⟩ := h
  let f := (MulAut.conj u).toMonoidHom
  have hT : ((u • T : Sylow 2 G) : Subgroup G) = (T : Subgroup G).map f := rfl
  have hB : (A.map (MulAut.conj u).toMonoidHom).map
      (MulAut.conj (u * g * u⁻¹)).toMonoidHom =
        (A.map (MulAut.conj g).toMonoidHom).map f := by
    rw [map_conj_comp, map_conj_comp]
    congr 2
    group
  refine ⟨u * g * u⁻¹, u * c, ?_⟩
  dsimp only
  rw [hB, hT, ← map_localSubgroup]
  refine ⟨map_mono hBT, map_mono hBK, ?_, ?_, ?_, ?_⟩
  · rw [centralizer_map, ← Subgroup.map_inf _ _ f (MulAut.conj u).injective]
    exact map_mono hcent
  · rw [card_subgroupOf_eq_inf, ← Subgroup.map_inf _ _ f (MulAut.conj u).injective,
      card_map_of_injective (MulAut.conj u).injective, ← card_subgroupOf_eq_inf]
    exact hcard
  · rw [subgroupOf_le_core_iff (map_mono hBK),
      ← map_pCoreIn_of_injective 2 _ f (MulAut.conj u).injective,
      map_le_map_iff_of_injective (MulAut.conj u).injective,
      ← subgroupOf_le_core_iff hBK]
    exact hcore
  · rw [← Subgroup.map_sup, hgen, map_top_of_surjective _ (MulAut.conj u).surjective]

/-- A calculation at any one Sylow suffices for the outer branch. This
transports elementary eight-groups without replacing them by four-groups. -/
theorem centralizerPlacement_outer_of_one_sylow (S : Sylow 2 G)
    (hS : ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ (S : Subgroup G) →
      1 < Group.rank A → ¬ A ≤ innerPart (ZMod 3) → CentralizerPlacement S A)
    (T : Sylow 2 G) (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup G)) (hr : 1 < Group.rank A)
    (hout : ¬ A ≤ innerPart (ZMod 3)) : CentralizerPlacement T A := by
  classical
  obtain ⟨u,hu⟩ := MulAction.exists_smul_eq G T S
  let f := (MulAut.conj u).toMonoidHom
  let B := A.map f
  let : IsElementaryAbelian 2 A := hA
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hBS : B ≤ (S : Subgroup G) := by
    rw [← hu]
    exact map_mono hAT
  have hrB : 1 < Group.rank B := by
    have he : Group.rank A = Group.rank B :=
      Group.rank_congr (MulEquiv.subgroupMap (MulAut.conj u) A)
    exact he ▸ hr
  have hoB : ¬ B ≤ innerPart (ZMod 3) := by
    intro h
    apply hout
    intro a ha
    have hh := h (mem_map_of_mem f ha)
    have hback := (inferInstance : (innerPart (ZMod 3)).Normal).conj_mem _ hh u⁻¹
    simpa [f, MulAut.conj_apply, mul_assoc] using hback
  have hh := centralizerPlacement_conj S B u⁻¹ (hS B hB hBS hrB hoB)
  have ht : u⁻¹ • S = T := by rw [← hu, inv_smul_smul]
  have hb : B.map (MulAut.conj u⁻¹).toMonoidHom = A := by
    change (A.map (MulAut.conj u).toMonoidHom).map (MulAut.conj u⁻¹).toMonoidHom = A
    rw [map_conj_comp, inv_mul_cancel]
    have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    rw [hid, Subgroup.map_id]
  rwa [ht, hb] at hh

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry
