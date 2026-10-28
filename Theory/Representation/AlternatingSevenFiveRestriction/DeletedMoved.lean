module
public import Theory.Representation.AlternatingSevenFiveRestriction.CoreEmbedding
public import Theory.Representation.BinaryPermutation.FiveCentralExtension
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.AlternatingFiveTwists
/-!
# The marked deleted A₅ moved space inside deleted A₇

A Sylow-normalized A₅ fixes two letters. Evaluation at those letters gives
an upper bound of four on its moved space in the seven-point core. The
embedded five-point core is fully moved, so it is exactly that space.
Odd-degree core coordinates and automorphism twists give the literal
four-dimensional deleted A₅ module for any prescribed marking.

Source: Aschbacher–Smith, C.5.13, printed p.163, used in the deleted A₇
row of 10.2.9, printed pp.751–752.
-/

public section
open Subgroup Representation Representation.BinaryOffender Module
namespace BinaryPermutation

private theorem five_core_moved :
    subspaceCommutator (coreRepresentation (Fin 5)) ⊤ (alternatingGroup (Fin 5)) = ⊤ := by
  apply top_unique
  intro v _
  have hz : 20 • v = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (R := ZMod 2)]
    change (20 : ZMod 2) • v = 0
    rw [show (20 : ZMod 2) = 0 from rfl, zero_smul]
  have hv : v = ∑ g ∈ FiveCentralExtension.cubes, (coreRepresentation (Fin 5) g v - v) := by
    rw [Finset.sum_sub_distrib, FiveCentralExtension.core_sum,
      Finset.sum_const, FiveCentralExtension.cubes_card, hz, sub_zero]
  rw [hv]
  exact Submodule.sum_mem _ fun g hg => Submodule.subset_span
    ⟨g, FiveCentralExtension.cubes_even g hg, v, Submodule.mem_top, rfl⟩

private theorem fixed_pair_moved_bound
    (B : Subgroup (alternatingGroup (Fin 7))) (i k : Fin 7) (hik : i ≠ k)
    (hB : B = fixingSubgroup (alternatingGroup (Fin 7)) ({i,k} : Set (Fin 7))) :
    finrank (ZMod 2) (subspaceCommutator (alternatingCoreRepresentation (Fin 7)) ⊤ B) ≤ 4 := by
  let p : core (Fin 7) →ₗ[ZMod 2] (ZMod 2 × ZMod 2) :=
    ((LinearMap.proj i).comp (core (Fin 7)).subtype).prod
      ((LinearMap.proj k).comp (core (Fin 7)).subtype)
  have hp : Function.Surjective p := by
    have hl : ∃ l : Fin 7, l ≠ i ∧ l ≠ k := by
      by_cases h0 : (0 : Fin 7) = i
      · by_cases h1 : (1 : Fin 7) = k
        · exact ⟨2, by omega, by omega⟩
        · exact ⟨1, by omega, h1⟩
      · by_cases h0k : (0 : Fin 7) = k
        · by_cases h1 : (1 : Fin 7) = i
          · exact ⟨2, by omega, by omega⟩
          · exact ⟨1, h1, by omega⟩
        · exact ⟨0, h0, h0k⟩
    obtain ⟨l, hli, hlk⟩ := hl
    rintro ⟨a,b⟩
    let v : core (Fin 7) := ⟨Pi.single i a + Pi.single k b - Pi.single l (a+b), by
      rw [mem_core]
      simp only [Pi.sub_apply, Pi.add_apply, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      simp⟩
    refine ⟨v, ?_⟩
    apply Prod.ext <;> simp [p, v, hik, hik.symm, hli.symm, hlk.symm]
  have hd : finrank (ZMod 2) p.ker = 4 := by
    have h := p.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hp, finrank_top, finrank_prod,
      finrank_self, finrank_core] at h
    norm_num at h ⊢
    omega
  have hm : subspaceCommutator (alternatingCoreRepresentation (Fin 7)) ⊤ B ≤ p.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b,hb,v,hv,rfl⟩
    have hb' := (mem_fixingSubgroup_iff (alternatingGroup (Fin 7))).mp (hB ▸ B.inv_mem hb)
    have hi : b.val.symm i = i := hb' i (by simp)
    have hk : b.val.symm k = k := hb' k (by simp)
    change p ((alternatingCoreRepresentation (Fin 7)) b v - v) = 0
    apply Prod.ext
    · change v.val (b.val.symm i) - v.val i = 0
      rw [hi, sub_self]
    · change v.val (b.val.symm k) - v.val k = 0
      rw [hk, sub_self]
  exact (Submodule.finrank_mono hm).trans hd.le

theorem exists_five_core_moved_embedding
    (B : Subgroup (alternatingGroup (Fin 7))) (e : B ≃* alternatingGroup (Fin 5))
    (S : Sylow 2 (alternatingGroup (Fin 7)))
    (hSN : (S : Subgroup _) ≤ normalizer (B : Set (alternatingGroup (Fin 7)))) :
    ∃ eB : B ≃* alternatingGroup (Fin 5),
    ∃ j : core (Fin 5) →ₗ[ZMod 2] core (Fin 7), Function.Injective j ∧
      (∀ (b : B) v, j (coreRepresentation (Fin 5) (eB b).val v) =
        coreRepresentation (Fin 7) b.val.val (j v)) ∧
      j.range = subspaceCommutator (alternatingCoreRepresentation (Fin 7)) ⊤ B := by
  obtain ⟨eB,j,hj,hact⟩ := exists_five_core_embedding B e S hSN
  refine ⟨eB,j,hj,hact,?_⟩
  have hm : j.range ≤ subspaceCommutator (alternatingCoreRepresentation (Fin 7)) ⊤ B := by
    have he := subspaceCommutator_map_embedding
      ((alternatingCoreRepresentation (Fin 7)).comp B.subtype) (coreRepresentation (Fin 5))
      ((alternatingGroup (Fin 5)).subtype.comp eB.toMonoidHom) j (fun b v => (hact b v).symm) ⊤ ⊤
    have hmap : (⊤ : Subgroup B).map ((alternatingGroup (Fin 5)).subtype.comp eB.toMonoidHom) =
        alternatingGroup (Fin 5) := by
      rw [← Subgroup.map_map, map_top_of_surjective _ eB.surjective,
        ← MonoidHom.range_eq_map, range_subtype]
    rw [hmap, five_core_moved, Submodule.map_top] at he
    rw [← he]
    have hle := subspaceCommutator_mono_left
      ((alternatingCoreRepresentation (Fin 7)).comp B.subtype) (show j.range ≤ ⊤ from le_top) ⊤
    simpa only [subspaceCommutator_comp_map, ← MonoidHom.range_eq_map, range_subtype] using hle
  apply Submodule.eq_of_le_of_finrank_le hm
  rw [LinearMap.finrank_range_of_inj hj, SevenPointChiefFactor.fiveCore_finrank]
  obtain ⟨i,k,hik,hB⟩ := Theory.SpecificGroups.Alternating.SevenFivePlacement.exists_fixed_pair B e S hSN
  exact fixed_pair_moved_bound B i k hik hB
end BinaryPermutation

namespace BinaryPermutation

theorem exists_five_natural_moved_embedding
    (B : Subgroup (alternatingGroup (Fin 7))) (e : B ≃* alternatingGroup (Fin 5))
    (S : Sylow 2 (alternatingGroup (Fin 7)))
    (hSN : (S : Subgroup _) ≤ normalizer (B : Set (alternatingGroup (Fin 7)))) :
    ∃ j : natural (Fin 5) →ₗ[ZMod 2] natural (Fin 7), Function.Injective j ∧
      (∀ (b : B) v, j (alternatingNaturalRepresentation (Fin 5) (e b) v) =
        alternatingNaturalRepresentation (Fin 7) b.val (j v)) ∧
      j.range = subspaceCommutator (alternatingNaturalRepresentation (Fin 7)) ⊤ B := by
  obtain ⟨eB,j,hj,hact,hrange⟩ := exists_five_core_moved_embedding B e S hSN
  let E5 := coreEquivNatural (Fin 5) (by decide)
  let E7 := coreEquivNatural (Fin 7) (by decide)
  let j0 := E7.toLinearMap.comp (j.comp E5.symm.toLinearMap)
  have hi : Function.Injective j0 := E7.injective.comp (hj.comp E5.symm.injective)
  have ha (b : B) (v : natural (Fin 5)) :
      j0 (alternatingNaturalRepresentation (Fin 5) (eB b) v) =
        alternatingNaturalRepresentation (Fin 7) b.val (j0 v) := by
    obtain ⟨v,rfl⟩ := E5.surjective v
    change E7 (j (E5.symm (naturalRepresentation (Fin 5) (eB b).val (E5 v)))) = _
    rw [← coreEquivNatural_equivariant, E5.symm_apply_apply, hact,
      coreEquivNatural_equivariant]
    simp only [j0, LinearMap.comp_apply, LinearEquiv.coe_coe, E5.symm_apply_apply]
    rfl
  have hr : j0.range = subspaceCommutator (alternatingNaturalRepresentation (Fin 7)) ⊤ B := by
    have he := subspaceCommutator_map_embedding (alternatingNaturalRepresentation (Fin 7))
      (alternatingCoreRepresentation (Fin 7)) (MonoidHom.id _) E7.toLinearMap
      (fun g v => (coreEquivNatural_equivariant (Fin 7) (by decide) g.val v).symm) B ⊤
    rw [Submodule.map_top, LinearEquiv.range, Subgroup.map_id, ←hrange] at he
    change (E7.toLinearMap.comp (j.comp E5.symm.toLinearMap)).range = _
    rw [LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ E5.symm.range]
    exact he.symm
  let a : MulAut (alternatingGroup (Fin 5)) := eB.symm.trans e
  obtain ⟨c,hc⟩ := Representation.AlternatingFiveTwists.deleted_twist a
  let J := j0.comp c.symm.toLinearMap
  refine ⟨J,hi.comp c.symm.injective,?_,?_⟩
  · intro b v
    have hc' : c.symm (alternatingNaturalRepresentation (Fin 5) (e b) v) =
        alternatingNaturalRepresentation (Fin 5) (eB b) (c.symm v) := by
      apply c.injective
      rw [c.apply_symm_apply]
      have h := hc (eB b) (c.symm v)
      change c (alternatingNaturalRepresentation (Fin 5) (eB b) (c.symm v)) =
        alternatingNaturalRepresentation (Fin 5) (e (eB.symm (eB b))) (c (c.symm v)) at h
      rw [eB.symm_apply_apply, c.apply_symm_apply] at h
      exact h.symm
    change j0 (c.symm _) = alternatingNaturalRepresentation (Fin 7) b.val (j0 (c.symm v))
    rw [hc', ha]
  · change (j0.comp c.symm.toLinearMap).range = _
    rw [LinearMap.range_comp_of_range_eq_top _ c.symm.range, hr]

theorem exists_five_natural_moved_equiv
    (B : Subgroup (alternatingGroup (Fin 7))) (e : B ≃* alternatingGroup (Fin 5))
    (S : Sylow 2 (alternatingGroup (Fin 7)))
    (hSN : (S : Subgroup _) ≤ normalizer (B : Set (alternatingGroup (Fin 7)))) :
    ∃ E : subspaceCommutator (alternatingNaturalRepresentation (Fin 7)) ⊤ B ≃ₗ[ZMod 2]
        natural (Fin 5), ∀ (b : B) v,
      (E.symm (alternatingNaturalRepresentation (Fin 5) (e b) v) : natural (Fin 7)) =
        alternatingNaturalRepresentation (Fin 7) b.val (E.symm v) := by
  obtain ⟨j,hj,hact,hrange⟩ := exists_five_natural_moved_embedding B e S hSN
  let E := (LinearEquiv.ofEq _ _ hrange.symm).trans (LinearEquiv.ofInjective j hj).symm
  refine ⟨E,?_⟩
  intro b v
  exact hact b v
end BinaryPermutation
