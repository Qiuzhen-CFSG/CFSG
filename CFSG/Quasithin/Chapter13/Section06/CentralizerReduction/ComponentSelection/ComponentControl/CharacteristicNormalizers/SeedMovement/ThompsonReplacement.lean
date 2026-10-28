module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.CharacteristicNormalizers.SeedMovement.Module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.Thompson
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.Characteristic
public import Theory.GroupTheory.CComponent.SeedAction
/-!
# A moving component in the Thompson normalizer

If H = K₀C_T(v) factors as N_H(J(C_T(v))) C_H(⟨z^H⟩), its
normal centralizer is solvable: it cannot contain the moving C-component
residual K₀. The normalizer residual is consequently a C-component and
still moves z. Its ambient image is invariant under C_T(v) and normalizes
the nontrivial characteristic Thompson subgroup. That subgroup supplies
the nontrivial two-core required by the genuine local family.

This is the residual-lifting step in the independent seed-action route to
13.6.16(2). The factorization is an explicit input here; the intrinsic
B.5.6 implication supplies it in the nonquasisimple action case. Assertion
(1), applied to the constructed moving member, then rules out this case.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, A.3.3,
pp.42–43, B.2.7, p.77, and 13.6.16(2), p.930.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.SeedMovement
open NonquasisimpleFactorization
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual normalizer residual gives a moving invariant local component. -/
theorem moving_thompson_replacement
    (T : Sylow 2 G) (z v : G) (hvT : v ∈ T) (hv : v ≠ 1)
    (K : Subgroup G) (hK : K ∈ Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v))
    (hS : Tv (T : Subgroup G) v ≤ normalizer (K : Set G))
    (hm : ¬ K ≤ centralizer ({z} : Set G))
    (hzH : z ∈ K ⊔ Tv (T : Subgroup G) v)
    (P : Sylow 2 (K ⊔ Tv (T : Subgroup G) v : Subgroup G))
    (hP : (P : Subgroup (K ⊔ Tv (T : Subgroup G) v : Subgroup G)).map
      (K ⊔ Tv (T : Subgroup G) v).subtype = Tv (T : Subgroup G) v)
    (hfact : normalizer (elementaryAbelianMaxJ (P : Subgroup (K ⊔ Tv (T : Subgroup G) v : Subgroup G)) : Set _) ⊔
      centralizer (seedSpan (K ⊔ Tv (T : Subgroup G) v) z hzH : Set (K ⊔ Tv (T : Subgroup G) v : Subgroup G)) = ⊤) :
    ∃ K₂ : Subgroup G, K₂ ∈ Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v) ∧
      Tv (T : Subgroup G) v ≤ normalizer (K₂ : Set G) ∧
      ¬ K₂ ≤ centralizer ({z} : Set G) ∧
      K₂ ≤ normalizer (elementaryAbelianMaxJ (Tv (T : Subgroup G) v) : Set G) := by
  let S := Tv (T : Subgroup G) v
  let H := K ⊔ S
  let W := seedSpan H z hzH
  let B := K.subgroupOf H
  let J := elementaryAbelianMaxJ (P : Subgroup H)
  let N := normalizer (J : Set H)
  let C := centralizer (W : Set H)
  let M := N.map H.subtype
  let K₂ := (solvableResidual M).map M.subtype
  let := Chapter1.mem_L_isPerfect hK.2
  let : Group.IsNilpotent S := (Chapter1.isSylowIn_iff.mp hK.2.2.1).1.isNilpotent
  have hres : (solvableResidual H).map H.subtype = K :=
    map_residual_sup_eq_of_perfect_of_solvable K S hS
  have hr : solvableResidual H = B := by
    apply map_injective H.subtype_injective
    rw [hres, map_subgroupOf_eq_of_le le_sup_left]
  have hrc : (solvableResidual H).IsCComponent := hr.symm ▸ hK.2.1
  have hmv : ¬ solvableResidual H ≤ centralizer ({⟨z, hzH⟩} : Set H) := by
    intro hc
    apply hm
    rw [← hres]
    rintro _ ⟨x, hx, rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hc hx)))
  have hC : C ≤ centralizer ({⟨z, hzH⟩} : Set H) := by
    intro c hc
    exact mem_centralizer_singleton_iff.mpr ((hc _ (seed_mem H z hzH)).symm)
  obtain ⟨hccomp, hmove⟩ := moving_residual_of_centralizing_normal_supplement C N
    ⟨z, hzH⟩ hrc hmv hC (by rwa [sup_comm])
  let e : N ≃* M := N.equivMapOfInjective H.subtype H.subtype_injective
  have hMc : (solvableResidual M).IsCComponent := by
    have hh := hccomp.map_equiv e
    rwa [map_solvableResidual_eq e.toMonoidHom e.surjective] at hh
  have hmap : ((solvableResidual N).map N.subtype).map H.subtype = K₂ := by
    rw [map_map]
    change (solvableResidual N).map (M.subtype.comp e.toMonoidHom) = _
    rw [← map_map, map_solvableResidual_eq e.toMonoidHom e.surjective]
  have hmove₂ : ¬ K₂ ≤ centralizer ({z} : Set G) := by
    intro hc
    apply hmove
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hc (hmap ▸ mem_map_of_mem H.subtype hx))
  have hJM : J.map H.subtype = elementaryAbelianMaxJ S :=
    thompson_join_sylow_map (T : Subgroup G) K v P hP
  have hSM : S ≤ M := by
    change Tv (T : Subgroup G) v ≤ M
    rw [← hP]
    apply map_mono
    exact (P : Subgroup H).le_normalizer.trans (by
      intro g hg
      rw [mem_normalizer_iff_map_conj_eq] at hg ⊢
      change (P : Subgroup H).map (MulAut.conj g).toMonoidHom = _ at hg
      change J.map (MulAut.conj g).toMonoidHom = _
      rw [← elementaryAbelianMaxJ_map_equiv, hg])
  have hMN : M ≤ normalizer (elementaryAbelianMaxJ S : Set G) := by
    rw [← hJM]
    exact J.le_normalizer_map H.subtype
  have h₂M : K₂ ≤ M := map_subtype_le _
  have h₂H : K₂ ≤ H := h₂M.trans (map_subtype_le N)
  have hS₂ : S ≤ normalizer (K₂ : Set G) := hSM.trans
    (M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (solvableResidual M)))
  let D : Subgroup S := elementaryAbelianMaxJ ⊤
  let : D.Characteristic := elementaryAbelianMaxJ_top_characteristic
  have hD : D.map S.subtype = elementaryAbelianMaxJ S := thompson_centralizer_map _ _
  have hDne : D ≠ ⊥ := thompson_centralizer_ne_bot T v hvT hv
  have hJS : elementaryAbelianMaxJ S ≤ S := sSup_le fun _ hA => hA.1
  have hSD : S ≤ normalizer (elementaryAbelianMaxJ S : Set G) := hSM.trans hMN
  have hcore : elementaryAbelianMaxJ S ≤ (K₂ ⊔ S).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (T.isPGroup'.to_le (hJS.trans inf_le_left))
      (hJS.trans le_sup_right) (sup_le (h₂M.trans hMN) hSD)
  have hlocal : K₂ ∈ Chapter1.L G S := by
    have hcomp : (K₂.subgroupOf M).IsCComponent := by
      change ((solvableResidual M).map M.subtype |>.comap M.subtype).IsCComponent
      rwa [comap_map_eq_self_of_injective M.subtype_injective]
    refine ⟨hcomp.subgroupOf_of_le le_sup_left (sup_le h₂M hSM),
      hK.2.2.1.restrict le_sup_right (sup_le h₂H le_sup_right), ?_⟩
    intro he
    have hbot : D.map S.subtype = ⊥ := le_bot_iff.mp (hD ▸ he ▸ hcore)
    exact hDne ((map_eq_bot_iff_of_injective D S.subtype_injective).mp hbot)
  exact ⟨K₂, ⟨h₂H.trans (sup_le hK.1 inf_le_right), hlocal⟩, hS₂, hmove₂, h₂M.trans hMN⟩
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.SeedMovement

end
