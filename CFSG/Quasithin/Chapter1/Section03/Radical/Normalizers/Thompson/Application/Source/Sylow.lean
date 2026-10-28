module
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Application.Source.Preliminaries
public import Stellmacher.ElementaryAbelianMaxGlobal

/-!
# The actual Thompson image is Sylow in the global image

Every maximum elementary subgroup conjugates into the prescribed Sylow
subgroup, so J(G) is the normal closure of J(T). The original quotient
Thompson image J lies in the selected product [O₂′(G*),J]J; its normality
and Sylow-intersection identity are proved by the native solvable offender
argument. This identifies the selected product with the image of J(G),
retaining the original star map and the literal Sylow subtype image.

Source: Aschbacher--Smith B.2.16(2), printed p.79.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.ThompsonSource
universe u
variable {G : Type u} [Group G] [Finite G]

theorem global_thompson_eq_normalClosure (T : Sylow 2 G) :
    elementaryAbelianMaxJ (⊤ : Subgroup G) =
      normalClosure (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  let N := normalClosure (elementaryAbelianMaxJ (T : Subgroup G) : Set G)
  let : (elementaryAbelianMaxJ (⊤ : Subgroup G)).Characteristic :=
    elementaryAbelianMaxJ_top_characteristic
  apply le_antisymm ?_ (normalClosure_le_normal (elementaryAbelianMaxJ_sylow_le_top T))
  apply sSup_le
  intro A hA
  obtain ⟨S,hAS⟩ := hA.2.1.isPGroup.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G S T
  let e := MulAut.conj g
  have hST : (S : Subgroup G).map e.toMonoidHom = T := by
    change ((g • S : Sylow 2 G) : Subgroup G) = T
    rw [hg]
  have hAT : A.map e.toMonoidHom ≤ (T : Subgroup G) := (map_mono hAS).trans hST.le
  have hAm : A.map e.toMonoidHom ∈ elementaryAbelianMaxSubgroups (T : Subgroup G) := by
    refine ⟨hAT,hA.2.1.map e.toMonoidHom,?_⟩
    intro B _ hB
    rw [card_map_of_injective e.injective]
    exact hA.2.2 B le_top hB
  intro a ha
  have hx : g * a * g⁻¹ ∈ N :=
    le_normalClosure (le_sSup hAm (mem_map_of_mem e.toMonoidHom ha))
  have hi := (inferInstance : N.Normal).conj_mem _ hx g⁻¹
  simpa [N, mul_assoc] using hi

theorem source_thompson_sylow (hs : Group.IsSolvable G)
    (hf : generalizedFitting G = pCore 2 G) (T : Sylow 2 G)
    (hn : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (closure T : Set G)) :
    Chapter1.IsSylowIn 2
      ((elementaryAbelianMaxJ (T : Subgroup G)).map (starMap (closure T)))
      ((elementaryAbelianMaxJ (⊤ : Subgroup G)).map (starMap (closure T))) := by
  let q := starMap (closure T)
  let J := (elementaryAbelianMaxJ (T : Subgroup G)).map q
  let L := (elementaryAbelianMaxJ (⊤ : Subgroup G)).map q
  let B := (T : Subgroup G) ⊓ centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ (T : Subgroup G)) : Set G)
  have hT : (T : Subgroup G) ≠ ⊥ := by
    intro h
    apply hn
    have he : elementaryAbelianMaxJ (T : Subgroup G) = ⊥ := by
      apply bot_unique
      simpa only [h] using (show elementaryAbelianMaxJ (T : Subgroup G) ≤ T from sSup_le fun _ h => h.1)
    rw [he]
    exact bot_le
  have hsec := sectionTwo_of_sylow_ne_bot hs hf T hT
  have hJ : J ≠ ⊥ := by
    intro hz
    apply hn
    simpa only [q,starMap,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz
  have h22 := SectionTwo.lemma_two_two hsec T q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    ((T : Subgroup G).map q) J (B.map q) rfl B rfl rfl rfl hJ
  let E := ⁅SectionOne.oddCore (CentralQuotient (closure T)),J⁆ ⊔ J
  let : E.Normal := h22.part_a
  have hE : E = normalClosure (J : Set (CentralQuotient (closure T))) := by
    apply le_antisymm
    · exact sup_le ((commutator_mono le_rfl (show J ≤ normalClosure (J : Set _) from
        le_normalClosure)).trans (commutator_le_right _ _)) le_normalClosure
    · exact normalClosure_le_normal (show J ≤ E from le_sup_right)
  have hL : E = L := by
    rw [hE]
    change normalClosure (q '' (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) = L
    rw [← map_normalClosure _ q (QuotientGroup.mk'_surjective _),
      ← global_thompson_eq_normalClosure T]
  let S := T.mapSurjective (QuotientGroup.mk'_surjective (centralizer (closure T : Set G)))
  have hJL : J = (S : Subgroup (CentralQuotient (closure T))) ⊓ L := by
    rw [← hL]
    exact SectionOne.oddCore_commutator_join_sylow_inf S J
      (map_mono (show elementaryAbelianMaxJ (T : Subgroup G) ≤ T from sSup_le fun _ h => h.1))
  let : L.Normal := hL ▸ (inferInstance : E.Normal)
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal L
  refine ⟨P,?_⟩
  rw [hP, subgroupOf_map_subtype]
  exact hJL.symm
end CFSG.Quasithin.Chapter1.RadicalNormalizers.ThompsonSource
