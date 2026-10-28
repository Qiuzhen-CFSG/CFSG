module
public import CFSG.Quasithin.Chapter14.Section02.ProperSpan
public import Theory.GroupTheory.ElementaryThompsonQuasisimpleCore

/-!
# The original completion component and its Thompson commutator

In the remaining branch Y≤L, the completion is LS. The original
characteristic-subgroup exclusion prevents L from normalizing J(S).
The normal-component Thompson lemma then gives L=[L,J(S)] whenever the
actual two-core quotient is quasisimple. This supplies the commutator input
for the source FF-module argument. The quotient condition remains explicit;
this theorem does not classify the marked containing component.

Source: Aschbacher--Smith 14.2.15, printed p.986.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_proper_component_thompson_commutator_of_residual_le
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K S : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hi : S.relIndex (T : Subgroup G) = 2)
    (hgen : K ⊔ (T : Subgroup G) = H)
    (hK : K ∈ Chapter1.L G S) (hSN : S ≤ normalizer (K : Set G))
    (hcore : (K ⊔ sourceResidual M Mc ⊔ S).pCoreIn 2 ≠ ⊥)
    (hs : Chapter1.IsSylowIn 2 S (K ⊔ sourceResidual M Mc ⊔ S)) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    let L := (solvableResidual X).map X.subtype
    IsQuasisimple (L ⧸ pCore 2 L) → sourceResidual M Mc ≤ L →
      L = ⁅L,elementaryAbelianMaxJ S⁆ := by
  let X := K ⊔ sourceResidual M Mc ⊔ S
  let L := (solvableResidual X).map X.subtype
  change IsQuasisimple (L ⧸ pCore 2 L) → sourceResidual M Mc ≤ L →
    L = ⁅L,elementaryAbelianMaxJ S⁆
  intro hq hYL
  obtain ⟨hL,hKL,hgenL⟩ := source_proper_completion_component hG T hempty hM hu hmany
    hcard e K S hST hK hSN hcore hs
  have hLX : L ≤ X := map_subtype_le _
  have hSX : S ≤ X := le_sup_right
  obtain ⟨P,hP⟩ := hs
  have hPS : (P : Subgroup X) = S.subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hSX]
  have hSne : S ≠ ⊥ := by
    intro he
    exact hcore (bot_unique ((pCoreIn_le_sylow X P).trans (hP.trans he).le))
  let : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).mpr hSne
  let C := elementaryAbelianMaxJ (⊤ : Subgroup S)
  have hCne : C ≠ ⊥ := elementaryAbelianMaxJ_top_ne_bot_of_isPGroup (T.isPGroup'.to_le hST)
  have hCmap : C.map S.subtype = elementaryAbelianMaxJ S := by
    change (elementaryAbelianMaxJ (⊤ : Subgroup S)).map S.subtype = _
    rw [←elementaryAbelianMaxJ_map_injective S.subtype S.subtype_injective,
      ←MonoidHom.range_eq_map,range_subtype]
  have hLZ := source_proper_completion_component_noncentral hG T hempty hM hu hmany
    hcard e H hH K S hST hgen hK hSN hcore ⟨P,hP⟩
  have hnot := source_proper_component_characteristic_exclusion hG T hempty hM hu
    hmany hcard e H hH K S L hST hi hgen hKL hLZ C
    elementaryAbelianMaxJ_top_characteristic hCne
  rw [hCmap] at hnot
  let L₀ := L.subgroupOf X
  have hL₀ : L₀ = solvableResidual X := comap_map_eq_self_of_injective X.subtype_injective _
  let : L₀.Normal := hL₀.symm ▸ inferInstance
  let := hq
  let : IsQuasisimple (L₀ ⧸ pCore 2 L₀) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLX) (pCore_map_iso 2 _)).symm
  have hgenLS : L ⊔ S = X := by
    change L ⊔ sourceResidual M Mc ⊔ S = X at hgenL
    simpa only [sup_of_le_left hYL] using hgenL
  have hgen₀ : L₀ ⊔ (P : Subgroup X) = ⊤ := by
    apply map_injective X.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hLX,hP,
      ←MonoidHom.range_eq_map,range_subtype]
    exact hgenLS
  have hJmap : (elementaryAbelianMaxJ (P : Subgroup X)).map X.subtype =
      elementaryAbelianMaxJ S := by
    rw [←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,hP]
  have hnot₀ : ¬ L₀ ≤ normalizer (elementaryAbelianMaxJ (P : Subgroup X) : Set X) := by
    intro hn
    apply hnot
    rw [←map_subgroupOf_eq_of_le hLX,←hJmap]
    exact (map_mono hn).trans ((elementaryAbelianMaxJ (P : Subgroup X)).le_normalizer_map X.subtype)
  have he := eq_commutator_maxJ_of_quasisimple_core_of_not_normalizes P L₀ hL.2 hgen₀ hnot₀
  have hm := congrArg (Subgroup.map X.subtype) he
  simpa only [L₀,map_subgroupOf_eq_of_le hLX,map_commutator,hJmap] using hm

end CFSG.Quasithin.Chapter14.Section02
