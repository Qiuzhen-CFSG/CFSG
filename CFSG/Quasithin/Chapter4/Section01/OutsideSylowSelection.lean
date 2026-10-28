module
public import CFSG.Quasithin.Chapter4.Defs
public import Theory.Quasithin.EvenCharacteristic
public import Mathlib.Data.Set.Finite.Lemmas
/-!
# Selecting an outside local subgroup with a Sylow intersection

Among maximal two-local overgroups of a normalized subgroup L outside M,
choose H maximizing the order of T ∩ H. Sylow conjugacy inside M then
makes this intersection Sylow in H ∩ M. Every strict extension X of that
intersection in T has L X as a uniqueness subgroup: another outside
overgroup would have a larger intersection with T.

This is the maximal-intersection step of Aschbacher–Smith 4.3.3(a),
printed pp.613–614, independent of the subsequent component analysis.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4
variable {G : Type*} [Group G] [Finite G]

/-- A maximal Sylow intersection of an outside overgroup is locally Sylow. -/
theorem maximal_intersection_sylow
    (T : Sylow 2 G) {L M H : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hML : M ≤ normalizer (L : Set G))
    (hH : IsMaximalTwoLocal H) (hLH : L ≤ H) (hHM : H ≠ M)
    (hmax : ∀ K : Subgroup G, IsMaximalTwoLocal K → L ≤ K → K ≠ M →
      Nat.card ((T : Subgroup G) ⊓ K : Subgroup G) ≤ Nat.card ((T : Subgroup G) ⊓ H : Subgroup G)) :
    ∃ P : Sylow 2 (H ⊓ M : Subgroup G),
      (P : Subgroup (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype = (T : Subgroup G) ⊓ H := by
  let S := (T : Subgroup G) ⊓ H
  let A := H ⊓ M
  have hSA : S ≤ A := le_inf inf_le_right (inf_le_left.trans hTM)
  obtain ⟨P,hSP⟩ := ((T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
    (K := A)).exists_le_sylow
  let W := (P : Subgroup A).map A.subtype
  have hSW : S ≤ W := by
    rw [← map_subgroupOf_eq_of_le hSA]
    exact map_mono hSP
  have hWA : W ≤ A := map_subtype_le _
  have hWM : W ≤ M := hWA.trans inf_le_right
  obtain ⟨Q,hWQ⟩ := ((P.isPGroup'.map A.subtype).comap_subtype (K := M)).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M Q (T.subtype hTM)
  let e := MulAut.conj (g : G)
  have hQg : ((Q : Subgroup M).map M.subtype).map e.toMonoidHom = (T : Subgroup G) := by
    have hh := congrArg (fun Z : Sylow 2 M => (Z : Subgroup M).map M.subtype) hg
    change (((Q : Subgroup M).map (MulAut.conj g).toMonoidHom).map M.subtype) = _ at hh
    rw [map_map] at hh ⊢
    change (Q : Subgroup M).map (M.subtype.comp (MulAut.conj g).toMonoidHom) = _ at hh
    change (Q : Subgroup M).map (e.toMonoidHom.comp M.subtype) =
      ((T : Subgroup G).subgroupOf M).map M.subtype at hh
    rwa [map_subgroupOf_eq_of_le hTM] at hh
  have hWg : W.map e.toMonoidHom ≤ (T : Subgroup G) := by
    rw [← hQg]
    apply map_mono
    rw [← map_subgroupOf_eq_of_le hWM]
    exact map_mono hWQ
  have hLg : L.map e.toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp (hML g.property)
  have hMg : M.map e.toMonoidHom = M := mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer g.property)
  have hHge : H.map e.toMonoidHom ≠ M := by
    intro he
    apply hHM
    apply map_injective (f := e.toMonoidHom) e.injective
    exact he.trans hMg.symm
  have hbound := hmax (H.map e.toMonoidHom)
    (Theory.Quasithin.isMaximalTwoLocal_map e hH)
    (hLg ▸ map_mono (f := e.toMonoidHom) hLH) hHge
  have hWbound := card_le_of_le (le_inf hWg (map_mono (f := e.toMonoidHom) (hWA.trans inf_le_left)))
  rw [card_map_of_injective e.injective] at hWbound
  exact ⟨P, (eq_of_le_of_card_ge hSW (hWbound.trans hbound)).symm⟩

/-- Source 4.3.3(a), with the maximal outside intersection selected internally. -/
theorem exists_maximal_sylow_intersection
    (T : Sylow 2 G) {L M : Subgroup G}
    (hu : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) M)
    (hML : M ≤ normalizer (L : Set G))
    (hnot : ¬ UniqueMaximalOvergroup L M) :
    ∃ H : Subgroup G, IsMaximalTwoLocal H ∧ L ≤ H ∧ H ≠ M ∧
      (T : Subgroup G) ⊓ H < (T : Subgroup G) ∧
      (∃ P : Sylow 2 (H ⊓ M : Subgroup G),
        (P : Subgroup (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype = (T : Subgroup G) ⊓ H) ∧
      ∀ X : Subgroup G, (T : Subgroup G) ⊓ H < X → X ≤ (T : Subgroup G) →
        UniqueMaximalOvergroup (L ⊔ X) M := by
  classical
  let candidates : Set (Subgroup G) := {H | IsMaximalTwoLocal H ∧ L ≤ H ∧ H ≠ M}
  have hc : candidates.Nonempty := by
    by_contra hn
    apply hnot
    refine ⟨hu.1,le_sup_left.trans hu.2.1,?_⟩
    intro H hH hLH
    by_contra he
    exact hn ⟨H,hH,hLH,he⟩
  obtain ⟨H,hH,hmax⟩ := Set.exists_max_image candidates
    (fun H => Nat.card ((T : Subgroup G) ⊓ H : Subgroup G)) candidates.toFinite hc
  have hTM : (T : Subgroup G) ≤ M := le_sup_right.trans hu.2.1
  refine ⟨H,hH.1,hH.2.1,hH.2.2,?_,?_,?_⟩
  · apply lt_of_le_of_ne inf_le_left
    intro he
    exact hH.2.2 (hu.2.2 H hH.1 (sup_le hH.2.1 (inf_eq_left.mp he)))
  · exact maximal_intersection_sylow T hTM hML hH.1 hH.2.1 hH.2.2
      (fun K hK hLK hKM => hmax K ⟨hK,hLK,hKM⟩)
  · intro X hSX hXT
    refine ⟨hu.1,sup_le (le_sup_left.trans hu.2.1) (hXT.trans hTM),?_⟩
    intro K hK hLXK
    by_contra hKM
    have hXK : X ≤ (T : Subgroup G) ⊓ K := le_inf hXT (le_sup_right.trans hLXK)
    have he : (T : Subgroup G) ⊓ H = (T : Subgroup G) ⊓ K :=
      eq_of_le_of_card_ge (hSX.le.trans hXK)
        (hmax K ⟨hK,le_sup_left.trans hLXK,hKM⟩)
    exact hSX.not_ge (hXK.trans he.ge)
end CFSG.Quasithin.Chapter4
