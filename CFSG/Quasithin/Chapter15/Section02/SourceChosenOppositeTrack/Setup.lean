module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenSetup
public import CFSG.Quasithin.Chapter15.Section01.ChosenNormalizerSource
public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs.Completion
public import Theory.GroupTheory.ReducedNormal.Equiv

/-!
# The source normalizer pair in its generated subgroup

Let N = N_M(C_T(V)) and L = ⟨N,H⟩. The genuine 15.1.9(5--6) normalizer
results provide reducedness of V, F*(N) = O₂(N), and O₂(L) = 1. Both vertices
and the common Sylow are restricted to L. The equality O₂(N) = C_T(V),
together with reducedness, gives the literal F.7.6 Sylow-centralizer equality
inside the first vertex. The constructed seed maps to the original V and
lies in the second vertex's two-core by the prepared 15.1.11 input.

This first vertex is N, not an identification of N with M. Its ambient action
is compared with the M-action by `Action.lean`; the final source consumer uses
M ∩ H = T to control the second-vertex centralizer.

Source: Aschbacher--Smith, 15.1.9--11, printed pp.1088--1089;
F.7.1 and F.7.6, printed pp.311--312; Section 15.2, pp.1119--1120.
-/

public section

open Subgroup Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterF.Section07.Track
namespace CFSG.Quasithin.Chapter15.Section02.ChosenOppositeTrack
open Section01 ChapterD
variable {G : Type*} [Group G] [Finite G]

/-- Construct the actual F.7 coset-graph inputs, retaining the original
ambient seed and the inclusion of the first vertex in M. -/
theorem normalizer_source_setup
    (T : Sylow 2 G) {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS) :
    let N := chosenNormalizer T M V
    let L := N ⊔ H
    let F : Bool → Subgroup L := fun i => if i then H.subgroupOf L else N.subgroupOf L
    ∃ D : SourceSetup F, D.V ≠ ⊥ ∧ D.seed.map L.subtype = V ∧
      (F false).map L.subtype ≤ M ∧ D.seed ≤ (F true).pCoreIn 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := h.prepared.elementary
  let N := chosenNormalizer T M V
  let L := N ⊔ H
  let A := N.subgroupOf L
  let B := H.subgroupOf L
  let F : Bool → Subgroup L := fun i => if i then B else A
  have hTN : (T : Subgroup G) ≤ N :=
    sylow_le_chosenNormalizer T h.maximal.1.2 h.prepared.normalized
  have hTH : (T : Subgroup G) ≤ H := hg.outside.1.1.2
  have hTL : (T : Subgroup G) ≤ L := hTN.trans le_sup_left
  have hVN : V ≤ N := module_le_chosenNormalizer T h.maximal.1.2
    h.prepared.le_selected h.prepared.normalized
  let eA : A ≃* N := subgroupOfEquivOfLe (show N ≤ L from le_sup_left)
  let W := (V.subgroupOf N).map eA.symm.toMonoidHom
  have hr : IsPReduced 2 W :=
    (chosenNormalizer_reduced T h.maximal.1.2 h.prepared.le_selected
      h.prepared.normalized h.prepared.seed_span).map_equiv eA.symm
  have hw : (W.map A.subtype).map L.subtype = V := by
    rw [map_map, map_map]
    have he : (L.subtype.comp A.subtype).comp eA.symm.toMonoidHom = N.subtype := by
      ext x
      rfl
    rw [he, map_subgroupOf_eq_of_le hVN]
  have hWne : W ≠ ⊥ := by
    intro he
    rw [he, Subgroup.map_bot, Subgroup.map_bot] at hw
    exact h.prepared.nontrivial hw.symm
  have hfitN := chosenNormalizer_generalizedFitting h.ambient T h.maximal.1.2
    h.prepared.le_selected h.prepared.nontrivial h.prepared.normalized
  have hfitA : generalizedFitting A = pCore 2 A := by
    apply map_injective (f := eA.toMonoidHom) eA.injective
    rw [map_generalizedFitting_equiv, pCore_map_iso, hfitN]
  have hcore : pCore 2 L = ⊥ :=
    source_chosenNormalizer_join_twoCore_eq_bot h.ambient T h.empty h.maximal
      h.centralizing h.prepared.nontrivial h.prepared.normalized
      h.prepared.seed_span hg.outside
  have hgen : F false ⊔ F true = ⊤ := by
    apply map_injective L.subtype_injective
    change (N.subgroupOf L ⊔ H.subgroupOf L).map L.subtype = (⊤ : Subgroup L).map L.subtype
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show N ≤ L from le_sup_left),
      map_subgroupOf_eq_of_le (show H ≤ L from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
  let S := T.subtype hTL
  have hSA : (S : Subgroup L) ≤ A := fun _ hx => hTN hx
  have hSB : (S : Subgroup L) ≤ B := fun _ hx => hTH hx
  let P : ∀ i, Sylow 2 (F i) := fun i => S.subtype (by
    cases i
    · exact hSA
    · exact hSB)
  have hR : N.pCoreIn 2 = (T : Subgroup G) ⊓ centralizer (V : Set G) :=
    chosenNormalizer_twoCore T h.maximal.1.2 h.prepared.le_selected
      h.prepared.normalized h.prepared.seed_span
  have hQ : ((pCore 2 A).map A.subtype).map L.subtype = N.pCoreIn 2 := by
    rw [map_map]
    change (pCore 2 A).map (N.subtype.comp eA.toMonoidHom) = _
    rw [← map_map, pCore_map_iso]
    rfl
  have hc : ((S.subtype hSA : Sylow 2 A) : Subgroup A) ⊓ centralizer (W : Set A) =
      (centralizer (W : Set A)).pCoreIn 2 := by
    rw [AmalgamLocalCores.reduced_centralizer_core _ hr]
    apply le_antisymm
    · intro x hx
      have hxT : ((x : L) : G) ∈ (T : Subgroup G) := hx.1
      have hxC : ((x : L) : G) ∈ centralizer (V : Set G) := by
        rw [← hw]
        rintro y ⟨z, ⟨w, hw, rfl⟩, rfl⟩
        exact congrArg (fun a : A => ((a : L) : G)) (hx.2 w hw)
      have hxQ : ((x : L) : G) ∈ ((pCore 2 A).map A.subtype).map L.subtype := by
        rw [hQ, hR]
        exact ⟨hxT, hxC⟩
      obtain ⟨z, ⟨w, hw, rfl⟩, he⟩ := hxQ
      have he' : w = x := Subtype.ext (Subtype.ext he)
      exact he' ▸ hw
    · exact le_inf (pCore_isPGroup.le_sylow_of_normal (P false))
        (le_centralizer_iff.mp hr.le_centralizer_pCore)
  let D : SourceSetup F := {
    finite := fun _ => inferInstance
    generates := hgen
    characteristicTwo := hfitA
    core_free := by
      let e : (F false ⊔ F true : Subgroup L) ≃* L :=
        (MulEquiv.subgroupCongr hgen).trans topEquiv
      apply (map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
      rw [pCore_map_iso]
      exact hcore
    sylow := P
    same_sylow := (map_subgroupOf_eq_of_le hSA).trans
      (map_subgroupOf_eq_of_le hSB).symm
    V := W
    reduced := hr
    centralizer_eq := hc }
  refine ⟨D, hWne, hw, ?_, ?_⟩
  · change A.map L.subtype ≤ M
    rw [map_subgroupOf_eq_of_le (show N ≤ L from le_sup_left)]
    exact inf_le_left
  · apply (map_le_map_iff_of_injective L.subtype_injective).mp
    rw [show D.seed.map L.subtype = V from hw,
      ← AmalgamLocalCores.pCoreIn_map_of_injective 2 L.subtype L.subtype_injective,
      show (F true).map L.subtype = H from
        map_subgroupOf_eq_of_le (show H ≤ L from le_sup_right)]
    exact h.prepared.inside_core H hg.outside

end CFSG.Quasithin.Chapter15.Section02.ChosenOppositeTrack
