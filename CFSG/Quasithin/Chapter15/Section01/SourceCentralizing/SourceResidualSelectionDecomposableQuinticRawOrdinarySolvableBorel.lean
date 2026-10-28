module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.SolvableBorel
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawBorel

/-!
# The ordinary solvable marked intersection from actual residual control

The original characteristic-normalizer and residual-normalizer bounds control
the solvable component orbit of its actual Borel. No global residual
centralization or marked generation is used. The internal import reuses only
the proof package's raw solvable-control helper; no private name occurs in
the public type.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Intrinsic solvable Sylow control and the original literal local bounds
identify the ordinary marked intersection with its actual Borel. -/
theorem raw_ordinary_solvable_borel_eq (H Mc S L : Subgroup G)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hSM : S ≤ H ⊓ Mc) (hS : IsPGroup 2 S) (hSyl : Chapter1.IsSylowIn 2 S H)
    (hLG : L ≤ H) (hL : IsComponent H (L.subgroupOf H))
    (hSL : Chapter1.IsSylowIn 2 (S ⊓ L) L)
    (hcontrol : ((H ⊓ Mc).pCoreIn 2).characteristicNormalizerClosure ≤ Mc)
    (hbound : normalizer ((pResidual 2 (H ⊓ Mc : Subgroup G)).map
      (H ⊓ Mc).subtype : Set G) ≤ Mc)
    (hsol : Group.IsSolvable ((H ⊓ Mc) ⊓ L : Subgroup G))
    (hc : SolvableSylowControl 2 L)
    (hB : HasCharacteristicTwo ((normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype)) :
    ((H ⊓ Mc) ⊓ L) = (normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype := by
  let N := H ⊓ Mc
  let A := N ⊓ L
  let B := (normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype
  let := hsol
  obtain ⟨P,hP⟩ := hSL
  have hPA : S ⊓ L ≤ A := inf_le_inf_right L hSM
  have hcore : A.pCoreIn 2 = S ⊓ L := by
    have hh := SolvableSylowControl.core_intersection L A hc P (hP ▸ hPA)
    rw [inf_eq_left.mpr (show A ≤ L from inf_le_right),hP] at hh
    exact hh
  have hnA : N ⊓ normalizer (L : Set G) ≤ normalizer (A : Set G) :=
    (le_inf (inf_le_left.trans N.le_normalizer) inf_le_right).trans
      inf_normalizer_le_normalizer_inf
  have hnP : N ⊓ normalizer (L : Set G) ≤ normalizer (S ⊓ L : Set G) := by
    change N ⊓ normalizer (L : Set G) ≤ normalizer ((S ⊓ L : Subgroup G) : Set G)
    rw [←hcore]
    exact hnA.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  have hb : B = L ⊓ normalizer (S ⊓ L : Set G) := by
    rw [show B = (normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype from rfl,
      ←subgroupOf_normalizer_eq (show S ⊓ L ≤ L from inf_le_right),subgroupOf_map_subtype]
    exact inf_comm _ _
  have hinv : N ⊓ normalizer (L : Set G) ≤ normalizer (B : Set G) := by
    rw [hb]
    exact (le_inf inf_le_right (hnP.trans (normalizer (S ⊓ L : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hupper : A ≤ B := by
    rw [hb]
    refine le_inf inf_le_right ?_
    change A ≤ normalizer ((S ⊓ L : Subgroup G) : Set G)
    rw [←hcore]
    exact A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  have hSB : S ⊓ L ≤ B := hb ▸ le_inf inf_le_right (S ⊓ L).le_normalizer
  obtain ⟨Q,hQ⟩ := P.exists_map_subtype_eq_of_le
    (show B ≤ L from map_subtype_le _) (hP ▸ hSB)
  have hBc : B.pCoreIn 2 = S ⊓ L := le_antisymm
    ((pCoreIn_le_sylow _ Q).trans_eq (hQ.trans hP))
    (le_pCoreIn_of_normalizes (hS.to_le inf_le_left) hSB (hb ▸ inf_le_right))
  have hBcore : pCore 2 B = (Q : Subgroup B) := by
    apply map_injective B.subtype_injective
    exact hBc.trans (hQ.trans hP).symm
  have hodd : Odd (Nat.card (B ⧸ pCore 2 B)) := by
    apply Nat.not_even_iff_odd.mp
    intro heven
    have hd : 2 ∣ (pCore 2 B).index := even_iff_two_dvd.mp heven
    rw [hBcore] at hd
    exact Q.not_dvd_index hd
  have hBL : B ≤ L := map_subtype_le _
  obtain ⟨hf,ho⟩ := hL.relative_local_orbit_fitting_odd hLG hBL
    (show N ≤ H from inf_le_left) hinv hB hodd
  have hBH : componentOrbit B N ≤ H := by
    apply iSup_le
    intro a
    rintro x ⟨b,hb,rfl⟩
    exact H.mul_mem (H.mul_mem a.property.1 (hLG (hBL hb))) (H.inv_mem a.property.1)
  have hle := raw_solvable_control H Mc S (componentOrbit B N)
    hH hSM hSyl hcontrol hbound hBH (le_normalizer_componentOrbit _ _) hf ho
  exact le_antisymm hupper (le_inf ((le_componentOrbit _ _).trans hle) hBL)

end CFSG.Quasithin.Chapter15.Section01
