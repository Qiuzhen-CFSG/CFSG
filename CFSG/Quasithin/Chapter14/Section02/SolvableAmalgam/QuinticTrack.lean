module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.Source
public import CFSG.Quasithin.Chapter14.Section02.ProperSpan
public import CFSG.Quasithin.ChapterF.Section07.Track
public import Theory.GroupTheory.SylowOmegaSpan
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure

/-!
# The literal source track for the quintic recognition branch

Put X=YT and L=X∨H for the original selected outside subgroup H. The
source core calculation gives O₂(L)=1, while H centralizes the prescribed
Sylow central involution. Consequently X moves that involution. Its cubic
quotient gives a reduced omega span with the required centralizer, and the
original residual-span theorem identifies this seed with the actual plane V.
Restricting both vertices to L constructs all F.7 source hypotheses and
retains the prescribed common Sylow. No generation of the full ambient G,
second cubic quotient, marked amalgam, or completion is assumed.

Source: Aschbacher--Smith14.2.21, p.988, the asymmetric F.1.12 input;
F.7.1,6--11, pp.311--313, for the critical-track construction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem pair_generates (A B : Subgroup G) :
    A.subgroupOf (A ⊔ B) ⊔ B.subgroupOf (A ⊔ B) = ⊤ := by
  apply (map_injective (A ⊔ B).subtype_injective)
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
    map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]

private theorem source_vertex_fitting {H K : Type*} [Group H] [Group K]
    [Finite H] [Finite K] (e : H ≃* K)
    (h : generalizedFitting K = pCore 2 K) :
    generalizedFitting H = pCore 2 H := by
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [map_generalizedFitting_equiv, pCore_map_iso, h]

omit [Finite G] in
private theorem map_source_seed (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) :
    (SylowOmegaSpan.seed (T.subtype hTH)).map H.subtype = centralInvolutions T := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    have hy' := (mem_omegaCenterIn_iff _ _).mp hy
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨hy'.1,?_,congrArg Subtype.val hy'.2.2⟩
    rw [mem_centralizer_iff]
    intro s hs
    exact congrArg Subtype.val (mem_centralizer_iff.mp hy'.2.1 ⟨s,hTH hs⟩ hs)
  · intro hx
    have hx' := (mem_omegaCenterIn_iff _ _).mp hx
    refine ⟨⟨x,hTH hx'.1⟩,?_,rfl⟩
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨hx'.1,?_,Subtype.ext hx'.2.2⟩
    rw [mem_centralizer_iff]
    intro s hs
    exact Subtype.ext (mem_centralizer_iff.mp hx'.2.1 s hs)

/-- The literal cubic residual vertex supplies a nontrivial source track,
inside the actual group generated with the selected outside vertex. -/
theorem source_residual_vertex_track
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let L := X ⊔ H
    let F : Bool → Subgroup L := fun i => if i then H.subgroupOf L else X.subgroupOf L
    ∃ D : ChapterF.Section07.Track.SourceSetup F, D.V ≠ ⊥ ∧
      D.seed.map L.subtype = localModule T M ∧
      (D.sylow false : Subgroup (F false)).map
        (L.subtype.comp (F false).subtype) = (T : Subgroup G) := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L := X ⊔ H
  let A := X.subgroupOf L
  let B := H.subgroupOf L
  let F : Bool → Subgroup L := fun i => if i then B else A
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hTL : (T : Subgroup G) ≤ L := hTX.trans le_sup_left
  have hXM : X ≤ M := sup_le (sourceResidual_le _ _) hM.1.2
  have hXH : X ∈ Chapter1.HOver G (T : Set G) :=
    Chapter3.mem_HOver_of_sylow_interval T hTX hXM
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  have hcX : centralizer (pCore 2 X : Set X) ≤ pCore 2 X :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hXH)
  have hfitX : generalizedFitting X = pCore 2 X :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2 hcX
  have hcore : pCore 2 L = ⊥ := by
    let d : L ≃* (H ⊔ X : Subgroup G) := MulEquiv.subgroupCongr (sup_comm X H)
    apply (map_eq_bot_iff_of_injective _ (f := d.toMonoidHom) d.injective).mp
    rw [pCore_map_iso]
    exact source_solvable_amalgam_twoCore_eq_bot hG T hempty hM hu hmany hcard e H hH.1.2
  have hHZ : H ≤ centralizer (centralInvolutions T : Set G) :=
    (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  have hZcard := plane_centralInvolutions_card T M hM.1.2 hcard e
  have hnX : ¬ centralInvolutions T ≤ centralizer (X : Set G) := by
    intro hn
    have hb := AmalgamLocalCores.common_normal_eq_bot X H (centralInvolutions T)
      (le_inf ((centralInvolutions_le_sylow T).trans hTX)
        ((centralInvolutions_le_sylow T).trans hTH))
      ((le_centralizer_iff.mp hn).trans (_root_.centralizer_le_normalizer _))
      (hHZ.trans (_root_.centralizer_le_normalizer _)) hcore hcX
    rw [hb,card_bot] at hZcard
    omega
  let S := T.subtype hTL
  have hSA : (S : Subgroup L) ≤ A := fun x hx => hTX hx
  have hSB : (S : Subgroup L) ≤ B := fun x hx => hTH hx
  let P : ∀ i, Sylow 2 (F i) := fun i => S.subtype (by
    cases i
    · exact hSA
    · exact hSB)
  let eA : A ≃* X := subgroupOfEquivOfLe (show X ≤ L from le_sup_left)
  have hfitA : generalizedFitting A = pCore 2 A := source_vertex_fitting eA hfitX
  have hcA : centralizer (pCore 2 A : Set A) ≤ pCore 2 A := by
    simpa only [hfitA] using centralizer_generalizedFitting_le A
  obtain ⟨_,⟨eX⟩⟩ := source_residualSylow_quotient hG T hempty hM hu hmany hcard e
  let qA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3) :=
    (QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).trans eX
  have hi : (P false : Subgroup (F false)).index = 3 :=
    SymmetricThreeTwoCore.sylow_index_three qA (P false)
  have hsmap : (SylowOmegaSpan.seed (P false)).map A.subtype = centralInvolutions S :=
    map_source_seed S A hSA
  have hzmap : (centralInvolutions S).map L.subtype = centralInvolutions T :=
    map_source_seed T L hTL
  have hn : ¬ SylowOmegaSpan.seed (P false) ≤ center A := by
    intro hn
    apply hnX
    rw [← hzmap, ← hsmap, map_map]
    rintro _ ⟨z,hz,rfl⟩
    rw [mem_centralizer_iff]
    intro x hx
    let a : A := ⟨⟨x,(show X ≤ L from le_sup_left) hx⟩,hx⟩
    exact congrArg (fun a : A => (a : L).val) (mem_center_iff.mp (hn hz) a)
  have hr := SylowOmegaSpan.span_reduced (P false) hi hn hcA
  have hg : F false ⊔ F true = ⊤ := pair_generates X H
  let D : ChapterF.Section07.Track.SourceSetup F := {
    finite := fun _ => inferInstance
    generates := hg
    characteristicTwo := hfitA
    core_free := by
      let d : (F false ⊔ F true : Subgroup L) ≃* L :=
        (MulEquiv.subgroupCongr hg).trans topEquiv
      apply (map_eq_bot_iff_of_injective _ (f := d.toMonoidHom) d.injective).mp
      rw [pCore_map_iso]
      exact hcore
    sylow := P
    same_sylow := (map_subgroupOf_eq_of_le hSA).trans
      (map_subgroupOf_eq_of_le hSB).symm
    V := SylowOmegaSpan.span (P false)
    reduced := hr
    centralizer_eq := by
      rw [AmalgamLocalCores.reduced_centralizer_core _ hr]
      rw [SylowOmegaSpan.span_centralizer (P false) hi hn]
      exact inf_eq_right.mpr (pCore_isPGroup.le_sylow_of_normal (P false)) }
  refine ⟨D,SylowOmegaSpan.span_ne_bot _ hn,?_,?_⟩
  · have hZA : centralInvolutions S ≤ A := by
      rw [←hsmap]
      exact map_subtype_le _
    have hs : SylowOmegaSpan.seed (P false) = (centralInvolutions S).subgroupOf A := by
      apply map_injective A.subtype_injective
      rw [hsmap,map_subgroupOf_eq_of_le hZA]
    change ((SylowOmegaSpan.span (P false)).map A.subtype).map L.subtype = _
    rw [SylowOmegaSpan.span,hs,normalClosure_subgroupOf_eq_conjugateSpanBy _ _ hZA,
      map_subgroupOf_eq_of_le (conjugateSpanBy_le_self hZA),map_conjugateSpanBy,hzmap,
      map_subgroupOf_eq_of_le (show X ≤ L from le_sup_left)]
    apply le_antisymm
    · exact conjugateSpanBy_mono le_rfl hXM
    · rw [source_plane_module_residual_span hG T hempty hM hu hmany hcard e]
      exact conjugateSpanBy_mono le_rfl le_sup_left
  · rw [← map_map]
    change (((S.subtype hSA : Sylow 2 A) : Subgroup A).map A.subtype).map L.subtype = _
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hSA]
    change ((T.subtype hTL : Sylow 2 L) : Subgroup L).map L.subtype = _
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTL]

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
