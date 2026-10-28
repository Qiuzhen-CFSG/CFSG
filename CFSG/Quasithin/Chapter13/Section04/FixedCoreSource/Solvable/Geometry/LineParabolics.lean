module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.CoveredSelection
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.SymmetricThreePair
public import Theory.GroupTheory.SylowNormalizedResidual
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The original solvable line residue

The checked local product constructs H/O₂(H)≅S₃×S₃ and the normal
Thompson span I/O₂(I)≅S₃. The literal subgroups H∩M and IT are therefore
the two maximal overgroups of the original T in H. Their intersection is
T and they exhaust the maximal overgroups; no parabolic geometry is
assumed. Adjoining T also gives IT/O₂(IT)≅S₃ and O²(IT)=O²(I), with both
residuals mapped by their original inclusion homomorphisms.

The endpoint applies this to R₁ from Notation13.2.1 in both action-kernel
and covering cases. It supplies the first vertex of the13.4.7 amalgam and
the line residue of the later C₃ system. The earlier13.2.2,13.3.9 and
13.4.2–3 inputs retain discharge with qt-d-1341-fixed-core-source;
the genuine universal Structural1222 input remains universal.
Source: Aschbacher–Smith13.4.8–9, printed pp.905–906.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem centralizer_rankTwo_of_source_product
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcore : IsPGroup 2 (centralCore L)) (z : V)
    (hz : z.val ∉ centralizer (L : Set G))
    (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (R : Subgroup G) (hRT : R ≤ T)
    (hquot :
      let I := conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z.val} : Set G))
      Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)))
    (hprod :
      let H := centralizer ({z.val} : Set G)
      H = firstCentralizerResidual L z.val ⊔
        conjugateSpanBy (elementaryAbelianMaxJ R) H ⊔ (T : Subgroup G))
    (hinter : centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G) =
      firstCentralizerResidual L z.val ⊔ (T : Subgroup G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G)) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
    Quasithin.I5.RankTwoParabolics H ((T : Subgroup G).subgroupOf H)
      ((normalizer (L : Set G)).subgroupOf H) ((I ⊔ (T : Subgroup G)).subgroupOf H) := by
  let H := centralizer ({z.val} : Set G)
  let K := H ⊓ normalizer (L : Set G)
  let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hzT
  have hIH : I ≤ H := conjugateSpanBy_le_self
    ((sSup_le fun _ hA => hA.1).trans (hRT.trans hTH))
  have hKH : K ≤ H := inf_le_left
  let N := I.subgroupOf H
  let A := K.subgroupOf H
  let S := T.subtype hTH
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hIH).mpr
    (le_normalizer_conjugateSpanBy _ _)
  have hSA : (S : Subgroup H) ≤ A := by
    intro t ht
    change t.val ∈ K
    rw [show K = firstCentralizerResidual L z.val ⊔ (T : Subgroup G) from hinter]
    exact (show (T : Subgroup G) ≤ firstCentralizerResidual L z.val ⊔ (T : Subgroup G)
      from le_sup_right) ht
  have hA : A ≠ ⊤ := by
    intro he
    apply hout
    intro a ha
    exact (show (⟨a,ha⟩ : H) ∈ A from he ▸ mem_top _).2
  have hgen : N ⊔ A = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hIH,map_subgroupOf_eq_of_le hKH,
      ← MonoidHom.range_eq_map,range_subtype]
    rw [show K = firstCentralizerResidual L z.val ⊔ (T : Subgroup G) from hinter,
      ← sup_assoc,sup_comm I]
    exact hprod.symm
  obtain ⟨eI⟩ := hquot
  let eN := subgroupOfEquivOfLe hIH
  obtain ⟨eK⟩ := normalizer_centralizer_quotient D m hcore z hz hinter
  let eA := subgroupOfEquivOfLe hKH
  obtain ⟨eH⟩ := centralizer_pair_quotient_of_source_product D m hcore z hz hzT
    R hRT ⟨eI⟩ hprod hinter hout
  have hp := Quasithin.I5.RankTwoParabolics.of_normal_symmetricThree_supplement eH N A
    ((QuotientGroup.congr _ _ eN (pCore_map_iso 2 eN)).trans eI)
    ((QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).trans eK) S hSA hA hgen
  have hjoin : (I ⊔ (T : Subgroup G)).subgroupOf H = N ⊔ (S : Subgroup H) := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hIH,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTH,map_subgroupOf_eq_of_le (sup_le hIH hTH)]
  change Quasithin.I5.RankTwoParabolics H (S : Subgroup H)
    ((normalizer (L : Set G)).subgroupOf H) ((I ⊔ (T : Subgroup G)).subgroupOf H)
  rw [hjoin]
  simpa only [A,K,inf_subgroupOf_left] using hp

/-- Adjoining the original Sylow subgroup preserves the Thompson span's S₃ quotient. -/
theorem thompson_sylow_join_quotient
    {z : G} (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (R : Subgroup G) (hRT : R ≤ T)
    (hquot :
      let I := conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z} : Set G))
      Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3))) :
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z} : Set G))
    let P := I ⊔ (T : Subgroup G)
    Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) := by
  let H := centralizer ({z} : Set G)
  let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
  let P := I ⊔ (T : Subgroup G)
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
  have hIH : I ≤ H := conjugateSpanBy_le_self
    ((sSup_le fun _ hA => hA.1).trans (hRT.trans hTH))
  have hIP : I ≤ P := le_sup_left
  have hTP : (T : Subgroup G) ≤ P := le_sup_right
  let N := I.subgroupOf P
  let S := (T : Subgroup G).subgroupOf P
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hIP).mpr
    ((sup_le hIH hTH).trans (le_normalizer_conjugateSpanBy _ _))
  obtain ⟨eI⟩ := hquot
  let eN := subgroupOfEquivOfLe hIP
  have hgen : N ⊔ S = ⊤ := by
    apply map_injective P.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hIP,map_subgroupOf_eq_of_le hTP,
      ← MonoidHom.range_eq_map,range_subtype]
  exact NormalSymmetricThree.quotient_symmetricThree_of_normal_twoGroup_supplement N S
    ((QuotientGroup.congr _ _ eN (pCore_map_iso 2 eN)).trans eI)
    T.isPGroup'.comap_subtype hgen

theorem original_R1_line_parabolics
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcase : normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G) ∨ ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hVJ : V ≤ elementaryAbelianMaxJ (firstFlagCore h structural D m))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1342 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
    let P := I ⊔ (T : Subgroup G)
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      Quasithin.I5.RankTwoParabolics H ((T : Subgroup G).subgroupOf H)
        ((normalizer (L : Set G)).subgroupOf H) (P.subgroupOf H) ∧
      Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
      P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) := by
  obtain ⟨ordinary,_,hI,_,hprod,hinter,_,hstar,_⟩ := centralizer_pair_quotient_of_original_R1
    h₀ h structural D m hcase z hz hzL hVJ hout hfusion h1339 hsolv hindex h1342
  obtain ⟨eL⟩ := ordinary
  have hcore : IsPGroup 2 (centralCore L) := by
    rw [centralCore_eq_twoCore_of_ordinary eL]
    exact pCore_isPGroup
  have hRT := (firstFlagCore_local_data h structural D m z hz hzL).1
  exact ⟨⟨eL⟩,centralizer_rankTwo_of_source_product D m hcore z hzL hz
    (firstFlagCore h structural D m) hRT hI hprod hinter hout,
    thompson_sylow_join_quotient hz (firstFlagCore h structural D m) hRT hI,hstar⟩

/-- The two-residual of IT is the literal embedded two-residual of I. -/
theorem thompson_sylow_join_residual
    {z : G} (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (R : Subgroup G) (hRT : R ≤ T) :
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z} : Set G))
    let P := I ⊔ (T : Subgroup G)
    (pResidual 2 P).map P.subtype = (pResidual 2 I).map I.subtype := by
  let H := centralizer ({z} : Set G)
  let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
  let P := I ⊔ (T : Subgroup G)
  let K := (pResidual 2 I).map I.subtype
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
  have hIH : I ≤ H := conjugateSpanBy_le_self
    ((sSup_le fun _ hA => hA.1).trans (hRT.trans hTH))
  have hIN : H ≤ normalizer (I : Set G) := le_normalizer_conjugateSpanBy _ _
  have hKP : K ≤ P := (map_subtype_le _).trans le_sup_left
  have hTP : (T : Subgroup G) ≤ P := le_sup_right
  have hPN : P ≤ normalizer (K : Set G) := ((sup_le hIH hTH).trans hIN).trans
    (normalizer_le_normalizer_characteristic_image I (pResidual 2 I))
  let W := K.subgroupOf P
  let S := (T : Subgroup G).subgroupOf P
  let : W.Normal := (normal_subgroupOf_iff_le_normalizer hKP).mpr hPN
  have hp : IsPPerfect 2 W := (isPPerfect_embedded_pResidual 2 I).of_surjective
    (subgroupOfEquivOfLe hKP).symm.toMonoidHom (subgroupOfEquivOfLe hKP).symm.surjective
  have hgen : W ⊔ S = ⊤ := by
    apply map_injective P.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hKP,map_subgroupOf_eq_of_le hTP,
      ← MonoidHom.range_eq_map,range_subtype]
    apply le_antisymm (sup_le hKP hTP)
    exact sup_le (le_embedded_pResidual_sup_sylow_of_normalizes T I (hTH.trans hIN)) le_sup_right
  have hr := pResidual_eq_of_isPPerfect_sup W S hp T.isPGroup'.comap_subtype hgen
  change (pResidual 2 P).map P.subtype = K
  rw [hr,map_subgroupOf_eq_of_le hKP]


end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
