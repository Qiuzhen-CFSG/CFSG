module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.PlanePairAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.Geometry.LineParabolics
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.CoveredPlacement
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.CoveredSelection
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.FirstFlagCore
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.Amalgam
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.LineParabolics
public import Theory.GroupTheory.NormalCharacteristicTwoCore

/-!
# Relative centralizers and exclusion of the product amalgam: structure at the original group

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
solvable-centralizer recognition on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907;
see the original `Solvable/Geometry/Amalgam` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem original_R1_amalgam_centralizers_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcase : normalizer (ChapterB.baumann (firstFlagCore_at h structural D m) : Set G) ≤
      normalizer (L : Set G) ∨ ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hVJ : V ≤ elementaryAbelianMaxJ (firstFlagCore_at h structural D m))
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
      (normalizer (L : Set G)).subtype = L)
    (B : Subgroup G) (hBM : B ≤ normalizer (L : Set G))
    (hBmax : IsCoatom (B.subgroupOf (normalizer (L : Set G))))
    (hgen : (centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G)) ⊔ B =
      normalizer (L : Set G))
    (hfixed : centralizer ((omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer ((pResidual 2 B).map B.subtype : Set G) : Subgroup G) : Set G) =
        normalizer (L : Set G)) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore_at h structural D m)) H
    let P := I ⊔ (T : Subgroup G)
    let X := P ⊔ B
    X ∈ Chapter1.H G →
    let K₁ := (pResidual 2 P).map P.subtype
    let K₂ := (pResidual 2 B).map B.subtype
    let C₁ := X ⊓ centralizer ((omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (K₁ : Set G) : Subgroup G) : Set G)
    let C₂ := X ⊓ centralizer ((omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (K₂ : Set G) : Subgroup G) : Set G)
    X ⊓ normalizer (L : Set G) = B ∧ X ⊓ H = P ∧
      C₁ = P ∧ C₂ = B ∧ (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
      (primeToResidual 3 C₁).map C₁.subtype = K₁ := by
  dsimp only
  intro hX
  obtain ⟨_,hp,⟨eP⟩,hstar⟩ := original_R1_line_parabolics_at
    h₀ h structural D m hcase z hz hzL hVJ hout hfusion h1339 hsolv hindex h1342
  have hTH := original_sylow_le_centralizer hz
  have hRT := (firstFlagCore_local_data_at h structural D m z hz hzL).1
  have hIH : conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore_at h structural D m))
      (centralizer ({z.val} : Set G)) ≤ centralizer ({z.val} : Set G) := conjugateSpanBy_le_self
    ((sSup_le fun _ hA => hA.1).trans (hRT.trans hTH))
  exact LocalGeometry.amalgam_residual_centralizers_at h structural z.val hz _ B _
    le_sup_right (sup_le hIH hTH) hp.right_maximal hstar.1.2 eP
    hBM hBmax hgen hfixed hX le_sup_left le_sup_right

private theorem not_two_group_of_symmetricThree_quotient_at
    {A : Type*} [Group A] [Finite A]
    (e : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) : ¬ IsPGroup 2 A := by
  intro hp
  obtain ⟨n,hn⟩ := ((hp.to_quotient (pCore 2 A)).of_equiv e).exists_card_eq
  have hd : 3 ∣ Nat.card (Equiv.Perm (Fin 3)) := by
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
  rw [hn] at hd
  exact (by decide : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

/-- The source product alternative13.4.7(1i) is impossible: its residual
commutator bound would make M and H normalize the same nontrivial two-core. -/
theorem thompson_residual_not_commuting_with_inside_residual_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {z : G} (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (R : Subgroup G) (hRT : R ≤ T)
    (hquot :
      let I := conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z} : Set G))
      Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)))
    (hout : ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hTB : (T : Subgroup G) ≤ B)
    (hgen : (centralizer ({z} : Set G) ⊓ normalizer (L : Set G)) ⊔ B =
      normalizer (L : Set G)) :
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z} : Set G))
    let K := (pResidual 2 I).map I.subtype
    ¬ ⁅K,(pResidual 2 B).map B.subtype⁆ ≤ K.pCoreIn 2 := by
  let H := centralizer ({z} : Set G)
  let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
  let K := (pResidual 2 I).map I.subtype
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
  have hIH : I ≤ H := conjugateSpanBy_le_self
    ((sSup_le fun _ hA => hA.1).trans (hRT.trans hTH))
  have hKI : K ≤ I := map_subtype_le _
  have hKH : K ≤ H := hKI.trans hIH
  have hnH : H ≤ normalizer (K : Set G) :=
    (le_normalizer_conjugateSpanBy _ _).trans
      (normalizer_le_normalizer_characteristic_image I (pResidual 2 I))
  have hKne : K ≠ ⊥ := by
    intro hb
    have hr : pResidual 2 I = ⊥ := (map_eq_bot_iff_of_injective _ I.subtype_injective).mp hb
    have hp := isPGroup_quotient_pResidual (G := I) 2
    obtain ⟨eI⟩ := hquot
    exact not_two_group_of_symmetricThree_quotient_at eI (hp.of_equiv
      ((QuotientGroup.quotientMulEquivOfEq hr).trans QuotientGroup.quotientBot))
  let N := K.subgroupOf H
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hKH).mpr hnH
  have hn : N ≠ ⊥ := by
    intro hb
    apply hKne
    change K.subgroupOf H = ⊥ at hb
    rw [←map_subgroupOf_eq_of_le hKH,hb,Subgroup.map_bot]
  have hHchar : centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (h₀.qtke.evenCharacteristic T)
      (centralizer_mem_HOver hz hz1))
  have hcore : K.pCoreIn 2 ≠ ⊥ := by
    intro hb
    have hk : pCore 2 K = ⊥ := (map_eq_bot_iff_of_injective _ K.subtype_injective).mp hb
    let e := subgroupOfEquivOfLe hKH
    apply twoCore_ne_bot_of_normal_of_centralizer_le N hHchar hn
    apply (map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective).mp
    rw [pCore_map_iso 2 e,hk]
  change ¬ ⁅K,(pResidual 2 B).map B.subtype⁆ ≤ K.pCoreIn 2
  intro hcomm
  have hBN : (pResidual 2 B).map B.subtype ≤ normalizer (K : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hcomm.trans (pCoreIn_le 2 K))
  have hBT : B ≤ normalizer (K : Set G) := by
    have hb := congrArg (map B.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTB))
    rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTB,
      ← MonoidHom.range_eq_map,range_subtype] at hb
    rw [←hb]
    exact sup_le hBN (hTH.trans hnH)
  have hMN : normalizer (L : Set G) ≤ normalizer (K : Set G) := by
    rw [←hgen]
    exact sup_le (inf_le_left.trans hnH) hBT
  have hchar := normalizer_le_normalizer_characteristic_image K (pCore 2 K)
  have hmax := (h.source_normalizer_maximal_unique_at structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).1
  have hNM : normalizer (K.pCoreIn 2 : Set G) ≤ normalizer (L : Set G) :=
    hmax.2 ⟨K.pCoreIn 2,hcore,isPGroup_pCoreIn 2 K,rfl⟩ (hMN.trans hchar)
  exact hout (hnH.trans (hchar.trans hNM))

theorem original_R1_excludes_amalgam_product_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcase : normalizer (ChapterB.baumann (firstFlagCore_at h structural D m) : Set G) ≤
      normalizer (L : Set G) ∨ ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hVJ : V ≤ elementaryAbelianMaxJ (firstFlagCore_at h structural D m))
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
      (normalizer (L : Set G)).subtype = L)
    (B : Subgroup G) (hTB : (T : Subgroup G) ≤ B)
    (hgen : (centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G)) ⊔ B =
      normalizer (L : Set G)) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore_at h structural D m)) H
    let P := I ⊔ (T : Subgroup G)
    let K₁ := (pResidual 2 P).map P.subtype
    let K₂ := (pResidual 2 B).map B.subtype
    ¬ ⁅K₁,K₂⁆ ≤ K₁.pCoreIn 2 := by
  obtain ⟨_,_,hI,_,_,_,_,_,_⟩ := centralizer_pair_quotient_of_original_R1_at
    h₀ h structural D m hcase z hz hzL hVJ hout hfusion h1339 hsolv hindex h1342
  have hRT := (firstFlagCore_local_data_at h structural D m z hz hzL).1
  dsimp only
  rw [thompson_sylow_join_residual hz (firstFlagCore_at h structural D m) hRT]
  exact thompson_residual_not_commuting_with_inside_residual_at h₀ h structural hz
    (fun he => hzL (he ▸ one_mem _)) (firstFlagCore_at h structural D m) hRT hI hout B hTB hgen

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
