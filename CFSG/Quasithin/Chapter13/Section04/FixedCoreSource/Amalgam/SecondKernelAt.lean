module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondKernel
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondNoncommutingAt
public import Theory.GroupTheory.PResidual.Restriction

/-!
This guarded version uses earlier structure only at the original G,T.
All literal residuals, quotient maps and original source hypotheses are retained.

# The full action kernel of the actual second amalgam

The centralizer of the second omega span fixes both original seed lines.
Using the genuine source identity N_G(L)=LT, it therefore lies in the
first flag parabolic P=L₁T. As a normal subgroup of the second join, it
either lies in O₂(P) or contains O²(P)=L₁. In the latter case residual
recovery makes L₁ normal in the whole join, contradicting the proved
failure of Y₂ to normalize L₁. Thus the kernel is a normal two-group;
reducedness gives the reverse containment and the exact equality O₂(Y).

Both ambient and intrinsic kernel equalities refer to the same original
omega span. The earlier source equality N_G(L)=LT remains explicit. No
second-amalgam kernel or residual-classification callback is assumed.
Source: Aschbacher--Smith 13.4.7(3), printed p.903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Solvable
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

theorem original_plane_second_action_kernel_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcentral : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂))
    (hs : Group.IsSolvable (A ⊔ B : Subgroup G))
    (hcomm : ¬ ⁅(pResidual 2 A).map A.subtype,(pResidual 2 B).map B.subtype⁆ ≤
      centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) : Set G))
    (Wplane : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hWplane : Module.finrank (ZMod 2) Wplane = 2)
    (hTplane : (T : Subgroup G) ≤ normalizer (m.naturalPreimage Wplane : Set G))
    (hBplane : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage Wplane : Set G))
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G)) :
    let X := A ⊔ B
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let Y₂ := (MarkedCubicRecognition.centralThreeResidual X).map X.subtype
    let P := firstFlagNormalizer T L V
    let Y := P ⊔ (Y₂ ⊔ (T : Subgroup G))
    let U := conjugateSpanBy Z Y
    Y ⊓ centralizer (U : Set G) = Y.pCoreIn 2 ∧
      centralizer (U.subgroupOf Y : Set Y) = pCore 2 Y := by
  let X := A ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let Y₂ := (MarkedCubicRecognition.centralThreeResidual X).map X.subtype
  let P := firstFlagNormalizer T L V
  let Q := Y₂ ⊔ (T : Subgroup G)
  let Y := P ⊔ Q
  let U := conjugateSpanBy Z Y
  let L₁ := (pResidual 2 P).map P.subtype
  have hTP : (T : Subgroup G) ≤ P := sylow_le_firstFlagNormalizer
  have hTY : (T : Subgroup G) ≤ Y := hTP.trans le_sup_left
  have hUY : U ≤ Y := conjugateSpanBy_le
    (fun z hz => hTY ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) Y.le_normalizer
  obtain ⟨_,_,_,_,_,_,hg,_,hred,_,_,_⟩ :=
    original_plane_second_amalgam_at h₀ h structural D m hTA hTB eA eB hne
      hindexL hindexA hindexB hcentral hs hcomm Wplane hWplane hTplane hBplane
  have hnot := (original_plane_second_noncommuting_at h₀ h structural D m
    hTA hTB eA eB hne hindexL hindexA hindexB hcentral hs hcomm
    Wplane hWplane hTplane hBplane).2.1
  obtain ⟨_,hseed,_,_,_,_,_,hZL⟩ := original_pair_source_seed_at h structural D m
    hTA hTB eA eB hne hindexL hindexA hindexB hcentral
  have hex : ∃ z ∈ Z, z ∉ centralizer (L : Set G) := by
    by_contra hh
    have hz : Z ≤ centralizer (L : Set G) := by
      intro z hz
      by_contra hn
      exact hh ⟨z,hz,hn⟩
    rw [inf_eq_left.mpr hz,relIndex_self] at hindexL
    omega
  obtain ⟨z,hz,hzL⟩ := hex
  let v : V := ⟨z,(hseed.le hz).1⟩
  let := hred.normal
  let N := centralizer (U.subgroupOf Y : Set Y)
  let K := N.map Y.subtype
  have hKeq : K = Y ⊓ centralizer (U : Set G) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.property,fun u hu => congrArg Subtype.val (hy ⟨u,hUY hu⟩ hu)⟩
    · rintro ⟨hx,hc⟩
      exact ⟨⟨x,hx⟩,fun u hu => Subtype.ext (hc u.val hu),rfl⟩
  have hYK : Y ≤ normalizer (K : Set G) := by
    have hh := N.le_normalizer_map Y.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  have hKZ : K ≤ centralizer (Z : Set G) := by
    rw [hKeq]
    exact inf_le_right.trans (centralizer_le (le_conjugateSpanBy Z Y))
  have hKM : K ≤ normalizer (L : Set G) := by
    rw [←fixed_centralizer_eq_normalizer_at h structural D m]
    change K ≤ centralizer ((V ⊓ centralizer (L : Set G) : Subgroup G) : Set G)
    rw [←hZL]
    exact hKZ.trans (centralizer_le inf_le_left)
  have hKP : K ≤ P := by
    change K ≤ (L ⊔ (T : Subgroup G)) ⊓ normalizer
      (V ⊓ omegaOneCenterAmbient (T : Subgroup G) : Set G)
    rw [first_flag_normalizer_eq_centralizer_at h structural D m v hz hzL]
    exact le_inf (hKM.trans_eq hM)
      (hKZ.trans (centralizer_le (Set.singleton_subset_iff.mpr hz)))
  have hnotNK : ¬ L₁ ≤ K := by
    intro hh
    have hR := embedded_pResidual_eq_of_le_of_residual_le 2 hKP hh
    have hn := hYK.trans (normalizer_le_normalizer_characteristic_image K (pResidual 2 K))
    rw [hR] at hn
    exact hnot (le_sup_left.trans (le_sup_right.trans hn))
  have hnotN : ¬ (pResidual 2 (P.subgroupOf Y)).map (P.subgroupOf Y).subtype ≤ N := by
    intro hh
    have hm := map_mono (f := Y.subtype) hh
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le le_sup_left] at hm
    exact hnotNK hm
  have hcore := (hg.left_subnormal_core_iff_not_residual_le N
    (inferInstance : N.Normal).isSubnormal).mpr hnotN
  have hNP : N ≤ P.subgroupOf Y := by
    intro n hn
    exact hKP (mem_map_of_mem Y.subtype hn)
  rw [inf_eq_right.mpr hNP] at hcore
  have hpN : IsPGroup 2 N :=
    ((pCore_isPGroup (p := 2) (G := P.subgroupOf Y)).map
      (P.subgroupOf Y).subtype).to_le hcore
  have hN : N = pCore 2 Y := le_antisymm (le_sSup ⟨inferInstance,hpN⟩)
    (le_centralizer_iff.mp hred.le_centralizer_pCore)
  refine ⟨?_,hN⟩
  rw [←hKeq]
  exact congrArg (Subgroup.map Y.subtype) hN

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
