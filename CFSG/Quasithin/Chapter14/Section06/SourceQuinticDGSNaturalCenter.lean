module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticDGSFullKernel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.SmallSolvableS3ThreeCenter
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearCenterNatural
public import Stellmacher.OmegaOneCenterMap

/-!
# The exact original quintic commutator and cubic natural center

The general crossing-core index makes the quintic core move the original
plane.  The original flag bounds its displacement by the central line,
giving equality for the plane and its whole H-span, in both quotient rows.
The marked common Sylow, original center orders and centerlessness then
construct the natural action at the cubic endpoint.  The entire marking is
carried through the original completion inclusion, retaining both kernels.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.AmalgamGraph Representation
open Subgroup.CosetGeometry.RankTwo
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter12.Section08
open ChapterF.Source ChapterF.Source.DGS85
open CommutingThreeProfile.ReducedLayer
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem normal_four_minimal_of_centerless
    {A : Type*} [Group A] [Finite A] (Z : Subgroup A)
    (hc : Nat.card Z = 4) (hz : center A = ⊥)
    (N : Subgroup A) [N.Normal] (hNZ : N ≤ Z) : N = ⊥ ∨ N = Z := by
  have hd : Nat.card N ∣ 2^2 := by simpa only [hc,show (2:ℕ)^2=4 from rfl] using card_dvd_of_le hNZ
  obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  interval_cases k
  · exact Or.inl (card_eq_one.mp he)
  · left
    apply bot_unique
    rw [←hz]
    exact central_of_normal_card_two N he
  · exact Or.inr (eq_of_le_of_card_ge hNZ (by rw [hc,he]; decide))

omit [Finite G] in
private theorem natural_center_injective_image
    {A : Type u} [Group A] (f : A →* G) (hf : Function.Injective f)
    (L Z Q : Subgroup A) (hn : Noncommuting.HasNaturalCenter L Z Q) :
    Noncommuting.HasNaturalCenter (L.map f) (Z.map f) (Q.map f) := by
  obtain ⟨k,_,_,_,π,hπ,hker,⟨d⟩⟩ := hn
  let eL := L.equivMapOfInjective f hf
  let eZ := Z.equivMapOfInjective f hf
  let π' := π.comp eL.symm.toMonoidHom
  have hmem (R B : Subgroup A) (x : R) : f (x : A) ∈ B.map f ↔ (x : A) ∈ B := by
    constructor
    · rintro ⟨y,hy,he⟩
      exact hf he ▸ hy
    · exact mem_map_of_mem f
  refine ⟨k,inferInstance,inferInstance,inferInstance,π',hπ.comp eL.symm.surjective,?_,?_⟩
  · ext l
    obtain ⟨a,rfl⟩ := eL.surjective l
    change π (eL.symm (eL a)) = 1 ↔ f (a : A) ∈ Q.map f
    rw [eL.symm_apply_apply,←MonoidHom.mem_ker,hker,hmem]
    rfl
  · refine ⟨{
      section_le := map_mono d.section_le
      kernel_le := ?_
      normalized := (map_mono d.normalized).trans (Z.le_normalizer_map f)
      coordinates := d.coordinates.comp eZ.symm.toMonoidHom
      onto := d.onto.comp eZ.symm.surjective
      kernel_eq := ?_
      equivariant := ?_ }⟩
    · rw [Stellmacher.omegaOneCenterAmbient_map_injective f hf]
      exact map_mono d.kernel_le
    · ext z
      obtain ⟨a,rfl⟩ := eZ.surjective z
      change d.coordinates (eZ.symm (eZ a)) = 1 ↔
        f (a : A) ∈ Stellmacher.omegaOneCenterAmbient (L.map f)
      rw [eZ.symm_apply_apply,d.coordinates_eq_one_iff,
        Stellmacher.omegaOneCenterAmbient_map_injective f hf,hmem]
    · intro l z
      obtain ⟨a,rfl⟩ := eL.surjective l
      obtain ⟨v,rfl⟩ := eZ.surjective z
      change (d.coordinates (eZ.symm _)).toAdd =
        SL2NaturalOffenders.NoStrong.natural (π (eL.symm (eL a)))
          (d.coordinates (eZ.symm (eZ v))).toAdd
      rw [eL.symm_apply_apply,eZ.symm_apply_apply]
      convert d.equivariant a v using 1
      · congr 2
        apply eZ.injective
        rw [eZ.apply_symm_apply]
        apply Subtype.ext
        change f (a : A) * f (v : A) * (f (a : A))⁻¹ = f ((a : A) * v * (a : A)⁻¹)
        rw [map_mul,map_mul,map_inv]
      · rfl

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
include hG hempty hM hu hmany hcard e

/-- The original quintic core moves the plane and its whole span by exactly
the original central line, including the Sz(2) quotient branch. -/
theorem source_quintic_core_commutators
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    ⁅localModule T M,H.pCoreIn 2⁆ = centralInvolutions T ∧
      ⁅conjugateSpanBy (localModule T M) H,H.pCoreIn 2⁆ = centralInvolutions T := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow H (T.subtype hH.1.1.2)).trans_eq
      (map_subgroupOf_eq_of_le hH.1.1.2)
  obtain ⟨hXcore,_⟩ := Section02.source_residualSylow_quotient hG T hempty hM hu hmany hcard e
  have hcross := Section02.SolvableAmalgam.source_quintic_crossing_core_index
    hG T hempty hM hu hmany hcard e H hH hi
  have hnot : ¬ H.pCoreIn 2 ≤ X.pCoreIn 2 := by
    intro hh
    have hone : (H.pCoreIn 2 ⊓ X.pCoreIn 2).relIndex (H.pCoreIn 2) = 1 :=
      relIndex_eq_one.mpr (le_inf le_rfl hh)
    change (H.pCoreIn 2 ⊓ X.pCoreIn 2).relIndex (H.pCoreIn 2) = 2 at hcross
    omega
  obtain ⟨he,F,hp,_,_,hloc⟩ := Section02.source_lemma_14_2_6
    hG T hempty hM hu hmany hcard e
  let := he
  obtain ⟨_,hl,_,_,_,_⟩ := hloc H hH.1
  have hup : ⁅conjugateSpanBy (localModule T M) H,H.pCoreIn 2⁆ ≤ centralInvolutions T := by
    have hh := hl.commutator_U_core_le_point
    change ⁅conjugateSpanBy (rankTwoSeed T M) H,H.pCoreIn 2⁆ ≤ F.Vi 1 at hh
    simpa only [Section02.rankTwoSeed_eq_localModule,hp] using hh
  have hseed : ⁅localModule T M,H.pCoreIn 2⁆ ≤ centralInvolutions T :=
    (commutator_mono (le_conjugateSpanBy _ _) le_rfl).trans hup
  have hne : ⁅localModule T M,H.pCoreIn 2⁆ ≠ ⊥ := by
    intro hz
    apply hnot
    rw [hXcore]
    exact le_inf (hQT.trans le_sup_right)
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz))
  have hline : ⁅localModule T M,H.pCoreIn 2⁆ = centralInvolutions T := by
    apply eq_of_le_of_card_ge hseed
    rw [plane_centralInvolutions_card T M hM.1.2 hcard e]
    have hp := Nat.card_pos (α := (⁅localModule T M,H.pCoreIn 2⁆ : Subgroup G))
    have hn : Nat.card (⁅localModule T M,H.pCoreIn 2⁆ : Subgroup G) ≠ 1 :=
      fun hh => hne (card_eq_one.mp hh)
    omega
  exact ⟨hline,le_antisymm hup (hline ▸ commutator_mono (le_conjugateSpanBy _ _) le_rfl)⟩

set_option maxHeartbeats 800000 in
/-- The original cubic endpoint has its actual natural-center action, with
the full core kernel and the same reduced-to-original inclusion retained. -/
theorem source_quintic_cubic_natural_center
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let L : Fin 2 → Subgroup G := ![H,X]
    let F := Reduction.reducedFamily L (T : Subgroup G)
    center X = ⊥ ∧
      Noncommuting.HasNaturalCenter (star L (T : Subgroup G) true)
        (Z F (base F true)) (Q F (base F true)) ∧
      Noncommuting.HasNaturalCenter X (localModule T M) (X.pCoreIn 2) := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L : Fin 2 → Subgroup G := ![H,X]
  let J := Reduction.G₀ L (T : Subgroup G)
  let F := Reduction.reducedFamily L (T : Subgroup G)
  let A := star L (T : Subgroup G) true
  obtain ⟨hF,_,hS,_,hP,_,hmaps,_⟩ :=
    source_quintic_dgs_reduced_pair hG T hempty hM hu hmany hcard e H hH hi
  change HypothesisF11 L (T : Subgroup G) at hF
  change SuzukiContainment.reducedSylow L (T : Subgroup G) = T at hS
  change ∀ i, Reduction.P₀ L (T : Subgroup G) i = L i at hP
  have hpar : parabolic L (T : Subgroup G) 1 = X := by
    calc
      _ = Reduction.P₀ L (T : Subgroup G) 1 := by rw [Reduction.P₀_eq_source hF,hS]
      _ = X := hP 1
  have hstar : starredParabolic L (T : Subgroup G) 1 = X :=
    le_antisymm ((starredParabolic_le 1).trans_eq hpar)
      (local_le_starredParabolic (L := L) (S := (T : Subgroup G)) 1)
  have hAX : A = X.subgroupOf J := by change (starredParabolic L (T : Subgroup G) 1).subgroupOf J = _; rw [hstar]
  have hAF : A = F true := by
    change (starredParabolic L (T : Subgroup G) 1).subgroupOf J =
      (Reduction.P₀ L (T : Subgroup G) 1).subgroupOf J
    rw [hstar,hP]
    rfl
  have hXJ : X ≤ J := by
    rw [←hstar]
    exact star_le_completion 1
  let eA : A ≃* X := (MulEquiv.subgroupCongr hAX).trans (subgroupOfEquivOfLe hXJ)
  have hAmap : A.map J.subtype = X := by rw [hAX,map_subgroupOf_eq_of_le hXJ]
  have hm := Section02.SolvableAmalgam.source_index_five_models
    hG T hempty hM hu hmany hcard e H hH.1 hi
  obtain ⟨_,⟨eX⟩⟩ := Section02.source_residualSylow_quotient hG T hempty hM hu hmany hcard e
  obtain ⟨hb,a,beta,a',hc,hab,hd,hcomm,hdisp⟩ :=
    source_quintic_dgs_critical_three hG T hempty hM hu hmany hcard e H hH hi
  have hzX : center X = ⊥ := Assembly.small_solvable_s3_original_center_eq_bot hF hm ⟨eX⟩
    hpar hc hab hd (by change b F = 3 at hb; change 1 < b F; omega) hcomm hdisp
  have hzA : center A = ⊥ := by
    apply bot_unique
    intro z hz
    have hh := (MulEquivClass.apply_mem_center_iff eA).mpr hz
    change eA z ∈ center X at hh
    rw [hzX,mem_bot] at hh
    exact mem_bot.mpr (eA.injective (hh.trans (map_one eA).symm))
  obtain ⟨hZH,hZX⟩ := source_quintic_dgs_center_markings hG T hempty hM hu hmany hcard e H hH hi
  change (Z F (base F false)).map J.subtype = centralInvolutions T at hZH
  change (Z F (base F true)).map J.subtype = localModule T M at hZX
  have hfour : Nat.card (Z F (base F true)) = 4 := by
    rw [←card_map_of_injective J.subtype_injective,hZX]
    exact hcard
  have htwo : Nat.card (Z F (base F false)) = 2 := by
    rw [←card_map_of_injective J.subtype_injective,hZH]
    exact plane_centralInvolutions_card T M hM.1.2 hcard e
  have hZA : Z F (base F true) ≤ A := by
    rw [hAF]
    simpa only [stabilizer,Subgroup.CosetGeometry.stabilizer_base] using
      Z_le_stabilizer F (base F true)
  have hmin : ∀ N : Subgroup A, N.Normal → N ≤ (Z F (base F true)).subgroupOf A →
      N = ⊥ ∨ N = (Z F (base F true)).subgroupOf A := by
    intro N hn hNZ
    let := hn
    exact normal_four_minimal_of_centerless _
      ((Nat.card_congr (subgroupOfEquivOfLe hZA).toEquiv).trans hfour) hzA N hNZ
  have hzy : Z F (base F false) ≤ Z F (base F true) := by
    apply (Subgroup.map_le_map_iff_of_injective J.subtype_injective).mp
    rw [hZH,hZX]
    exact le_conjugateSpanBy _ _
  have hcy : ⁅V F (base F false) 1,Q F (base F false)⁆ = Z F (base F false) := by
    apply map_injective J.subtype_injective
    rw [map_commutator,
      (source_quintic_dgs_span_and_full_kernel hG T hempty hM hu hmany hcard e H hH hi).2.1,
      (hmaps false).2,hZH]
    exact (source_quintic_core_commutators hG T hempty hM hu hmany hcard e H hH hi).2
  obtain ⟨S,hS⟩ := (source_quintic_dgs_common_sylow hG T hempty hM hu hmany hcard e H hH hi).2.2 true
  have hsyl : ∃ R : Sylow 2 A, (R : Subgroup A).map A.subtype =
      Q F (base F false) ⊔ Q F (base F true) := by
    rw [hAF]
    exact ⟨S,hS.1⟩
  obtain ⟨R,hR⟩ := hsyl
  have hn : Noncommuting.HasNaturalCenter A (Z F (base F true)) (Q F (base F true)) :=
    source_linear_hasNaturalCenter hF true R hR
      (eX.trans SLTwoPermThree.sl2Two_equiv_perm_three.some.symm)
      (by simpa only [Nat.card_zmod,show (2:ℕ)^2=4 from rfl] using hfour)
      (by simpa only [Bool.not_true,Nat.card_zmod] using htwo)
      hzy hcy.le hmin hzA
  refine ⟨hzX,hn,?_⟩
  have ho := natural_center_injective_image J.subtype J.subtype_injective A
    (Z F (base F true)) (Q F (base F true)) hn
  rw [hAmap,hZX,(hmaps true).2] at ho
  exact ho

end CFSG.Quasithin.Chapter14.Section06
