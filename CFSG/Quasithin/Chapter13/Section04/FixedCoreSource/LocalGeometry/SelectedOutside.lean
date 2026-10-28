module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableRowReduction
public import CFSG.Quasithin.Chapter13.Section03.PointResidualImage.PrimeDivisors
public import Theory.GroupTheory.ElementaryEightFixedPointOrder24
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# Selected-component control of the original normalizer residual

At the actual component K of an escaping nonsolvable point centralizer,
apply source 13.3.8 with outside overgroup M = N_G(L) and subgroup
R = O²(C_M(V)). Normality is retained in M, not asserted in C_G(z).
The selected linear-three and ordinary-six geometries give the full omega
center inside the original V. Hence R fixes a nonzero omega vector in K's
own chosen module. The elementary-eight and natural A6 point actions have
{2,3}-images. Their prime-set residual centralizes K/O2(K); characteristic
two and the core-free join force it to vanish. A selected augmentation
module uses the already proved augmentation outside theorem instead.

The final theorem constructs K, its guarded Hypothesis1223, its own module
and quotient marking, and the precise outside application. No root
augmentation marking is transferred to K. OrdinaryNormalizerRecognition
uses this prime-set bound to kill R and discharge the normalizer supplement.
Earlier structural, module, 13.3.2/16 and large-distance inputs remain explicit.
Source: Aschbacher--Smith 13.3.8 and 13.4.6(4), printed pp.886--887,898.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Nonsolvable
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {K U H Y : Subgroup G}

private theorem selected_outside_core_free
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hH : H ∈ Chapter1.HOutside G (T : Set G) (normalizer (K : Set G) : Set G)) :
    pCore 2 (K ⊔ H : Subgroup G) = ⊥ := by
  by_contra hne
  let J := K ⊔ H
  have hQne : J.pCoreIn 2 ≠ ⊥ := by
    intro he
    exact hne (((pCore 2 J).map_eq_bot_iff_of_injective J.subtype_injective).mp he)
  have hn : J ≤ normalizer (J.pCoreIn 2 : Set G) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hu := (h.source_normalizer_maximal_unique_at structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2
  have hb : J ≤ normalizer (K : Set G) := hn.trans
    (normalizer_le_of_unique_maximalTwoLocal hu (isPGroup_pCoreIn 2 J) hQne
      ((sup_le le_sup_left (show (T : Subgroup G) ≤ J from
        fun x hx => mem_sup_right (hH.1.2 hx))).trans hn))
  exact hH.2 (fun x hx => hb (mem_sup_right hx))

private theorem chosen_nonzero_omega
    (D : ChosenModule T K U) (hTU : (T : Subgroup G) ≤ normalizer (U : Set G)) :
    ∃ w : U, w ≠ 1 ∧ w.val ∈ omegaOneCenterAmbient (T : Subgroup G) := by
  let A := U.subgroupOf (T : Subgroup G)
  let : A.Normal := normal_subgroupOf_of_le_normalizer hTU
  have hA : A ≠ ⊥ := by
    intro he
    have hh := map_subgroupOf_eq_of_le D.le_sylow
    change A.map (T : Subgroup G).subtype = U at hh
    rw [he,Subgroup.map_bot] at hh
    exact D.ne_bot hh.symm
  let : Nontrivial A := (nontrivial_iff_ne_bot A).mpr hA
  let : Fact (IsPGroup 2 T) := ⟨T.isPGroup'⟩
  obtain ⟨a,hane,hac⟩ := exists_nontrivial_center_mem_normal (N := A) (p := 2)
  let w : U := ⟨a.val.val,a.property⟩
  have hw : w ≠ 1 := by
    intro he
    apply hane
    exact Subtype.ext (Subtype.ext (show a.val.val = 1 from
      congrArg (fun x : U => x.val) he))
  refine ⟨w,hw,?_⟩
  rw [mem_omegaOneCenterAmbient_iff]
  refine ⟨D.le_sylow w.property,?_,?_⟩
  · let := D.elementary
    exact elemPow_eq_one_of_isElementaryAbelian w.val w.property
  · intro t ht
    have hh := mem_center_iff.mp hac (⟨t,ht⟩ : T)
    exact congrArg (fun x : T => x.val) hh

private theorem twoThree_of_card_dvd_twenty_four {A : Type*} [Group A] [Finite A]
    (hc : Nat.card A ∣ 24) : IsPiGroup twoThreePrimes A := by
  rw [IsPiGroup_iff]
  intro p hd
  change p.val = 2 ∨ p.val = 3
  have hd' : p.val ∣ 2^3*3 := hd.trans hc
  rcases p.property.dvd_mul.mp hd' with hd | hd
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
      (p.property.dvd_of_dvd_pow hd) |>.resolve_left p.property.ne_one)
  · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp hd |>.resolve_left p.property.ne_one)

/-- The actual chosen elementary eight detects the prime-set residual of an
outside normal subgroup fixing its nonzero omega point. -/
theorem selected_eight_outside_twoThree_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (hs : IsSimpleGroup (K ⧸ pCore 2 K)) (hcard : Nat.card U = 8)
    (hH : H ∈ Chapter1.HOutside G (T : Set G) (normalizer (K : Set G) : Set G))
    (hYH : Y ≤ H) (hnY : H ≤ normalizer (Y : Set G))
    (hYN : Y ≤ normalizer (K : Set G))
    (hcZ : Y ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    IsPiGroup twoThreePrimes Y := by
  let := D.elementary
  obtain ⟨w,hw,hwZ⟩ := chosen_nonzero_omega D ((structural K h).2.2 U D).1
  have hcw : Y ≤ centralizer ({w.val} : Set G) :=
    hcZ.trans (centralizer_le (Set.singleton_subset_iff.mpr hwZ))
  have hYU : Y ≤ normalizer (U : Set G) :=
    h.source_point_normalizes_chosen_at structural D w.property
      (fun he => hw (Subtype.ext he)) (le_inf hYN hcw)
  let f : Y →* MulAut U := U.normalizerMonoidHom.comp (inclusion hYU)
  have hfix : ∀ a : f.range, (a : MulAut U) w = w := by
    rintro ⟨a,y,rfl⟩
    apply Subtype.ext
    change y.val * w.val * y.val⁻¹ = w.val
    rw [mem_centralizer_singleton_iff.mp (hcw y.property),mul_inv_cancel_right]
  have hpi := twoThree_of_card_dvd_twenty_four
    (elementaryEight_fixed_point_image_card_dvd_twentyfour hcard w hw f.range hfix)
  have hr := piResidual_le_ker_of_range twoThreePrimes f hpi
  let N := (piResidual twoThreePrimes Y).map Y.subtype
  have hNC : N ≤ centralizer (U : Set G) := by
    rintro _ ⟨y,hy,rfl⟩
    have hh : inclusion hYU y ∈ U.normalizerMonoidHom.ker := hr hy
    rw [normalizerMonoidHom_ker] at hh
    exact hh
  have hnC : K ≤ normalizer (centralizer (U : Set G) : Set G) :=
    D.normalizes.trans (normalizer_le_normalizer_centralizer U)
  have hcomm : ⁅K,N⁆ ≤ K ⊓ centralizer (U : Set G) := by
    refine le_inf (le_normalizer_iff_commutator_le_left.mp
      ((map_subtype_le _).trans hYN)) ?_
    rw [commutator_comm]
    exact (commutator_mono hNC le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hnC)
  have hk : K ⊓ centralizer (U : Set G) = K.pCoreIn 2 := by
    rw [pCoreIn,←D.centralizer_eq_core_of_simple hs]
    apply le_antisymm
    · intro k hk
      exact ⟨⟨k,hk.1⟩,hk.2,rfl⟩
    · rintro _ ⟨k,hk,rfl⟩
      exact ⟨k.property,hk⟩
  have hQH : K.pCoreIn 2 ≤ H := by
    have hh := pCoreIn_le_sylow (K ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] at hh
    exact ((pCoreIn_mono_of_normalizes (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le K.le_normalizer ((structural K h).1))).trans hh).trans hH.1.2
  exact twoThree_of_residual_commutator K H Y (K.pCoreIn 2) hYH hnY hQH
    (isPGroup_pCoreIn 2 K)
    (K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
    (hcomm.trans_eq hk) (selected_outside_core_free h structural hH)
    ((Chapter1.mem_He_iff).mp
      (Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T) hH.1))

/-- Source 13.3.8 at a selected ordinary A6 component: its actual module may
be natural or five-dimensional, and both cases retain the full normalizer. -/
theorem selected_six_outside_twoThree_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) {z : G} (mark : ComponentModuleAt D z)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hH : H ∈ Chapter1.HOutside G (T : Set G) (normalizer (K : Set G) : Set G))
    (hYH : Y ≤ H) (hnY : H ≤ normalizer (Y : Set G))
    (hp : IsPPerfect 2 Y) (hYN : Y ≤ normalizer (K : Set G))
    (hcZ : Y ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    IsPiGroup twoThreePrimes Y := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hs : IsSimpleGroup (K ⧸ pCore 2 K) := eK.isSimpleGroup
  cases mark with
  | linearThree q e he =>
    apply selected_eight_outside_twoThree_at h structural D hs ?_ hH hYH hnY hYN hcZ
    rw [Nat.card_congr e.toEquiv]
    change Nat.card BinaryLinearThree.Vector = 8
    simp [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
  | coreSix m _ =>
    exact augmentation_outside_twoThree_at h structural D m H hH Y hYH hnY hp hYN
  | naturalSix q e he =>
    let := D.elementary
    let N := normalizer (K : Set G)
    let P := N ⊓ normalizer (U : Set G)
    have hKP : K ≤ P := le_inf K.le_normalizer D.normalizes
    obtain ⟨w,hw,hwZ⟩ := chosen_nonzero_omega D ((structural K h).2.2 U D).1
    have hcw : Y ≤ centralizer ({w.val} : Set G) :=
      hcZ.trans (centralizer_le (Set.singleton_subset_iff.mpr hwZ))
    have hYU : Y ≤ normalizer (U : Set G) :=
      h.source_point_normalizes_chosen_at structural D w.property
        (fun he => hw (Subtype.ext he)) (le_inf hYN hcw)
    let α : K →* alternatingGroup (Fin 6) :=
      q.toMonoidHom.comp (QuotientGroup.mk' (centralCore K))
    let E : Additive U ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6) :=
      LinearEquiv.ofBijective (e.toMonoidHom.toAdditiveLeft.toZModLinearMap 2) e.bijective
    have hE (k : K) (v : Additive U) :
        E (Section08.TransvectionQuotients.FiveSeed.BarMarking.conjugationRepresentation P U inf_le_right
          (inclusion hKP k) v) =
          BinaryPermutation.alternatingNaturalRepresentation (Fin 6) (α k) (E v) := he k v.toMul
    have hQH : K.pCoreIn 2 ≤ H := by
      have hh := pCoreIn_le_sylow (K ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
      rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] at hh
      exact ((pCoreIn_mono_of_normalizes
        (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)
        (sup_le K.le_normalizer ((structural K h).1))).trans hh).trans hH.1.2
    exact Section03.PointResidualImage.twoThree_of_natural_point N K U H Y hKP inf_le_left
      α (q.surjective.comp (QuotientGroup.mk'_surjective _)) eK E hE (le_inf hYN hYU)
      hYH hnY hQH (selected_outside_core_free h structural hH)
      ((Chapter1.mem_He_iff).mp
        (Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T) hH.1))
      (Additive.ofMul w) hw hcw

open Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
variable {L V : Subgroup G}

/-- The literal residual O²(C_M(V)) in 13.4.6(4) is a {2,3}-group.
The outside overgroup is M itself; relative normality is not transferred to C_G(z).
All selected components and their module markings are constructed. -/
theorem nonsolvable_normalizer_residual_twoThree
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hnonsolv : ¬ Group.IsSolvable (centralizer ({z.val} : Set G))) :
    IsPiGroup twoThreePrimes (normalizerActionResidual L V) := by
  obtain ⟨K,hK,hfK,_,hHN,_,hKM,hLK⟩ := augmentation_exists_escaping_component_at
    h₀ h (structural G T) m h1332 hzT (fun he => hzL (he ▸ one_mem _)) hout hnonsolv
  have hindex := original_omega_fixed_index_at h₀ h (structural G T) D m earlier
  have hstar := Section03.Noncentrality.source1332_faithful_maximal h₀.qtke T h1332 hfK
  have hK12 := h₀.hypothesis1311.hypothesis1223
    ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hfK |>.2⟩
    (component_quotient_quasisimple h1332 hfK)
  let M := normalizer (L : Set G)
  let R := normalizerActionResidual L V
  have hRM : R ≤ M := (map_subtype_le _).trans inf_le_left
  obtain ⟨_,hnR,hRC,hpR,hRz⟩ := normalizer_action_residual_at h (structural G T) D m
  have hRN : R ≤ normalizer (K : Set G) := (hRz z.val z.property).trans hHN
  have hM : M ∈ Chapter1.HOutside G (T : Set G) (normalizer (K : Set G) : Set G) := by
    refine ⟨⟨Chapter1.mem_H_of_isTwoLocal ?_,D.sylow_normalizes_component⟩,?_⟩
    · exact (h.source_normalizer_maximal_unique_at (structural G T)
        (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).1.1
    · intro hh
      exact hLK (L.le_normalizer.trans hh)
  rcases selected_component_ordinary_or_linear hl h₀ h structural D m h1332
      fixed five covered h13316 hindex z hzT hzL hK hHN hKM hfK with hlin | hsix
  · obtain ⟨eK⟩ := hlin
    obtain ⟨DK,q,e,_,_,_,hZ,_⟩ := linear_component_marking hl h₀ h structural modules
      D m h1332 fixed hindex z hzT hzL hK.1 hHN hKM hfK eK
    let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
    let : IsSimpleGroup BinaryLinearThree.Group := Matrix.PSL3Two.equiv.isSimpleGroup
    have hc : Nat.card (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) = 8 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card BinaryLinearThree.Vector = 8
      simp [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
    exact selected_eight_outside_twoThree_at hK12 (structural G T) DK eK.isSimpleGroup hc
      hM hRM hnR hRN (hRC.trans (centralizer_le (hZ.le.trans inf_le_left)))
  · obtain ⟨eK⟩ := hsix
    obtain ⟨DK,⟨mark⟩,_,_,_,_,hZ,_⟩ := ordinary_six_component_geometry h₀ h structural modules
      D m h1332 fixed hindex z hzT hzL hK hHN hKM hfK eK
    exact selected_six_outside_twoThree_at hK12 (structural G T) DK mark eK hM hRM hnR
      hpR hRN (hRC.trans (centralizer_le (hZ.le.trans inf_le_left)))

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
