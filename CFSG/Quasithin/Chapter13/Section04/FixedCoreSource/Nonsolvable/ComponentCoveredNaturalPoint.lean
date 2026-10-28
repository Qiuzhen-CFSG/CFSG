module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentRecognition
public import Theory.Representation.BinaryPermutation.SixNaturalCoverPoint
public import Theory.GroupTheory.NormalCentralQuotientAction.Maps

/-!
# The common point radical in the covered natural component case

The natural-module marking identifies the selected point centralizer with
a two-group extension of a point preimage in the cubic A₆ cover. It is a
{2,3}-group and has three-rank at least two. Reciprocal cubic generation
transfers that rank to the original augmentation component, ruling out its
ordinary quotient. Thus the original component is also covered.

The same {2,3} calculation identifies O² with O^{3′}; adjoining the actual
Sylow subgroup identifies the selected point centralizer with the original
L₁T. The already proved original covered Baumann normalizer bound therefore
applies to this literal point radical. ComponentCoveredNatural supplies the
selected natural module's Thompson comparison and excludes the case;
EscapingUniqueness applies the result in the universal comparison.

All original earlier-source inputs and their final discharge remain with
the existing owners. This does not assert the nonsolvable contradiction.
Source: Aschbacher--Smith 13.4.10(2--3), printed p.908.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V U : Subgroup G}

/-- The marked natural action above a cubic A₆ cover has point three-rank
at least two, using its literal point-centralizer map. -/
theorem covered_natural_point_structure
    (DK : ChosenModule T K U)
    (hc : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    (q : (K ⧸ centralCore K) ≃* alternatingGroup (Fin 6))
    (e : U ≃* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (he : ∀ (k : K) (v : U),
      (e (U.normalizerMonoidHom ⟨k.val,DK.normalizes k.property⟩ v)).toAdd =
        BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
          (q (QuotientGroup.mk' (centralCore K) k)) (e v).toAdd)
    (w : U) (hw : w ≠ 1) :
    2 ≤ primeRank 3 (K ⊓ centralizer ({w.val} : Set G) : Subgroup G) ∧
      IsPiGroup twoThreePrimes (K ⊓ centralizer ({w.val} : Set G) : Subgroup G) := by
  let qZ := (centralPreimageQuotientEquiv (pCore 2 K)).symm.trans q
  let f := qZ.toMonoidHom.comp (QuotientGroup.mk' (center (K ⧸ pCore 2 K)))
  have hf : Function.Surjective f := qZ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = center (K ⧸ pCore 2 K) := by
    ext x
    change qZ (QuotientGroup.mk' _ x) = 1 ↔ x ∈ center _
    rw [qZ.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hfK (k : K) : f (QuotientGroup.mk' (pCore 2 K) k) =
      q (QuotientGroup.mk' (centralCore K) k) := by
    change q ((centralPreimageQuotientEquiv (pCore 2 K)).symm _) = _
    congr 1
    apply (Equiv.symm_apply_eq _).mpr
    exact (centralPreimageQuotientEquiv_mk (pCore 2 K) k).symm
  let S := BinaryPermutation.SixNaturalCoverPoint.point (e w).toAdd
  have hmem (k : K) : f (QuotientGroup.mk' (pCore 2 K) k) ∈ S ↔
      k.val ∈ centralizer ({w.val} : Set G) := by
    change BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
      (f (QuotientGroup.mk' (pCore 2 K) k)) (e w).toAdd = (e w).toAdd ↔ _
    rw [hfK,←he k w,Multiplicative.toAdd.injective.eq_iff,e.injective.eq_iff,Subtype.ext_iff]
    change k.val * w.val * k.val⁻¹ = w.val ↔ _
    rw [mul_inv_eq_iff_eq_mul,mem_centralizer_singleton_iff,eq_comm]
  let C := K ⊓ centralizer ({w.val} : Set G)
  let g : C →* S.comap f :=
    ((QuotientGroup.mk' (pCore 2 K)).comp (inclusion inf_le_left)).codRestrict _
      (fun k => (hmem (inclusion inf_le_left k)).mpr k.property.2)
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨k,hk⟩ := QuotientGroup.mk'_surjective (pCore 2 K) a.val
    have hs : f (QuotientGroup.mk' (pCore 2 K) k) ∈ S := hk ▸ a.property
    exact ⟨⟨k.val,k.property,(hmem k).mp hs⟩,Subtype.ext hk⟩
  have hkg : IsPGroup 2 g.ker := by
    have heq : g.ker = (pCore 2 K).comap (inclusion (show C ≤ K from inf_le_left)) := by
      ext x
      change (⟨QuotientGroup.mk' (pCore 2 K) (inclusion inf_le_left x),_⟩ : S.comap f) = 1 ↔ _
      rw [Subtype.ext_iff]
      exact QuotientGroup.eq_one_iff _
    rw [heq]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  have hr := BinaryPermutation.SixNaturalCoverPoint.two_le_rank_preimage f hf
    (hker ▸ le_rfl) (hker ▸ hc) (e w).toAdd
      (fun hh => hw (e.injective (hh.trans e.map_one.symm)))
  have hcop : Nat.Coprime 3 (Nat.card g.ker) := by
    obtain ⟨n,hn⟩ := hkg.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  refine ⟨(primeRank_eq_of_surjective_of_coprime 3 g hg hcop).symm ▸ hr,?_⟩
  have hS : Nat.card S = 24 := BinaryPermutation.SixNaturalCoverPoint.point_card
    (e w).toAdd (fun hh => hw (e.injective (hh.trans e.map_one.symm)))
  have hP : Nat.card (S.comap f) = 72 := by
    rw [card_eq_card_quotient_mul_card_subgroup (f.ker.subgroupOf (S.comap f)),
      card_quotient_subgroupOf_comap_eq (f := f) (hf := hf) (H := S),
      Nat.card_congr (subgroupOfEquivOfLe (ker_le_comap (f := f) (H := S))).toEquiv,
      hS,hker,hc]
  obtain ⟨n,hn⟩ := hkg.exists_card_eq
  have hC : Nat.card C = 72 * 2 ^ n := by
    rw [card_eq_card_quotient_mul_card_subgroup g.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hg).toEquiv,hP,hn]
  rw [IsPiGroup_iff]
  intro p hp
  change p.val = 2 ∨ p.val = 3
  change p.val ∣ Nat.card C at hp
  rw [hC,show 72 * 2 ^ n = 2 ^ (n+3) * 3 ^ 2 by ring] at hp
  rcases p.property.dvd_mul.mp hp with h2 | h3
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
      (p.property.dvd_of_dvd_pow h2) |>.resolve_left p.property.ne_one)
  · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp
      (p.property.dvd_of_dvd_pow h3) |>.resolve_left p.property.ne_one)

/-- An actual covered natural selected component forces the original
augmentation component to be covered. The reciprocal O^{3′} residual is
unchanged, so its point rank rules out the ordinary original row. -/
theorem covered_original_of_natural_component
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hKN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (hc : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    (DK : ChosenModule T K
      ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆)
    (q : (K ⧸ centralCore K) ≃* alternatingGroup (Fin 6))
    (e : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) ≃*
      Multiplicative (BinaryPermutation.natural (Fin 6)))
    (he : ∀ (k : K) (v : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G)),
      (e ((⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G).normalizerMonoidHom
        ⟨k.val,DK.normalizes k.property⟩ v)).toAdd =
          BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
            (q (QuotientGroup.mk' (centralCore K) k)) (e v).toAdd) :
    Nat.card (center (L ⧸ pCore 2 L)) = 3 ∧
      2 ≤ primeRank 3 (Solvable.firstCentralizerResidual L z.val) ∧
      Solvable.firstCentralizerResidual K m.constant.val =
        Solvable.firstCentralizerResidual L z.val := by
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  let qZ := (centralPreimageQuotientEquiv (pCore 2 K)).symm.trans q
  have hrec := six_component_reciprocal_residual h₀ h structural D m hzT hz1 hK hKN
    (component_quotient_quasisimple h1332 hfK) qZ
  obtain ⟨w,hw,hC⟩ := component_fixed_generator_point h₀ h structural m hzT hz1 hK.1
    (h1332 K hfK).1 hKM
  have hr := (covered_natural_point_structure DK hc q e he w hw).1
  rw [←hC,←Solvable.firstCentralizerResidual_threeRank,hrec] at hr
  refine ⟨?_,hr,hrec⟩
  let := h.quasisimple
  have hn : ¬ 2 ∣ Nat.card (center (L ⧸ pCore 2 L)) :=
    PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot 2) (center (L ⧸ pCore 2 L)) le_rfl
  have ho : Odd (Nat.card (center (L ⧸ pCore 2 L))) :=
    Nat.not_even_iff_odd.mp (fun hh => hn (even_iff_two_dvd.mp hh))
  rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 6 (by decide)
      (augmentationCentralQuotient D m) ho with hcL | ⟨_,hcL⟩
  · let eL := GLS3.Chapter5.OddCentralCovers.alternatingEquivOfCenterCardOne 6
      (augmentationCentralQuotient D m) hcL
    have hu := core_component_point_threeRank_le_one D m eL z hzL
    rw [←Solvable.firstCentralizerResidual_threeRank] at hu
    omega
  · exact hcL

/-- Both covered components use the same literal point parabolic and radical.
The original Baumann normalizer bound feeds the selected natural module's
Thompson comparison. -/
theorem covered_natural_component_common_point
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hKN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (hc : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    (DK : ChosenModule T K
      ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆)
    (q : (K ⧸ centralCore K) ≃* alternatingGroup (Fin 6))
    (e : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) ≃*
      Multiplicative (BinaryPermutation.natural (Fin 6)))
    (he : ∀ (k : K) (v : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G)),
      (e ((⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G).normalizerMonoidHom
        ⟨k.val,DK.normalizes k.property⟩ v)).toAdd =
          BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
            (q (QuotientGroup.mk' (centralCore K) k)) (e v).toAdd) :
    Nat.card (center (L ⧸ pCore 2 L)) = 3 ∧
      ∃ w : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G),
        w ≠ 1 ∧ (T : Subgroup G) ≤ centralizer ({w.val} : Set G) ∧
        Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G) =
          (K ⊔ (T : Subgroup G)) ⊓ centralizer ({w.val} : Set G) ∧
        normalizer (ChapterB.baumann
          (((K ⊔ (T : Subgroup G)) ⊓ centralizer ({w.val} : Set G)).pCoreIn 2) : Set G) ≤
          normalizer (L : Set G) := by
  obtain ⟨hcL,_,hrec⟩ := covered_original_of_natural_component h₀ h structural D m h1332
    z hzT hzL hK hKN hKM hfK hc DK q e he
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  obtain ⟨w,hw,hTw,hpoint⟩ := component_fixed_generator_point_overgroup
    h₀ h structural m hzT hz1 hK.1 (h1332 K hfK).1 hKM
  have hC : K ⊓ centralizer ({m.constant.val} : Set G) =
      K ⊓ centralizer ({w.val} : Set G) := by
    have hh := congrArg (fun B : Subgroup G => K ⊓ B) hpoint
    simpa only [←inf_assoc,inf_eq_left.mpr (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)] using hh
  have h23 := (covered_natural_point_structure DK hc q e he w hw).2
  have hP : Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G) =
      (K ⊔ (T : Subgroup G)) ⊓ centralizer ({w.val} : Set G) := by
    rw [←hrec,Solvable.firstCentralizerResidual_eq,hC,
      ←twoResidual_eq_primeToResidual_three h23]
    exact embedded_pointResidual_sup_sylow T K (h1332 K hfK).1 w.val hTw
  refine ⟨hcL,w,hw,hTw,hP,?_⟩
  rw [←hP]
  exact covered_augmentation_baumann_normalizer h structural D m hcL z hzT hzL
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
