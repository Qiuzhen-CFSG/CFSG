module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.SourceAssembly
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.OriginalResidual
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.SeedProjection

/-!
# Original-source Borel and diagonal coordinates for the exchanged PSL₂ branch

The preceding residual theorem supplies O^{3′}(H)=K₀. Original 13.7.3(9)
supplies theta(H∩M)=L₁, the natural flag supplies cubic generation and both
local models, and original 13.8.13 supplies solvable-overgroup exclusion.
The complete marked Borel calculation therefore forces n=2 and the covered
A₆ local model. Its final projection equation is transported back to the
literal marked subgroups of H/O₂(H), giving L₀*K₂*=L₁,+*K₂*.

All earlier source hypotheses are retained unchanged. No Borel choice,
residual identity, local-action conclusion or final parameter is assumed.
The module classification and the orthogonal critical-pair contradiction
are still required for the complete 13.8.16(1) branch.
Source: Aschbacher--Smith, 13.8.16(1), printed p.952 (PDF p.969).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.Original
open SourceCompletion TransvectionRecognition.Component.ModelExtension SourceConclusion
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
  (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G)) = H)
  (hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K)
include d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving

theorem borel_diagonal {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (K : Set G)) :
    ∃ (hK : K ⊔ K.conjBy t ≤ H) (hTH : T ≤ H)
      (e : Source.starImage H (K ⊔ K.conjBy t) ≃*
        Source.starImage H K × Source.starImage H K)
      (S : Sylow 2 (Source.starImage H (K ⊔ K.conjBy t))),
      let Kstar := Source.starImage H (K ⊔ K.conjBy t)
      let Bstar := SourceTorus.chosenStarBorel H (K ⊔ K.conjBy t) S
      let B₀ := SourceTorus.chosenLift H (K ⊔ K.conjBy t) hK S
      let C := SourceActions.CommonTorus H (K ⊔ K.conjBy t) e S
      let Z := SourceActions.D₀ H (K ⊔ K.conjBy t) hK e S hn hmodel L
      let P := SourceActions.Dplus H (K ⊔ K.conjBy t) hK e S hn hmodel L T V₁
      let π := factorProjection H (K ⊔ K.conjBy t) e
      (∀ a b, (e.symm (a, b) : Source.Hstar H) = (a : Source.Hstar H) *
        (QuotientGroup.mk' (pCore 2 H) ⟨t, hTH ht⟩ * b *
          (QuotientGroup.mk' (pCore 2 H) ⟨t, hTH ht⟩)⁻¹)) ∧
      (S : Subgroup Kstar).map Kstar.subtype = Source.starImage H (T ⊓ (K ⊔ K.conjBy t)) ∧
      Source.starImage H (T ⊓ (K ⊔ K.conjBy t)) ≤ Bstar ∧
      Source.starImage H B₀ = Bstar ∧ Group.IsSolvable B₀ ∧
      one L T V₁ ≤ B₀ ∧ B₀ ≤ M ∧ one L T V₁ ⊔ T ≤ normalizer (B₀ : Set G) ∧
      Even n ∧ primeRank 3 B₀ = 2 ∧ primeRank 3 (one L T V₁) = 2 ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      (∃ a : ℕ, 2 ^ n - 1 = 3 ^ a) ∧ n = 2 ∧ one L T V₁ = residual B₀ ∧
      zero L ≤ one L T V₁ ∧ plus L T V₁ ≤ one L T V₁ ∧
      Nat.card (zero L ⧸ pCore 2 (zero L)) = 3 ∧
      Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3 ∧
      Function.Injective (fun x : Z => (x : C × C).1) ∧
      Function.Injective (fun x : Z => (x : C × C).2) ∧
      Function.Injective (fun x : P => (x : C × C).1) ∧
      Function.Injective (fun x : P => (x : C × C).2) ∧
      Z.map (MonoidHom.fst C C) = P.map (MonoidHom.fst C C) ∧
      Z.map (MonoidHom.snd C C) = P.map (MonoidHom.snd C C) ∧
      π.ker = (Source.starImage H (K.conjBy t)).subgroupOf Kstar ∧
      ((Source.starImage H (zero L)).subgroupOf Kstar).map π =
        ((Source.starImage H (plus L T V₁)).subgroupOf Kstar).map π := by
  have hi := moving_index d h hF9all hcentral hcomm hsource hH hKH hK hmoving
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  have horbit := orbit_eq_two_conjugates H K T hKH hTH hi ht htn
  have hres := threeResidual d h hF9all hcentral hcomm hsource hH hKH hK hmoving hn hmodel
  rw [horbit] at hres
  have hgenerated : H = (K ⊔ K.conjBy t) ⊔ one L T V₁ ⊔ (T : Subgroup G) := by
    rw [← horbit, sup_assoc]
    exact hgen.symm
  have hnatural : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) →
      Nonempty (LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃) := by
    intro hc
    rcases local_quotient_alternatives d with ⟨e, he⟩ | ⟨e, he⟩
    · obtain ⟨f⟩ := hc
      have hh := Nat.card_congr (centerCongr (f.symm.trans e)).toEquiv
      rw [Representation.Hexacode.even_center_card,
        alternatingGroup.center_eq_bot (by simp), card_bot] at hh
      omega
    · exact local_covered_flag_model d e he
  have hne : one L T V₁ ≠ ⊥ := by
    intro he
    have hs := Section07.ModelExclusions.seed_commutator_point_residual (localNaturalSetup d)
    change ⁅V₃, one L T V₁⁆ = V₃ at hs
    rw [he, commutator_bot_right] at hs
    have hc := d.seed_card
    rw [← hs, card_bot] at hc
    contradiction
  let := LocalFitting.local_solvable d
  apply exists_borel_diagonal H K L T V V₁ V₃ M ht hgenerated
    ⟨T.subtype hTH, by rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH]⟩ hK
    (SolvableSource.component_fitting_source d h hF9all hcentral hcomm hsource hH K hK).2
    hi htn hn hmodel hres
    (Section07.ModelExclusions.theta_intersection (localNaturalSetup d) h hH).symm
    (fun x => ⟨1, by simpa using
      Section07.ModelExclusions.point_residual_quotient_cube (localNaturalSetup d) x⟩) hne
  · exact hH.2.1.trans d.first_normalizer.le
  · rw [d.local_normalizer]
  · intro J hJ hJN hs
    apply SolvableSource.solvable_overgroup_source d h hF9all hcentral hcomm hsource J hJ
    · exact hJN.trans d.first_normalizer.ge
    · exact hs
  · rcases local_quotient_alternatives d with ⟨e, _⟩ | ⟨e, _⟩
    · exact Or.inl ⟨e⟩
    · exact Or.inr ⟨e⟩
  · exact LocalFitting.ordinary_core_card d
  · exact hnatural
  · intro hc
    obtain ⟨a⟩ := hnatural hc
    exact CoverFactorization.source_factorization a

/-- The actual marked cosets used by the projection contradiction, with
all Borel, cubic-residual, theta and local-action inputs discharged. -/
theorem diagonal_cosets {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (K : Set G)) :
    n = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      zero L ≤ one L T V₁ ∧ plus L T V₁ ≤ one L T V₁ ∧
      Source.starImage H (zero L) ⊔ Source.starImage H (K.conjBy t) =
        Source.starImage H (plus L T V₁) ⊔ Source.starImage H (K.conjBy t) := by
  obtain ⟨hKO, hTH, e, S, _, _, _, _, _, hLB, _, _, _, _, _, hcover,
    _, hn2, _, hz, hp, _, _, _, _, _, _, _, _, hker, himage⟩ :=
    borel_diagonal d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving hn hmodel ht htn
  refine ⟨hn2, hcover, hz, hp, ?_⟩
  let N := Source.starImage H (K ⊔ K.conjBy t)
  have hone : one L T V₁ ≤ K ⊔ K.conjBy t :=
    hLB.trans (borelLift_le H (K ⊔ K.conjBy t) hKO _)
  have hzN : Source.starImage H (zero L) ≤ N := map_mono (subgroupOf_mono H (hz.trans hone))
  have hpN : Source.starImage H (plus L T V₁) ≤ N := map_mono (subgroupOf_mono H (hp.trans hone))
  have hKN : Source.starImage H (K.conjBy t) ≤ N := map_mono (subgroupOf_mono H le_sup_right)
  have he := join_kernel_eq_of_projected_images (factorProjection H (K ⊔ K.conjBy t) e)
    ((Source.starImage H (zero L)).subgroupOf N)
    ((Source.starImage H (plus L T V₁)).subgroupOf N) himage
  rw [hker] at he
  have hh := congrArg (map N.subtype) he
  dsimp only [N] at hzN hpN hKN hh
  simpa only [Subgroup.map_sup, map_subgroupOf_eq_of_le hzN,
    map_subgroupOf_eq_of_le hpN, map_subgroupOf_eq_of_le hKN] using hh

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.Original
