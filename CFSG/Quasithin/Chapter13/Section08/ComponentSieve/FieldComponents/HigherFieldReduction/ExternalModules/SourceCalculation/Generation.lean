module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.SourceCalculation.EarlierData
public import Theory.GroupTheory.PrimeRankNormalIntersection

/-!
# Source supplement generation in the external branch

Source: Aschbacher–Smith, proof of 13.8.20(a), printed pp.954–955,
with the marked elementary-nine quotient from Notation 13.2.1–2.

For covered L₁, a Sylow three-subgroup maps injectively through the actual
star homomorphism and gives an elementary plane E in H*. Normality of the
external cubic X* puts X* in E. The SQTK three-rank bound forces E to meet
K*: otherwise the conjugation action of E on K* has a fixed element of
order three, yielding an elementary subgroup of order 27. Thus E is
contained in K*X*. The source Sylow two-subgroup contains O₂(L₁), and the
Sylow supplement of that two-core gives the required H* = K*X*T*.

No placement of the separate L₀ direction or full-L₁ commutator identity
is used. The literal star kernel is retained throughout.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender InvertedCubicTensor Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.SourceCalculation
open Components.Swapped.LinearTwo
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open FFSections
universe u
variable {G : Type u} [Group G] [Finite G]
variable (H K X L V V₃ V₁ M : Subgroup G) (T : Sylow 2 G)
  [(K.subgroupOf H).Normal]
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
  (P : Sylow 2 (Source.Hstar H)) {𝒦 : GroupClass.{u}}
  (f : SourceOrbit.F918Hypotheses H K L (one L (T : Subgroup G) V₁) (T : Subgroup G) V V₃ V₁ ρ P 𝒦)
  (S : Sylow 2 (Source.starImage H K))
  (d : EarlierLocalData H K X L (T : Subgroup G) V V₃ V₁ M S)

include f d in
/-- Both source local cases give the exact actor generation used by the
constituent orbit argument. In the covered case the elementary plane is
absorbed modulo K*, and its two-core is absorbed by the actual Sylow T. -/
theorem source_supplement_generation
    (ha : ExternalXAlternative H K X)
    (hmodel : Structure.HigherFieldCarrier (Source.starImage H K)) :
    Source.starImage H K ⊔ (Source.starImage H X ⊔ (P : Subgroup (Source.Hstar H))) = ⊤ := by
  have hgen : H = K ⊔ (one L (T : Subgroup G) V₁ ⊔ (T : Subgroup G)) := by
    rw [f.generation, f.single_component, f.overlap]
  rcases d.local_cases with ⟨_, hX⟩ | ⟨_, hcov, hX⟩
  · exact ordinary_star_generation H K X (one L (T : Subgroup G) V₁)
      (T : Subgroup G) hgen hX (P : Subgroup (Source.Hstar H)) f.sylow_image
  · let D := one L (T : Subgroup G) V₁
    have hDH : D ≤ H := le_sup_left.trans f.setup.local_le
    obtain ⟨a⟩ := d.covered_action hcov
    have hfactor := d.covered_factor hcov
    let : IsElementaryAbelian 3 (D ⧸ pCore 2 D) := {
      toIsMulCommutative := a.one_quotient_commutative hfactor
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (a.one_quotient_cube hfactor) }
    have hN : Nat.Coprime 3 (Nat.card (pCore 2 D)) := by
      obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := D)).exists_card_eq
      rw [hn]
      exact (by decide : Nat.Coprime 3 2).pow_right n
    let q := starHom H D hDH
    have hq : Nat.Coprime 3 (Nat.card q.ker) := by
      obtain ⟨n, hn⟩ := (TorusModels.starHom_ker_isTwoGroup H D hDH).exists_card_eq
      rw [hn]
      exact (by decide : Nat.Coprime 3 2).pow_right n
    have hTD := T_normalizes_one L (T : Subgroup G) V₁ f.setup.line_normalized
    have hQT : D.pCoreIn 2 ≤ T := by
      have hncore := hTD.trans (normalizer_le_normalizer_characteristic_image D (pCore 2 D))
      exact le_sup_left.trans (le_of_eq (T.is_maximal'
        ((isPGroup_pCoreIn 2 D).to_sup_of_normal_left' T.isPGroup' hncore) le_sup_right))
    have hNP : (pCore 2 D).map q ≤ (P : Subgroup (Source.Hstar H)) := by
      rw [← starImage_map_subtype H D hDH, f.sylow_image]
      exact map_mono (subgroupOf_mono H hQT)
    obtain ⟨hXD, hp, hc, _, _⟩ := Structure.MarkedBorel.selected_local_inputs
      L (T : Subgroup G) V V₁ V₃ X T.isPGroup' f.setup.line_normalized d.marked_cases
      d.ordinary_card d.covered_action d.covered_factor d.seed_commutator
    obtain ⟨hcstar, hnot, hn, hrK⟩ := Structure.external_cubic_rank 𝒦 H K X
      f.sqtk f.component_le f.component hp hc ha
    let : (Source.starImage H X).Normal := hn
    let : (Source.starImage H K).Normal := by unfold Source.starImage; infer_instance
    have hrs : primeRank 3 (Source.starImage H K) ≤ 1 := by
      rw [← Structure.threeRank_eq_star H K f.component_le f.component.subnormal]
      exact hrK
    obtain ⟨_, _, hdiv, _⟩ := hmodel.external_structure hrs
    have hr : primeRank 3 (Source.Hstar H) ≤ 2 :=
      (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans
        (f.sqtk.stronglyQuasithin 3 Nat.prime_three (by decide))
    have hXR : Source.starImage H X ≤ q.range := by
      rw [range_starHom H D hDH]
      exact map_mono (subgroupOf_mono H hXD)
    have hD := MonoidHom.range_le_sup_of_elementary_plane_quotient (pCore 2 D)
      hN (a.one_quotient_card hfactor) q hq (Source.starImage H K)
      (Source.starImage H X) (P : Subgroup (Source.Hstar H)) hdiv hr hcstar hXR hnot hNP
    rw [range_starHom H D hDH] at hD
    have hfull := ordinary_star_generation H K D D (T : Subgroup G) hgen rfl
      (P : Subgroup (Source.Hstar H)) f.sylow_image
    apply top_unique
    rw [← hfull]
    exact sup_le le_sup_left (sup_le hD (le_sup_right.trans le_sup_right))

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.SourceCalculation
end
