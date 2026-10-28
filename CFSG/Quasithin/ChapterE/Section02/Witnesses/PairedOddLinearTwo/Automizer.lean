module
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentAutomizerSQTK
public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.InnerSylow
public import Theory.GroupTheory.ComponentTwoCore.ElementaryNormalizer
public import Theory.GroupTheory.NormalizerAction.ElementaryTransport
public import Theory.GroupTheory.TwoConjugateProduct.Projection

/-!
# Original elementary actors on a paired odd-linear component

The genuine component automizer is a core-free minimal parabolic with the
original Sylow image. Its odd-linear model supplies a nonsquare in the
component Sylow, so the original elementary normal subgroup preserves the
component. Its automizer image is elementary and normal in the marked
Sylow. The prime-field source bounds place that image in the component
image and give it order at most two. Both conclusions are pulled back
through the literal normalizer quotient.

Source: Aschbacher–Smith E.2.7, printed p.219.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.PairedOddLinearTwo
variable {H : Type*} [Group H] [Finite H]

theorem source_component_placement
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p) (hp : p = 7 ∨ 9 < p)
    (hH : IsStronglyQuasithin H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    {K : Subgroup H} (hK : IsComponent H K) (hC : K.IsCComponent)
    [IsSimpleGroup K] (hrad : solvableRadical H = ⊥)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (e : K ≃* PSL(2,F))
    (V : Subgroup H) [IsElementaryAbelian 2 V]
    (hVT : V ≤ T) (hVN : (T : Subgroup H) ≤ normalizer (V : Set H)) :
    V ≤ normalizer (K : Set H) ∧ V ≤ K ⊔ centralizer (K : Set H) ∧
      Nat.card ((V.subgroupOf (normalizer (K : Set H))).map (NormalizerAction.quotient K)) ≤ 2 := by
  have hz : center K = ⊥ := center_eq_bot_of_isSubnormal_of_solvableRadical_eq_bot hrad hK.1
  let L := NormalizerAction.componentImage K
  let d := NormalizerAction.componentEquivOfCenterEqBot K hz
  let eL : L ≃* PSL(2,F) := d.symm.trans e
  obtain ⟨S,hS,hPs,_⟩ := Structure.source_component_automizer hH T hP hK hgen
  have hcore := Structure.source_component_automizer_core hK S hPs
  have hO : pCore 2 (NormalizerAction.Star K) = ⊥ := le_bot_iff.mp
    ((ChapterB.minimalParabolicTwoCore_le_core S hPs).trans hcore.le)
  have hLS : L ⊔ (S : Subgroup (NormalizerAction.Star K)) = ⊤ := by
    rw [hS]
    exact component_automizer_sylow_supplement T hK
      (Structure.generating_component_orbit_eq_residual hH T hK hgen)
  obtain ⟨Q,hQ⟩ := T.exists_subgroupOf_eq_of_subnormal K hK.1
  have hsq : ∃ s : K, s ∈ (Q : Subgroup K) ∧ s ^ 2 ≠ 1 := by
    rcases hp with hp | hp
    · exact Structure.prime_seven_inner_sylow_nonsquare (hF.trans hp) e Q
    · let Q' := Q.mapSurjective (f := d.toMonoidHom) d.surjective
      obtain ⟨s,hs,hs2⟩ := Structure.prime_linear_source_inner_sylow_nonsquare
        S hPs L hLS ho hF hp eL Q'
      refine ⟨d.symm s,mem_map_equiv.mp hs,?_⟩
      intro he
      exact hs2 (by simpa only [map_pow,map_one,d.apply_symm_apply] using congrArg d he)
  obtain ⟨s,hs,hs2⟩ := hsq
  have hsT : (s:H) ∈ T := by
    have hh : s ∈ (T : Subgroup H).subgroupOf K := hQ ▸ hs
    exact hh
  have hN : V ≤ normalizer (K : Set H) :=
    elementary_le_component_normalizer_of_nonsquare K V hK hC hrad s s.property
      (hVN hsT) (fun hh => hs2 (Subtype.ext hh))
  let W := (V.subgroupOf (normalizer (K : Set H))).map (NormalizerAction.quotient K)
  let : IsElementaryAbelian 2 (V.subgroupOf (normalizer (K : Set H))) :=
    IsElementaryAbelian.subgroupOf hN
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hWS : W ≤ S := by rw [hS]; exact map_mono (subgroupOf_mono _ hVT)
  have hSW : (S : Subgroup (NormalizerAction.Star K)) ≤ normalizer (W : Set (NormalizerAction.Star K)) := by
    rw [hS]
    exact NormalizerAction.normalized_image K T V hVN
  have hWL : W ≤ L := by
    rcases hp with hp | hp
    · exact Structure.prime_seven_source_elementary_le_component S hPs hcore L hLS
        (hF.trans hp) eL W inferInstance hWS hSW
    · exact Structure.prime_linear_source_elementary_le_component S hPs L hLS hO
        ho hF hp eL W inferInstance hWS hSW
  refine ⟨hN,NormalizerAction.le_component_centralizer_of_image_le K V hN hWL,?_⟩
  change Nat.card W ≤ 2
  rcases hp with hp | hp
  · by_contra! hh
    have hn : W ≠ ⊥ := by intro he; rw [he,card_bot] at hh; omega
    obtain hh2 | hh4 := two_or_four_of_elementary_ne_bot W hn
    · omega
    · exact Structure.prime_seven_source_not_elementary_four S hPs hcore L hLS
        (hF.trans hp) eL W inferInstance hWS hSW hh4
  · exact Structure.prime_linear_source_elementary_card_le_two S hPs L hLS hO
      ho hF hp eL W inferInstance hWS hSW

end CFSG.Quasithin.ChapterE.Witnesses.PairedOddLinearTwo
