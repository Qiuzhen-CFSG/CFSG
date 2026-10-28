module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.CoreRecognition.Inputs
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion.SecondNormalizer.Contracts

/-!
# The independent cubic-centralizer bound in 47.3

For a cubic element y of the selected component E(C_G(t)), the two
second-centralizer alternatives both exclude a factor 27. In the relatively
normal root-four-group case its centralizer embeds in the actual A₄ × A₅
root normalizer, of order 720. In the product case it has order 180.
An abelian ambient Sylow three-subgroup containing y would contradict this
bound. Sylow conjugacy then excludes commutativity for every Sylow three.

These arguments use neither the A₆ cover nor the later Sylow normalizer
calculation. The second-centralizer alternative remains an explicit premise.

Source: Aschbacher, *Sporadic Groups* (1994), 47.3, printed p.262,
the paragraph preceding the calculation of |C_G(X)|.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
namespace CoreSylowInputs

variable {G : Type*} [Group G] [Finite G] {D : Seed G}
private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The full marked root normalizer, before any first-centralizer recognition. -/
theorem root_normalizer_card (S : InvolutionGeometry.SelectedGeometry D) :
    Nat.card (normalizer (InvolutionGeometry.rootCore S.t : Set G)) = 720 := by
  rw [Nat.card_congr S.normalizerEquiv.toEquiv, Nat.card_prod,
    InvolutionGeometry.card_A5, nat_card_alternatingGroup]
  norm_num

/-- Relative normality puts the cubic centralizer inside the root normalizer. -/
theorem cubic_centralizer_le_root_normalizer
    (S : InvolutionGeometry.SelectedGeometry D) {y : G}
    (hy : y ∈ InvolutionGeometry.rootComponent S.t)
    (hn : SecondNormalizer.RootNormal S y) :
    SecondNormalizer.cubicCentralizer y ≤
      normalizer (InvolutionGeometry.rootCore S.t : Set G) := by
  exact (normal_subgroupOf_iff_le_normalizer
    (SecondNormalizer.rootCore_le_cubicCentralizer S hy)).mp hn

/-- Both independent alternatives have three-part at most nine. -/
theorem cubic_centralizer_not_twenty_seven
    (S : InvolutionGeometry.SelectedGeometry D)
    (hAlt : SecondNormalizer.CentralizerAlternatives S)
    {y : G} (hy : y ∈ InvolutionGeometry.rootComponent S.t) (hyo : orderOf y = 3) :
    ¬ 27 ∣ Nat.card (SecondNormalizer.cubicCentralizer y) := by
  intro hd
  rcases hAlt y hy hyo with hn | he
  · have h := hd.trans (card_dvd_of_le (cubic_centralizer_le_root_normalizer S hy hn))
    rw [root_normalizer_card S] at h
    norm_num at h
  · have hc : Nat.card (SecondNormalizer.cubicCentralizer y) = 180 := by
      rw [Nat.card_congr he.some.toEquiv, Nat.card_prod,
        nat_card_alternatingGroup]
      norm_num [Nat.card_eq_fintype_card]
    rw [hc] at hd
    norm_num at hd

/-- The ambient source order gives order 27 independently of either centralizer. -/
theorem three_card (hG : Nat.card G = 604800) (P : Sylow 3 G) : Nat.card P = 27 := by
  rw [P.card_eq_multiplicity, hG]
  decide +kernel

/-- No ambient Sylow three-subgroup centralizes a cubic element of the component. -/
theorem sylow_not_le_cubic_centralizer (E : EarlierConclusions D)
    (hAlt : SecondNormalizer.CentralizerAlternatives E.geometry)
    {y : G} (hy : y ∈ InvolutionGeometry.rootComponent E.geometry.t)
    (hyo : orderOf y = 3) (P : Sylow 3 G) :
    ¬ (P : Subgroup G) ≤ SecondNormalizer.cubicCentralizer y := by
  intro hle
  apply cubic_centralizer_not_twenty_seven E.geometry hAlt hy hyo
  simpa only [three_card E.card P] using card_dvd_of_le hle

/-- The source alternatives already force every ambient Sylow three to be nonabelian. -/
theorem three_noncommutative (E : EarlierConclusions D)
    (hAlt : SecondNormalizer.CentralizerAlternatives E.geometry)
    (P : Sylow 3 G) : ¬ IsMulCommutative P := by
  intro hcomm
  let := hcomm
  obtain ⟨y, hy, hyo, _⟩ := SecondNormalizer.exists_component_three E.geometry
  have hp : IsPGroup 3 (zpowers y) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, hyo]; rfl)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have hqc : IsMulCommutative Q := IsMulCommutative.of_comm fun a b =>
    (Q.equiv P).injective (by simp only [map_mul]; exact mul_comm _ _)
  exact sylow_not_le_cubic_centralizer E hAlt hy hyo Q
    ((le_centralizer_iff_isMulCommutative.mpr hqc).trans (centralizer_le hQ))

/-- Only the elementary prime-cube center calculation is needed at this stage. -/
theorem three_center_card (E : EarlierConclusions D)
    (hAlt : SecondNormalizer.CentralizerAlternatives E.geometry)
    (P : Sylow 3 G) : Nat.card (center P) = 3 :=
  card_center_eq_prime_of_card_eq_prime_cube (three_card E.card P)
    (three_noncommutative E hAlt P)

/-- The center's image has order three in the original ambient group. -/
theorem three_center_image_card (E : EarlierConclusions D)
    (hAlt : SecondNormalizer.CentralizerAlternatives E.geometry)
    (P : Sylow 3 G) : Nat.card ((center P).map (P : Subgroup G).subtype) = 3 := by
  rw [card_map_of_injective (P : Subgroup G).subtype_injective,
    three_center_card E hAlt P]

/-- A cubic component element cannot generate the center of an ambient Sylow. -/
theorem three_center_image_ne_component_cubic (E : EarlierConclusions D)
    (hAlt : SecondNormalizer.CentralizerAlternatives E.geometry)
    {y : G} (hy : y ∈ InvolutionGeometry.rootComponent E.geometry.t)
    (hyo : orderOf y = 3) (P : Sylow 3 G) :
    (center P).map (P : Subgroup G).subtype ≠ zpowers y := by
  intro he
  apply sylow_not_le_cubic_centralizer E hAlt hy hyo P
  rw [SecondNormalizer.cubicCentralizer, ← he]
  intro p hp a ha
  obtain ⟨b, hb, rfl⟩ := ha
  exact congrArg Subtype.val (mem_center_iff.mp hb (⟨p, hp⟩ : P)).symm

end CoreSylowInputs
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
