module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Geometry.PlaneGeometry
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.CentralizerAction.Quotient

/-!
# Invariant residual directions through the actual rank-two quotient

A direction is two-perfect with three-part three, normal in Y and invariant
under S. The genuine S₃ × S₃ quotient has two-group kernel. Each direction
maps to a normal cubic axis, and two-perfectness lifts equality through the
kernel. Thus any two directions generating Y are the only directions.

For the first choice of Hypothesis 15.3.10, the actual orthogonal coordinates
construct the two residual plane centralizers and identify Y_L and Y_C with
them, in either orientation. For the second choice, the same quotient argument
identifies any centralizing direction with Y_C when [V,Y_L] is nontrivial.

The source S-invariance and second-choice centralizing direction are supplied
separately by ResidualInvariance and SecondChoice, and combined in SourceAssembly.
These results do not assume that the section-centralizer residual Y_C is an
ordinary centralizer, or that its total order is three.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.11(5), 15.3.12(2), and 15.3.23, printed pp.1123–1125 and 1128.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree
open CFSG.Quasithin.Chapter15.Section03.RankTwo
variable {G : Type*} [Group G]

/-- A residual direction means a two-perfect subgroup with three-part three,
normal in Y and invariant under S. This definition imposes no total-order bound. -/
structure ResidualDirection (Y S A : Subgroup G) : Prop where
  le : A ≤ Y
  normal : (A.subgroupOf Y).Normal
  invariant : S ≤ normalizer (A : Set G)
  perfect : IsPPerfect 2 A
  three_part : 3 ^ (Nat.card A).factorization 3 = 3

/-- The genuine rank-two shadow has exactly two invariant residual directions.
The proof uses its actual quotient homomorphism and two-group kernel to lift
the two coordinate axes; no quotient direction is identified merely by its order. -/
theorem rankTwoShadow_residual_directions [Finite G] {Y S A B : Subgroup G}
    (hY : IsPPerfect 2 Y) (h9 : Nat.card (Y ⧸ pCore 2 Y) = 9)
    (hS : IsPGroup 2 S) (hSY : S ≤ normalizer (Y : Set G))
    (hshadow : RankTwoShadow Y S)
    (hA : ResidualDirection Y S A) (hB : ResidualDirection Y S B)
    (hgen : Y = A ⊔ B) :
    A ≠ B ∧ ∀ N : Subgroup G, ResidualDirection Y S N ↔ N = A ∨ N = B := by
  obtain ⟨f, hf, hk, _⟩ := rankTwoShadow_map_data hY h9 hS hSY hshadow
  let H := Y ⊔ S
  let im (N : Subgroup G) := (N.subgroupOf H).map f
  have hn (N : Subgroup G) (hN : ResidualDirection Y S N) :
      (N.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le ((normal_subgroupOf_iff_le_normalizer hN.le).mp hN.normal) hN.invariant)
  have hp (N : Subgroup G) (hN : ResidualDirection Y S N) :
      IsPPerfect 2 (N.subgroupOf H) := hN.perfect.of_surjective
    (subgroupOfEquivOfLe (show N ≤ H from hN.le.trans le_sup_left)).symm.toMonoidHom
    (subgroupOfEquivOfLe (show N ≤ H from hN.le.trans le_sup_left)).symm.surjective
  have direction (N : Subgroup G) (hN : ResidualDirection Y S N) :
      im N = SymmetricThreeProduct.leftThree ∨ im N = SymmetricThreeProduct.rightThree := by
    let : (im N).Normal := (hn N hN).map f hf
    apply SymmetricThreeProduct.normal_twoPerfect_threePart _
      ((hp N hN).of_surjective (f.subgroupMap _) (f.subgroupMap_surjective _))
    rw [threePart_map_of_twoGroup_kernel f hk,
      Nat.card_congr (subgroupOfEquivOfLe (show N ≤ H from hN.le.trans le_sup_left)).toEquiv]
    exact hN.three_part
  have lift (N K : Subgroup G) (hN : ResidualDirection Y S N)
      (hK : ResidualDirection Y S K) (he : im N = im K) : N = K := by
    let : (N.subgroupOf H).Normal := hn N hN
    let : (K.subgroupOf H).Normal := hn K hK
    have heq := eq_of_normal_twoPerfect_of_map_eq f hk _ _ (hp N hN) (hp K hK) he
    have hm := congrArg (Subgroup.map H.subtype) heq
    simpa only [map_subgroupOf_eq_of_le (show N ≤ H from hN.le.trans le_sup_left),
      map_subgroupOf_eq_of_le (show K ≤ H from hK.le.trans le_sup_left)] using hm
  have hne : A ≠ B := by
    intro he
    have hYA : Y = A := by simpa only [← he, sup_idem] using hgen
    have hh := threePart_of_twoCore_quotient_nine h9
    rw [hYA, hA.three_part] at hh
    norm_num at hh
  refine ⟨hne, fun N => ⟨fun hN => ?_, ?_⟩⟩
  · rcases direction N hN with hn | hn <;>
      rcases direction A hA with ha | ha <;>
      rcases direction B hB with hb | hb <;>
      first
      | exact Or.inl (lift N A hN hA (hn.trans ha.symm))
      | exact Or.inr (lift N B hN hB (hn.trans hb.symm))
      | exact (hne (lift A B hA hB (ha.trans hb.symm))).elim
  · rintro (rfl | rfl)
    · exact hA
    · exact hB

/-- In particular, a direction centralizing V must be Y_C when Y_L moves V.
Its order, two-perfectness and invariance are hypotheses to be proved for the
literal residual O²(C_Y(V)) in the second-choice application. -/
theorem centralizing_direction_eq_YC [Finite G] (d : LocalData G) (L K : Subgroup G)
    (h9 : Nat.card (d.Yplus ⧸ pCore 2 d.Yplus) = 9)
    (hshadow : RankTwoShadow d.Yplus d.S)
    (hL : ResidualDirection d.Yplus d.S (YL d L))
    (hC : ResidualDirection d.Yplus d.S (YC d L))
    (hgen : d.Yplus = YL d L ⊔ YC d L)
    (hK : ResidualDirection d.Yplus d.S K) (hKV : K ≤ centralizer (d.V : Set G))
    (hne : ⁅d.V, YL d L⁆ ≠ ⊥) : K = YC d L := by
  have hY := yplus_perfect_of_choice d.choice
  have hSY := planeStabilizer_normalizes_yplus d.action d.T d.sylow_le 1 d.choice
  rcases ((rankTwoShadow_residual_directions hY h9 (d.T.isPGroup'.to_le inf_le_left)
    hSY hshadow hL hC hgen).2 K).mp hK with he | he
  · have hcen : d.V ≤ centralizer (YL d L : Set G) :=
      le_centralizer_iff.mp (he ▸ hKV)
    exact (hne (commutator_eq_bot_iff_le_centralizer.mpr hcen)).elim
  · exact he

/-- The genuine 15.3.12 normality and three-part conclusions make both
component residuals directions as soon as their S-invariance is established. -/
theorem component_residual_directions [Finite G] (d : LocalData G) (L : Subgroup G)
    (hYL : d.Yplus ≤ normalizer (L : Set G))
    (hSL : d.S ≤ normalizer (YL d L : Set G))
    (hSC : d.S ≤ normalizer (YC d L : Set G))
    (hL3 : 3 ^ (Nat.card (YL d L)).factorization 3 = 3)
    (hC3 : 3 ^ (Nat.card (YC d L)).factorization 3 = 3) :
    ResidualDirection d.Yplus d.S (YL d L) ∧
      ResidualDirection d.Yplus d.S (YC d L) := by
  exact ⟨⟨(ComponentIntersection.intersectionResidual_le _ _).trans inf_le_left,
    normal_subgroupOf_of_le_normalizer (ComponentIntersection.normalizes_intersectionResidual hYL),
    hSL, ComponentIntersection.intersectionResidual_isPPerfect _ _, hL3⟩,
    ⟨(ComponentIntersection.centralizerResidual_le _ _).trans inf_le_left,
    normal_subgroupOf_of_le_normalizer (ComponentIntersection.normalizes_centralizerResidual hYL),
    hSC, ComponentIntersection.centralizerResidual_isPPerfect _ _, hC3⟩⟩

/-- In the first choice, the actual orthogonal coordinates and quotient
actions identify the component residuals with the two plane centralizers.
The two orientations are retained; no component-to-coordinate marking is assumed. -/
theorem residualPlaneFactors_of_first_choice [Finite G] (d : LocalData G)
    (L : Subgroup G) (hY : d.Yplus = d.Y)
    (h7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h9 : Nat.card (d.Yplus ⧸ pCore 2 d.Yplus) = 9)
    (hshadow : RankTwoShadow d.Yplus d.S)
    (hL : ResidualDirection d.Yplus d.S (YL d L))
    (hC : ResidualDirection d.Yplus d.S (YC d L))
    (hgen : d.Yplus = YL d L ⊔ YC d L) : ResidualPlaneFactors d L := by
  let i : OrthogonalPlaneIndex := 1
  let j : OrthogonalPlaneIndex := Multiplicative.ofAdd (1 : ZMod 2)
  have hij : i ≠ j := by decide
  have hY9 : Nat.card (d.Y ⧸ pCore 2 d.Y) = 9 := hY ▸ h9
  have hYM : d.Y ≤ d.M := Chapter14.SourcePreliminaries.sourceResidual_le _ _
  have hSY : d.S ≤ normalizer (d.Y : Set G) := by
    rw [← hY]
    exact planeStabilizer_normalizes_yplus d.action d.T d.sylow_le 1 d.choice
  have hpY : IsPPerfect 2 d.Y := residualY_isPPerfect _ _
  have hc := residualY_fullActionCoordinateFacts d.action h7
  have dir (k : OrthogonalPlaneIndex) :
      ResidualDirection d.Yplus d.S (centralizingFactor d.Y (d.action.plane k)) := by
    rw [hY]
    exact ⟨centralizingFactor_le_left _ _,
      centralizingFactor_normal (perfect_normalizes_planes d.action hYM hpY k),
      normalizes_centralizingFactor hSY
        (planeStabilizer_normalizes_planes d.action d.T d.sylow_le 1 k),
      centralizingFactor_isPPerfect _ _, residual_subgroup_three_part_of_image d.action
        (centralizingFactor_le_left _ _) h7 hY9 (hc.image_card k)⟩
  have hAB : d.Yplus = centralizingFactor d.Y (d.action.plane i) ⊔
      centralizingFactor d.Y (d.action.plane j) := hY.trans
    (residual_plane_generation_of_images d.action hij h7 hY9 (hc.image_card i) (hc.image_card j))
  have hdirs := rankTwoShadow_residual_directions (yplus_perfect_of_choice d.choice)
    h9 (d.T.isPGroup'.to_le inf_le_left)
    (planeStabilizer_normalizes_yplus d.action d.T d.sylow_le 1 d.choice)
    hshadow (dir i) (dir j) hAB
  have hne := (rankTwoShadow_residual_directions (yplus_perfect_of_choice d.choice)
    h9 (d.T.isPGroup'.to_le inf_le_left)
    (planeStabilizer_normalizes_yplus d.action d.T d.sylow_le 1 d.choice)
    hshadow hL hC hgen).1
  rcases (hdirs.2 _).mp hL with hLi | hLj <;>
    rcases (hdirs.2 _).mp hC with hCi | hCj
  · exact (hne (hLi.trans hCi.symm)).elim
  · exact ⟨i, j, hij, hLi, hCj⟩
  · exact ⟨j, i, hij.symm, hLj, hCi⟩
  · exact (hne (hLj.trans hCj.symm)).elim

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree
end
