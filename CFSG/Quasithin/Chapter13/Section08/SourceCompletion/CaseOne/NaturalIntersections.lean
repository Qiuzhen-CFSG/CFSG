module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.NaturalConjugates
public import CFSG.Quasithin.Chapter13.Section07.PairSeedComplement

/-!
# The two seed complements in the nonabelian-span branch

The nonorthogonal source conjugator has square in O₂(LT) and nontrivial
image of the conjugate U_H in H/O₂(H). The original seed-complement theorem
then identifies W₂ = V ∩ U_H ∩ U_Hˡ with V₃ ∩ V₃ˡ and gives its order four.
It complements V₁ in V₃. The spanning property of the chosen point and the
finite subgroup product formula also make it a complement to V₁ V₁ˡ in V.

The literal O²(C_{L₁}(V₁ V₁ˡ)) normalizes both seed spans and W₂: fixing
the two points puts it in both corresponding normalizers of U_H, and L₁
normalizes V. The final theorem constructs the conjugator, both complements,
and these actions together, retaining the nontrivial star image.

The full-denominator and nonabelian hypotheses are the contrary branch of
13.8.33. Cubic movement, the chief-factor contradiction, and the subsequent
Steinberg/permutation and 13.4.1 exclusions remain with
`qt-d-138-a6-endgame-source`; the earlier ordinary setup remains with
`qt-d-138-six-g2-source`. No strict denominator or chief count is assumed.
Source: Aschbacher--Smith, Lemma 13.8.33, printed p.966, using 13.7.10(9).
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open CriticalGeometry TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
/-- The source O²(C_{L₁}(V₁ V₁ˡ)) acts on both seed spans and their
intersection in V. The residual and conjugation maps are literal. -/
theorem pair_residual_normalizes
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁) (hH : H = G₁) (l : L) :
    let U := Source.UH H V₃
    let X := residual (sourceOne L T V₁ ⊓ centralizer ((V₁ ⊔ V₁.conjBy (l : G) : Subgroup G) : Set G))
    X ≤ normalizer (U : Set G) ∧
      X ≤ normalizer (U.conjBy (l : G) : Set G) ∧
      X ≤ normalizer ((V ⊓ U ⊓ U.conjBy (l : G) : Subgroup G) : Set G) := by
  dsimp only
  let U := Source.UH H V₃
  let P := V₁.conjBy (l : G)
  let X := residual (sourceOne L T V₁ ⊓ centralizer ((V₁ ⊔ P : Subgroup G) : Set G))
  have hpoint : normalizer (V₁ : Set G) ≤ normalizer (U : Set G) := by
    rw [← d.first_normalizer, ← hH]
    exact le_normalizer_conjugateSpanBy V₃ H
  have hconj : normalizer (P : Set G) ≤ normalizer (U.conjBy (l : G) : Set G) := by
    change normalizer (V₁.map (MulAut.conj (l : G)).toMonoidHom : Set G) ≤
      normalizer (U.map (MulAut.conj (l : G)).toMonoidHom : Set G)
    rw [← map_equiv_normalizer_eq, ← map_equiv_normalizer_eq]
    exact map_mono hpoint
  have hXL : X ≤ L ⊔ (T : Subgroup G) :=
    (residual_le _).trans (inf_le_left.trans ((one_le _ _ _).trans inf_le_left))
  have hXc : X ≤ centralizer ((V₁ ⊔ P : Subgroup G) : Set G) := (residual_le _).trans inf_le_right
  have hXu : X ≤ normalizer (U : Set G) :=
    (hXc.trans (centralizer_le (show V₁ ≤ V₁ ⊔ P from le_sup_left))).trans
      ((Subgroup.centralizer_le_normalizer _).trans hpoint)
  have hXug : X ≤ normalizer (U.conjBy (l : G) : Set G) :=
    (hXc.trans (centralizer_le (show P ≤ V₁ ⊔ P from le_sup_right))).trans
      ((Subgroup.centralizer_le_normalizer _).trans hconj)
  exact ⟨hXu, hXug, (le_inf
    ((le_inf (hXL.trans d.normalizes_V) hXu).trans inf_normalizer_le_normalizer_inf)
    hXug).trans inf_normalizer_le_normalizer_inf⟩


/-- The actual W₂ is the intersection of the seed hyperplanes. It complements
V₁ in V₃ and the two-point span in V. The selected conjugator retains
nontrivial star action, and the literal point-pair residual acts on both
seed spans and W₂. -/
theorem exists_nonabelian_seed_intersection
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hn : ¬ IsMulCommutative (Source.UL L H V₃)) :
    ∃ l : L,
      (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
        (inclusion le_sup_left l)) ^ 2 = 1 ∧
      V ≤ V₃ ⊔ V₁.conjBy (l : G) ∧
      ¬ V₁.conjBy (l : G) ≤ V₃ ∧
      (Source.UH H V₃).conjBy (l : G) ≤ H ∧
      Source.starImage H ((Source.UH H V₃).conjBy (l : G)) ≠ ⊥ ∧
      let W := V ⊓ Source.UH H V₃ ⊓ (Source.UH H V₃).conjBy (l : G)
      Disjoint V₁ W ∧ V₁ ⊔ W = V₃ ∧ Nat.card W = 4 ∧
        W = V₃ ⊓ V₃.conjBy (l : G) ∧
        Disjoint (V₁ ⊔ V₁.conjBy (l : G)) W ∧
        (V₁ ⊔ V₁.conjBy (l : G)) ⊔ W = V ∧
        let X := residual (sourceOne L T V₁ ⊓ centralizer ((V₁ ⊔ V₁.conjBy (l : G) : Subgroup G) : Set G))
        X ≤ normalizer (Source.UH H V₃ : Set G) ∧
          X ≤ normalizer ((Source.UH H V₃).conjBy (l : G) : Set G) ∧
          X ≤ normalizer (W : Set G) := by
  obtain ⟨l, hs, hspan, hout, hlH, hstar⟩ :=
    exists_nonorthogonal_involutive_star d hF9 c hH hDH hDg hcentral hn
  have hi := seed_intersection d hF9 c hDH hDg
  have hPV : V₁ ≤ V := d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)
  have hconjV : V₁.conjBy (l : G) ≤ V := by
    have he : V.conjBy (l : G) = V :=
      mem_normalizer_iff_map_conj_eq.mp (d.normalizes_V (mem_sup_left l.property))
    exact (map_mono hPV).trans he.le
  have hnot : ¬ V₁.conjBy (l : G) ≤ Source.UH H V₃ := by
    intro hu
    exact hout ((le_inf hconjV hu).trans hi.le)
  let g : (L ⊔ (T : Subgroup G) : Subgroup G) := inclusion le_sup_left l⁻¹
  have hgsq : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1 := by
    change (QuotientGroup.mk' _ (inclusion le_sup_left l⁻¹))^2 = 1
    rw [map_inv, map_inv, inv_pow, hs, inv_one]
  have hgout : ¬ ChapterF.Section09.Setup.conjugate V₁ (g : G) ≤ Source.UH H V₃ := by
    simpa only [ChapterF.Section09.Setup.conjugate, ChapterG.Section02.Setup.conjugate,
      Subgroup.conjBy, g, Subgroup.coe_inclusion, Subgroup.coe_inv,
      inv_inv] using hnot
  have hw := Section07.pair_seed_complement (localNaturalSetup d) hF9
    (show IsMulCommutative (Source.UH H V₃) from inferInstance) g hgsq hgout
  have hw' : Disjoint V₁ ((Source.UH H V₃).conjBy (l : G) ⊓ V₃) ∧
      V₁ ⊔ ((Source.UH H V₃).conjBy (l : G) ⊓ V₃) = V₃ ∧
      Nat.card ((Source.UH H V₃).conjBy (l : G) ⊓ V₃ : Subgroup G) = 4 ∧
      (Source.UH H V₃).conjBy (l : G) ⊓ V₃ = V₃.conjBy (l : G) ⊓ V₃ := by
    simp only [ChapterF.Section09.Setup.conjugate, ChapterG.Section02.Setup.conjugate,
      g, Subgroup.coe_inclusion, Subgroup.coe_inv, inv_inv] at hw
    exact ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1⟩
  let W := (Source.UH H V₃).conjBy (l : G) ⊓ V₃
  let P := V₁.conjBy (l : G)
  have hWV : W ≤ V := inf_le_right.trans d.seed_le
  have hBV : V₁ ⊔ P ≤ V := sup_le hPV hconjV
  have hj : (V₁ ⊔ P) ⊔ W = V := by
    calc
      (V₁ ⊔ P) ⊔ W = (V₁ ⊔ W) ⊔ P := by ac_rfl
      _ = V₃ ⊔ P := by rw [hw'.2.1]
      _ = V := le_antisymm (sup_le d.seed_le hconjV) hspan
  let : IsMulCommutative V := (Section07.NaturalAction.elementary (localNaturalSetup d)).toIsMulCommutative
  have norm (A B : Subgroup G) (hA : A ≤ V) (hB : B ≤ V) :
      B ≤ normalizer (A : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro b hb a ha
    exact congrArg Subtype.val (mul_comm (⟨a, hA ha⟩ : V) ⟨b, hB hb⟩)
  have hPcard : Nat.card P = 2 :=
    (card_map_of_injective (MulAut.conj (l : G)).injective).trans d.line_card
  have hm := card_mul_eq_card_inf_mul_card_sup_of_normalizes V₁ P (norm V₁ P hPV hconjV)
  rw [d.line_card, hPcard] at hm
  have hBc : Nat.card (V₁ ⊔ P : Subgroup G) ≤ 4 := by
    apply Nat.le_of_dvd (by decide : 0 < 4)
    exact ⟨Nat.card (V₁ ⊓ P : Subgroup G), by nlinarith [hm]⟩
  have hVc : Nat.card V = 16 := by
    calc
      Nat.card V = Nat.card (BinaryPermutation.natural (Fin 6)) := Nat.card_congr d.coordinate.toEquiv
      _ = 16 := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
          BinaryPermutation.finrank_natural_even (Fin 6) (by decide), Fintype.card_fin]
        norm_num
  have hmW := card_mul_eq_card_inf_mul_card_sup_of_normalizes (V₁ ⊔ P) W
    (norm (V₁ ⊔ P) W hBV hWV)
  rw [hw'.2.2.1, hj, hVc] at hmW
  have hIc : Nat.card ((V₁ ⊔ P) ⊓ W : Subgroup G) = 1 := by
    have hpos : 0 < Nat.card ((V₁ ⊔ P) ⊓ W : Subgroup G) := Nat.card_pos
    nlinarith
  have hd : Disjoint (V₁ ⊔ P) W := disjoint_iff.mpr (eq_bot_of_card_eq _ hIc)
  have hX := pair_residual_normalizes d hH l
  dsimp only at hX
  rw [hi, inf_comm V₃ ((Source.UH H V₃).conjBy (l : G))] at hX
  refine ⟨l, hs, hspan, hout, hlH, hstar, ?_⟩
  dsimp only
  rw [hi, inf_comm V₃ ((Source.UH H V₃).conjBy (l : G))]
  exact ⟨hw'.1, hw'.2.1, hw'.2.2.1, hw'.2.2.2.trans (inf_comm _ _), hd, hj, hX⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
