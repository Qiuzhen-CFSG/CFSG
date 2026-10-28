module

public import CFSG.Quasithin.ChapterF.Section09.Intersections.Representative
public import CFSG.Quasithin.Chapter13.Section08.SourceDefs

/-!
# The chosen conjugator and centralizers in 13.7.10

The source chooses g with square one modulo the two-core before defining
D_H, D_(Hᵍ), E_H and E_(Hᵍ). F.9.6 therefore exchanges these literal
intersections in both directions. No exchange by an arbitrary representative
of the displaced point is used.

For 13.7.10(6), the order-two point V₁ᵍ is disjoint from U_H by (1).
F.9.6(3) bounds [D_H,U_Hᵍ] by that point and normalization bounds it by
U_H, so the commutator is trivial. Conjugating gives the other centralizer
containment. The earlier 13.7.3(7) commutator bound then gives both conclusions
of (6), again using the disjoint point for [D_H,A].

F.9.1 applicability, U_H≤O₂(LT) from 13.7.3(3), the bound from 13.7.3(7),
and the point escape in 13.7.10(1) remain their original earlier-source inputs.
Section 13.7's assembly owns their construction and the choice of g.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
13.7.9–10, printed pp.941–942.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section07.ConjugateIntersections
open ChapterF.Section09.Setup
variable {G : Type*} [Group G] [Finite G]

/-- The literal source groups shared with the Section 13.8 notation. -/
def sourceSetup (T : Sylow 2 G) (L V V₃ V₁ H : Subgroup G) :
    ChapterF.Section09.Setup G := ⟨T, L, V, V₃, V₁, H⟩

/-- The two displayed exchanges before 13.7.10, with the original quotient map. -/
theorem source_exchanges (T : Sylow 2 G) (L V V₃ V₁ H : Subgroup G)
    (h : (sourceSetup T L V V₃ V₁ H).Hypothesis)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g) ^ 2 = 1) :
    conjugate (Section08.Source.UH H V₃ ⊓ conjugate (Section08.Source.QH H) (g : G))
        (g : G) =
      conjugate (Section08.Source.UH H V₃) (g : G) ⊓ Section08.Source.QH H ∧
    conjugate (Section08.Source.VH H V ⊓ conjugate (Section08.Source.QH H) (g : G))
        (g : G) =
      conjugate (Section08.Source.VH H V) (g : G) ⊓ Section08.Source.QH H := by
  obtain ⟨hD, _, hE, _⟩ := h.intersection_exchange_of_core_quotient_square g hs
  exact ⟨hD, hE⟩

omit [Finite G] in
private theorem inf_eq_bot_of_card_two_of_not_le (A B : Subgroup G)
    (hc : Nat.card A = 2) (hn : ¬ A ≤ B) : A ⊓ B = ⊥ := by
  obtain ⟨a, _, ha⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hc
  apply eq_bot_iff.mpr
  intro x hx
  by_contra hx1
  have hxne : x ≠ 1 := by simpa only [mem_bot] using hx1
  have hax : (⟨x, hx.1⟩ : A) = a := ha _ (fun he => hxne (congrArg Subtype.val he))
  apply hn
  intro y hy
  by_cases hy1 : y = 1
  · exact hy1 ▸ B.one_mem
  · have hay := ha (⟨y, hy⟩ : A) (fun he => hy1 (congrArg Subtype.val he))
    have hxy : y = x := congrArg Subtype.val (hay.trans hax.symm)
    rw [hxy]
    exact hx.2

variable {D : ChapterF.Section09.Setup G}

/-- 13.7.10(1): the point-span equality forces escape because U_H is abelian
and V_H is nonabelian. The point-span input follows from the chosen nonorthogonal point. -/
theorem lemma_13_7_10_one (_h : D.Hypothesis) (g : G)
    (hspan : D.V ≤ D.Vplus ⊔ conjugate D.V₁ g)
    (hUabelian : IsMulCommutative D.UH) (hVnonabelian : ¬ IsMulCommutative D.VH) :
    ¬ conjugate D.V₁ g ≤ D.UH := by
  intro hp
  let : IsMulCommutative D.UH := hUabelian
  have hV : D.V ≤ D.UH :=
    hspan.trans (sup_le (le_conjugateSpanBy D.Vplus D.H) hp)
  have hVH : D.VH ≤ D.UH :=
    conjugateSpanBy_le hV (le_normalizer_conjugateSpanBy D.Vplus D.H)
  exact hVnonabelian (le_centralizer_iff_isMulCommutative.mp
    (hVH.trans ((le_centralizer D.UH).trans (centralizer_le hVH))))

/-- The chosen g preserves the global two-core, so its conjugate U_H lies in H. -/
theorem conjugate_UH_le_H (h : D.Hypothesis) (g : D.LT)
    (hU : D.UH ≤ D.LT.pCoreIn 2) : conjugate D.UH (g : G) ≤ D.H := by
  have hN : D.LT ≤ normalizer (D.LT.pCoreIn 2 : Set G) :=
    D.LT.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image D.LT (pCore 2 D.LT))
  have he : conjugate (D.LT.pCoreIn 2) (g : G) = D.LT.pCoreIn 2 :=
    mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (D.LT.pCoreIn 2 : Set G)).inv_mem (hN g.property))
  have hT : D.LT.pCoreIn 2 ≤ (D.T : Subgroup G) := by
    rw [← h.sylow_centralizer]
    exact inf_le_left
  exact (map_mono hU).trans (he.le.trans (hT.trans h.T_le_H))

/-- The centralizer step of 13.7.10(6), including its symmetry and both conclusions.
Here A is exactly V_Hᵍ∩O₂(LT). -/
theorem lemma_13_7_10_six (h : D.Hypothesis) (g : D.LT)
    (hs : (QuotientGroup.mk' (pCore 2 D.LT) g) ^ 2 = 1)
    (hU : D.UH ≤ D.LT.pCoreIn 2)
    (hpoint : ¬ conjugate D.V₁ (g : G) ≤ D.UH)
    (hHC : ⁅D.H ⊓ centralizer (D.UH : Set G), D.VH⁆ ≤ D.V₁) :
    ⁅D.DH (g : G), conjugate D.UH (g : G)⁆ = ⊥ ∧
    D.DHg (g : G) ≤ D.H ⊓ centralizer (D.UH : Set G) ∧
    ⁅D.DH (g : G), conjugate D.VH (g : G) ⊓ D.LT.pCoreIn 2⁆ = ⊥ ∧
    ⁅D.DHg (g : G), D.VH⁆ ≤ D.V₁ := by
  have hsq := h.square_mem_local_of_core_quotient_square g hs
  have hswap := h.intersection_exchange_of_core_quotient_square g hs
  have hUtwice := h.conjugate_twice_eq_of_square (A := D.UH)
    (le_normalizer_conjugateSpanBy D.Vplus D.H) hsq
  have hUgH := conjugate_UH_le_H h g hU
  have hpointCard : Nat.card (conjugate D.V₁ (g : G)) = 2 :=
    (Nat.card_congr (D.V₁.equivMapOfInjective (MulAut.conj (g : G)⁻¹).toMonoidHom
      (MulAut.conj (g : G)⁻¹).injective).symm.toEquiv).trans h.point_card
  have hdis := inf_eq_bot_of_card_two_of_not_le _ _ hpointCard hpoint
  have hnormal := le_normalizer_conjugateSpanBy D.Vplus D.H
  have hc : ⁅D.DH (g : G), conjugate D.UH (g : G)⁆ = ⊥ := by
    have hp := (commutator_mono
      (inf_le_inf_right _ (conjugateSpanBy_mono h.plus_le le_rfl)) le_rfl).trans
        (h.commutator_EH_conjugate_UH (g : G))
    have hu : ⁅D.DH (g : G), conjugate D.UH (g : G)⁆ ≤ D.UH :=
      (commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp (hUgH.trans hnormal))
    exact eq_bot_iff.mpr ((le_inf hp hu).trans hdis.le)
  have hcg : ⁅D.DHg (g : G), D.UH⁆ = ⊥ := by
    have hm := congrArg (fun A : Subgroup G => conjugate A (g : G)) hc
    change (⁅D.DH (g : G), conjugate D.UH (g : G)⁆).map
      (MulAut.conj (g : G)⁻¹).toMonoidHom =
      (⊥ : Subgroup G).map (MulAut.conj (g : G)⁻¹).toMonoidHom at hm
    rw [map_commutator, Subgroup.map_bot] at hm
    change ⁅conjugate (D.DH (g : G)) (g : G),
      conjugate (conjugate D.UH (g : G)) (g : G)⁆ = ⊥ at hm
    simpa only [hswap.1, hUtwice] using hm
  have hDHC : D.DHg (g : G) ≤ D.H ⊓ centralizer (D.UH : Set G) :=
    le_inf (inf_le_right.trans (pCoreIn_le 2 D.H))
      (commutator_eq_bot_iff_le_centralizer.mp hcg)
  have hlast := (commutator_mono hDHC le_rfl).trans hHC
  refine ⟨hc, hDHC, ?_, hlast⟩
  have hm := map_mono (f := (MulAut.conj (g : G)⁻¹).toMonoidHom) hlast
  rw [map_commutator] at hm
  change ⁅conjugate (D.DHg (g : G)) (g : G), conjugate D.VH (g : G)⁆ ≤
    conjugate D.V₁ (g : G) at hm
  rw [hswap.2.1] at hm
  have hp : ⁅D.DH (g : G), conjugate D.VH (g : G) ⊓ D.LT.pCoreIn 2⁆ ≤
      conjugate D.V₁ (g : G) := (commutator_mono le_rfl inf_le_left).trans hm
  have hA : conjugate D.VH (g : G) ⊓ D.LT.pCoreIn 2 ≤ D.H := by
    have hT : D.LT.pCoreIn 2 ≤ (D.T : Subgroup G) := by
      rw [← h.sylow_centralizer]
      exact inf_le_left
    exact inf_le_right.trans (hT.trans h.T_le_H)
  have hu : ⁅D.DH (g : G), conjugate D.VH (g : G) ⊓ D.LT.pCoreIn 2⁆ ≤ D.UH :=
    (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hA.trans hnormal))
  exact eq_bot_iff.mpr ((le_inf hp hu).trans hdis.le)

/-- The actual nonabelian-closure application: (1) supplies the escape used in (6).
The source's chosen quotient involution supplies the exchange; no separate
intersection equality or point-escape conclusion is assumed. -/
theorem source_centralizer_conclusions (h : D.Hypothesis) (g : D.LT)
    (hs : (QuotientGroup.mk' (pCore 2 D.LT) g) ^ 2 = 1)
    (hU : D.UH ≤ D.LT.pCoreIn 2)
    (hspan : D.V ≤ D.Vplus ⊔ conjugate D.V₁ (g : G))
    (hUabelian : IsMulCommutative D.UH) (hVnonabelian : ¬ IsMulCommutative D.VH)
    (hHC : ⁅D.H ⊓ centralizer (D.UH : Set G), D.VH⁆ ≤ D.V₁) :
    ¬ conjugate D.V₁ (g : G) ≤ D.UH ∧
    ⁅D.DH (g : G), conjugate D.UH (g : G)⁆ = ⊥ ∧
    D.DHg (g : G) ≤ D.H ⊓ centralizer (D.UH : Set G) ∧
    ⁅D.DH (g : G), conjugate D.VH (g : G) ⊓ D.LT.pCoreIn 2⁆ = ⊥ ∧
    ⁅D.DHg (g : G), D.VH⁆ ≤ D.V₁ := by
  have hp := lemma_13_7_10_one h (g : G) hspan hUabelian hVnonabelian
  exact ⟨hp, lemma_13_7_10_six h g hs hU hp hHC⟩

end CFSG.Quasithin.Chapter13.Section07.ConjugateIntersections
