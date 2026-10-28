module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.NaturalMovement
public import Theory.GroupTheory.PResidual.Restriction

/-!
# Symmetry of the actual seed pair and its residual

For a two-point span P, O²(C_{L₁}(P)) equals O²(C_{LT}(P)).
This follows by restriction to a subgroup containing the two-residual,
and removes the dependence on which point defines the first parabolic.
The chosen conjugator squares into O₂(LT), which centralizes V and lies
in H. It consequently swaps the two seed spans, fixes their intersection,
and normalizes this same literal point-pair residual.

The final application combines these identities with the constructed
nonabelian source pair and its full W₂ movement. It retains the actual
star image, complements and whole seed spans. The subsequent quotient
irreducibility, star/core identities and chief-factor exclusion remain
with `qt-d-138-a6-endgame-source`; earlier ordinary setup remains with
`qt-d-138-six-g2-source`.
Source: Aschbacher--Smith, Lemma 13.8.33, printed p.966, the transport
from U_H V/V to U_Hˡ V/V before identifying the star image.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The point-pair residual can be taken in LT before selecting either
point parabolic. This preserves the intrinsic two-residual convention. -/
theorem pair_residual_eq_local_centralizer (P : Subgroup G) (hline : V₁ ≤ P) :
    residual (sourceOne L T V₁ ⊓ centralizer (P : Set G)) =
      residual ((L ⊔ (T : Subgroup G)) ⊓ centralizer (P : Set G)) := by
  apply embedded_pResidual_eq_of_le_of_residual_le 2
    (inf_le_inf_right _ ((one_le _ _ _).trans inf_le_left))
  apply le_inf
  · apply embedded_pResidual_mono 2
    exact le_inf inf_le_left ((inf_le_right.trans (centralizer_le hline)).trans
      (Subgroup.centralizer_le_normalizer _))
  · exact (residual_le _).trans inf_le_right

/-- Squaring into the original local two-core exchanges the two seed spans
and fixes their intersection and the actual point-pair residual. -/
theorem involutive_seed_pair_exchange
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (l : L)
    (hs : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
      (inclusion le_sup_left l)) ^ 2 = 1) :
    let U := Source.UH H V₃
    let W := V ⊓ U ⊓ U.conjBy (l : G)
    let X := residual (sourceOne L T V₁ ⊓
      centralizer ((V₁ ⊔ V₁.conjBy (l : G) : Subgroup G) : Set G))
    (U.conjBy (l : G)).conjBy (l : G) = U ∧
      W.conjBy (l : G) = W ∧ X.conjBy (l : G) = X := by
  dsimp only
  let K := L ⊔ (T : Subgroup G)
  let U := Source.UH H V₃
  let P := V₁ ⊔ V₁.conjBy (l : G)
  have hsq : (l : G) ^ 2 ∈ K.pCoreIn 2 := by
    have hh : (inclusion (show L ≤ K from le_sup_left) l) ^ 2 ∈ pCore 2 K := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (pCore 2 K) ((inclusion le_sup_left l) ^ 2) = 1
      rwa [map_pow]
    exact mem_map_of_mem K.subtype hh
  have hQ : K.pCoreIn 2 ≤ (T : Subgroup G) ⊓ centralizer (V : Set G) :=
    hF9.sylow_centralizer.symm.le
  have hlineV : V₁ ≤ V := d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)
  have hPP : (V₁.conjBy (l : G)).conjBy (l : G) = V₁ := by
    rw [conjBy_conjBy, ← pow_two]
    exact mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.centralizer_le_normalizer _) (centralizer_le hlineV (hQ hsq).2))
  have hUU : (U.conjBy (l : G)).conjBy (l : G) = U := by
    rw [conjBy_conjBy, ← pow_two]
    exact mem_normalizer_iff_map_conj_eq.mp
      (le_normalizer_conjugateSpanBy V₃ H (hF9.T_le_H (hQ hsq).1))
  have hV : V.conjBy (l : G) = V :=
    mem_normalizer_iff_map_conj_eq.mp (d.normalizes_V (mem_sup_left l.property))
  have hP : P.conjBy (l : G) = P := by
    change (V₁ ⊔ V₁.conjBy (l : G)).map (MulAut.conj (l : G)).toMonoidHom = _
    rw [Subgroup.map_sup]
    change V₁.conjBy (l : G) ⊔ (V₁.conjBy (l : G)).conjBy (l : G) = P
    rw [hPP, sup_comm]
  refine ⟨hUU, ?_, ?_⟩
  · change ((V ⊓ U) ⊓ U.conjBy (l : G)).map (MulAut.conj (l : G)).toMonoidHom = _
    rw [map_inf _ _ _ (MulAut.conj (l : G)).injective,
      map_inf _ _ _ (MulAut.conj (l : G)).injective]
    change V.conjBy (l : G) ⊓ U.conjBy (l : G) ⊓ (U.conjBy (l : G)).conjBy (l : G) = _
    rw [hV, hUU]
    ac_rfl
  · rw [pair_residual_eq_local_centralizer P le_sup_left]
    apply mem_normalizer_iff_map_conj_eq.mp
    apply normalizer_le_residual_normalizer
    apply inf_normalizer_le_normalizer_inf
    exact ⟨K.le_normalizer (mem_sup_left l.property),
      normalizer_le_normalizer_centralizer P (mem_normalizer_iff_map_conj_eq.mpr hP)⟩

/-- The nonabelian contrary branch supplies a symmetric pair with full
W₂ movement and nontrivial literal star image. No cubic lift, symmetry,
normality or displacement is left as an extra source premise. -/
theorem exists_nonabelian_symmetric_movement
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hn : ¬ IsMulCommutative (Source.UL L H V₃)) :
    ∃ l : L,
      (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
        (inclusion le_sup_left l)) ^ 2 = 1 ∧
      ¬ V₁.conjBy (l : G) ≤ V₃ ∧
      (Source.UH H V₃).conjBy (l : G) ≤ H ∧
      Source.starImage H ((Source.UH H V₃).conjBy (l : G)) ≠ ⊥ ∧
      let U := Source.UH H V₃
      let W := V ⊓ U ⊓ U.conjBy (l : G)
      let X := residual (sourceOne L T V₁ ⊓
        centralizer ((V₁ ⊔ V₁.conjBy (l : G) : Subgroup G) : Set G))
      Disjoint V₁ W ∧ V₁ ⊔ W = V₃ ∧ Nat.card W = 4 ∧
        W = V₃ ⊓ V₃.conjBy (l : G) ∧
        Disjoint (V₁ ⊔ V₁.conjBy (l : G)) W ∧
        (V₁ ⊔ V₁.conjBy (l : G)) ⊔ W = V ∧
        X ≤ normalizer (U : Set G) ∧
        X ≤ normalizer (U.conjBy (l : G) : Set G) ∧
        X ≤ normalizer (W : Set G) ∧ ⁅W, X⁆ = W ∧
        (U.conjBy (l : G)).conjBy (l : G) = U ∧
        W.conjBy (l : G) = W ∧ X.conjBy (l : G) = X := by
  obtain ⟨l, hs, _, hout, hUH, hstar, hW⟩ :=
    exists_nonabelian_seed_movement d hF9 c hH hDH hDg hcentral hn
  dsimp only at hW ⊢
  obtain ⟨hU, hWi, hXi⟩ := involutive_seed_pair_exchange d hF9 l hs
  refine ⟨l, hs, hout, hUH, hstar, hW.1, hW.2.1, hW.2.2.1,
    hW.2.2.2.1, hW.2.2.2.2.1, hW.2.2.2.2.2.1,
    hW.2.2.2.2.2.2.1, hW.2.2.2.2.2.2.2.1,
    hW.2.2.2.2.2.2.2.2.1, hW.2.2.2.2.2.2.2.2.2, hU, hWi, hXi⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
