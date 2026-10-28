module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.Pair
public import Theory.GroupTheory.AlmostSpecialIntersection
public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# The literal denominator of the opposite-core quotient

The preceding Frattini bound gives [W∩Wʸ,I]≤V. Hence N=(W∩Wʸ)V
is an I-invariant two-group. The complementary point/three-space
geometry puts V inside I, and its two summands inside the two generators
of Q. It follows that N≤Q, with normality in I and in Q. Conjugation
therefore defines an action on the literal quotient Q/(N.subgroupOf Q).
Only the upper Frattini bound is used, also in the abelian W=U branch.
Source: Aschbacher--Smith 11.5.7, printed p.783.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

omit [Finite G] in
private theorem normalizes_join (A B C : Subgroup G)
    (hAC : A ≤ normalizer (C : Set G)) (hAB : ⁅A,B⁆ ≤ C) :
    A ≤ normalizer ((B ⊔ C : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro a ha x hx
  have h : B ⊔ C ≤ (B ⊔ C).comap (MulAut.conj a).toMonoidHom := by
    apply sup_le
    · intro b hb
      have hh := (B ⊔ C).mul_mem
        (mem_sup_right (hAB (commutator_mem_commutator ha hb))) (mem_sup_left hb)
      change a * b * a⁻¹ ∈ B ⊔ C
      simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hh
    · intro c hc
      exact mem_sup_right (le_normalizer_iff.mp hAC a ha c hc)
  exact h hx

/-- V₃ lies in either choice of the source temporary W. -/
theorem threeSpace_le_auxiliaryW : E.V₃ ≤ auxiliaryW E := by
  classical
  unfold auxiliaryW
  split
  · exact (D.centralQuotientPreimage_le _).trans (le_conjugateSpanBy V E.G₁)
  · exact le_conjugateSpanBy E.V₃ E.G₁

/-- The complementary natural subspaces put the original V in the actual join. -/
theorem seed_le_oppositeJoin (m : MarkedFlag E) (y : G)
    (hsplit : V = E.V₃ ⊔ E.V₁.map (MulAut.conj y).toMonoidHom) :
    V ≤ oppositeJoin (auxiliaryW E) y := by
  apply hsplit.le.trans
  exact sup_le ((threeSpace_le_auxiliaryW E).trans le_sup_left)
    ((map_mono (m.point_lt_threeSpace.le.trans (threeSpace_le_auxiliaryW E))).trans
      le_sup_right)

/-- The ambient Sylow normalization descends to both opposite generators. -/
theorem oppositeJoin_normalizes_seed (m : MarkedFlag E) {y : G} (hy : y ∈ L)
    (hW : E.W ≤ E.G₁.pCoreIn 2) :
    oppositeJoin (auxiliaryW E) y ≤ normalizer (V : Set G) := by
  have hT : E.G₁.pCoreIn 2 ≤ T := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le m.sylow_le_point_normalizer] using
      pCoreIn_le_sylow E.G₁ (T.subtype m.sylow_le_point_normalizer)
  have hn : auxiliaryW E ≤ normalizer (V : Set G) :=
    ((auxiliaryW_le_W E).trans hW).trans (hT.trans E.input.sylow_normalizes)
  apply sup_le hn
  have hyv : V.map (MulAut.conj y).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp (D.normalizes hy)
  simpa only [hyv] using (map_mono (f := (MulAut.conj y).toMonoidHom) hn).trans (V.le_normalizer_map _)

/-- The intersection is central modulo V, with only Φ(W)≤V₁. -/
theorem intersection_commutator_le_seed (m : MarkedFlag E) {y : G} (hy : y ∈ L)
    (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hPhi : (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁) :
    ⁅auxiliaryW E ⊓ (auxiliaryW E).map (MulAut.conj y).toMonoidHom,
      oppositeJoin (auxiliaryW E) y⁆ ≤ V := by
  have hp : IsPGroup 2 (auxiliaryW E) :=
    (isPGroup_pCoreIn 2 E.G₁).to_le ((auxiliaryW_le_W E).trans hW)
  have hd := derived_le_of_frattini_image_le hp hPhi
  have hyV : E.V₁.map (MulAut.conj y).toMonoidHom ≤ V := by
    have he := mem_normalizer_iff_map_conj_eq.mp (D.normalizes hy)
    exact (map_mono (f := (MulAut.conj y).toMonoidHom) E.V₁_le).trans he.le
  apply intersection_commutator_sup_le (hd.trans E.V₁_le) _
    (oppositeJoin_normalizes_seed E m hy hW)
  rw [← map_commutator]
  exact (map_mono hd).trans hyV

/-- Relative normality of the denominator is proved before forming the quotient. -/
theorem oppositeJoin_normalizes_denominator (m : MarkedFlag E) {y : G} (hy : y ∈ L)
    (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hPhi : (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁) :
    oppositeJoin (auxiliaryW E) y ≤ normalizer (pairDenominator E y : Set G) := by
  apply normalizes_join _ _ _ (oppositeJoin_normalizes_seed E m hy hW)
  rw [commutator_comm]
  exact intersection_commutator_le_seed E m hy hW hPhi

/-- The denominator is an invariant two-subgroup of I, hence lies in O₂(I). -/
theorem denominator_le_opposite_core (m : MarkedFlag E) {y : G} (hy : y ∈ L)
    (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hPhi : (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁)
    (hsplit : V = E.V₃ ⊔ E.V₁.map (MulAut.conj y).toMonoidHom) :
    pairDenominator E y ≤ (oppositeJoin (auxiliaryW E) y).pCoreIn 2 := by
  have hp : IsPGroup 2 (auxiliaryW E) :=
    (isPGroup_pCoreIn 2 E.G₁).to_le ((auxiliaryW_le_W E).trans hW)
  have hJ : IsPGroup 2 (auxiliaryW E ⊓
      (auxiliaryW E).map (MulAut.conj y).toMonoidHom : Subgroup G) := hp.to_le inf_le_left
  have hN : IsPGroup 2 (pairDenominator E y) := by
    rw [pairDenominator, sup_comm]
    exact (@IsElementaryAbelian.isPGroup 2 _ _ D.elementary).to_sup_of_normal_left' hJ
      ((inf_le_left.trans le_sup_left).trans (oppositeJoin_normalizes_seed E m hy hW))
  exact le_pCoreIn_of_normalizes hN
    (sup_le (inf_le_left.trans le_sup_left) (seed_le_oppositeJoin E m y hsplit))
    (oppositeJoin_normalizes_denominator E m hy hW hPhi)

/-- Both natural subspaces of V occur in the literal two core intersections. -/
theorem denominator_le_corePair (m : MarkedFlag E) {y : G} (hy : y ∈ L)
    (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hPhi : (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁)
    (hsplit : V = E.V₃ ⊔ E.V₁.map (MulAut.conj y).toMonoidHom) :
    pairDenominator E y ≤ corePair (auxiliaryW E) y := by
  have hN := denominator_le_opposite_core E m hy hW hPhi hsplit
  have hV : V ≤ (oppositeJoin (auxiliaryW E) y).pCoreIn 2 := le_sup_right.trans hN
  apply sup_le
  · exact (le_inf inf_le_left (le_sup_left.trans hN)).trans le_sup_left
  · apply hsplit.le.trans
    exact sup_le
      ((le_inf (threeSpace_le_auxiliaryW E)
        ((D.centralQuotientPreimage_le _).trans hV)).trans le_sup_left)
      ((le_inf (map_mono (m.point_lt_threeSpace.le.trans (threeSpace_le_auxiliaryW E)))
        ((show E.V₁.map (MulAut.conj y).toMonoidHom ≤ V from
          le_sup_right.trans hsplit.ge).trans hV)).trans le_sup_right)

/-- Normality in Q uses its actual inclusion in I, without ambient normality. -/
theorem denominator_normal_in_corePair (m : MarkedFlag E) {y : G} (hy : y ∈ L)
    (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hPhi : (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁) :
    ((pairDenominator E y).subgroupOf (corePair (auxiliaryW E) y)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  apply le_trans _ (oppositeJoin_normalizes_denominator E m hy hW hPhi)
  exact sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)

/-- The literal quotient with its original induced I-action and representative formula. -/
theorem exists_induced_action (m : MarkedFlag E) {y : G} (hy : y ∈ L)
    (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hPhi : (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁)
    (hcore : (oppositeJoin (auxiliaryW E) y).pCoreIn 2 ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    let I := oppositeJoin (auxiliaryW E) y
    let Q := corePair (auxiliaryW E) y
    let N := pairDenominator E y
    let _ := denominator_normal_in_corePair E m hy hW hPhi
    ∃ ρ : I →* MulAut (Q ⧸ N.subgroupOf Q),
      ∀ i : I, ∀ q : Q, ∀ hq : (i : G) * (q : G) * (i : G)⁻¹ ∈ Q,
        ρ i (QuotientGroup.mk' (N.subgroupOf Q) q) =
          QuotientGroup.mk' (N.subgroupOf Q) ⟨(i : G) * (q : G) * (i : G)⁻¹, hq⟩ := by
  have hp := source_corePair_properties E m hy hcore
  have hIQ := (normal_subgroupOf_iff_le_normalizer
    (hp.1.trans (pCoreIn_le 2 _))).mp hp.2.1
  obtain ⟨ρ,hρ⟩ := exists_quotient_conjugation_action _ _ _ hIQ
    (oppositeJoin_normalizes_denominator E m hy hW hPhi)
    (denominator_normal_in_corePair E m hy hW hPhi)
  exact ⟨ρ, fun i q _ => hρ i q⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
