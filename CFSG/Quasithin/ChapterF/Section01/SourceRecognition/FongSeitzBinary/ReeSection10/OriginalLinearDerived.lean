module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.LinearLarge
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.OriginalCharts
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalDerivedRadical

/-!
# Original endpoint and quotient applications of the linear derived bounds

The marked equivalence of the original first endpoint two-core transports
its actual derived subgroup to [U_s₁,U_s₁]. This gives original witnesses
for the all-parameter graph from (10.5), the binary diagonal generator,
and the entire ordered T₁ product when q>2. Both endpoint inclusion squares and the literal original
Q.q formula retain the same graph parameters and derived witness. An
arbitrary marked amalgam is used, so geometric markings are also covered.

These results discharge the indicated p.222 derived-containment steps;
they do not construct the characteristic denominator, V₁, or the finite
presentation equations. The full binary model remains in the contract.
Source: Fong--Seitz II (1974), printed p.222, before (10.6).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory ReeF4
open scoped IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open MarkedLocal ReeSource
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

include c in
private theorem originalSylow_derived_lift (x : S)
    (hx : sylowMap Q e h x ∈ linearDerived Q split) :
    ∃ v : commutator (pCore 2 (parabolic L S 0)), (v.val.val : G) = x := by
  have hk := remainder_le_panelKernel_of_marking Q split 0 c.linear c.linearSylow c.linearBorel
    (ReeSource.linear_normalizer_index c.linearSylow)
  let v := (originalDerivedRadicalEquiv Q e split 0 hk).symm ⟨sylowMap Q e h x,hx⟩
  have hv : endpointMap Q e 0 v.val.val = sylowMap Q e h x :=
    congrArg Subtype.val ((originalDerivedRadicalEquiv Q e split 0 hk).apply_symm_apply _)
  refine ⟨v,?_⟩
  have he : v.val.val = (⟨x,(show S ≤ parabolic L S 0 from le_sup_right.trans le_sup_left)
      x.property⟩ : parabolic L S 0) := by
    apply (Endpoint Q 0).subtype_injective.comp (endpoint Q e 0).injective
    change endpointMap Q e 0 v.val.val = endpointMap Q e 0 _
    rw [endpoint_sylow Q e h]
    exact hv
  exact congrArg Subtype.val he

/-- The p.222 graph is realized in the derived subgroup of the original
first endpoint two-core, not merely in an abstract isomorphic group. -/
theorem original_linearDerived_graph (α : CoefficientField m) :
    ∃ β : CoefficientField m, ∃ v : commutator (pCore 2 (parabolic L S 0)),
      (v.val.val : G) =
        (originalPositivePoint Q e h split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 3) (α,0) : G)*
        originalPositivePoint Q e h split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 1) (β,0) := by
  obtain ⟨β,hβ⟩ := exists_linearDerived_graph Q split c α
  let x := originalPositivePoint Q e h split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 3) (α,0)*
    originalPositivePoint Q e h split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 1) (β,0)
  have hx : sylowMap Q e h x ∈ linearDerived Q split := by
    dsimp only [x]
    rw [map_mul,originalPositivePoint_image,originalPositivePoint_image]
    exact hβ
  obtain ⟨v,hv⟩ := originalSylow_derived_lift Q e h split c x hx
  exact ⟨β,v,hv⟩

/-- Every original shifted Suzuki point lies in that same derived subgroup
when q>2. The statement keeps the complete two-parameter root. -/
theorem original_shiftedSuzuki_in_linearDerived (hm : 0 < m) (a b : CoefficientField m) :
    ∃ v : commutator (pCore 2 (parabolic L S 0)),
      (v.val.val : G) = originalPositivePoint Q e h split c (RingEquiv.refl _) (.inr 3) (a,b) := by
  apply originalSylow_derived_lift Q e h split c
  rw [originalPositivePoint_image]
  exact shiftedSuzuki_le_linearDerived_of_pos Q split c hm
    (positiveChart Q split c (RingEquiv.refl _) (.inr 3) (a,b)).property

include h in
/-- Both ordered endpoint inclusions preserve the derived graph word. -/
theorem original_linearDerived_graph_endpoints (α : CoefficientField m) :
    ∃ β : CoefficientField m, ∃ v : commutator (pCore 2 (parabolic L S 0)),
      ∀ i : Fin 2, ∃ hi : (v.val.val : G) ∈ parabolic L S i,
        endpointMap Q e i ⟨(v.val.val : G),hi⟩ =
          positivePoint Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 3) (α,0)*
          positivePoint Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 1) (β,0) := by
  obtain ⟨β,v,hv⟩ := original_linearDerived_graph Q e h split c α
  refine ⟨β,v,fun i => ?_⟩
  let x := originalPositivePoint Q e h split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 3) (α,0)
  let y := originalPositivePoint Q e h split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 1) (β,0)
  have hi : (v.val.val : G) ∈ parabolic L S i := by
    rw [hv]
    exact (show S ≤ parabolic L S i from le_sup_right.trans le_sup_left) (S.mul_mem x.property y.property)
  refine ⟨hi,?_⟩
  have he : (⟨(v.val.val : G),hi⟩ : parabolic L S i) =
      ⟨x,(show S ≤ parabolic L S i from le_sup_right.trans le_sup_left) x.property⟩ *
      ⟨y,(show S ≤ parabolic L S i from le_sup_right.trans le_sup_left) y.property⟩ := Subtype.ext hv
  rw [he,map_mul]
  exact congrArg₂ (·*·) (originalPositivePoint_endpoint Q e h split (pinnedInput Q split c)
    (RingEquiv.refl _) i (.inr 3) (α,0))
    (originalPositivePoint_endpoint Q e h split (pinnedInput Q split c)
      (RingEquiv.refl _) i (.inr 1) (β,0))


/-- The binary diagonal generator is realized in the same original derived
radical with the corrected native Suzuki representatives. -/
theorem original_binary_linearDerived_diagonal (c₀ : ReeSixHData Q split n 0)
    (hn : ¬ positiveRoot Q split (.inr 3) ≤ linearDerived Q split) :
    ∃ v : commutator (pCore 2 (parabolic L S 0)),
      (v.val.val : G) =
        (originalPositivePoint Q e h split (pinnedInput Q split c₀) (RingEquiv.refl _) (.inr 1) (1,0) : G)*
        originalPositivePoint Q e h split (pinnedInput Q split c₀) (RingEquiv.refl _) (.inr 3) (1,0) := by
  apply originalSylow_derived_lift Q e h split c₀
    (originalPositivePoint Q e h split (pinnedInput Q split c₀) (RingEquiv.refl _) (.inr 1) (1,0)*
      originalPositivePoint Q e h split (pinnedInput Q split c₀) (RingEquiv.refl _) (.inr 3) (1,0))
  rw [map_mul,originalPositivePoint_image,originalPositivePoint_image]
  exact binary_linearDerived_source_diagonal Q split c₀ hn

/-- The literal five-factor T₁ product on printed p.222 has an original
derived-radical witness when q>2, with all seven field parameters retained. -/
theorem original_T1_product_in_linearDerived (hm : 0 < m)
    (a b₁ b₂ d e₁ e₂ f : CoefficientField m) :
    ∃ v : commutator (pCore 2 (parabolic L S 0)),
      (v.val.val : G) =
        (originalPositivePoint Q e h split c (RingEquiv.refl _) (.inl 2) a : G)*
        originalPositivePoint Q e h split c (RingEquiv.refl _) (.inr 1) (b₁,b₂)*
        originalPositivePoint Q e h split c (RingEquiv.refl _) (.inl 3) d*
        originalPositivePoint Q e h split c (RingEquiv.refl _) (.inr 3) (e₁,e₂)*
        originalPositivePoint Q e h split c (RingEquiv.refl _) (.inl 1) f := by
  apply originalSylow_derived_lift Q e h split c
    (originalPositivePoint Q e h split c (RingEquiv.refl _) (.inl 2) a*
      originalPositivePoint Q e h split c (RingEquiv.refl _) (.inr 1) (b₁,b₂)*
      originalPositivePoint Q e h split c (RingEquiv.refl _) (.inl 3) d*
      originalPositivePoint Q e h split c (RingEquiv.refl _) (.inr 3) (e₁,e₂)*
      originalPositivePoint Q e h split c (RingEquiv.refl _) (.inl 1) f)
  simp only [map_mul,originalPositivePoint_image]
  apply T1_le_linearDerived_of_pos Q split c hm
  apply (T1 Q split).mul_mem
  · apply (T1 Q split).mul_mem
    · apply (T1 Q split).mul_mem
      · apply (T1 Q split).mul_mem
        · exact (show positiveRoot Q split (.inl 2) ≤ T1 Q split from
            le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))
            (positiveChart Q split c (RingEquiv.refl _) (.inl 2) a).property
        · exact (show positiveRoot Q split (.inr 1) ≤ T1 Q split from
            le_sup_right.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))
            (positiveChart Q split c (RingEquiv.refl _) (.inr 1) (b₁,b₂)).property
      · exact (show positiveRoot Q split (.inl 3) ≤ T1 Q split from
          le_sup_right.trans (le_sup_left.trans le_sup_left))
          (positiveChart Q split c (RingEquiv.refl _) (.inl 3) d).property
    · exact (show positiveRoot Q split (.inr 3) ≤ T1 Q split from le_sup_right.trans le_sup_left)
        (positiveChart Q split c (RingEquiv.refl _) (.inr 3) (e₁,e₂)).property
  · exact (show positiveRoot Q split (.inl 1) ≤ T1 Q split from le_sup_right)
      (positiveChart Q split c (RingEquiv.refl _) (.inl 1) f).property

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory ReeF4
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open MarkedLocal
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (h : HypothesisF11 L S) (split : SplitData Q.tits)
  {n m : ℕ} (c : ReeSixHData Q split n m)

include h in
/-- The graph witness uses the literal original Q.q and its actual original
derived radical. This statement includes the binary field. -/
theorem original_linearDerived_graph_quotient (α : CoefficientField m) :
    ∃ β : CoefficientField m, ∃ v : commutator (pCore 2 (parabolic L S 0)),
      Q.q ⟨(v.val.val : G),parabolic_le_generated 0 v.val.val.property⟩ =
        positivePoint Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 3) (α,0)*
        positivePoint Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 1) (β,0) := by
  obtain ⟨β,v,hv⟩ := original_linearDerived_graph_endpoints Q (originalMarkedIso Q) h split c α
  obtain ⟨hi,he⟩ := hv 0
  exact ⟨β,v,(originalMarkedIso_left_apply Q _).symm.trans he⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
