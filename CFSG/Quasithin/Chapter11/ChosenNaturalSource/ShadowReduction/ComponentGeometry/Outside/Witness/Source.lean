module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Witness.NormalSection
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Witness.OddExtension
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Prime

/-!
# The original outside R₁-Sylow witness and conditional G₂ exclusion

In the equality row, retain the constructed subgroup R₁O²(H), its escape
and its actual Sylow subgroup. The normal-section weak-closure argument
supplies its generation-one bound using precisely the earlier 11.2.2
clauses. The odd-extension row reuses the proved O₂,₂′(K) construction,
including every permitted primary kernel and nonsplit extension.

For the prime PSL₂ row, component minimality shows that K escapes M
unless K=L₁. The proved radical containment then gives R₁=O₂(KT), so
normalization of W₀(R₁,V) excludes this last row. We thus construct the
original selected H and OutsideRadicalWitness on the unchanged field flag.
The completed E.3.19 consumer supplies the final conditional contradiction.

All preceding source inputs remain explicit: the surviving list and earlier
geometry, full 11.3.2, Kz=K, and the literal 11.2.2 weak-closure clauses.
Their producers are qt-d-1222-natural-local-geometry,
qt-d-1222-shadow-linear-geometry, qt-d-1222-shadow-component-triangle and
qt-d-1222-shadow-component-comparison. OddKernelNormalizer remains with
qt-d-1222-natural-odd-kernel-normalizer. The parent
qt-d-1222-shadow-components owns their discharge. This does not assert
unconditional G₂ exclusion or the universal strict-component 11.4.4 bound.

Source: Aschbacher--Smith, 11.4.3--11.5.1, printed pp.778--779.
-/

public noncomputable section
open Subgroup Theory.GroupTheory CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside
open NormalSection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)

/-- If the component lies in M, minimality of the actual C-component
identifies it with the perfect first residual. -/
theorem ofFlag_component_eq_of_le_normalizer
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hKM : (ofFlag S f X z H).K ≤ normalizer (L : Set G)) :
    (ofFlag S f X z H).K = (ofFlag S f X z H).L₁ := by
  let E := ofFlag S f X z H
  have hAK : f.Li 0 ≤ E.K := le_conjugateSpanBy _ _
  have htop : (⊤ : Subgroup E.K).IsCComponent := by
    simpa only [subgroupOf_self] using
      h.line_component.2.subgroupOf_of_le le_rfl h.line_component.1
  have hlocal := Triangle.Reselection.flag_residual_mem_local D S f 0
  have hne : f.Li 0 ≠ ⊥ := by
    intro heq
    apply hlocal.1.ne_bot
    rw [heq, bot_subgroupOf]
  let A := (f.Li 0).subgroupOf E.K
  have hAne : A ≠ ⊥ := by
    intro heq
    apply hne
    simpa only [A,map_subgroupOf_eq_of_le hAK,Subgroup.map_bot] using
      congrArg (map E.K.subtype) heq
  let : Group.IsPerfect (f.Li 0) := LocalGeometry.localResidual_perfect _
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hAK).symm.toMonoidHom)
    (subgroupOfEquivOfLe hAK).symm.surjective
  have hn : E.K ≤ normalizer (f.Li 0 : Set G) :=
    (le_inf hKM E.K_le_G₁).trans
      Comparison.EarlierGeometry.line_stabilizer_normalizes_seed
  let : A.Normal := normal_subgroupOf_of_le_normalizer hn
  have ht : (⊤ : Subgroup E.K) ≤ A :=
    htop.minimal A le_top hAne inferInstance (inferInstance : A.Normal).isSubnormal
  exact le_antisymm (fun k hk => ht (show (⟨k,hk⟩ : E.K) ∈ ⊤ from mem_top _)) hAK

/-- The original outside R₁-Sylow witness for every surviving source row,
with the literal smaller carrier and both generation parameters equal to one.
Only earlier geometry, its G₂ weak-closure clauses and OddKernelNormalizer remain. -/
theorem ofFlag_surviving_selected_radical_witness
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hs : (1 : ℕ∞) < @globalS G _ V D.elementary)
    (hC : centralizer (weakCentralizer V (f.Ri 0) 1 : Set G) ≤ normalizer (L : Set G))
    (hN : normalizer (indexedWeakClosure V (f.Ri 0) 0 : Set G) ≤ normalizer (L : Set G)) :
    ∃ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      J ≤ Gz (ofFlag S f X z J) ∧ SelectedResidualAlternative (ofFlag S f X z J) ∧
      generationParameter J = 1 ∧
      ∃ w : OutsideRadicalWitness (ofFlag S f X z J),
        w.H₁ = (ofFlag S f X z J).R₁ ⊔ (pResidual 2 J).map J.subtype := by
  let E := ofFlag S f X z H
  by_cases hK : E.K = E.L₁
  · obtain ⟨J,hJ,hJz,hsel,hn,hinside,hout,hSyl,_⟩ :=
      Generation.ofFlag_equal_selected_generation_one S f X z H h he hK hNT hlinear h1132 hcontrol
    have h' : Comparison.EarlierGeometry (ofFlag S f X z J) :=
      ⟨h.point_mem,h.point_fixed,h.point_ne_one,h.seed_centralizes,
        h.line_component,h.point_component,h.normalizer_split⟩
    have hn₁ := ofFlag_equal_carrier_generation_one S f X z J h' he hK hlinear h1132
      hcontrol hJ hJz hsel hs hC hN
    obtain ⟨P,hP⟩ := hSyl
    exact ⟨J,hJ,hJz,hsel,hn,⟨_,P,hP,hinside,hout,hn₁⟩,rfl⟩
  have hout : ¬ E.K ≤ E.M := fun hKM => hK (ofFlag_component_eq_of_le_normalizer S f X z H h hKM)
  have hAK : f.Li 0 ≤ E.K := le_conjugateSpanBy _ _
  have hA : f.Li 0 ≠ ⊥ := by
    intro hbot
    have hlocal := Triangle.Reselection.flag_residual_mem_local D S f 0
    apply hlocal.1.ne_bot
    rw [hbot,bot_subgroupOf]
  have hKc : Source.NormalComponentIn (centralizer (f.Vi 0 : Set G)) E.K :=
    ⟨⟨h.line_component_centralizes,h.line_component.2.subgroupOf_of_le
      h.line_component_centralizes (Subgroup.centralizer_le_normalizer _)⟩,
      normal_subgroupOf_of_le_normalizer
        ((Subgroup.centralizer_le_normalizer _).trans E.G₁_normalizes_K)⟩
  have hR := Radical.ofFlag_surviving_radical_containment S f X z H E.K hKc hA hAK
    ((f.invariant 0).trans E.G₁_normalizes_K) hcase
  cases hcase with
  | equal heq => exact (hK heq.symm).elim
  | sl2Prime _ hn p hp hm =>
    obtain ⟨J,hJ,hJz,hsel,hgen,w,hw,_⟩ :=
      ofFlag_odd_selected_radical_witness S f X z H h he hn hp hm
    exact ⟨J,hJ,hJz,hsel,hgen,w,hw⟩
  | psl2Prime _ _ p _ hp hm _ =>
    exact (ofFlag_prime_impossible S f X z H h hR (by omega) hm hout hN).elim

/-- Conditional original 11.5.1 contradiction, feeding the constructed
literal witness to the completed E.3.19 consumer. -/
theorem ofFlag_surviving_impossible
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hs : (1 : ℕ∞) < @globalS G _ V D.elementary)
    (hC : centralizer (weakCentralizer V (f.Ri 0) 1 : Set G) ≤ normalizer (L : Set G))
    (hN : normalizer (indexedWeakClosure V (f.Ri 0) 0 : Set G) ≤ normalizer (L : Set G)) :
    False := by
  obtain ⟨J,_,_,_,_,w,_⟩ := ofFlag_surviving_selected_radical_witness S f X z H
    h hcase he hNT hlinear h1132 hcontrol hs hC hN
  exact D.rankOne_R1_weakClosure_impossible S f w.H₁ w.sylow w.sylow_image
    w.generation_one w.outside hs hC hN

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside
