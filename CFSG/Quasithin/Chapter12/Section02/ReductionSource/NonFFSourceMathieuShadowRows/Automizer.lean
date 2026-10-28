module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuShadowRows.Automizer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuPointControl
public import Theory.Mathieu.M22.Properties.TwoRank
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit

/-!
# The full original automizer in the two simple M22 rows

The existing marking of the LT actor supplies the component's faithful code
or cocode action. Descending that action through its actual quotient embeds
M22 as the original component image in Aut_G(W). The containment N_G(W) ≤
N_G(L) makes this image normal. Binary absolute irreducibility extends the
same coordinates to all of Aut_G(W), without discarding its outer actors.

The preimage of the inner M22 and the kernel of the normalizer action remain
the literal original subgroups. The two-rank bound gives r ≤ 7 on the same
orbit, discharging the group-rank premise used in the M22 part of 8.1.3.
The point-centralizer, stronger lower bound and fixed-span calculations
remain to be established. Source: Aschbacher--Smith H.13.1--2, H.14.3 and
8.1.3, printed pp.395--397 and713--714, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

private theorem change_coordinates
    {A B C : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    [AddCommGroup B] [Module (ZMod 2) B] [AddCommGroup C] [Module (ZMod 2) C]
    (c : A ≃ₗ[ZMod 2] B) (e : A ≃ₗ[ZMod 2] C)
    (f : A →ₗ[ZMod 2] A) (g : B →ₗ[ZMod 2] B) (t : C →ₗ[ZMod 2] C)
    (hc : ∀ v, c (f v) = g (c v)) (he : ∀ v, e (f v) = t (e v)) (v : B) :
    (c.symm.trans e) (g v) = t ((c.symm.trans e) v) := by
  obtain ⟨w,rfl⟩ := c.surjective v
  change e (c.symm (g (c w))) = t (e (c.symm (c w)))
  rw [←hc,c.symm_apply_apply,c.symm_apply_apply,he]

private theorem m22_faithful_of_no_invariants
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Nontrivial U]
    (σ : Representation (ZMod 2) M22 U) (hz : σ.invariants = ⊥) :
    Function.Injective σ := by
  let := m22_isSimpleGroup
  rcases σ.normal_ker.eq_bot_or_eq_top with hk | hk
  · exact σ.ker_eq_bot_iff.mp hk
  · have he : σ = 1 := MonoidHom.ker_eq_top_iff.mp hk
    obtain ⟨u,hu⟩ := exists_ne (0 : U)
    have hm : u ∈ σ.invariants := by intro g; rw [he]; rfl
    rw [hz,Submodule.mem_bot] at hm
    exact (hu hm).elim

omit [Finite G] in
/-- The existing component marking in the coordinates of the original
orbit. This pointwise equation does not unfold the chosen coordinates in
the downstream centralizer arguments. -/
theorem sourceOrbit_m22_component_coordinates
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    (σ : Representation (ZMod 2) M22 U)
    (τ : Representation (ZMod 2) MathieuCode.m22PairStabilizer U)
    (hτ : τ.comp m22ToPairStabilizer = σ)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent τ)
    (l : L) (v : Additive D.sourceOrbit) :
    (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv)
      (automizerRepresentation D.sourceOrbit (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
        (inclusion D.sourceOrbit_component_normalizes l)) v) =
      σ (d.componentEquiv (D.orbitComponentHom l))
        ((D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv) v) := by
  have hc (w : D.orbitSpace) : D.sourceOrbitCoordinates
      (D.orbitRepresentation (D.orbitComponentHom l) w) =
      automizerRepresentation D.sourceOrbit (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
      (inclusion D.sourceOrbit_component_normalizes l)) (D.sourceOrbitCoordinates w) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (D.sourceOrbitCoordinates_apply
      (D.orbitRepresentation (D.orbitComponentHom l) w)).trans
        (congrArg (fun x : G => (l : G) * x * (l : G)⁻¹)
          (D.sourceOrbitCoordinates_apply w).symm)
  apply change_coordinates D.sourceOrbitCoordinates d.equivalence.toLinearEquiv
    (D.orbitRepresentation (D.orbitComponentHom l))
    (automizerRepresentation D.sourceOrbit (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
      (inclusion D.sourceOrbit_component_normalizes l))) (σ (d.componentEquiv (D.orbitComponentHom l))) hc
  intro w
  have he := LinearMap.congr_fun (d.equivalence.isIntertwining' (D.orbitComponentHom l)) w
  change d.equivalence (D.orbitRepresentation (D.orbitComponentHom l) w) =
    τ (d.embedding (D.orbitComponentHom l)) (d.equivalence w) at he
  exact he.trans ((congrArg (fun b => τ b (d.equivalence w))
    (d.on_component (D.orbitComponentHom l))).trans
      (congrArg (fun r : Representation (ZMod 2) M22 U =>
        r (d.componentEquiv (D.orbitComponentHom l)) (d.equivalence w)) hτ))

private def shadowComponentAction : L →* Automizer D.sourceOrbit :=
  D.sourceOrbit.normalizerMonoidHom.rangeRestrict.comp
    (inclusion D.sourceOrbit_component_normalizes)

omit [Finite G] in
private theorem component_image :
    D.shadowComponentAction.range = inducedAutomizer D.sourceOrbit L := by
  ext b
  constructor
  · rintro ⟨l,rfl⟩
    exact ⟨inclusion D.sourceOrbit_component_normalizes l,l.property,rfl⟩
  · rintro ⟨l,hl,rfl⟩
    exact ⟨⟨l,hl⟩,rfl⟩

private theorem component_image_normal
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    D.shadowComponentAction.range.Normal := by
  let N := normalizer (D.sourceOrbit : Set G)
  let qN := D.sourceOrbit.normalizerMonoidHom.rangeRestrict
  let : (L.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer
    (D.sourceOrbit_normalizer_le h)
  rw [D.component_image]
  exact Normal.map inferInstance qN D.sourceOrbit.normalizerMonoidHom.rangeRestrict_surjective

private theorem full_m22_marking
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] [Nontrivial U]
    (σ : Representation (ZMod 2) M22 U) (hσ : Function.Injective σ)
    [σ.IsIrreducible] [σ.IsAbsolutelyIrreducible]
    (τ : Representation (ZMod 2) MathieuCode.m22PairStabilizer U)
    (hτ : τ.comp m22ToPairStabilizer = σ)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent τ) :
    let E := D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv
    ∃ a : Automizer D.sourceOrbit →* MathieuCode.m22PairStabilizer, Function.Injective a ∧
      (∀ b v, E (automizerRepresentation D.sourceOrbit b v) = τ (a b) (E v)) ∧
      (∀ l : L, a (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
        (inclusion D.sourceOrbit_component_normalizes l)) =
          m22ToPairStabilizer (d.componentEquiv (D.orbitComponentHom l))) ∧
      m22ToPairStabilizer.range.comap a = inducedAutomizer D.sourceOrbit L ∧
      (a.range = m22ToPairStabilizer.range ∨ a.range = ⊤) := by
  let : D.shadowComponentAction.range.Normal := D.component_image_normal h
  exact MathieuShadowRows.covered_normal_m22_marking
    (H := Automizer D.sourceOrbit) (K := L) (W := Additive D.sourceOrbit) (U := U)
    (automizerRepresentation D.sourceOrbit) (automizerRepresentation_injective _)
    σ hσ τ hτ D.shadowComponentAction (inducedAutomizer D.sourceOrbit L) D.component_image
    (d.componentEquiv.toMonoidHom.comp D.orbitComponentHom)
    (d.componentEquiv.surjective.comp D.orbitComponentHom_surjective)
    (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv)
    (D.sourceOrbit_m22_component_coordinates σ τ hτ d)

/-- Extend the existing code marking to the full original automizer, with
the same linear coordinates and the actual inner-component preimage. -/
theorem sourceOrbit_m22_code_full_automizer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation) :
    let E := D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv
    ∃ a : Automizer D.sourceOrbit →* MathieuCode.m22PairStabilizer, Function.Injective a ∧
      (∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
        m22OuterCodeRepresentation (a b) (E v)) ∧
      (∀ l : L, a (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
        (inclusion D.sourceOrbit_component_normalizes l)) =
          m22ToPairStabilizer (d.componentEquiv (D.orbitComponentHom l))) ∧
      m22ToPairStabilizer.range.comap a = inducedAutomizer D.sourceOrbit L ∧
      (a.range = m22ToPairStabilizer.range ∨ a.range = ⊤) := by
  let : Nontrivial M22Code := Module.nontrivial_of_finrank_pos
    (by rw [finrank_m22Code]; decide : 0 < Module.finrank (ZMod 2) M22Code)
  let := m22Code_isIrreducible
  let := m22Code_isAbsolutelyIrreducible
  exact D.full_m22_marking h m22CodeRepresentation
    (m22_faithful_of_no_invariants _ m22Code_invariants_eq_bot)
    m22OuterCodeRepresentation (by
      apply MonoidHom.ext
      intro g
      apply LinearMap.ext
      intro v
      exact m22OuterCodeRepresentation_restrict g v) d

/-- The cocode marking also extends without changing the orbit, component,
or chosen linear equivalence. Outer actors remain in the pair stabilizer. -/
theorem sourceOrbit_m22_cocode_full_automizer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCocodeRepresentation) :
    let E := D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv
    ∃ a : Automizer D.sourceOrbit →* MathieuCode.m22PairStabilizer, Function.Injective a ∧
      (∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
        m22OuterCocodeRepresentation (a b) (E v)) ∧
      (∀ l : L, a (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
        (inclusion D.sourceOrbit_component_normalizes l)) =
          m22ToPairStabilizer (d.componentEquiv (D.orbitComponentHom l))) ∧
      m22ToPairStabilizer.range.comap a = inducedAutomizer D.sourceOrbit L ∧
      (a.range = m22ToPairStabilizer.range ∨ a.range = ⊤) := by
  let : Nontrivial M22Cocode := Module.nontrivial_of_finrank_pos
    (by rw [finrank_m22Cocode]; decide : 0 < Module.finrank (ZMod 2) M22Cocode)
  let := m22Cocode_isIrreducible
  let := m22Cocode_isAbsolutelyIrreducible
  exact D.full_m22_marking h m22CocodeRepresentation
    (m22_faithful_of_no_invariants _ m22Cocode_invariants_eq_bot)
    m22OuterCocodeRepresentation rfl d

omit [Finite G] in
/-- Every such full marking retains the entire original centralizer kernel. -/
theorem sourceOrbit_m22_full_marking_kernel
    (a : Automizer D.sourceOrbit →* MathieuCode.m22PairStabilizer) (ha : Function.Injective a) :
    (a.comp D.sourceOrbit.normalizerMonoidHom.rangeRestrict).ker =
      (centralizer (D.sourceOrbit : Set G)).subgroupOf
        (normalizer (D.sourceOrbit : Set G)) := by
  rw [MonoidHom.ker_comp_of_injective _ _ ha,MonoidHom.ker_rangeRestrict,
    Subgroup.normalizerMonoidHom_ker]

/-- Table 7.2.1's rank-five bound for the entire original M22 automizer. -/
theorem sourceOrbit_m22_automizer_twoRank_le_five
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M22))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    primeRank 2 (Automizer D.sourceOrbit) ≤ 5 := by
  have hb (a : Automizer D.sourceOrbit →* MathieuCode.m22PairStabilizer)
      (ha : Function.Injective a) : primeRank 2 (Automizer D.sourceOrbit) ≤ 5 :=
    (Theory.GroupTheory.primeRank_le_of_injective 2
      (m22PairStabilizerEquivAut.toMonoidHom.comp a)
      (m22PairStabilizerEquivAut.injective.comp ha)).trans
        m22_automorphism_twoRank_le_five
  rcases D.sourceOrbit_m22_simple_marking_of_many h hmany hV hq hnon with hc | hc
  · obtain ⟨d⟩ := hc
    obtain ⟨a,ha,_⟩ := D.sourceOrbit_m22_code_full_automizer h.toHypothesis1221 d
    exact hb a ha
  · obtain ⟨d⟩ := hc
    obtain ⟨a,ha,_⟩ := D.sourceOrbit_m22_cocode_full_automizer h.toHypothesis1221 d
    exact hb a ha

/-- The fundamental weak-closure inequality now gives the original M22
upper bound with no remaining group-rank or marking premise. -/
theorem sourceOrbit_m22_globalR_le_seven
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M22))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    globalR D.sourceOrbit ≤ 7 := by
  exact Chapter7.fwci_upper_bound D.sourceOrbit_weakClosure_setup
    (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon)
    (D.sourceOrbit_m22_automizer_twoRank_le_five h hmany hV hq hnon)
    (D.sourceOrbit_mathieu_globalW_le_two h hmany hV (Or.inr (Or.inl hq)) hnon)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
