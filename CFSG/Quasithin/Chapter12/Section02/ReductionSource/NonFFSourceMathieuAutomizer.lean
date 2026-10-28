module
public import Theory.Representation.BinaryNormalExtension
public import Theory.Representation.BinaryOffender.SylowTransport
public import Theory.GroupTheory.GeneralizedFitting.InnerAutomorphisms
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM23Code
public import Theory.Representation.MathieuCodeRestriction.Duality.Absolute
public import Theory.Mathieu.M24.Properties.AutomorphismTwoRank
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit

/-!
# Full ambient automizers in the large Mathieu rows

The original component image is normal in Aut_G(W), by the proved containment
N_G(W) ≤ N_G(L). When the component quotient is M23 or M24, the source marking
removes the cover and makes it the whole orbit actor. All native automorphisms
are inner, and absolute irreducibility makes the binary linear centralizer
trivial. Thus its image fills the full automizer, with the original intertwiner.

This closes the action-transport premise in the actual M23 code exclusion:
the surviving M23 source row is cocode on Aut_G(W). The same construction gives
both M24 markings. Their native two-rank bounds give r ≤ 6 and r ≤ 8 by the
fundamental weak-closure inequality and the proved w ≤ 2.
The stronger cocode lower bounds and ambient J4 recognition remain separate.

Source: Aschbacher--Smith, 7.1.1,7.2.1,7.5.1 and7.5.4, printed pp.697--700;
H.13.2 and H.14.1, pp.395--397.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative

private theorem normal_range_eq_top_of_inner_absolute
    {H A E W : Type*} [Group H] [Group A]
    [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    [AddCommGroup W] [Module (ZMod 2) W] [Nontrivial E]
    (ρ : Representation (ZMod 2) A E) [ρ.IsIrreducible] [ρ.IsAbsolutelyIrreducible]
    (τ : Representation (ZMod 2) H W) (hτ : Function.Injective τ)
    (f : A →* H) (hf : Function.Injective f) [f.range.Normal]
    (e : E ≃ₗ[ZMod 2] W) (he : ∀ a v, e (ρ a v) = τ (f a) (e v))
    (hi : Function.Surjective (MulAut.conj : A →* MulAut A)) : f.range = ⊤ := by
  have hc : centralizer (f.range : Set H) = ⊥ := by
    apply bot_unique
    intro g hg
    apply mem_bot.mpr
    apply hτ
    let t := e.trans ((LinearMap.GeneralLinearGroup.toLinearEquiv (τ.asGroupHom g)).trans e.symm)
    have ht : t = 1 := BinaryNormalExtension.centralizer_eq_one_of_absolutelyIrreducible ρ t (by
      intro a v
      apply e.injective
      change e (e.symm (τ g (e (ρ a v)))) = e (ρ a (e.symm (τ g (e v))))
      rw [e.apply_symm_apply, he, he, e.apply_symm_apply]
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      rw [mem_centralizer_iff.mp hg (f a) ⟨a,rfl⟩])
    ext w
    obtain ⟨v,rfl⟩ := e.surjective w
    have hv := congrArg e (LinearEquiv.congr_fun ht v)
    change e (e.symm (τ g (e v))) = e v at hv
    simpa only [e.apply_symm_apply,map_one,Module.End.one_apply] using hv
  let d : A ≃* f.range := f.ofInjective hf
  have hj : Function.Surjective (MulAut.conj : f.range →* MulAut f.range) := by
    intro a
    obtain ⟨x,hx⟩ := hi (MulAut.congr d.symm a)
    refine ⟨d x,?_⟩
    apply (MulAut.congr d.symm).injective
    rw [MulAut.congr_conj,d.symm_apply_apply]
    exact hx
  apply top_unique
  intro g _
  obtain ⟨l,hl⟩ := hj (MulAut.conjNormal (H := f.range) g)
  have hm : g ∈ (MulAut.innerSubgroup f.range).comap MulAut.conjNormal := ⟨l,hl⟩
  rw [MulAut.conjNormal_comap_innerSubgroup,hc,sup_bot_eq] at hm
  exact hm

private theorem marked_normal_range_complete
    {H K A E W : Type*} [Group H] [Group K] [Group A]
    [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E] [Nontrivial E]
    [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) K E) [σ.IsIrreducible] [σ.IsAbsolutelyIrreducible]
    (τ : Representation (ZMod 2) H W) (hσ : Function.Injective σ) (hτ : Function.Injective τ)
    (q : A →* K) (hq : Function.Surjective q) (k : A →* H) [k.range.Normal]
    (c : E ≃ₗ[ZMod 2] W) (hact : ∀ a v, c (σ (q a) v) = τ (k a) (c v))
    (hi : Function.Surjective (MulAut.conj : K →* MulAut K)) :
    ∃ a : H ≃* K, ∃ F : W ≃ₗ[ZMod 2] E, ∀ b v, F (τ b v) = σ (a b) (F v) := by
  obtain ⟨f,hf,heq,hfq⟩ := faithful_action_factor σ τ hσ hτ q hq k c hact
  have hfr : f.range = k.range := by
    have hcomp : f.comp q = k := MonoidHom.ext hfq
    rw [←hcomp,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr hq,←MonoidHom.range_eq_map]
  let : f.range.Normal := hfr ▸ inferInstance
  have htop := normal_range_eq_top_of_inner_absolute σ τ hτ f hf c heq hi
  let a : K ≃* H := MulEquiv.ofBijective f ⟨hf,MonoidHom.range_eq_top.mp htop⟩
  refine ⟨a.symm,c.symm,?_⟩
  intro b v
  apply c.injective
  rw [c.apply_symm_apply,heq,c.apply_symm_apply]
  change τ b v = τ (a (a.symm b)) v
  rw [a.apply_symm_apply]

private theorem change_coordinates
    {E W U : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup U] [Module (ZMod 2) U]
    (c : E ≃ₗ[ZMod 2] W) (e : E ≃ₗ[ZMod 2] U)
    (f : E →ₗ[ZMod 2] E) (g : W →ₗ[ZMod 2] W) (a : U →ₗ[ZMod 2] U)
    (hc : ∀ v, c (f v) = g (c v)) (he : ∀ v, e (f v) = a (e v)) (v : U) :
    (e.symm.trans c) (a v) = g ((e.symm.trans c) v) := by
  obtain ⟨w,rfl⟩ := e.surjective v
  change c (e.symm (a (e w))) = g (c (e.symm (e w)))
  rw [←he,e.symm_apply_apply,e.symm_apply_apply,hc]

private theorem component_top_of_inner_quotient
    {A S : Type*} [Group A] [Finite A] [Group S]
    (J : Subgroup A) (hf : Theory.GroupTheory.generalizedFitting A = J)
    (hJ : Theory.GroupTheory.IsQuasisimple J)
    (e : J ⧸ center J ≃* S) (hi : Function.Surjective (MulAut.conj : S →* MulAut S)) : J = ⊤ := by
  subst J
  let := hJ
  exact Theory.GroupTheory.generalizedFitting_eq_top_of_inner_centralQuotient e hi

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Theory.GroupTheory ChapterE Chapter7.NormalizedSource Sporadic.Mathieu
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem sourceOrbit_complete_marking
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hC : D.orbitComponent = ⊤)
    {K W : Type*} [Group K] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] [Nontrivial W]
    (σ : Representation (ZMod 2) K W) [σ.IsIrreducible] [σ.IsAbsolutelyIrreducible]
    (hσ : Function.Injective σ) (hi : Function.Surjective (MulAut.conj : K →* MulAut K))
    (e : D.orbitActor ≃* K) (E : D.orbitSpace ≃ₗ[ZMod 2] W)
    (he : ∀ a v, E (D.orbitRepresentation a v) = σ (e a) (E v)) :
    ∃ a : Automizer D.sourceOrbit ≃* K, ∃ F : Additive D.sourceOrbit ≃ₗ[ZMod 2] W,
      ∀ b v, F (automizerRepresentation D.sourceOrbit b v) = σ (a b) (F v) := by
  let N := normalizer (D.sourceOrbit : Set G)
  let qN := D.sourceOrbit.normalizerMonoidHom.rangeRestrict
  let k : L →* Automizer D.sourceOrbit := qN.comp (inclusion D.sourceOrbit_component_normalizes)
  let q : L →* K := e.toMonoidHom.comp (D.orbitComponent.subtype.comp D.orbitComponentHom)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨l,hl⟩ := D.orbitComponentHom_surjective ⟨e.symm x,hC ▸ mem_top _⟩
    refine ⟨l,?_⟩
    change e (D.orbitComponentHom l) = x
    rw [hl]
    exact e.apply_symm_apply x
  have hk : k.range = (L.subgroupOf N).map qN := by
    ext a
    constructor
    · rintro ⟨l,rfl⟩
      exact ⟨inclusion D.sourceOrbit_component_normalizes l,l.property,rfl⟩
    · rintro ⟨l,hl,rfl⟩
      exact ⟨⟨l,hl⟩,rfl⟩
  let : (L.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer
    (D.sourceOrbit_normalizer_le h)
  let : k.range.Normal := hk ▸ Normal.map inferInstance qN
    D.sourceOrbit.normalizerMonoidHom.rangeRestrict_surjective
  have hc (l : L) (w : D.orbitSpace) :
      D.sourceOrbitCoordinates (D.orbitRepresentation (D.orbitComponentHom l) w) =
        automizerRepresentation D.sourceOrbit (k l) (D.sourceOrbitCoordinates w) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (D.sourceOrbitCoordinates_apply
      (D.orbitRepresentation (D.orbitComponentHom l) w)).trans
        (congrArg (fun x : G => (l : G) * x * (l : G)⁻¹)
          (D.sourceOrbitCoordinates_apply w).symm)
  let c := E.symm.trans D.sourceOrbitCoordinates
  have hact (l : L) (w : W) :
      c (σ (q l) w) = automizerRepresentation D.sourceOrbit (k l) (c w) :=
    change_coordinates D.sourceOrbitCoordinates E
      (D.orbitRepresentation (D.orbitComponentHom l))
      (automizerRepresentation D.sourceOrbit (k l)) (σ (q l))
      (hc l) (he (D.orbitComponentHom l)) w
  exact marked_normal_range_complete σ (automizerRepresentation D.sourceOrbit)
    hσ (automizerRepresentation_injective _) q hq k c hact hi

/-- The code/cocode marking is on the entire literal ambient automizer. -/
theorem sourceOrbit_m23_automizer_marking
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M23)) :
    MathieuCode.IsM23Code (automizerRepresentation D.sourceOrbit) ∨
      MathieuCode.IsM23Cocode (automizerRepresentation D.sourceOrbit) := by
  have hC : D.orbitComponent = ⊤ := by
    obtain ⟨e⟩ := hq
    exact component_top_of_inner_quotient _ hs.fitting hs.quasisimple e m23_conj_surjective
  rcases (MathieuMarkings.m23_marking D.orbitRepresentation D.orbitComponent hs hq).2
      with hc | hd
  · obtain ⟨e,E,hE⟩ := hc
    let := MathieuCode.m23Code_isIrreducible
    let := MathieuCode.m23Code_isAbsolutelyIrreducible
    exact Or.inl (D.sourceOrbit_complete_marking h hC _ MathieuCode.m23Code_faithful
      m23_conj_surjective e E hE)
  · obtain ⟨e,E,hE⟩ := hd
    let := MathieuCode.m23Cocode_isIrreducible
    let := MathieuCode.m23Cocode_isAbsolutelyIrreducible
    exact Or.inr (D.sourceOrbit_complete_marking h hC _ MathieuCode.m23Cocode_faithful
      m23_conj_surjective e E hE)

/-- The M24 code/cocode marking extends to the full literal ambient automizer. -/
theorem sourceOrbit_m24_automizer_marking
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24)) :
    MathieuSmall.IsM24ToddOrDual (automizerRepresentation D.sourceOrbit) := by
  have hC : D.orbitComponent = ⊤ := by
    obtain ⟨e⟩ := hq
    exact component_top_of_inner_quotient _ hs.fitting hs.quasisimple e
      M24OuterRestriction.conj_surjective
  obtain ⟨e,hc | hd⟩ := MathieuMarkings.m24_marking D.orbitRepresentation D.orbitComponent hs hq
  · obtain ⟨E⟩ := hc
    let := MathieuCode.cocode_isIrreducible
    let := MathieuCode.cocode_isAbsolutelyIrreducible
    obtain ⟨a,F,hF⟩ := D.sourceOrbit_complete_marking h hC _ MathieuCode.cocode_faithful
      M24OuterRestriction.conj_surjective e E.toLinearEquiv
      (fun g v => LinearMap.congr_fun (E.isIntertwining' g) v)
    exact ⟨a,Or.inl ⟨Representation.Equiv.mk F (fun g => LinearMap.ext (hF g))⟩⟩
  · obtain ⟨E⟩ := hd
    let := MathieuCode.code_isIrreducible
    let := MathieuCode.code_isAbsolutelyIrreducible
    obtain ⟨a,F,hF⟩ := D.sourceOrbit_complete_marking h hC _ MathieuCode.code_faithful
      M24OuterRestriction.conj_surjective e E.toLinearEquiv
      (fun g v => LinearMap.congr_fun (E.isIntertwining' g) v)
    exact ⟨a,Or.inr ⟨Representation.Equiv.mk F (fun g => LinearMap.ext (hF g))⟩⟩

/-- With the source hypotheses constructed internally, the M23 row is the
cocode on the actual automizer: the code exclusion now applies literally. -/
theorem sourceOrbit_m23_cocode_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M23))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    MathieuCode.IsM23Cocode (automizerRepresentation D.sourceOrbit) := by
  have hm : HasMathieuCentralQuotient D.orbitComponent := Or.inr (Or.inr (Or.inl hq))
  exact (D.sourceOrbit_m23_automizer_marking h.toHypothesis1221
    (D.sourceOrbit_chapterK_of_many h hmany hnon hV) hq).resolve_left
      (D.sourceOrbit_not_m23Code_of_mathieu h hmany hV hm hnon)

/-- The M23 two-rank entry belongs to the full automizer of the original orbit. -/
theorem sourceOrbit_m23_automizer_twoRank_le_four
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M23)) :
    primeRank 2 (Automizer D.sourceOrbit) ≤ 4 := by
  rcases D.sourceOrbit_m23_automizer_marking h hs hq with ⟨e,E,he⟩ | ⟨e,E,he⟩ <;>
    rw [primeRank_equiv 2 e] <;> exact m23_twoRank_le_four

/-- The M24 two-rank entry also belongs to the entire ambient automizer. -/
theorem sourceOrbit_m24_automizer_twoRank_le_six
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24)) :
    primeRank 2 (Automizer D.sourceOrbit) ≤ 6 := by
  obtain ⟨e,_⟩ := D.sourceOrbit_m24_automizer_marking h hs hq
  rw [primeRank_equiv 2 e]
  apply (primeRank_le_iff_elementary_card_le M24).mpr
  intro A hA
  let := hA
  exact m24_elementary_card_le_sixtyfour A

/-- The source weak-closure inequality gives r ≤ 6 in the M23 row, with
both the outside-generation and full-automizer inputs discharged. -/
theorem sourceOrbit_m23_globalR_le_six
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M23))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    globalR D.sourceOrbit ≤ 6 := by
  have hm : HasMathieuCentralQuotient D.orbitComponent := Or.inr (Or.inr (Or.inl hq))
  exact Chapter7.fwci_upper_bound D.sourceOrbit_weakClosure_setup
    (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon)
    (D.sourceOrbit_m23_automizer_twoRank_le_four h.toHypothesis1221
      (D.sourceOrbit_chapterK_of_many h hmany hnon hV) hq)
    (D.sourceOrbit_mathieu_globalW_le_two h hmany hV hm hnon)

/-- The same literal weak-closure inequality gives r ≤ 8 in the M24 row. -/
theorem sourceOrbit_m24_globalR_le_eight
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    globalR D.sourceOrbit ≤ 8 := by
  have hm : HasMathieuCentralQuotient D.orbitComponent := Or.inr (Or.inr (Or.inr hq))
  exact Chapter7.fwci_upper_bound D.sourceOrbit_weakClosure_setup
    (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon)
    (D.sourceOrbit_m24_automizer_twoRank_le_six h.toHypothesis1221
      (D.sourceOrbit_chapterK_of_many h hmany hnon hV) hq)
    (D.sourceOrbit_mathieu_globalW_le_two h hmany hV hm hnon)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
