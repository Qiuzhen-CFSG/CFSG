module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.ThreeCovers.Reduction
public import Theory.Representation.SLHigherNaturalFirstCohomology.SLThreeBinary

/-!
# The exceptional central cover on the B.5.9 seed

The actual projection U → U/C_U(L) is a perfect central cover: the seed is
commutator-generated. The inverse-transpose identification of the binary
natural dual and the checked H¹ calculation give a one-dimensional universal
cover kernel. A nonzero C_U(L) therefore makes U four-dimensional. Irreducibility
of the natural quotient, together with commutator generation, also proves that
U is indecomposable.

`seed_reducedNatural` retains the literal central quotient and the compatible
group and module identifications, starting from the B.5.1 moved section.
`seed_fourDimensionalCover` applies the full universal B.4.8(2) implication only
after constructing all its hypotheses. That earlier implication remains
explicit: its producer is `qt-b-04-natural-extensions` / `qt-b-04`, and
`qt-b05-general-classification` owns its final discharge. In particular this
module proves the conditional central-extension step, not B.4.8 itself.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed p.107; Remark I.1.5 and Lemma I.1.6(4), printed p.408; B.4.8(2),
printed p.91. B.4.8(3) concerns the other extension and is not used here.
-/

public section

set_option backward.isDefEq.respectTransparency false

open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.ThreeCovers.CentralExtension
open QuasisimpleSource QuasisimpleSource.ExtensionConsequences
universe u v w z
variable {D : Type u} [Group D] {U : Type v} [AddCommGroup U] [Module (ZMod 2) U]
  {σ : Representation (ZMod 2) D U}
  {E : Type w} [Group E] {W : Type z} [AddCommGroup W] [Module (ZMod 2) W]
  {τ : Representation (ZMod 2) E W}

private noncomputable def dualEquiv (e : ActionEquiv σ τ) : ActionEquiv σ.dual τ.dual where
  groupEquiv := e.groupEquiv
  linearEquiv := e.linearEquiv.symm.dualMap
  intertwines g f := by
    ext w
    change f (σ g⁻¹ (e.linearEquiv.symm w)) = f (e.linearEquiv.symm (τ (e.groupEquiv g)⁻¹ w))
    congr 1
    apply e.linearEquiv.injective
    rw [e.intertwines, e.linearEquiv.apply_symm_apply, e.linearEquiv.apply_symm_apply,
      e.groupEquiv.map_inv]

private theorem invariants_map (e : ActionEquiv σ τ) :
    σ.invariants.map e.linearEquiv.toLinearMap = τ.invariants := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩ g
    obtain ⟨g, rfl⟩ := e.groupEquiv.surjective g
    change τ (e.groupEquiv g) (e.linearEquiv v) = e.linearEquiv v
    rw [← e.intertwines, hv]
  · intro hw
    refine ⟨e.linearEquiv.symm w, ?_, e.linearEquiv.apply_symm_apply w⟩
    intro g
    apply e.linearEquiv.injective
    rw [e.intertwines, e.linearEquiv.apply_symm_apply, hw]

private noncomputable def reducedEquiv (e : ActionEquiv σ τ) :
    ActionEquiv (reducedAction σ) (reducedAction τ) where
  groupEquiv := e.groupEquiv
  linearEquiv := Submodule.Quotient.equiv σ.invariants τ.invariants e.linearEquiv (invariants_map e)
  intertwines g v := by
    induction v using Submodule.Quotient.induction_on with | _ v =>
    change Submodule.Quotient.mk (e.linearEquiv (σ g v)) =
      Submodule.Quotient.mk (τ (e.groupEquiv g) (e.linearEquiv v))
    rw [e.intertwines]

private noncomputable def wholeReducedEquiv {M : Subgroup D} (s : MovedSection σ M)
    (hm : moved σ M = ⊤) :
    ActionEquiv (reducedAction (σ.comp M.subtype)) (s.action.comp M.subtype) := by
  have hs : s.space.toSubmodule = ⊤ := s.space_eq.trans hm
  let q : s.space.toSubmodule ≃ₗ[ZMod 2] U :=
    LinearEquiv.ofBijective s.space.toSubmodule.subtype ⟨Subtype.val_injective,
      fun v => ⟨⟨v, hs.symm ▸ Submodule.mem_top⟩, rfl⟩⟩
  have hc : (Representation.invariants (σ.comp M.subtype)).map q.symm.toLinearMap = s.central.toSubmodule := by
    rw [s.central_eq]
    ext v
    constructor
    · rintro ⟨w, hw, he⟩ g
      apply Subtype.ext
      have hv : (v : U) = w := by
        have h := congrArg q he
        simpa [q] using h.symm
      change σ g v = v
      rw [hv]
      exact hw g
    · intro hv
      refine ⟨q v, ?_, q.symm_apply_apply v⟩
      intro g
      exact congrArg Subtype.val (hv g)
  refine ⟨MulEquiv.refl M,
    Submodule.Quotient.equiv _ _ q.symm hc, ?_⟩
  intro g v
  induction v using Submodule.Quotient.induction_on with | _ v =>
  change Submodule.Quotient.mk (q.symm (σ g v)) =
    Submodule.Quotient.mk (s.space.toRepresentation g (q.symm v))
  congr 1
  apply q.injective
  rw [q.apply_symm_apply]
  change σ g v = σ g (q (q.symm v))
  rw [q.apply_symm_apply]

private theorem dual_H1_dimension
    (e : ActionEquiv σ (linearNatural BinaryField.two 3)) :
    Module.finrank (ZMod 2) (H1 σ.dual) = 1 := by
  let a := transAction (dualEquiv e) (dualNaturalEquiv 3)
  rw [(H1Congr _ _ a.groupEquiv a.linearEquiv a.intertwines).finrank_eq]
  exact SLHigherNatural.finrank_H1_sl3_two

private noncomputable def centralProjection : σ.IntertwiningMap (reducedAction σ) :=
  σ.invariants.mkQ.intertwiningMap_of_isIntertwiningMap _ _ (fun _ _ => rfl)

private theorem dimension_four [Finite D] [FiniteDimensional (ZMod 2) U]
    (hm : Coinvariants.ker σ = ⊤) (hz : σ.invariants ≠ ⊥)
    (e : ActionEquiv (reducedAction σ) (linearNatural BinaryField.two 3)) :
    Module.finrank (ZMod 2) U = 4 := by
  let p := centralProjection (σ := σ)
  have hp : IsCover p := ⟨Submodule.mkQ_surjective _, by
    intro v hv
    exact (Submodule.Quotient.mk_eq_zero _).mp hv, hm⟩
  let : FiniteDimensional (ZMod 2)
      (Module.Dual (ZMod 2) (cocycles (reducedAction σ).dual)) :=
    Subspace.instModuleDualFiniteDimensional
  obtain ⟨q, hq, hqp⟩ := exists_universalCover_quotient p hp
  let r := universalCoverProjection (reducedAction σ)
  have hr : Function.Surjective r := by
    intro n
    obtain ⟨v, rfl⟩ := hp.1 n
    obtain ⟨x, rfl⟩ := hq v
    exact ⟨x, (hqp x).symm⟩
  have hN : Module.finrank (ZMod 2) (U ⧸ σ.invariants) = 3 := by
    exact e.linearEquiv.finrank_eq.trans (by simp [BinaryField.two])
  have hR := r.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hr, finrank_top,
    finrank_ker_universalCoverProjection, dual_H1_dimension e] at hR
  change Module.finrank (ZMod 2) (U ⧸ σ.invariants) + 1 = _ at hR
  have hle := LinearMap.finrank_le_finrank_of_surjective (f := q.toLinearMap) hq
  have hU := Submodule.finrank_quotient_add_finrank σ.invariants
  have hpos : 0 < Module.finrank (ZMod 2) σ.invariants := by
    have hn : Module.finrank (ZMod 2) σ.invariants ≠ 0 := fun h =>
      hz (Submodule.finrank_eq_zero.mp h)
    omega
  omega

private theorem indecomposable_of_natural_quotient
    (hm : Coinvariants.ker σ = ⊤)
    (e : ActionEquiv (reducedAction σ) (linearNatural BinaryField.two 3)) :
    IsIndecomposable σ := by
  let : IsIrreducible (reducedAction σ) :=
    irreducible_of_equiv e (linearNatural_irreducible BinaryField.two (by decide))
  let : Nontrivial (U ⧸ σ.invariants) :=
    Subrepresentation.irreducible_module_nontrivial (reducedAction σ)
  let : Nontrivial U := (Submodule.mkQ_surjective σ.invariants).nontrivial
  have htop (B : Subrepresentation σ) (h : σ.invariants ⊔ B.toSubmodule = ⊤) : B = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    rw [← hm]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩, rfl⟩
    have hv : v ∈ σ.invariants ⊔ B.toSubmodule := h.symm ▸ Submodule.mem_top
    obtain ⟨c,hc,b,hb,rfl⟩ := Submodule.mem_sup.mp hv
    change σ g (c + b) - (c + b) ∈ B.toSubmodule
    rw [map_add, hc g, add_sub_add_left_eq_sub]
    exact B.toSubmodule.sub_mem (B.apply_mem_toSubmodule g hb) hb
  refine ⟨inferInstance, fun A B hab => ?_⟩
  rcases Subrepresentation.le_or_sup_eq_top_of_irreducible_quotient (fixed σ) A with ha | ha
  · have hB : B = ⊤ := htop B (top_unique (by
      rw [← codisjoint_iff.mp hab.codisjoint]
      exact sup_le_sup ha le_rfl))
    left
    apply Subrepresentation.toSubmodule_injective
    have hd := hab.disjoint
    rw [hB] at hd
    exact disjoint_top.mp hd
  · have hA := htop A ha
    right
    apply Subrepresentation.toSubmodule_injective
    have hd := hab.disjoint
    rw [hA] at hd
    exact disjoint_top.mp hd.symm


variable {G : Type u} [Group G] [Finite G] {V : Type v} [AddCommGroup V]
  [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- The full B.4.8(2) implication. Its hypotheses concern a faithful
indecomposable four-dimensional action and its actual natural central quotient.
The offender statement uses the same group identification as that quotient.
The producer is B.4.8's owner (`qt-b-04-natural-extensions`); the B.5.6 source
assembly must discharge this universal earlier-source input. -/
@[expose] def EarlierB48Two : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (U : Type v) [AddCommGroup U]
    [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (σ : Representation (ZMod 2) D U),
    Function.Injective σ → IsIndecomposable σ → Module.finrank (ZMod 2) U = 4 →
    ∀ e : ActionEquiv (reducedAction σ) (linearNatural BinaryField.two 3),
      (∀ B, IsBestOffender σ B ↔
        IsFullCenterGroup BinaryField.two 3 (B.map e.groupEquiv.toMonoidHom)) ∧
      quadraticRatio σ = 1 ∧
      (∀ T : Sylow 2 D, fixedSpace σ (T : Subgroup D) = σ.invariants) ∧
      (∀ a : D, orderOf a = 2 → moved σ (zpowers a) = fixedSpace σ (zpowers a) ∧
        Module.finrank (ZMod 2) (fixedSpace σ (zpowers a)) = 2)

/-- The original L-action on U/C_U(L) is natural, with both maps built from
the faithful seed-component identification and the literal moved quotient. -/
noncomputable def seed_reducedNatural {K : GroupClass.{u}} {A L : Subgroup G}
    (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA)
    (s : MovedSection (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA))
    (hm : moved (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) = ⊤)
    (F : BinaryField) (hF : F.degree = 1)
    (e : ActionEquiv (s.action.comp (seedComponentImage ρ hLA).subtype) (linearNatural F 3)) :
    ActionEquiv (reducedAction (seedComponentAction ρ hLA)) (linearNatural BinaryField.two 3) :=
  transAction (reducedEquiv (seedComponentActionEquiv ρ hLA p))
    (transAction (wholeReducedEquiv s hm) (transAction e (degreeOneNaturalEquiv F hF 3)))

private theorem seed_commutator_top {K : GroupClass.{u}} {A L : Subgroup G}
    (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA)
    (hm : moved (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) = ⊤) :
    Coinvariants.ker (seedComponentAction ρ hLA) = ⊤ := by
  let a := seedComponentActionEquiv ρ hLA p
  apply top_unique
  rw [← hm]
  apply Submodule.span_le.mpr
  rintro _ ⟨g, hg, v, _, rfl⟩
  obtain ⟨l, hl⟩ := a.groupEquiv.surjective ⟨g, hg⟩
  have he := a.intertwines l v
  change seedComponentAction ρ hLA l v = seedQuotientAction ρ hLA (a.groupEquiv l) v at he
  rw [hl] at he
  rw [← he]
  exact Coinvariants.sub_mem_ker l v

private theorem seed_invariants_eq {K : GroupClass.{u}} {A L : Subgroup G}
    (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA) :
    Representation.invariants (seedComponentAction ρ hLA) =
      fixedSpace (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) := by
  let a := seedComponentActionEquiv ρ hLA p
  ext v
  constructor
  · intro hv g
    obtain ⟨l, rfl⟩ := a.groupEquiv.surjective g
    exact (a.intertwines l v).symm.trans (hv l)
  · intro hv l
    exact (a.intertwines l v).trans (hv (a.groupEquiv l))

/-- I.1.5 and the dual I.1.6(4) calculation give dimension four on the
literal seed, because its nonzero central kernel has dimension at most one. -/
theorem seed_dimension_four {K : GroupClass.{u}} {A L : Subgroup G}
    (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA)
    (s : MovedSection (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA))
    (hm : moved (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) = ⊤)
    (F : BinaryField) (hF : F.degree = 1)
    (e : ActionEquiv (s.action.comp (seedComponentImage ρ hLA).subtype) (linearNatural F 3))
    (hz : fixedSpace (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) ≠ ⊥) :
    Module.finrank (ZMod 2) (naturalSeedSpace ρ L A) = 4 := by
  let := p.source.finite_module
  let : FiniteDimensional (ZMod 2) (naturalSeedSpace ρ L A) := p.source.finite_module
  apply dimension_four (seed_commutator_top ρ hLA p hm)
    (by rwa [seed_invariants_eq ρ hLA p]) (seed_reducedNatural ρ hLA p s hm F hF e)

/-- Commutator generation rules out a central direct summand, and the
natural central quotient is irreducible. Hence the seed is indecomposable. -/
theorem seed_indecomposable {K : GroupClass.{u}} {A L : Subgroup G}
    (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA)
    (s : MovedSection (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA))
    (hm : moved (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) = ⊤)
    (F : BinaryField) (hF : F.degree = 1)
    (e : ActionEquiv (s.action.comp (seedComponentImage ρ hLA).subtype) (linearNatural F 3)) :
    IsIndecomposable (seedComponentAction ρ hLA) :=
  indecomposable_of_natural_quotient (seed_commutator_top ρ hLA p hm)
    (seed_reducedNatural ρ hLA p s hm F hF e)

/-- The exceptional central cover on the literal seed. All premises of
B.4.8(2) are established here; its full earlier-source implication remains
explicit for discharge by the general-classification assembly. Neither
U=[V,L] nor A≤L nor the B.4.8(3) extension is assumed. -/
theorem seed_fourDimensionalCover (h48 : EarlierB48Two.{u,v})
    {K : GroupClass.{u}} {A L : Subgroup G}
    (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA)
    (s : MovedSection (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA))
    (hm : moved (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) = ⊤)
    (F : BinaryField) (hF : F.degree = 1)
    (e : ActionEquiv (s.action.comp (seedComponentImage ρ hLA).subtype) (linearNatural F 3))
    (hz : fixedSpace (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) ≠ ⊥) :
    Nonempty (FourDimensionalCoverSource (seedComponentAction ρ hLA)) := by
  let := p.source.finite_module
  let : FiniteDimensional (ZMod 2) (naturalSeedSpace ρ L A) := p.source.finite_module
  let n := seed_reducedNatural ρ hLA p s hm F hF e
  have hd := seed_dimension_four ρ hLA p s hm F hF e hz
  have hi := seed_indecomposable ρ hLA p s hm F hF e
  obtain ⟨ho, hq, hs, ht⟩ :=
    h48 L (naturalSeedSpace ρ L A) (seedComponentAction ρ hLA) p.component_faithful hi hd n
  exact ⟨⟨hd, hi, n, ho, hq, hs, ht⟩⟩

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.ThreeCovers.CentralExtension
