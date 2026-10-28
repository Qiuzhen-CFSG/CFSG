module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.Construction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.Geometry
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorExtraction.Rows
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorModuleContract
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.Representation.NormalInvariants
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.BinaryPermutationMulAction

/-!
# The exceptional split-core branch of B.5.6

Suppose V splits over [V,F*(G₂)] and its fixed space. The classified
second-factor action proves C_{V₂}(F*(G₂)) = C_{V₂}(G₂): a nontrivial normal
subgroup has zero fixed space on each faithful irreducible natural module.
The doubled module is treated coordinatewise. In the four-dimensional
indecomposable, the natural three-space and any nonzero core-fixed space
would be complementary invariant subspaces. Generalized-Fitting
self-centralization supplies the required nontriviality, without a new model
classification input.

The published geometry then chooses the first four-space with globally
fixed second-factor displacements. Its saturation and V₂ are complementary
in V/C_V(G). The second factor is transported through the original inclusion
V₂ → V and the literal fixed quotients. Natural and doubled rows retain the
ambient moved space [V,G₂], whose quotient image is proved to equal the image
of V₂. This allows nonzero, globally fixed displacements of the chosen vector.

The only earlier-source parameter is the full `EarlierB48Three`, produced by
qt-b-04-natural-extensions. Every applicability hypothesis is proved on the
transported action, and every offender, ratio and involution clause is retained.
`FactorModuleConclusion` is the supplied B.5.11 output; its production and the
split/nonsplit assembly remain with the parent exceptional-extension task.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, final proof
of B.5.6, printed p.110, split L₂ case; B.4.8(3), printed p.91.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
namespace CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.SplitCase
universe u v w z
variable {D : Type u} [Group D] {U : Type v} [AddCommGroup U] [Module (ZMod 2) U]
  {σ : Representation (ZMod 2) D U}

private theorem core_ne_bot [Finite D] [Nontrivial D] : generalizedFitting D ≠ ⊥ := by
  intro h
  have hc := QuasisimpleSections.centralizer_generalizedFitting_le (G := D)
  rw [h] at hc
  have ht : (⊤ : Subgroup D) ≤ centralizer (↑(⊥ : Subgroup D) : Set D) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx1 : x = 1 := hx
    simp [hx1]
  exact top_ne_bot (le_bot_iff.mp (ht.trans hc))

private theorem irreducible_core_fixed [Finite D] [Nontrivial D]
    [IsIrreducible σ] (hf : Function.Injective σ) :
    fixedSpace σ (generalizedFitting D) = ⊥ := by
  by_contra hn
  have hk := le_ker_of_normal_invariants_ne_bot σ (generalizedFitting D) hn
  rw [(MonoidHom.ker_eq_bot_iff σ).mpr hf] at hk
  exact core_ne_bot (le_bot_iff.mp hk)

private theorem linear_faithful (F : BinaryField) (d : ℕ) :
    Function.Injective (linearNatural F d) := by
  intro g h he
  apply specialLinearNatural_injective d
  exact LinearMap.ext (fun v => LinearMap.congr_fun he v)

private theorem faithful_equiv {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    {τ : Representation (ZMod 2) E W} (e : ActionEquiv σ τ)
    (hf : Function.Injective τ) : Function.Injective σ := by
  intro g h he
  apply e.groupEquiv.injective
  apply hf
  ext w
  obtain ⟨v, rfl⟩ := e.linearEquiv.surjective w
  rw [← e.intertwines, ← e.intertwines]
  exact congrArg e.linearEquiv (LinearMap.congr_fun he v)

private theorem core_fixed_equiv {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    {τ : Representation (ZMod 2) E W} (e : ActionEquiv σ τ)
    (ht : fixedSpace τ (generalizedFitting E) = ⊥) :
    fixedSpace σ (generalizedFitting D) = ⊥ := by
  apply bot_unique
  intro v hv
  apply e.linearEquiv.injective
  rw [map_zero]
  apply (Submodule.mem_bot (ZMod 2)).mp
  rw [← ht]
  intro g
  have hg : (g : E) ∈ (generalizedFitting D).map e.groupEquiv.toMonoidHom := by
    rw [map_generalizedFitting_equiv]
    exact g.property
  obtain ⟨d,hd,he⟩ := hg
  change τ (g : E) (e.linearEquiv v) = e.linearEquiv v
  change e.groupEquiv d = (g : E) at he
  rw [← he, ← e.intertwines]
  exact congrArg e.linearEquiv (hv ⟨d,hd⟩)

private theorem symmetric_faithful :
    Function.Injective (BinaryPermutation.naturalRepresentation (Fin 5)) := by
  intro g h he
  apply BinaryPermutation.naturalMulAction_injective_of_odd (Fin 5) (by decide)
  apply MulEquiv.ext
  intro v
  exact congrArg Multiplicative.ofAdd (LinearMap.congr_fun he v.toAdd)

private theorem symmetric_irreducible :
    IsIrreducible (BinaryPermutation.naturalRepresentation (Fin 5)) := by
  let τ := BinaryPermutation.naturalRepresentation (Fin 5)
  let := BinaryPermutation.alternatingNatural_isIrreducible (Ω := Fin 5) (by decide)
  let : Nontrivial (BinaryPermutation.natural (Fin 5)) :=
    Subrepresentation.irreducible_module_nontrivial (τ.comp (alternatingGroup (Fin 5)).subtype)
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  let T : Subrepresentation (τ.comp (alternatingGroup (Fin 5)).subtype) :=
    ⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule g hv⟩
  rcases eq_bot_or_eq_top T with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    have ht := congrArg (fun S : Subrepresentation (τ.comp (alternatingGroup (Fin 5)).subtype) => S.toSubmodule) h
    exact ht
  · right
    apply Subrepresentation.toSubmodule_injective
    have ht := congrArg (fun S : Subrepresentation (τ.comp (alternatingGroup (Fin 5)).subtype) => S.toSubmodule) h
    exact ht

private theorem natural_core_fixed [Finite D] [Nontrivial D] (h : FactorNatural σ) :
    fixedSpace σ (generalizedFitting D) = ⊥ := by
  cases h with
  | linearTwo F hn =>
    obtain ⟨e⟩ := hn
    let := irreducible_of_equiv e (linearNatural_irreducible F (by decide : 2 ≤ 2))
    exact irreducible_core_fixed (faithful_equiv e (linear_faithful F 2))
  | linearThree F ho hn =>
    obtain ⟨e⟩ := hn
    let := irreducible_of_equiv e (linearNatural_irreducible F (by decide : 2 ≤ 3))
    exact irreducible_core_fixed (faithful_equiv e (linear_faithful F 3))
  | symmetricFive hn =>
    obtain ⟨e⟩ := hn
    let := irreducible_of_equiv e symmetric_irreducible
    exact irreducible_core_fixed (faithful_equiv e symmetric_faithful)

private theorem repeated_core_fixed [Finite D] [Nontrivial D]
    [IsIrreducible σ] (hf : Function.Injective σ) (r : ℕ) :
    fixedSpace (repeated σ r) (generalizedFitting D) = ⊥ := by
  have hz := irreducible_core_fixed hf
  apply bot_unique
  intro v hv
  change v = 0
  ext i
  apply (Submodule.mem_bot (ZMod 2)).mp
  rw [← hz]
  exact fun g => congrFun (hv g) i

private theorem four_core_fixed [Finite D] [Nontrivial D] [FiniteDimensional (ZMod 2) U]
    (h : FourDimensionalSource σ) : fixedSpace σ (generalizedFitting D) = ⊥ := by
  let := irreducible_of_equiv h.natural (linearNatural_irreducible BinaryField.two (by decide : 2 ≤ 3))
  have hn := irreducible_core_fixed (faithful_equiv h.natural (linear_faithful BinaryField.two 3))
  let C := fixedSubrepresentationOfNormal σ (generalizedFitting D)
  have hd : Disjoint h.space.toSubmodule C.toSubmodule := by
    apply Submodule.disjoint_def.mpr
    intro x hx hc
    have hf : (⟨x,hx⟩ : h.space.toSubmodule) ∈ fixedSpace h.space.toRepresentation (generalizedFitting D) :=
      fun g => Subtype.ext (hc g)
    rw [hn] at hf
    exact congrArg Subtype.val hf
  have hdim : Module.finrank (ZMod 2) h.space.toSubmodule = 3 :=
    h.natural.linearEquiv.finrank_eq.trans (Module.finrank_fin_fun (ZMod 2))
  by_contra hc
  have hc' : C.toSubmodule ≠ ⊥ := hc
  let : Nontrivial C.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hc'
  have hpos : 0 < Module.finrank (ZMod 2) C.toSubmodule := Module.finrank_pos
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq h.space.toSubmodule C.toSubmodule
  rw [hd.eq_bot, finrank_bot, add_zero, hdim] at hsum
  have hb := Submodule.finrank_le (h.space.toSubmodule ⊔ C.toSubmodule)
  rw [h.dimension] at hb
  have ht : h.space.toSubmodule ⊔ C.toSubmodule = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [h.dimension]; omega)
  rcases h.indecomposable.2 h.space C ⟨hd, codisjoint_iff.mpr ht⟩ with hN | hC
  · have he := congrArg (fun S : Subrepresentation σ => Module.finrank (ZMod 2) S.toSubmodule) hN
    change Module.finrank (ZMod 2) h.space.toSubmodule = Module.finrank (ZMod 2) (⊥ : Submodule (ZMod 2) U) at he
    rw [hdim, finrank_bot] at he
    omega
  · exact hc' (congrArg Subrepresentation.toSubmodule hC)

theorem factor_quotient_core_fixed [Finite D] [Nontrivial D] [FiniteDimensional (ZMod 2) U]
    (f : FactorModuleConclusion σ) :
    fixedSpace (((fixed σ).quotientImage f.space).toRepresentation.comp (⊤ : Subgroup D).subtype)
      (generalizedFitting (⊤ : Subgroup D)) = ⊥ := by
  cases f.actionCase with
  | natural hm hn => exact natural_core_fixed hn
  | doubleNatural F ho hm hn =>
    obtain ⟨e⟩ := hn
    let := linearNatural_irreducible F (by decide : 2 ≤ 3)
    let : Nontrivial (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) := e.groupEquiv.injective.nontrivial
    exact core_fixed_equiv e (repeated_core_fixed (linear_faithful F 3) 2)
  | exceptional hm h => exact four_core_fixed h

/-- Every factor allowed by B.5.6(3) has the same fixed space as its
actual generalized Fitting subgroup. The quotient is the original fixed quotient. -/
theorem factor_core_fixed [Finite D] [Nontrivial D] [FiniteDimensional (ZMod 2) U]
    (f : FactorModuleConclusion σ) :
    fixedSpace σ (generalizedFitting D) = σ.invariants := by
  apply le_antisymm
  · intro v hv
    have hvs : v ∈ f.space.toSubmodule ⊔ σ.invariants := by
      rw [f.supplement]; trivial
    obtain ⟨w,hw,z,hz,he⟩ := Submodule.mem_sup.mp hvs
    have hq : σ.invariants.mkQ w = σ.invariants.mkQ v := by
      rw [← he, map_add, (show σ.invariants.mkQ z = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hz), add_zero]
    let q : ((fixed σ).quotientImage f.space).toSubmodule := ⟨σ.invariants.mkQ v, w,hw,hq⟩
    have hqf : q ∈ fixedSpace
        (((fixed σ).quotientImage f.space).toRepresentation.comp (⊤ : Subgroup D).subtype)
        (generalizedFitting (⊤ : Subgroup D)) := by
      intro g
      apply Subtype.ext
      change σ.invariants.mkQ (σ (g.val.val) v) = σ.invariants.mkQ v
      have hg : g.val.val ∈ generalizedFitting D := by
        rw [← map_generalizedFitting_equiv (Subgroup.topEquiv : (⊤ : Subgroup D) ≃* D)]
        exact ⟨g.val,g.property,rfl⟩
      exact congrArg σ.invariants.mkQ (hv ⟨g.val.val,hg⟩)
    rw [factor_quotient_core_fixed f] at hqf
    exact (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val hqf)
  · exact fun _ hv g => hv g

variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- The local second-factor invariants are exactly the global fixed vectors
inside V₂, by the literal internal product G₁G₂. -/
theorem second_invariants (c : ComponentReduction.Conclusion ρ)
    {v : c.productConfiguration.fixed.toSubmodule} :
    v ∈ Representation.invariants (secondAction c) ↔ (v : V) ∈ ρ.invariants := by
  constructor
  · intro hv g
    obtain ⟨a,b,rfl⟩ := c.productConfiguration.product.exists_mul g
    have ha : ρ (a : G) (v : V) = v := by
      have hf : (v : V) ∈ fixedSpace ρ c.first := c.productConfiguration.fixed_eq ▸ v.property
      exact hf a
    have hb : ρ (b : G) (v : V) = v := congrArg Subtype.val (hv b)
    rw [map_mul, Module.End.mul_apply, hb, ha]
  · exact fun hv g => Subtype.ext (hv g)

/-- This discharges the fixed-space premise of `split_quotient_geometry`
using the actual factor conclusion, rather than an assumed comparison. -/
theorem second_core_fixed [Finite G] [FiniteDimensional (ZMod 2) V]
    (c : ComponentReduction.Conclusion ρ) [Nontrivial (second c)]
    (f : FactorModuleConclusion (secondAction c)) :
    fixedSpace ρ (secondCore c) ⊓ c.productConfiguration.fixed.toSubmodule ≤ ρ.invariants := by
  intro v hv
  apply (second_invariants c (v := ⟨v,hv.2⟩)).mp
  rw [← factor_core_fixed f]
  intro g
  apply Subtype.ext
  exact hv.1 ⟨g.val, ⟨g.val,g.property,rfl⟩⟩


section Transport
variable {E : Type u} [Group E] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  {τ : Representation (ZMod 2) E W}

private def pullSpace (e : ActionEquiv σ τ) (S : Subrepresentation τ) : Subrepresentation σ where
  toSubmodule := S.toSubmodule.comap e.linearEquiv.toLinearMap
  apply_mem_toSubmodule g v hv := by
    change e.linearEquiv (σ g v) ∈ S
    rw [e.intertwines]
    exact S.apply_mem_toSubmodule _ hv

private theorem moved_map (e : ActionEquiv σ τ) :
    (moved σ ⊤).map e.linearEquiv.toLinearMap = moved τ ⊤ := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨g,_,v,_,rfl⟩
    change e.linearEquiv (σ g v - v) ∈ moved τ ⊤
    rw [map_sub, e.intertwines]
    exact Submodule.subset_span ⟨e.groupEquiv g, mem_top _, e.linearEquiv v, Submodule.mem_top,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨g,_,v,_,rfl⟩
    obtain ⟨d,rfl⟩ := e.groupEquiv.surjective g
    obtain ⟨w,rfl⟩ := e.linearEquiv.surjective v
    refine ⟨σ d w - w, Submodule.subset_span ⟨d,mem_top _,w,Submodule.mem_top,rfl⟩,?_⟩
    change e.linearEquiv (σ d w - w) = _
    rw [map_sub, e.intertwines]

private theorem indecomposable_equiv (e : ActionEquiv σ τ) (hi : IsIndecomposable σ) :
    IsIndecomposable τ := by
  let := hi.1
  refine ⟨e.linearEquiv.injective.nontrivial, fun A B hc => ?_⟩
  have hd : Disjoint (pullSpace e A).toSubmodule (pullSpace e B).toSubmodule := by
    apply Submodule.disjoint_def.mpr
    intro x ha hb
    exact e.linearEquiv.map_eq_zero_iff.mp (Submodule.disjoint_def.mp hc.disjoint _ ha hb)
  have hs : (pullSpace e A).toSubmodule ⊔ (pullSpace e B).toSubmodule = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨a,ha,b,hb,h⟩ := Submodule.mem_sup.mp (hc.sup_eq_top.symm ▸ Submodule.mem_top (x := e.linearEquiv x))
    exact Submodule.mem_sup.mpr ⟨e.linearEquiv.symm a, by simpa [pullSpace] using ha,
      e.linearEquiv.symm b, by simpa [pullSpace] using hb, by
        apply e.linearEquiv.injective
        simpa only [map_add, LinearEquiv.apply_symm_apply] using h⟩
  have hzero (S : Subrepresentation τ) (hS : pullSpace e S = ⊥) : S = ⊥ := by
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro x hx
    have hmem : e.linearEquiv.symm x ∈ (pullSpace e S).toSubmodule := by
      change e.linearEquiv (e.linearEquiv.symm x) ∈ S.toSubmodule
      simpa using hx
    rw [hS] at hmem
    exact e.linearEquiv.symm.map_eq_zero_iff.mp hmem
  exact (hi.2 _ _ ⟨hd, codisjoint_iff.mpr hs⟩).imp (hzero A) (hzero B)

private noncomputable def pullAction (e : ActionEquiv σ τ) (S : Subrepresentation τ) :
    ActionEquiv (pullSpace e S).toRepresentation S.toRepresentation where
  groupEquiv := e.groupEquiv
  linearEquiv := e.linearEquiv.ofSubmodule' S.toSubmodule
  intertwines g v := Subtype.ext (e.intertwines g v)

/-- Transport a four-dimensional source module, verifying the hypotheses of
full B.4.8(3) on the new literal action and retaining all its conclusions. -/
theorem four_source_equiv [Finite D] [Finite E] [FiniteDimensional (ZMod 2) W]
    (h48 : EarlierB48Three.{u,v}) (e : ActionEquiv σ τ) (h : FourDimensionalSource σ) :
    Nonempty (FourDimensionalSource τ) := by
  let N := pullSpace (actionSymm e) h.space
  let q := pullAction (actionSymm e) h.space
  let n := FactorExtraction.transAction q h.natural
  have hm : N.toSubmodule = moved τ ⊤ := by
    change h.space.toSubmodule.comap e.linearEquiv.symm.toLinearMap = _
    rw [h.space_eq, Submodule.comap_equiv_eq_map_symm, LinearEquiv.symm_symm, moved_map e]
  have hf : Function.Injective τ := by
    have hn := faithful_equiv n (linear_faithful BinaryField.two 3)
    intro g k he
    apply hn
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun he v
  have hd : Module.finrank (ZMod 2) W = 4 := e.linearEquiv.finrank_eq.symm.trans h.dimension
  have hi := indecomposable_equiv e h.indecomposable
  obtain ⟨ho,hr,ha⟩ := h48 E W τ hf hi hd N hm n
  exact ⟨⟨hd,hi,N,hm,n,ho,hr,ha⟩⟩

private theorem natural_equiv (e : ActionEquiv σ τ) (h : FactorNatural σ) : FactorNatural τ := by
  cases h with
  | linearTwo F hn => exact .linearTwo F ⟨FactorExtraction.transAction (actionSymm e) hn.some⟩
  | linearThree F ho hn => exact .linearThree F ho ⟨FactorExtraction.transAction (actionSymm e) hn.some⟩
  | symmetricFive hn => exact .symmetricFive ⟨FactorExtraction.transAction (actionSymm e) hn.some⟩

end Transport


open ComponentReduction

/-- The supplement ensures that its image is the entire local fixed quotient. -/
private theorem factor_image_top (f : FactorModuleConclusion σ) :
    ((fixed σ).quotientImage f.space).toSubmodule = ⊤ := by
  change f.space.toSubmodule.map σ.invariants.mkQ = ⊤
  have h := congrArg (fun S : Submodule (ZMod 2) U => S.map σ.invariants.mkQ) f.supplement
  simpa only [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq, Submodule.map_top,
    LinearMap.range_eq_top.mpr σ.invariants.mkQ_surjective] using h

private noncomputable def factorImageEquiv (f : FactorModuleConclusion σ) :
    ActionEquiv (((fixed σ).quotientImage f.space).toRepresentation.comp (⊤ : Subgroup D).subtype)
      (reducedAction σ) where
  groupEquiv := Subgroup.topEquiv
  linearEquiv := (LinearEquiv.ofEq _ _ (factor_image_top f)).trans Submodule.topEquiv
  intertwines _ _ := rfl

private noncomputable def secondQuotientEquiv (c : ComponentReduction.Conclusion ρ) :
    ActionEquiv (reducedAction (secondAction c))
      (((fixed ρ).quotientImage c.productConfiguration.fixed).toRepresentation.comp (second c).subtype) := by
  let C := c.productConfiguration.fixed
  let τ : Representation (ZMod 2) (second c) C.toSubmodule := secondAction c
  let Q := (fixed ρ).quotientImage C
  let i : C.toSubmodule →ₗ[ZMod 2] Q.toSubmodule := {
    toFun := fun v => ⟨ρ.invariants.mkQ v, v,v.property,rfl⟩
    map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
    map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _) }
  have hk : τ.invariants = i.ker := by
    ext v
    change (v ∈ τ.invariants) ↔ i v = 0
    rw [second_invariants c]
    constructor
    · intro hv
      apply Subtype.ext
      exact (Submodule.Quotient.mk_eq_zero _).mpr hv
    · intro hv
      exact (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val hv)
  let j := τ.invariants.liftQ i hk.le
  have hj : Function.Bijective j := by
    constructor
    · apply (injective_iff_map_eq_zero j).mpr
      intro v hv
      induction v using Submodule.Quotient.induction_on with
      | _ v => exact (Submodule.Quotient.mk_eq_zero _).mpr (hk.symm ▸ hv)
    · rintro ⟨q,v,hv,rfl⟩
      exact ⟨τ.invariants.mkQ ⟨v,hv⟩,rfl⟩
  refine ⟨MulEquiv.refl _, LinearEquiv.ofBijective j hj, ?_⟩
  intro g v
  induction v using Submodule.Quotient.induction_on with | _ v => rfl

private noncomputable def secondFactorEquiv (c : ComponentReduction.Conclusion ρ)
    (f : FactorModuleConclusion (secondAction c)) :
    ActionEquiv
      (((fixed (secondAction c)).quotientImage f.space).toRepresentation.comp
        (⊤ : Subgroup (second c)).subtype)
      (((fixed ρ).quotientImage c.productConfiguration.fixed).toRepresentation.comp (second c).subtype) :=
  FactorExtraction.transAction (factorImageEquiv f) (secondQuotientEquiv c)

private theorem second_local_moved_le (c : ComponentReduction.Conclusion ρ) :
    (moved (secondAction c) ⊤).map c.productConfiguration.fixed.toSubmodule.subtype ≤
      moved ρ (second c) := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro _ ⟨g,_,v,_,rfl⟩
  exact Submodule.subset_span ⟨g,g.property,v,Submodule.mem_top,rfl⟩

/-- If the extracted row is natural or doubled, its original local moved
space supplements C_V(G). Thus the ambient moved space has the same quotient
image as V₂, even when the chosen vector has a nonzero fixed displacement. -/
theorem second_moved_supplement (c : ComponentReduction.Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (hm : f.space.toSubmodule = moved (secondAction c) ⊤) :
    moved ρ (second c) ⊔ ρ.invariants = c.productConfiguration.fixed.toSubmodule := by
  apply le_antisymm (sup_le (second_moved_le_fixed c he) (invariants_le_fixed c))
  intro v hv
  have hs : (⟨v,hv⟩ : c.productConfiguration.fixed.toSubmodule) ∈
      f.space.toSubmodule ⊔ Representation.invariants (secondAction c) := by
    rw [f.supplement]; trivial
  obtain ⟨w,hw,z,hz,h⟩ := Submodule.mem_sup.mp hs
  apply Submodule.mem_sup.mpr
  refine ⟨w,second_local_moved_le c ⟨w, hm ▸ hw,rfl⟩,
    z,(second_invariants c).mp hz,?_⟩
  exact congrArg Subtype.val h

private theorem second_moved_image (c : ComponentReduction.Conclusion ρ)
    (hs : moved ρ (second c) ⊔ ρ.invariants = c.productConfiguration.fixed.toSubmodule) :
    ((fixed ρ).quotientImage (secondMoved c)).toSubmodule =
      ((fixed ρ).quotientImage c.productConfiguration.fixed).toSubmodule := by
  change (moved ρ (second c)).map ρ.invariants.mkQ =
    c.productConfiguration.fixed.toSubmodule.map ρ.invariants.mkQ
  rw [← hs, Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]

private noncomputable def secondMovedEquiv (c : ComponentReduction.Conclusion ρ)
    (hs : moved ρ (second c) ⊔ ρ.invariants = c.productConfiguration.fixed.toSubmodule) :
    ActionEquiv
      (((fixed ρ).quotientImage c.productConfiguration.fixed).toRepresentation.comp (second c).subtype)
      (((fixed ρ).quotientImage (secondMoved c)).toRepresentation.comp (second c).subtype) where
  groupEquiv := MulEquiv.refl _
  linearEquiv := LinearEquiv.ofEq _ _ (second_moved_image c hs).symm
  intertwines _ _ := rfl

/-- Both natural alternatives keep their literal ambient moved space; the
exceptional alternative keeps every B.4.8(3) clause. All quotient maps are
induced by the original inclusion V₂ → V and the global fixed quotient. -/
theorem second_factor_case [Finite G] [FiniteDimensional (ZMod 2) V]
    (h48 : EarlierB48Three.{u,v}) (c : ComponentReduction.Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c)) :
    ∃ S : Subrepresentation ρ,
      ((fixed ρ).quotientImage S).toSubmodule =
        ((fixed ρ).quotientImage c.productConfiguration.fixed).toSubmodule ∧
      SourceFactorCase ρ (second c) S := by
  have e := secondFactorEquiv c f
  cases f.actionCase with
  | natural hm hn =>
    have hs := second_moved_supplement c he f hm
    exact ⟨secondMoved c,second_moved_image c hs,
      .natural rfl (natural_equiv (FactorExtraction.transAction e (secondMovedEquiv c hs)) hn)⟩
  | doubleNatural F ho hm hn =>
    have hs := second_moved_supplement c he f hm
    exact ⟨secondMoved c,second_moved_image c hs,
      .doubleNatural F ho rfl ⟨FactorExtraction.transAction (actionSymm (FactorExtraction.transAction e (secondMovedEquiv c hs))) hn.some⟩⟩
  | exceptional hm h =>
    obtain ⟨q⟩ := four_source_equiv h48 e h
    exact ⟨c.productConfiguration.fixed,rfl,.exceptional (second_moved_le_fixed c he) q⟩

end CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.SplitCase
namespace CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension
open ComponentReduction
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- The split L₂ branch in the final proof of B.5.6 (printed p.110).
The only earlier-source input is full B.4.8(3). Its applicability is proved
on both transported four-dimensional actions; no splitting or classification
certificate is assumed beyond the supplied B.5.11 factor conclusion. -/
theorem adequate_of_split [Finite G] {K : GroupClass.{u}}
    (h48 : EarlierB48Three.{u,v}) (hyp : FFHypothesis K ρ)
    (c : ComponentReduction.Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    [Nontrivial (second c)] (f : FactorModuleConclusion (secondAction c))
    (hs : SplitAtSecond c) : AdequateAlternative ρ := by
  let := hyp.finite_module
  obtain ⟨x,hx,hd,_hxf,hcompl⟩ :=
    split_quotient_geometry c he hs (SplitCase.second_core_fixed c f)
  have hx' : x ∉ c.sectionData.space.toSubmodule ⊔ fixedSpace ρ c.first := by
    simpa only [c.productConfiguration.fixed_eq] using hx
  obtain ⟨a⟩ := chosenModule_source h48 c.sectionData.space (first_moved c he) he hx'
  obtain ⟨b⟩ := SplitCase.four_source_equiv h48 (firstSaturatedEquiv c he x hx hd) a
  obtain ⟨S,hS,hcase⟩ := SplitCase.second_factor_case h48 c he f
  apply Or.inr
  apply NontrivialAdequateAlternative.twoFactors
  refine ⟨c.first,second c,c.productConfiguration.product,
    saturatedModule c he x hd,S,?_,?_,hcase⟩
  · rw [hS]
    exact hcompl
  · apply SourceFactorCase.exceptional _ b
    change moved ρ c.first ≤ chosenSpace c.sectionData.space.toSubmodule x ⊔ ρ.invariants
    rw [first_moved c he]
    exact le_sup_left.trans le_sup_left

end CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension

