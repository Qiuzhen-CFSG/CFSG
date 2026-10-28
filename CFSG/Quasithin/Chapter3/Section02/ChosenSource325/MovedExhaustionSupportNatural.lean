module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSupportClassification
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.Ranks
public import Theory.Quasithin.CoprimeRank
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# Natural support constituents and stability of the selected orbit

At three-rank one, the original perfect support has center prime to three.
Its literal central covering therefore preserves three-rank. The central orbit
section is fully moved and has no support-fixed vectors, so the complete B.5.1
classification identifies its actual action with a natural SL2, odd-degree
natural SL3, alternating-five, or doubled natural SL3 model.

An equivariant injection of the selected seed's central quotient into this
model yields its natural coordinates; in the doubled case choose a nonzero
coordinate projection. The map from the original support remains precisely
the original quotient projection followed by the model marking. Homogeneity
then makes every conjugate seed have the same type and hence equal the seed.
Thus the half-stabilizer orbit equals the seed, and the support image is
irreducible on the entire literal central orbit section.

The actual application is `SeedAlternativesMovedExhaustionSupportNatural`.
The remaining model and central-extension exclusions, component movement,
ambient multiplicities, Suzuki branch and U = W still belong to qt-baumann-fsu;
these statements establish the constituent-selection part of D.3.17, not its
final assertion that only natural SL3 survives.
Source: Aschbacher--Smith A.1.40--42, B.5.1 and D.3.17, printed
pp.31--32,99--103,203, in the proof of3.2.5, p.580; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterB.QuasisimpleSource
open ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
variable {H E : Type*} [Group H] [Finite H] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

omit [FiniteDimensional (ZMod 2) E] in
/-- The original central cover preserves the rank-one ternary bound. -/
theorem support_section_component_rank
    (ρ : Representation (ZMod 2) H E) (X P : Subgroup H) [IsQuasisimple X]
    (hr : primeRank 3 X = 1) (R : Submodule (ZMod 2) E)
    (hR : IsIrrPlusWith ρ X P R) :
    primeRank 3 ((X.subgroupOf (X ⊔ P)).map
      (KernelQuotient.projection (orbitSectionRepresentation ρ hR))) = 1 := by
  let c := supportSectionComponentCover ρ X P R hR
  let S : Sylow 3 X := default
  let := S.isCyclic_of_odd_of_primeRank_le_one (by decide : Odd 3) hr.le
  have hz := PerfectCentralCovering.not_dvd_card_kernel_of_abelian_sylow
    (QuotientGroup.mk' (center X)) (by rw [QuotientGroup.ker_mk']) S inferInstance
  rw [QuotientGroup.ker_mk'] at hz
  have hc : Nat.Coprime 3 (Nat.card c.toMonoidHom.ker) :=
    (Nat.prime_three.coprime_iff_not_dvd.mpr hz).of_dvd_right
      (card_dvd_of_le c.ker_le_center)
  exact (primeRank_eq_of_surjective_of_coprime 3 c.toMonoidHom c.surjective hc).symm.trans hr

omit [Finite H] [FiniteDimensional (ZMod 2) E] in
/-- Full support movement passes to the actual central orbit quotient. -/
theorem support_section_moved
    (ρ : Representation (ZMod 2) H E) (X P : Subgroup H)
    (R : Submodule (ZMod 2) E) (hR : IsIrrPlusWith ρ X P R) :
    let σ := orbitSectionRepresentation ρ hR
    moved (KernelQuotient.action σ)
      ((X.subgroupOf (X ⊔ P)).map (KernelQuotient.projection σ)) = ⊤ := by
  let J := X ⊔ P
  let W := orbitSpan ρ P R
  let hs := orbitSection_stable ρ hR.normalizes hR.isIrrPlus
  let τ : Representation (ZMod 2) J W := (invariantSubspace ρ J W hs).toRepresentation
  let σ := orbitSectionRepresentation ρ hR
  let δ := KernelQuotient.action σ
  let q := KernelQuotient.projection σ
  let X₀ := X.subgroupOf J
  have hm : subspaceCommutator τ ⊤ X₀ = ⊤ := by
    apply Submodule.map_injective_of_injective W.subtype_injective
    have he := subspaceCommutator_map_embedding (ρ.comp J.subtype) τ
      (MonoidHom.id J) W.subtype (fun _ _ => rfl) X₀ ⊤
    rw [Subgroup.map_id,subspaceCommutator_comp_map,Submodule.map_top,
      Submodule.range_subtype,map_subgroupOf_eq_of_le (show X ≤ J from le_sup_left)] at he
    rw [←he,Submodule.map_top,Submodule.range_subtype]
    exact orbitSpan_full_commutator ρ hR.normalizes hR.isIrrPlus
  let p := ((fixedSpace ρ X).comap W.subtype).mkQ
  have hact (j : J) (v : W) : (δ.comp q) j (p v) = p (τ j v) := by
    rw [MonoidHom.comp_apply,KernelQuotient.action_projection]
    rfl
  have he := subspaceCommutator_map_embedding (δ.comp q) τ (MonoidHom.id J) p hact X₀ ⊤
  rw [Subgroup.map_id,hm,Submodule.map_top,LinearMap.range_eq_top.mpr
    ((fixedSpace ρ X).comap W.subtype).mkQ_surjective] at he
  rw [subspaceCommutator_comp_map] at he
  exact he

omit [Finite H] [FiniteDimensional (ZMod 2) E] in
/-- Perfectness prevents new support-fixed vectors in the central quotient. -/
theorem support_section_fixed
    (ρ : Representation (ZMod 2) H E) (X P : Subgroup H) [Group.IsPerfect X]
    (R : Submodule (ZMod 2) E) (hR : IsIrrPlusWith ρ X P R) :
    let σ := orbitSectionRepresentation ρ hR
    fixedSpace (KernelQuotient.action σ)
      ((X.subgroupOf (X ⊔ P)).map (KernelQuotient.projection σ)) = ⊥ := by
  let J := X ⊔ P
  let W := orbitSpan ρ P R
  let σ := orbitSectionRepresentation ρ hR
  let q := KernelQuotient.projection σ
  let D := (X.subgroupOf J).map q
  apply bot_unique
  intro v hv
  obtain ⟨w,rfl⟩ := ((fixedSpace ρ X).comap W.subtype).mkQ_surjective v
  have hd (x : X) : ρ x.val w.val - w.val ∈ fixedSpace ρ X := by
    have hh := hv ⟨q (inclusion (show X ≤ J from le_sup_left) x),
      mem_map_of_mem q x.property⟩
    change KernelQuotient.action σ (q _) _ = _ at hh
    rw [KernelQuotient.action_projection] at hh
    exact (Submodule.Quotient.eq ((fixedSpace ρ X).comap W.subtype)).mp hh
  let f : X →* Multiplicative E := {
    toFun x := Multiplicative.ofAdd (ρ x.val w.val - w.val)
    map_one' := by simp
    map_mul' x y := by
      apply Multiplicative.toAdd.injective
      change ρ (x.val*y.val) w.val-w.val = (ρ x.val w.val-w.val)+(ρ y.val w.val-w.val)
      have hh := hd y x
      rw [map_sub] at hh
      rw [map_mul,Module.End.mul_apply]
      change ρ x.val (ρ y.val w.val)-ρ x.val w.val = ρ y.val w.val-w.val at hh
      rw [sub_eq_iff_eq_add] at hh
      rw [hh]
      abel }
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  intro x
  have hk := Abelianization.commutator_subset_ker f
  rw [Group.isPerfect_def.mp inferInstance] at hk
  exact sub_eq_zero.mp (congrArg Multiplicative.toAdd (hk (mem_top x)))

omit [Finite H] [FiniteDimensional (ZMod 2) E] in
private def fullMovedSpaceEquiv
    (ρ : Representation (ZMod 2) H E) (X : Subgroup H) (s : MovedSection ρ X)
    (hm : moved ρ X = ⊤) :
    ActionEquiv (s.space.toRepresentation.comp X.subtype) (ρ.comp X.subtype) :=
  ⟨MulEquiv.refl _, LinearEquiv.ofBijective s.space.toSubmodule.subtype
    ⟨Subtype.val_injective,fun v => ⟨⟨v,s.space_eq.symm ▸ hm.symm ▸ Submodule.mem_top⟩,rfl⟩⟩,
    fun _ _ => rfl⟩

omit [Finite H] [FiniteDimensional (ZMod 2) E] in
private def fullMovedSectionEquiv
    (ρ : Representation (ZMod 2) H E) (X : Subgroup H) (s : MovedSection ρ X)
    (hm : moved ρ X = ⊤) (hz : fixedSpace ρ X = ⊥) :
    ActionEquiv (s.action.comp X.subtype) (ρ.comp X.subtype) := by
  let e := fullMovedSpaceEquiv ρ X s hm
  have hf : Representation.invariants (s.space.toRepresentation.comp X.subtype) = ⊥ :=
    ExtensionConsequences.invariants_of_equiv e hz
  let q := ExtensionConsequences.movedQuotientEquiv s hf
  exact ⟨q.groupEquiv.trans e.groupEquiv,q.linearEquiv.trans e.linearEquiv,
    fun g v => (congrArg e.linearEquiv (q.intertwines g v)).trans
      (e.intertwines (q.groupEquiv g) (q.linearEquiv v))⟩

omit [Finite H] [FiniteDimensional (ZMod 2) E] in
/-- The exact remaining marked models of the whole support orbit section. -/
@[expose] def RankOneSupportOrbitModels (ρ : Representation (ZMod 2) H E) : Prop :=
  (∃ F : BinaryField, IsLinearNatural ρ F 2) ∨
  (∃ F : BinaryField, Odd F.degree ∧ IsLinearNatural ρ F 3) ∨
  IsAlternatingNatural ρ 5 ∨
  (∃ F : BinaryField, Odd F.degree ∧ IsRepeatedLinearNatural ρ F 3 2)

omit [FiniteDimensional (ZMod 2) E] in
private theorem rankOne_models_of_full_source
    (ρ : Representation (ZMod 2) H E) (X : Subgroup H)
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ X)
    (hr : primeRank 3 X = 1) (hm : moved ρ X = ⊤) (hz : fixedSpace ρ X = ⊥) :
    RankOneSupportOrbitModels (ρ.comp X.subtype) := by
  let s := c.sectionData
  let e := fullMovedSectionEquiv ρ X s hm hz
  have htrans {A W : Type} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
      {τ : Representation (ZMod 2) A W} (a : ActionEquiv (s.action.comp X.subtype) τ) :
      Nonempty (ActionEquiv (ρ.comp X.subtype) τ) := by
    let b := ExtensionConsequences.actionSymm e
    exact ⟨⟨b.groupEquiv.trans a.groupEquiv,b.linearEquiv.trans a.linearEquiv,
      fun g v => (congrArg a.linearEquiv (b.intertwines g v)).trans
        (a.intertwines (b.groupEquiv g) (b.linearEquiv v))⟩⟩
  cases rankOneAction_of_source ρ hr c.clause_one with
  | irreducible _ _ _ h _ =>
    cases h with
    | linearTwo F _ a _ _ => exact Or.inl ⟨F,htrans a⟩
    | linearThree F ho _ a _ => exact Or.inr (Or.inl ⟨F,ho,htrans a⟩)
    | symmetricFive a _ _ =>
      apply Or.inr ∘ Or.inr ∘ Or.inl
      apply htrans
      refine ⟨a.subgroupEquiv,a.action.linearEquiv,?_⟩
      intro g v
      have hh := a.action.intertwines ⟨g,a.contained g.property⟩ v
      rw [a.compatible] at hh
      exact hh
  | doubleThree F ho _ a _ _ =>
    let b := ExtensionConsequences.actionSymm (fullMovedSpaceEquiv ρ X s hm)
    exact Or.inr (Or.inr (Or.inr ⟨F,ho,⟨⟨b.groupEquiv.trans a.groupEquiv,
      b.linearEquiv.trans a.linearEquiv,
      fun g v => (congrArg a.linearEquiv (b.intertwines g v)).trans
        (a.intertwines (b.groupEquiv g) (b.linearEquiv v))⟩⟩⟩))

omit [FiniteDimensional (ZMod 2) E] in
/-- The full support orbit section has an actual natural or doubled-natural
model at three-rank one, with the possible alternating-five action retained. -/
theorem support_section_rankOne_models
    (ρ : Representation (ZMod 2) H E) (X P : Subgroup H) [IsQuasisimple X]
    (hr : primeRank 3 X = 1) (R : Submodule (ZMod 2) E)
    (hR : IsIrrPlusWith ρ X P R) (hclass : SupportSectionClassification ρ hR) :
    let σ := orbitSectionRepresentation ρ hR
    let D := (X.subgroupOf (X ⊔ P)).map (KernelQuotient.projection σ)
    RankOneSupportOrbitModels ((KernelQuotient.action σ).comp D.subtype) := by
  let σ := orbitSectionRepresentation ρ hR
  let δ := KernelQuotient.action σ
  let D := (X.subgroupOf (X ⊔ P)).map (KernelQuotient.projection σ)
  obtain ⟨_,hDJ,⟨c⟩⟩ := hclass
  let J := offenderSubgroup δ
  let C := D.subgroupOf J
  let α := δ.comp J.subtype
  have hm : moved α C = ⊤ := by
    change subspaceCommutator α ⊤ C = ⊤
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hDJ]
    exact support_section_moved ρ X P R hR
  have hz : fixedSpace α C = ⊥ := by
    rw [fixedSpace_comp_map,map_subgroupOf_eq_of_le hDJ]
    exact support_section_fixed ρ X P R hR
  have hrC : primeRank 3 C = 1 := by
    rw [primeRank_congr 3 (subgroupOfEquivOfLe hDJ)]
    exact support_section_component_rank ρ X P hr R hR
  have h := rankOne_models_of_full_source α C c hrC hm hz
  let e : ActionEquiv (δ.comp D.subtype) (α.comp C.subtype) :=
    ⟨(subgroupOfEquivOfLe hDJ).symm,LinearEquiv.refl _ _,fun _ _ => rfl⟩
  have ht {A W : Type} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
      {τ : Representation (ZMod 2) A W} (a : Nonempty (ActionEquiv (α.comp C.subtype) τ)) :
      Nonempty (ActionEquiv (δ.comp D.subtype) τ) := by
    obtain ⟨a⟩ := a
    exact ⟨⟨e.groupEquiv.trans a.groupEquiv,e.linearEquiv.trans a.linearEquiv,
      fun g v => (congrArg a.linearEquiv (e.intertwines g v)).trans
        (a.intertwines (e.groupEquiv g) (e.linearEquiv v))⟩⟩
  rcases h with ⟨F,h⟩ | ⟨F,ho,h⟩ | h | ⟨F,ho,h⟩
  · exact Or.inl ⟨F,ht h⟩
  · exact Or.inr (Or.inl ⟨F,ho,ht h⟩)
  · exact Or.inr (Or.inr (Or.inl (ht h)))
  · exact Or.inr (Or.inr (Or.inr ⟨F,ho,ht h⟩))

omit [Finite H] [FiniteDimensional (ZMod 2) E] in
private def supportSeedEmbedding
    (ρ : Representation (ZMod 2) H E) (X P : Subgroup H)
    (R : Submodule (ZMod 2) E) :
    centralQuotient ρ X R →ₗ[ZMod 2] centralQuotient ρ X (orbitSpan ρ P R) :=
  ((fixedSpace ρ X).comap R.subtype).liftQ
    (((fixedSpace ρ X).comap (orbitSpan ρ P R).subtype).mkQ.comp
      (Submodule.inclusion (le_orbitSpan ρ P R))) (by
        intro v hv
        exact (Submodule.Quotient.mk_eq_zero _).mpr hv)

omit [Finite H] [FiniteDimensional (ZMod 2) E] in
private theorem supportSeedEmbedding_injective
    (ρ : Representation (ZMod 2) H E) (X P : Subgroup H)
    (R : Submodule (ZMod 2) E) : Function.Injective (supportSeedEmbedding ρ X P R) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  induction v using Submodule.Quotient.induction_on with | _ v =>
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact (Submodule.Quotient.mk_eq_zero ((fixedSpace ρ X).comap (orbitSpan ρ P R).subtype)).mp hv

omit [Finite H] [FiniteDimensional (ZMod 2) E] in
private theorem supportSeedEmbedding_intertwines
    (ρ : Representation (ZMod 2) H E) (X P : Subgroup H) [IsQuasisimple X]
    (R : Submodule (ZMod 2) E) (hR : IsIrrPlusWith ρ X P R)
    (x : X) (v : centralQuotient ρ X R) :
    supportSeedEmbedding ρ X P R (centralQuotientRepresentation ρ X R hR.invariant x v) =
      KernelQuotient.action (orbitSectionRepresentation ρ hR)
        ((supportSectionComponentCover ρ X P R hR).toMonoidHom x)
          (supportSeedEmbedding ρ X P R v) := by
  rw [supportSectionComponentCover_apply,KernelQuotient.action_projection]
  induction v using Submodule.Quotient.induction_on with | _ v => rfl

private theorem equiv_of_simple_embedding
    {A B V W : Type*} [Group A] [Group B]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) A V) (τ : Representation (ZMod 2) B W)
    (hi : IsIrreducible σ) (ht : IsIrreducible τ)
    (f : A →* B) (hf : Function.Surjective f)
    (j : V →ₗ[ZMod 2] W) (hj : Function.Injective j)
    (he : ∀ a v, j (σ a v) = τ (f a) (j v)) :
    Nonempty (σ.Equiv (τ.comp f)) := by
  let := hi
  let : IsIrreducible (τ.comp f) := (irreducible_comp_surjective_iff f hf τ).mpr ht
  let p : σ.IntertwiningMap (τ.comp f) :=
    j.intertwiningMap_of_isIntertwiningMap _ _ he
  have hn : p ≠ 0 := by
    intro hp
    let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial σ
    obtain ⟨v,hv⟩ := exists_ne (0 : V)
    apply hv
    apply hj
    have hh := congrArg (fun t : σ.IntertwiningMap (τ.comp f) => t v) hp
    change j v = 0 at hh
    simpa only [map_zero] using hh
  exact ⟨p.ofBijective ((IsIrreducible.bijective_or_eq_zero p).resolve_right hn)⟩

private theorem equiv_of_simple_repeated_embedding
    {A B V W : Type*} [Group A] [Group B]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) A V) (τ : Representation (ZMod 2) B W)
    (hi : IsIrreducible σ) (ht : IsIrreducible τ)
    (f : A →* B) (hf : Function.Surjective f) (r : ℕ)
    (j : V →ₗ[ZMod 2] (Fin r → W)) (hj : Function.Injective j)
    (he : ∀ a v, j (σ a v) = repeated τ r (f a) (j v)) :
    Nonempty (σ.Equiv (τ.comp f)) := by
  classical
  let := hi
  let : IsIrreducible (τ.comp f) := (irreducible_comp_surjective_iff f hf τ).mpr ht
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial σ
  obtain ⟨v,hv⟩ := exists_ne (0 : V)
  have hjv : j v ≠ 0 := fun h => hv (hj (h.trans j.map_zero.symm))
  obtain ⟨i,hi⟩ : ∃ i : Fin r, j v i ≠ 0 := by
    by_contra! hh
    exact hjv (funext hh)
  let p : σ.IntertwiningMap (τ.comp f) :=
    ((LinearMap.proj i).comp j).intertwiningMap_of_isIntertwiningMap _ _
      (fun a w => congrFun (he a w) i)
  have hn : p ≠ 0 := by
    intro hp
    exact hi (congrArg (fun t : σ.IntertwiningMap (τ.comp f) => t v) hp)
  exact ⟨p.ofBijective ((IsIrreducible.bijective_or_eq_zero p).resolve_right hn)⟩

omit [Finite H] [FiniteDimensional (ZMod 2) E] in
/-- A marked natural constituent of the selected support seed. The actor map
is the original central orbit projection, followed by the displayed model mark. -/
@[expose] def SupportNaturalConstituent
    (ρ : Representation (ZMod 2) H E) {X P : Subgroup H}
    {R : Submodule (ZMod 2) E} (hR : IsIrrPlusWith ρ X P R) : Prop :=
  let σ := orbitSectionRepresentation ρ hR
  let D := (X.subgroupOf (X ⊔ P)).map (KernelQuotient.projection σ)
  let c := ((KernelQuotient.projection σ).subgroupMap (X.subgroupOf (X ⊔ P))).comp
    (subgroupOfEquivOfLe (show X ≤ X ⊔ P from le_sup_left)).symm.toMonoidHom
  let τ := centralQuotientRepresentation ρ X R hR.invariant
  (∃ (F : BinaryField) (e : D ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier),
    Nonempty (τ.Equiv ((linearNatural F 2).comp (e.toMonoidHom.comp c)))) ∨
  (∃ (F : BinaryField), Odd F.degree ∧
    ∃ e : D ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier,
    Nonempty (τ.Equiv ((linearNatural F 3).comp (e.toMonoidHom.comp c)))) ∨
  (∃ e : D ≃* alternatingGroup (Fin 5),
    Nonempty (τ.Equiv ((alternatingNatural 5).comp (e.toMonoidHom.comp c))))

omit [Finite H] [FiniteDimensional (ZMod 2) E] in
private theorem support_cover_map_eq
    (ρ : Representation (ZMod 2) H E) (X P : Subgroup H) [IsQuasisimple X]
    (R : Submodule (ZMod 2) E) (hR : IsIrrPlusWith ρ X P R) :
    (supportSectionComponentCover ρ X P R hR).toMonoidHom =
      ((KernelQuotient.projection (orbitSectionRepresentation ρ hR)).subgroupMap
        (X.subgroupOf (X ⊔ P))).comp
        (subgroupOfEquivOfLe (show X ≤ X ⊔ P from le_sup_left)).symm.toMonoidHom := by
  ext x
  exact supportSectionComponentCover_apply ρ X P R hR x

omit [FiniteDimensional (ZMod 2) E] in
/-- Select the original seed's natural constituent from the complete support
classification. A doubled orbit is projected onto a nonzero natural coordinate;
no natural seed or trivial covering kernel is assumed. -/
theorem support_natural_constituent
    (ρ : Representation (ZMod 2) H E) (X P : Subgroup H) [IsQuasisimple X]
    (hr : primeRank 3 X = 1) (R : Submodule (ZMod 2) E)
    (hR : IsIrrPlusWith ρ X P R) (hclass : SupportSectionClassification ρ hR) :
    SupportNaturalConstituent ρ hR := by

  let σ := orbitSectionRepresentation ρ hR
  let D := (X.subgroupOf (X ⊔ P)).map (KernelQuotient.projection σ)
  let c : X →* D := ((KernelQuotient.projection σ).subgroupMap (X.subgroupOf (X ⊔ P))).comp
    (subgroupOfEquivOfLe (show X ≤ X ⊔ P from le_sup_left)).symm.toMonoidHom
  have hmap : (supportSectionComponentCover ρ X P R hR).toMonoidHom = c :=
    support_cover_map_eq ρ X P R hR
  have hc : Function.Surjective c := hmap ▸ (supportSectionComponentCover ρ X P R hR).surjective
  let τ := centralQuotientRepresentation ρ X R hR.invariant
  have hi : IsIrreducible τ := hR.isIrrPlus.choose_spec.2
  let j := supportSeedEmbedding ρ X P R
  have hj := supportSeedEmbedding_injective ρ X P R
  have he (x : X) (v : centralQuotient ρ X R) :
      j (τ x v) = KernelQuotient.action σ (c x) (j v) := by
    have hh := supportSeedEmbedding_intertwines ρ X P R hR x v
    rw [hmap] at hh
    exact hh
  have lift_model {A W : Type} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
      (η : Representation (ZMod 2) A W) (hirr : IsIrreducible η)
      (a : ActionEquiv ((KernelQuotient.action σ).comp D.subtype) η) :
      Nonempty (τ.Equiv (η.comp (a.groupEquiv.toMonoidHom.comp c))) := by
    exact equiv_of_simple_embedding τ η hi hirr
      (a.groupEquiv.toMonoidHom.comp c) (a.groupEquiv.surjective.comp hc)
      (a.linearEquiv.toLinearMap.comp j) (a.linearEquiv.injective.comp hj)
      (fun x v => (congrArg a.linearEquiv (he x v)).trans
        (a.intertwines (c x) (j v)))
  rcases support_section_rankOne_models ρ X P hr R hR hclass with
    ⟨F,⟨a⟩⟩ | ⟨F,ho,⟨a⟩⟩ | ⟨a⟩ | ⟨F,ho,⟨a⟩⟩
  · exact Or.inl ⟨F,a.groupEquiv,lift_model _
      (ExtensionConsequences.linearNatural_irreducible F (by decide)) a⟩
  · exact Or.inr (Or.inl ⟨F,ho,a.groupEquiv,lift_model _
      (ExtensionConsequences.linearNatural_irreducible F (by decide)) a⟩)
  · obtain ⟨a⟩ := a
    exact Or.inr (Or.inr ⟨a.groupEquiv,lift_model (alternatingNatural 5)
      (BinaryPermutation.alternatingNatural_isIrreducible (Ω := Fin 5) (by decide)) a⟩)
  · apply Or.inr ∘ Or.inl
    refine ⟨F,ho,a.groupEquiv,?_⟩
    exact equiv_of_simple_repeated_embedding τ (linearNatural F 3) hi
      (ExtensionConsequences.linearNatural_irreducible F (by decide))
      (a.groupEquiv.toMonoidHom.comp c) (a.groupEquiv.surjective.comp hc) 2
      (a.linearEquiv.toLinearMap.comp j) (a.linearEquiv.injective.comp hj)
      (fun x v => (congrArg a.linearEquiv (he x v)).trans
        (a.intertwines (c x) (j v)))

omit [Finite H] [FiniteDimensional (ZMod 2) E] in
private theorem support_cover_action
    (ρ : Representation (ZMod 2) H E) (X P : Subgroup H) [IsQuasisimple X]
    (R : Submodule (ZMod 2) E) (hR : IsIrrPlusWith ρ X P R)
    (x : X) (v : centralQuotient ρ X (orbitSpan ρ P R)) :
    KernelQuotient.action (orbitSectionRepresentation ρ hR)
      ((supportSectionComponentCover ρ X P R hR).toMonoidHom x) v =
      centralQuotientRepresentation ρ X (orbitSpan ρ P R)
        (orbitSpan_component_invariant ρ hR.normalizes hR.isIrrPlus) x v := by
  rw [supportSectionComponentCover_apply,KernelQuotient.action_projection]
  rfl

omit [Finite H] [FiniteDimensional (ZMod 2) E] in
private theorem support_orbit_eq_of_repeated
    (ρ : Representation (ZMod 2) H E) (X P : Subgroup H) [IsQuasisimple X]
    (R : Submodule (ZMod 2) E) (hR : IsIrrPlusWith ρ X P R)
    {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
    (η : Representation (ZMod 2) A V) (hirr : IsIrreducible η) (r : ℕ)
    (a : ActionEquiv ((KernelQuotient.action (orbitSectionRepresentation ρ hR)).comp
      ((X.subgroupOf (X ⊔ P)).map (KernelQuotient.projection
        (orbitSectionRepresentation ρ hR))).subtype) (repeated η r)) :
    orbitSpan ρ P R = R := by
  let W := orbitSpan ρ P R
  let hW := orbitSpan_component_invariant ρ hR.normalizes hR.isIrrPlus
  let χ := fixedQuotientRepresentation ρ X
  let S := quotientImage ρ X R hR.invariant
  let Wbar := quotientImage ρ X W hW
  let c := supportSectionComponentCover ρ X P R hR
  let f := a.groupEquiv.toMonoidHom.comp c.toMonoidHom
  let eW : centralQuotient ρ X W ≃ₗ[ZMod 2] Wbar.toSubmodule :=
    centralQuotientImageEquiv ρ X W
  have hae (x : X) (v : centralQuotient ρ X W) :
      a.linearEquiv (centralQuotientRepresentation ρ X W hW x v) =
        repeated η r (f x) (a.linearEquiv v) := by
    exact (congrArg a.linearEquiv (support_cover_action ρ X P R hR x v).symm).trans
      (a.intertwines (c.toMonoidHom x) v)
  have model (Q : Subrepresentation χ) (hQ : Q.toSubmodule ≤ Wbar.toSubmodule)
      (hi : IsIrreducible Q.toRepresentation) :
      Nonempty (Q.toRepresentation.Equiv (η.comp f)) := by
    let k := eW.symm.toLinearMap.comp (Submodule.inclusion hQ)
    have hk : Function.Injective k :=
      eW.symm.injective.comp (Submodule.inclusion_injective hQ)
    have hke (x : X) (v : Q.toSubmodule) :
        k (Q.toRepresentation x v) = centralQuotientRepresentation ρ X W hW x (k v) := by
      apply eW.injective
      calc
        eW (k (Q.toRepresentation x v)) = Wbar.toRepresentation x (eW (k v)) := by
          change eW (eW.symm _) = Wbar.toRepresentation x (eW (eW.symm _))
          simp only [LinearEquiv.apply_symm_apply]
          rfl
        _ = eW (centralQuotientRepresentation ρ X W hW x (k v)) :=
          (centralQuotientImageEquiv_equivariant ρ X W hW x (k v)).symm
    exact equiv_of_simple_repeated_embedding Q.toRepresentation η hi hirr f
      (a.groupEquiv.surjective.comp c.surjective) r
      (a.linearEquiv.toLinearMap.comp k) (a.linearEquiv.injective.comp hk)
      (fun x v => (congrArg a.linearEquiv (hke x v)).trans (hae x (k v)))
  obtain ⟨b⟩ := model S (Submodule.map_mono (le_orbitSpan ρ P R))
    (quotientImage_irreducible ρ hR.isIrrPlus)
  apply le_antisymm _ (le_orbitSpan ρ P R)
  apply iSup_le
  intro p
  have hp := hR.isIrrPlus.map_normalizer ρ (hR.normalizes p.property)
  let Q := quotientImage ρ X (R.map (ρ p.val)) hp.choose
  have hQ : Q.toSubmodule ≤ Wbar.toSubmodule :=
    Submodule.map_mono (le_iSup (fun p : P => R.map (ρ p.val)) p)
  obtain ⟨d⟩ := model Q hQ (quotientImage_irreducible ρ hp)
  have same : SameModule S Q := by
    let e := b.trans d.symm
    exact ⟨e.toLinearEquiv,fun x v =>
      Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap x v⟩
  exact (hR.eq_of_isomorphic_conjugate ρ p same).le

omit [Finite H] [FiniteDimensional (ZMod 2) E] in
private theorem support_orbit_eq_of_simple
    (ρ : Representation (ZMod 2) H E) (X P : Subgroup H) [IsQuasisimple X]
    (R : Submodule (ZMod 2) E) (hR : IsIrrPlusWith ρ X P R)
    {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
    (η : Representation (ZMod 2) A V) (hirr : IsIrreducible η)
    (a : ActionEquiv ((KernelQuotient.action (orbitSectionRepresentation ρ hR)).comp
      ((X.subgroupOf (X ⊔ P)).map (KernelQuotient.projection
        (orbitSectionRepresentation ρ hR))).subtype) η) :
    orbitSpan ρ P R = R := by
  apply support_orbit_eq_of_repeated ρ X P R hR η hirr 1
  exact ⟨a.groupEquiv,a.linearEquiv.trans
    (LinearEquiv.funUnique (Fin 1) (ZMod 2) V).symm,fun _ _ => by
      ext i
      exact a.intertwines _ _⟩

omit [FiniteDimensional (ZMod 2) E] in
/-- Rank-one classification and the defining multiplicity-one property of the
selected seed force its entire half-stabilizer orbit to equal the seed. -/
theorem support_orbit_eq_seed
    (ρ : Representation (ZMod 2) H E) (X P : Subgroup H) [IsQuasisimple X]
    (hr : primeRank 3 X = 1) (R : Submodule (ZMod 2) E)
    (hR : IsIrrPlusWith ρ X P R) (hclass : SupportSectionClassification ρ hR) :
    orbitSpan ρ P R = R := by
  rcases support_section_rankOne_models ρ X P hr R hR hclass with
    ⟨F,⟨a⟩⟩ | ⟨F,ho,⟨a⟩⟩ | ⟨a⟩ | ⟨F,ho,⟨a⟩⟩
  · exact support_orbit_eq_of_simple ρ X P R hR (linearNatural F 2)
      (ExtensionConsequences.linearNatural_irreducible F (by decide)) a
  · exact support_orbit_eq_of_simple ρ X P R hR (linearNatural F 3)
      (ExtensionConsequences.linearNatural_irreducible F (by decide)) a
  · obtain ⟨a⟩ := a
    exact support_orbit_eq_of_simple ρ X P R hR (alternatingNatural 5)
      (BinaryPermutation.alternatingNatural_isIrreducible (Ω := Fin 5) (by decide)) a
  · exact support_orbit_eq_of_repeated ρ X P R hR (linearNatural F 3)
      (ExtensionConsequences.linearNatural_irreducible F (by decide)) 2 a

omit [FiniteDimensional (ZMod 2) E] in
/-- The support image acts irreducibly on the whole literal central orbit
section: homogeneity has removed the apparent repeated-natural possibility. -/
theorem support_section_irreducible
    (ρ : Representation (ZMod 2) H E) (X P : Subgroup H) [IsQuasisimple X]
    (hr : primeRank 3 X = 1) (R : Submodule (ZMod 2) E)
    (hR : IsIrrPlusWith ρ X P R) (hclass : SupportSectionClassification ρ hR) :
    let σ := orbitSectionRepresentation ρ hR
    let D := (X.subgroupOf (X ⊔ P)).map (KernelQuotient.projection σ)
    IsIrreducible ((KernelQuotient.action σ).comp D.subtype) := by
  let σ := orbitSectionRepresentation ρ hR
  let D := (X.subgroupOf (X ⊔ P)).map (KernelQuotient.projection σ)
  let c := supportSectionComponentCover ρ X P R hR
  let τ := centralQuotientRepresentation ρ X R hR.invariant
  let η := (KernelQuotient.action σ).comp D.subtype
  let j := supportSeedEmbedding ρ X P R
  have heq := support_orbit_eq_seed ρ X P hr R hR hclass
  have hj : Function.Surjective j := by
    intro v
    obtain ⟨w,rfl⟩ := ((fixedSpace ρ X).comap (orbitSpan ρ P R).subtype).mkQ_surjective v
    exact ⟨((fixedSpace ρ X).comap R.subtype).mkQ ⟨w.val,by simpa only [heq] using w.property⟩,rfl⟩
  let e : ActionEquiv τ (η.comp c.toMonoidHom) :=
    ⟨MulEquiv.refl _,LinearEquiv.ofBijective j
      ⟨supportSeedEmbedding_injective ρ X P R,hj⟩,
      supportSeedEmbedding_intertwines ρ X P R hR⟩
  apply (irreducible_comp_surjective_iff c.toMonoidHom c.surjective η).mp
  exact ExtensionConsequences.irreducible_of_equiv (ExtensionConsequences.actionSymm e)
    hR.isIrrPlus.choose_spec.2

omit [Finite H] [FiniteDimensional (ZMod 2) E] in
/-- The natural seed and its stable, irreducible central orbit section. Naming
this conclusion keeps the literal quotient instances local in Chapter12. -/
@[expose] def SupportNaturalSection
    (ρ : Representation (ZMod 2) H E) {X P : Subgroup H}
    {R : Submodule (ZMod 2) E} (hR : IsIrrPlusWith ρ X P R) : Prop :=
  SupportNaturalConstituent ρ hR ∧ orbitSpan ρ P R = R ∧
    P ≤ subspaceStabilizer ρ R ∧
    let σ := orbitSectionRepresentation ρ hR
    IsIrreducible ((KernelQuotient.action σ).comp
      ((X.subgroupOf (X ⊔ P)).map (KernelQuotient.projection σ)).subtype)

omit [FiniteDimensional (ZMod 2) E] in
/-- The complete selected-support conclusion from the genuine classification
and the original rank bound; its Chapter12 application adds no model premise. -/
theorem support_natural_section
    (ρ : Representation (ZMod 2) H E) (X P : Subgroup H) [IsQuasisimple X]
    (hr : primeRank 3 X = 1) (R : Submodule (ZMod 2) E)
    (hR : IsIrrPlusWith ρ X P R) (hclass : SupportSectionClassification ρ hR) :
    SupportNaturalSection ρ hR := by
  have he := support_orbit_eq_seed ρ X P hr R hR hclass
  refine ⟨support_natural_constituent ρ X P hr R hR hclass,he,?_,
    support_section_irreducible ρ X P hr R hR hclass⟩
  rw [←he]
  exact orbitSpan_invariant ρ P R

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
