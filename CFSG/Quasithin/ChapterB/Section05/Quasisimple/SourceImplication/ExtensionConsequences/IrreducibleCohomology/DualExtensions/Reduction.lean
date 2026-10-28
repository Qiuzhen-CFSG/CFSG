module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Reduction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection
public import Theory.Representation.FirstCohomologyDuality
public import Theory.Representation.BinaryOffender.SectionOffender
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.NormalInvariants
public import Theory.Representation.BinarySylowFixedSpace

/-!
# The actual dual covering in the ratio-one branches of B.5.1

The natural moved section embeds in V/C_V(L). Comparing fixed codimensions
on this embedded section and the fixed kernel proves C_V(L)=C_V(G) when
q(G,[V,L]/C_[V,L](L))=1 and the original best offenders generate G.
Perfectness of L makes V/C_V(L) fixed-point-free; the same equality case
makes its quotient by the embedded section trivial. Thus this is an actual
dual covering, including when [V,L] has a central lower attachment.

Cocycle restriction detects the fixed-space obstruction in any such cover.
The consumer lifts the resulting supplement back to the original module.
For the linear-two row its supplied Sylow-offender description and odd
coset averaging prove detection, and hence the full supplement assertion.
No cohomology, splitting, or earlier-source theorem is assumed there.
The G2 rows require the separate concrete octonion detection calculation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1(5),
printed pp.102–103; B.1.5, printed pp.69–70; I.1.5, printed p.408.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences.DualExtensions
universe u v w z
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

private theorem fixedCodim_injection {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) G W} (i : ρ.IntertwiningMap σ)
    (hi : Function.Injective i) (A : Subgroup G) : fixedCodim ρ A ≤ fixedCodim σ A := by
  have hfix : (fixedSpace σ A).comap i.toLinearMap = fixedSpace ρ A := by
    ext v
    constructor
    · intro hv a
      apply hi
      exact (IntertwiningMap.isIntertwining _ _ i a v).trans (hv a)
    · intro hv a
      exact (IntertwiningMap.isIntertwining _ _ i a v).symm.trans (congrArg i (hv a))
  let q := (fixedSpace ρ A).mapQ (fixedSpace σ A) i.toLinearMap (le_of_eq hfix.symm)
  apply LinearMap.finrank_le_finrank_of_injective (f := q)
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.ker_mapQ, hfix, Submodule.mkQ_map_self]

noncomputable def fixedQuotient (L : Subgroup G) [L.Normal] :=
  (fixedSubrepresentationOfNormal ρ L).quotientRepresentation

noncomputable def naturalInFixedQuotient {L : Subgroup G} [L.Normal]
    (s : MovedSection ρ L) : s.action.IntertwiningMap (fixedQuotient (ρ := ρ) L) := by
  let C := fixedSubrepresentationOfNormal ρ L
  let f := C.toSubmodule.mkQ.comp s.space.toSubmodule.subtype
  have hker : s.central.toSubmodule ≤ f.ker := by
    intro v hv
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    rw [s.central_eq] at hv
    exact fun g => congrArg Subtype.val (hv g)
  let i := s.central.toSubmodule.liftQ f hker
  exact i.intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g v
    induction v using Submodule.Quotient.induction_on with | _ v => rfl)

theorem naturalInFixedQuotient_injective {L : Subgroup G} [L.Normal]
    (s : MovedSection ρ L) : Function.Injective (naturalInFixedQuotient s) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro v hv
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    rw [s.central_eq]
    have hc := (Submodule.Quotient.mk_eq_zero (fixedSubrepresentationOfNormal ρ L).toSubmodule).mp hv
    exact fun g => Subtype.ext (hc g)

theorem offender_equality [Finite G] [FiniteDimensional (ZMod 2) V]
    {L : Subgroup G} [L.Normal] (s : MovedSection ρ L)
    (hq : quadraticRatio s.action = 1) {A : Subgroup G} (hA : IsOffender ρ A) :
    IsBestOffender s.action A ∧ fixedCodim s.action A = rank A ∧
      s.space.toSubmodule ⊔ fixedSpace ρ A = ⊤ ∧ fixedSpace ρ L ≤ fixedSpace ρ A := by
  have hu := fixedCodim_subrepresentation_le ρ s.space A
  have hqbound := fixedCodim_quotient_add_subrepresentation_le s.space.toRepresentation s.central A
  have hv := hA.2
  change fixedCodim s.action A + _ ≤ _ at hqbound
  have hs : IsOffender s.action A := ⟨hA.1, by omega⟩
  obtain ⟨hb, he⟩ := hs.best_and_codim_eq_of_quadraticRatio_eq_one _ hq
  have hspan := (fixedCodim_subrepresentation_eq_iff ρ s.space A).mp (by omega)
  have hi := fixedCodim_injection (naturalInFixedQuotient s)
    (naturalInFixedQuotient_injective s) A
  have hc := fixedCodim_quotient_add_subrepresentation_le ρ (fixedSubrepresentationOfNormal ρ L) A
  have hz : fixedCodim (fixedSubrepresentationOfNormal ρ L).toRepresentation A = 0 := by
    change fixedCodim (fixedQuotient (ρ := ρ) L) A + _ ≤ _ at hc
    omega
  have hfix := (fixedCodim_eq_zero_iff (fixedSubrepresentationOfNormal ρ L).toRepresentation A).mp hz
  refine ⟨hb, he, hspan, ?_⟩
  intro v hv a
  have hx : (⟨v, hv⟩ : (fixedSubrepresentationOfNormal ρ L).toSubmodule) ∈
      fixedSpace (fixedSubrepresentationOfNormal ρ L).toRepresentation A := by
    rw [hfix]; trivial
  exact congrArg Subtype.val (hx a)

theorem section_generated [Finite G] [FiniteDimensional (ZMod 2) V]
    {L : Subgroup G} [L.Normal] (s : MovedSection ρ L)
    (hq : quadraticRatio s.action = 1) (hj : offenderSubgroup ρ = ⊤) :
    offenderSubgroup s.action = ⊤ := by
  apply top_unique
  rw [← hj]
  apply iSup_le
  intro A
  apply iSup_le
  rintro ⟨hA, _⟩
  exact le_iSup_of_le A (le_iSup_of_le
    ⟨(offender_equality s hq (hA.isOffender ρ)).1, le_top⟩ le_rfl)

theorem fixed_eq_invariants [Finite G] [FiniteDimensional (ZMod 2) V]
    {L : Subgroup G} [L.Normal] (s : MovedSection ρ L)
    (hq : quadraticRatio s.action = 1) (hj : offenderSubgroup ρ = ⊤) :
    fixedSpace ρ L = ρ.invariants := by
  have ht : offenderSubgroup ρ ≤ subspaceKernel ρ (fixedSpace ρ L) ⊤ := by
    apply iSup_le
    intro A
    apply iSup_le
    rintro ⟨hA, _⟩ a ha
    exact ⟨mem_top _, fun v hv => (offender_equality s hq (hA.isOffender ρ)).2.2.2 hv ⟨a, ha⟩⟩
  rw [hj] at ht
  exact le_antisymm (fun v hv g => (ht (mem_top g)).2 v hv) (fun _ hv g => hv g)

private theorem moved_trivial_quotient [Finite G] [FiniteDimensional (ZMod 2) V]
    {L : Subgroup G} [L.Normal] (s : MovedSection ρ L)
    (hq : quadraticRatio s.action = 1) (hj : offenderSubgroup ρ = ⊤) :
    HasTrivialQuotient s.space := by
  have ht : offenderSubgroup ρ ≤ s.space.quotientRepresentation.ker := by
    apply iSup_le
    intro A
    apply iSup_le
    rintro ⟨hA, _⟩ a ha
    rw [MonoidHom.mem_ker]
    apply LinearMap.ext
    intro v
    exact quotient_trivial_of_sup_fixedSpace ρ s.space A
      (offender_equality s hq (hA.isOffender ρ)).2.2.1 a ha v
  rw [hj] at ht
  intro g v
  have he := LinearMap.congr_fun (MonoidHom.mem_ker.mp (ht (mem_top g)))
    (s.space.toSubmodule.mkQ v)
  exact (Submodule.Quotient.eq _).mp he

private theorem fixedQuotient_no_fixed {L : Subgroup G} [L.Normal] [Group.IsPerfect L] :
    OneCohomology.fixed (fixedQuotient (ρ := ρ) L) = ⊥ := by
  apply bot_unique
  intro v hv
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    have hd (g : L) : ρ g v - v ∈ fixedSpace ρ L :=
      (Submodule.Quotient.eq _).mp (hv g)
    let f : L →* Multiplicative V :=
      { toFun := fun g => Multiplicative.ofAdd (ρ g v - v)
        map_one' := by simp
        map_mul' := by
          intro g t
          apply Multiplicative.toAdd.injective
          change ρ (g * t : L) v - v = (ρ g v - v) + (ρ t v - v)
          have hh := hd t g
          rw [map_sub] at hh
          simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
          change ρ g (ρ t v) - ρ g v = ρ t v - v at hh
          rw [sub_eq_iff_eq_add] at hh
          rw [hh]
          abel }
    let : Group.IsPerfect f.range := Group.IsPerfect.range f
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    intro g
    have he := congrArg Subtype.val (Subsingleton.elim (⟨f g, g, rfl⟩ : f.range) 1)
    exact sub_eq_zero.mp (congrArg Multiplicative.toAdd he)

theorem actual_dualCover [Finite G] [FiniteDimensional (ZMod 2) V]
    {L : Subgroup G} [L.Normal] [Group.IsPerfect L] (s : MovedSection ρ L)
    (hq : quadraticRatio s.action = 1) (hj : offenderSubgroup ρ = ⊤) :
    IsDualCover (naturalInFixedQuotient s).range := by
  refine ⟨?_, fixedQuotient_no_fixed (ρ := ρ) (L := L)⟩
  intro g v
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    exact ⟨s.central.toSubmodule.mkQ ⟨ρ g v - v, moved_trivial_quotient s hq hj g v⟩,
      (map_sub (fixedSubrepresentationOfNormal ρ L).toSubmodule.mkQ _ _).symm⟩

/-- Restriction to A detects the zero class in first cohomology. The cocycle
vanishes on A literally; no desired module splitting is included in this definition. -/
def CocycleDetection (τ : Representation (ZMod 2) G V) (A : Subgroup G) : Prop :=
  ∀ f : cocycles τ, (∀ a ∈ A, f.val a = 0) → ∃ v, principal τ v = f

private theorem base_no_fixed {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) G W} (i : ρ.IntertwiningMap σ)
    (hi : Function.Injective i) (hc : IsDualCover i.range) : OneCohomology.fixed ρ = ⊥ := by
  apply bot_unique
  intro v hv
  have hh : i v ∈ OneCohomology.fixed σ := by
    intro g
    exact (IntertwiningMap.isIntertwining _ _ i g v).symm.trans (congrArg i (hv g))
  rw [hc.2] at hh
  exact hi (hh.trans (map_zero i).symm)

/-- A detected cocycle forces every A-fixed vector of the actual dual cover
into the embedded natural module. The covering is arbitrary and its embedding
is retained; the fixed-space obstruction is a conclusion. -/
theorem fixed_le_range_of_detection {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) G W} (i : ρ.IntertwiningMap σ)
    (hi : Function.Injective i) (hc : IsDualCover i.range) {A : Subgroup G}
    (hdet : CocycleDetection ρ A) : fixedSpace σ A ≤ i.range.toSubmodule := by
  obtain ⟨d, hd, hdi⟩ := exists_dualCoverEmbedding i hi hc
  intro w hw
  obtain ⟨v, hv⟩ := hdet (d w) (by
    intro a ha
    have he := (IntertwiningMap.isIntertwining _ _ d a w).symm.trans
      (congrArg d (hw ⟨a, ha⟩))
    change d w + principal ρ ((d w).val a) = d w at he
    apply principal_injective (base_no_fixed i hi hc)
    exact (add_eq_left.mp he).trans (map_zero _).symm)
  exact ⟨v, hd ((hdi v).trans hv)⟩

/-- Odd Sylow index detects the cocycle. This proves the dual-cover geometry
for the linear-two row without any assumption on a chosen extension. -/
theorem sylow_cocycleDetection [Finite G] (S : Sylow 2 G)
    (hf : OneCohomology.fixed ρ = ⊥) : CocycleDetection ρ (S : Subgroup G) := by
  intro f hfa
  have hfix : f ∈ fixedSpace (universalAction ρ) S := by
    intro a
    change f + principal ρ (f.val a) = f
    rw [hfa a a.property, map_zero, add_zero]
  obtain ⟨w, hw, hv⟩ := BinarySylowFixedSpace.fixed_lift_mod_trivial_quotient
    (universalAction ρ) S (principal ρ).range (by
      intro g c
      exact ⟨c.val g, by change principal ρ (c.val g) = (c + principal ρ (c.val g)) - c; abel⟩)
    f hfix
  have hw0 : w = 0 := by
    have hm : w ∈ OneCohomology.fixed (universalAction ρ) := hw
    rwa [fixed_universalAction ρ hf] at hm
  rw [hw0, sub_zero] at hv
  exact hv

/-- Transport detection along the literal group and action equivalence. -/
theorem CocycleDetection.of_equiv {H : Type w} [Group H]
    {W : Type z} [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) H W} (e : ActionEquiv ρ σ) (A : Subgroup G)
    (hdet : CocycleDetection σ (A.map e.groupEquiv.toMonoidHom)) : CocycleDetection ρ A := by
  intro f hf
  let t := cocyclesCongr ρ σ e.groupEquiv e.linearEquiv e.intertwines
  obtain ⟨w, hw⟩ := hdet (t f) (by
    rintro _ ⟨a, ha, rfl⟩
    change e.linearEquiv (f.val (e.groupEquiv.symm (e.groupEquiv a))) = 0
    rw [e.groupEquiv.symm_apply_apply, hf a ha, map_zero])
  refine ⟨e.linearEquiv.symm w, t.injective ?_⟩
  rw [cocyclesCongr_principal, e.linearEquiv.apply_symm_apply]
  exact hw

/-- Consumer on the original moved section. The proof constructs V/C_V(L),
proves it is a dual cover of [V,L]/C_[V,L](L), applies the fixed-space
obstruction, and lifts back using C_V(L)=C_V(G). -/
theorem supplement_of_cocycleDetection [Finite G] {K : CFSG.Quasithin.GroupClass.{u}}
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (hq : quadraticRatio s.action = 1) {A : Subgroup G} (hA : IsOffender ρ A)
    (hdet : CocycleDetection s.action A) : s.space.toSubmodule ⊔ ρ.invariants = ⊤ := by
  let := h.finite_module
  let := h.quasisimple
  let := component_normal_of_fitting_eq_sup_center L h.fitting
  let C := fixedSubrepresentationOfNormal ρ L
  let i := naturalInFixedQuotient s
  have hc := actual_dualCover s hq h.generated
  have hf := fixed_le_range_of_detection i (naturalInFixedQuotient_injective s) hc hdet
  have hC := fixed_eq_invariants s hq h.generated
  rw [← hC]
  apply top_unique
  intro v _
  obtain ⟨u, hu, c, hca, rfl⟩ := Submodule.mem_sup.mp
    ((offender_equality s hq hA).2.2.1 ▸ Submodule.mem_top (x := v))
  have hqfix : C.toSubmodule.mkQ c ∈ fixedSpace (fixedQuotient (ρ := ρ) L) A :=
    fun a => congrArg C.toSubmodule.mkQ (hca a)
  obtain ⟨t, ht⟩ := hf hqfix
  obtain ⟨w, rfl⟩ := s.central.toSubmodule.mkQ_surjective t
  have hwc : c - w ∈ fixedSpace ρ L :=
    (Submodule.Quotient.eq _).mp ht.symm
  exact Submodule.mem_sup.mpr ⟨u + w, s.space.toSubmodule.add_mem hu w.property,
    c - w, hwc, by abel⟩

/-- The linear-two row has no upper extension, even when the moved module has
a nonzero central lower attachment. All hypotheses come from its actual row. -/
theorem linearTwo_supplement [Finite G] {K : CFSG.Quasithin.GroupClass.{u}}
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (hg : offenderSubgroup s.action = L)
    (hoff : ∀ A, IsBestOffender s.action A → ∃ S : Sylow 2 L,
      A = (S : Subgroup L).map L.subtype)
    (hq : quadraticRatio s.action = 1) : s.space.toSubmodule ⊔ ρ.invariants = ⊤ := by
  let := h.finite_module
  let := h.quasisimple
  let := component_normal_of_fitting_eq_sup_center L h.fitting
  have hL : L = ⊤ := hg.symm.trans (section_generated s hq h.generated)
  obtain ⟨A, hA⟩ := source_isFF h
  obtain ⟨S, hs⟩ := hoff A (offender_equality s hq hA).1
  let e : L ≃* G := (MulEquiv.subgroupCongr hL).trans Subgroup.topEquiv
  have he : e.toMonoidHom = L.subtype := by ext; rfl
  let T : Sylow 2 G := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hT : (T : Subgroup G) = A := by
    change (S : Subgroup L).map e.toMonoidHom = A
    rw [he, hs]
  have hf := base_no_fixed (naturalInFixedQuotient s) (naturalInFixedQuotient_injective s)
    (actual_dualCover s hq h.generated)
  apply supplement_of_cocycleDetection h s hq hA
  rw [← hT]
  exact sylow_cocycleDetection T hf

end CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences.DualExtensions
