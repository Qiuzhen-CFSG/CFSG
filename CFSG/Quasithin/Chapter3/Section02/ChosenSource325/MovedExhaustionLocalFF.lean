module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.FFQuasisimple
public import Theory.GroupTheory.PerfectCentralizerLift
public import Theory.Representation.BinaryOffender.IrreducibleMovedGeneration
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# The faithful local FF section in the moved chosen-seed argument

The Sylow part of the component centralizer fixing a section forces its
faithful action image to have trivial two-core. Perfectness lifts the image
centralizer, so this remains valid for a quasisimple central cover. The full
corrected B.5.1 theorem then applies to the literal offender subgroup.

Two distinct simple component types cannot occur in a homogeneous chart:
projection onto a nonzero coordinate identifies each simple copy. For a fully
moved, fixed-free section B.5.1 therefore leaves the actual natural-plus-dual
model for SL₄(2) or SL₅(2). These cases remain possible FF modules.

The original Chapter12 application is SeedAlternativesMovedExhaustionLocalFF.
The quotient offender, binary multiplicity argument and final Source325
assembly remain with qt-baumann-fsu.
Source: Aschbacher--Smith B.5.1(3) and D.3.9(1), printed pp.99--103,199--200,
used in D.3.13 and 3.2.5, pp.202,580; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
universe u
variable {H E : Type u} [Group H] [Finite H] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

omit [Finite H] [FiniteDimensional (ZMod 2) E] in
private theorem image_component_ne_bot
    (ρ : Representation (ZMod 2) H E) (K : Subgroup H) (hn : ¬ K ≤ ρ.ker) :
    actionSubgroup ρ K ≠ ⊥ := by
  intro hz
  apply hn
  intro k hk
  have he : actionHom ρ k = 1 := (map_eq_bot_iff K).mp hz hk
  exact (congrArg (imageRepresentation ρ) he).trans (map_one _)

omit [FiniteDimensional (ZMod 2) E] in
/-- The actual faithful section image has trivial two-core. -/
theorem local_section_image_twoCore_eq_bot
    (ρ : Representation (ZMod 2) H E) (K : Subgroup H) [K.Normal] [IsQuasisimple K]
    (hn : ¬ K ≤ ρ.ker) (S : Sylow 2 H)
    (hfix : (S : Subgroup H) ⊓ centralizer (K : Set H) ≤ ρ.ker) :
    pCore 2 (actionImage ρ) = ⊥ := by
  let q := actionHom ρ
  let D := actionSubgroup ρ K
  have hq : Function.Surjective q := ρ.asGroupHom.rangeRestrict_surjective
  let : D.Normal := (inferInstance : K.Normal).map q hq
  let : Nontrivial D := (Subgroup.nontrivial_iff_ne_bot D).mpr (image_component_ne_bot ρ K hn)
  let : IsQuasisimple D := IsQuasisimple.of_surjective (q.subgroupMap K)
    (q.subgroupMap_surjective K)
  have hker : q.ker ≤ centralizer (K : Set H) := by
    have hK : IsComponent H K := ⟨(inferInstance : K.Normal).isSubnormal,inferInstance⟩
    apply le_centralizer_iff.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply (hK.normal_dichotomy q.ker).resolve_left
    intro hk
    apply hn
    intro k hkK
    exact (congrArg (imageRepresentation ρ) (hk hkK)).trans (map_one _)
  have hDC : pCore 2 (actionImage ρ) ≤ centralizer (D : Set (actionImage ρ)) := by
    have hD : IsComponent (actionImage ρ) D := ⟨(inferInstance : D.Normal).isSubnormal,inferInstance⟩
    rcases hD.normal_dichotomy (pCore 2 (actionImage ρ)) with hh | hh
    · let : Group.IsNilpotent D := (pCore_isPGroup.to_le hh).isNilpotent
      exact (Group.IsPerfect.not_isSolvable D IsNilpotent.to_isSolvable).elim
    · exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh)
  have hNC : (pCore 2 (actionImage ρ)).comap q ≤ centralizer (K : Set H) := by
    have hh := Subgroup.comap_mono (f := q) hDC
    change _ ≤ (centralizer (K.map q : Set (actionImage ρ))).comap q at hh
    rwa [comap_centralizer_map_eq_of_perfect q K hker] at hh
  have hOS : pCore 2 (actionImage ρ) ≤ (S : Subgroup H).map q :=
    pCore_isPGroup.le_sylow_of_normal (S.mapSurjective hq)
  apply bot_unique
  intro x hx
  obtain ⟨s,hs,rfl⟩ := hOS hx
  have hk : s ∈ ρ.ker := hfix ⟨hs,hNC hx⟩
  apply (actionHom_eq_one_iff ρ s).mpr
  intro v
  exact LinearMap.congr_fun hk v

/-- All six corrected B.5.1 clauses on the literal section action image. -/
theorem local_section_ff_classification
    (ρ : Representation (ZMod 2) H E) (K : Subgroup H) [K.Normal] [IsQuasisimple K]
    (hn : ¬ K ≤ ρ.ker) (S : Sylow 2 H)
    (hfix : (S : Subgroup H) ⊓ centralizer (K : Set H) ≤ ρ.ker)
    (hquot : IsPGroup 2 (H ⧸ K)) (hsq : IsSQTK KnownSimple.IsKnownSimple K)
    (hff : IsFFModule (imageRepresentation ρ)) :
    actionSubgroup ρ K ≤ offenderSubgroup (imageRepresentation ρ) ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((imageRepresentation ρ).comp (offenderSubgroup (imageRepresentation ρ)).subtype)
        ((actionSubgroup ρ K).subgroupOf (offenderSubgroup (imageRepresentation ρ)))) := by
  let q := actionHom ρ
  let D := actionSubgroup ρ K
  have hq : Function.Surjective q := ρ.asGroupHom.rangeRestrict_surjective
  let : D.Normal := (inferInstance : K.Normal).map q hq
  let : Nontrivial D := (Subgroup.nontrivial_iff_ne_bot D).mpr (image_component_ne_bot ρ K hn)
  let : IsQuasisimple D := IsQuasisimple.of_surjective (q.subgroupMap K)
    (q.subgroupMap_surjective K)
  have hquot' : IsPGroup 2 (actionImage ρ ⧸ D) := by
    have hm : K ≤ D.comap q := fun _ hk => mem_map_of_mem q hk
    exact hquot.of_surjective (QuotientGroup.map K D q hm)
      (QuotientGroup.map_surjective_of_surjective _ _ q
        ((QuotientGroup.mk'_surjective _).comp hq) hm)
  have hsq' : IsSQTK KnownSimple.IsKnownSimple D :=
    ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.quasisimple_section_sqtk
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple) hsq
      (ChapterA.Section02.IsSectionOf.of_surjective (q.subgroupMap K) (q.subgroupMap_surjective K))
  exact ChapterB.QuasisimpleSource.SourceCompletion.ff_quasisimple_source_conclusion
    (imageRepresentation ρ) D hquot' (local_section_image_twoCore_eq_bot ρ K hn S hfix)
    hsq' (imageRepresentation_injective ρ) hff
end CFSG.Quasithin.Chapter3.Section02.ChosenSource325

namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterB.QuasisimpleSource
variable {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]

private theorem simple_equiv_homogeneous_constituent
    (ρ : Representation (ZMod 2) H E)
    {P F : Type*} [Group P] [AddCommGroup F] [Module (ZMod 2) F]
    (σ : Representation (ZMod 2) P F) (e : ActionEquiv ρ σ)
    (r : ℕ) (W : Subrepresentation σ) (hiW : IsIrreducible W.toRepresentation)
    (f : F ≃ₗ[ZMod 2] (Fin r → W.toSubmodule))
    (hf : ∀ g v, f (σ g v) = repeated W.toRepresentation r g (f v))
    (I : Subrepresentation ρ) (hi : IsIrreducible I.toRepresentation) :
    Nonempty (I.toRepresentation.Equiv (W.toRepresentation.comp e.groupEquiv.toMonoidHom)) := by
  let τ := W.toRepresentation.comp e.groupEquiv.toMonoidHom
  let := hi
  let : IsIrreducible τ :=
    (irreducible_comp_surjective_iff e.groupEquiv.toMonoidHom e.groupEquiv.surjective _).mpr hiW
  let : Nontrivial I.toSubmodule := Subrepresentation.irreducible_module_nontrivial I.toRepresentation
  obtain ⟨v,hv⟩ := exists_ne (0 : I.toSubmodule)
  have hne : f (e.linearEquiv v.val) ≠ 0 := by
    intro hz
    apply hv
    apply Subtype.ext
    apply e.linearEquiv.injective
    apply f.injective
    simpa using hz
  obtain ⟨i,hi⟩ : ∃ i : Fin r, f (e.linearEquiv v.val) i ≠ 0 := by
    by_contra! hh
    exact hne (funext hh)
  let p : I.toRepresentation.IntertwiningMap τ :=
    ((LinearMap.proj i).comp (f.toLinearMap.comp (e.linearEquiv.toLinearMap.comp I.toSubmodule.subtype))).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g v
      change f (e.linearEquiv (ρ g v.val)) i = W.toRepresentation (e.groupEquiv g) (f (e.linearEquiv v.val) i)
      rw [e.intertwines,hf]
      rfl)
  have hp : p ≠ 0 := by
    intro hz
    exact hi (congrArg (fun q : I.toRepresentation.IntertwiningMap τ => q v) hz)
  exact ⟨p.ofBijective ((IsIrreducible.bijective_or_eq_zero p).resolve_right hp)⟩

/-- A homogeneous chart cannot contain two distinct simple types, even after
an actual change of actor and vector coordinates. -/
theorem same_simple_types_of_homogeneous_chart
    (ρ : Representation (ZMod 2) H E)
    {P F : Type*} [Group P] [AddCommGroup F] [Module (ZMod 2) F]
    (σ : Representation (ZMod 2) P F) (e : ActionEquiv ρ σ)
    (hh : IsHomogeneousAction σ) (I J : Subrepresentation ρ)
    (hi : IsIrreducible I.toRepresentation) (hj : IsIrreducible J.toRepresentation) :
    Nonempty (I.toRepresentation.Equiv J.toRepresentation) := by
  obtain ⟨r,_,W,hw,f,hf⟩ := hh
  obtain ⟨a⟩ := simple_equiv_homogeneous_constituent ρ σ e r W hw f hf I hi
  obtain ⟨b⟩ := simple_equiv_homogeneous_constituent ρ σ e r W hw f hf J hj
  exact ⟨a.trans b.symm⟩

/-- B.5.1(3) leaves precisely the binary natural-plus-dual model on a
fully moved, fixed-free module containing two distinct simple component types. -/
theorem naturalDual_of_source_distinct_simple_types
    (ρ : Representation (ZMod 2) H E) (K : Subgroup H)
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ K)
    (hm : moved ρ K = ⊤) (hz : fixedSpace ρ K = ⊥)
    {P F : Type*} [Group P] [AddCommGroup F] [Module (ZMod 2) F]
    (τ : Representation (ZMod 2) P F) (a : ActionEquiv τ (ρ.comp K.subtype))
    (I J : Subrepresentation τ)
    (hi : IsIrreducible I.toRepresentation) (hj : IsIrreducible J.toRepresentation)
    (hne : ¬ Nonempty (I.toRepresentation.Equiv J.toRepresentation)) :
    ∃ d : ℕ, (d = 4 ∨ d = 5) ∧ IsNaturalPlusDual τ d := by
  let s := c.sectionData
  have hs : s.space.toSubmodule = ⊤ := s.space_eq.trans hm
  let f : s.space.toSubmodule ≃ₗ[ZMod 2] E :=
    LinearEquiv.ofBijective s.space.toSubmodule.subtype
      ⟨Subtype.val_injective,fun v => ⟨⟨v,hs ▸ Submodule.mem_top⟩,rfl⟩⟩
  let e : ActionEquiv (s.space.toRepresentation.comp K.subtype) (ρ.comp K.subtype) :=
    ⟨MulEquiv.refl K,f,fun _ _ => rfl⟩
  rcases c.clause_three with hh | ⟨d,hd,⟨b⟩⟩
  · have hfix : Representation.invariants (s.space.toRepresentation.comp K.subtype) = ⊥ :=
      ExtensionConsequences.invariants_of_equiv e hz
    let q := ExtensionConsequences.movedQuotientEquiv s hfix
    let t : ActionEquiv (s.action.comp K.subtype) (ρ.comp K.subtype) :=
      ⟨q.groupEquiv.trans e.groupEquiv,q.linearEquiv.trans e.linearEquiv,
        fun g v => (congrArg e.linearEquiv (q.intertwines g v)).trans
          (e.intertwines (q.groupEquiv g) (q.linearEquiv v))⟩
    let b := ExtensionConsequences.actionSymm t
    let ab : ActionEquiv τ (s.action.comp K.subtype) :=
      ⟨a.groupEquiv.trans b.groupEquiv,a.linearEquiv.trans b.linearEquiv,
        fun g v => (congrArg b.linearEquiv (a.intertwines g v)).trans
          (b.intertwines (a.groupEquiv g) (a.linearEquiv v))⟩
    exact (hne (same_simple_types_of_homogeneous_chart _ _ ab hh I J hi hj)).elim
  · let t := ExtensionConsequences.actionSymm e
    let chart : ActionEquiv τ (s.space.toRepresentation.comp K.subtype) :=
      ⟨a.groupEquiv.trans t.groupEquiv,a.linearEquiv.trans t.linearEquiv,
        fun g v => (congrArg t.linearEquiv (a.intertwines g v)).trans
          (t.intertwines (a.groupEquiv g) (a.linearEquiv v))⟩
    exact ⟨d,hd,⟨⟨chart.groupEquiv.trans b.groupEquiv,chart.linearEquiv.trans b.linearEquiv,
      fun g v => (congrArg b.linearEquiv (chart.intertwines g v)).trans
        (b.intertwines (chart.groupEquiv g) (chart.linearEquiv v))⟩⟩⟩
end CFSG.Quasithin.Chapter3.Section02.ChosenSource325

namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterB.QuasisimpleSource
universe u
variable {H E : Type u} [Group H] [Finite H] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- The literal FF section with two distinct simple types is the binary
natural-plus-dual module. Faithfulness on the component identifies its image;
no such identification is assumed before proving injectivity. -/
theorem local_section_ff_naturalDual
    (ρ : Representation (ZMod 2) H E) (K : Subgroup H) [K.Normal] [IsQuasisimple K]
    (hf : Function.Injective (ρ.comp K.subtype)) (S : Sylow 2 H)
    (hfix : (S : Subgroup H) ⊓ centralizer (K : Set H) ≤ ρ.ker)
    (hquot : IsPGroup 2 (H ⧸ K)) (hsq : IsSQTK KnownSimple.IsKnownSimple K)
    (hff : IsFFModule (imageRepresentation ρ))
    (hm : moved ρ K = ⊤) (hz : fixedSpace ρ K = ⊥)
    (I J : Subrepresentation (ρ.comp K.subtype))
    (hi : IsIrreducible I.toRepresentation) (hj : IsIrreducible J.toRepresentation)
    (hne : ¬ Nonempty (I.toRepresentation.Equiv J.toRepresentation)) :
    ∃ d : ℕ, (d = 4 ∨ d = 5) ∧ IsNaturalPlusDual (ρ.comp K.subtype) d := by
  let q := actionHom ρ
  let C := actionSubgroup ρ K
  let δ := imageRepresentation ρ
  have hn : ¬ K ≤ ρ.ker := by
    intro hk
    have htriv : ∀ x : K, x = 1 := by
      intro x
      apply hf
      exact (hk x.property).trans (map_one _).symm
    let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
    exact Group.IsPerfect.not_isMulCommutative K ⟨⟨fun x y => by rw [htriv x,htriv y]⟩⟩
  obtain ⟨hCJ,⟨c⟩⟩ := local_section_ff_classification ρ K hn S hfix hquot hsq hff
  let O := offenderSubgroup δ
  let C₀ := C.subgroupOf O
  let α := δ.comp O.subtype
  have hqi : Function.Injective (q.subgroupMap K) := by
    intro x y he
    apply hf
    exact congrArg (fun z : C => δ z.val) he
  let ek : K ≃* C := MulEquiv.ofBijective (q.subgroupMap K) ⟨hqi,q.subgroupMap_surjective K⟩
  let a : ActionEquiv (ρ.comp K.subtype) (α.comp C₀.subtype) :=
    ⟨ek.trans (subgroupOfEquivOfLe hCJ).symm,LinearEquiv.refl _ _,fun _ _ => rfl⟩
  have hm' : moved α C₀ = ⊤ := by
    change subspaceCommutator α ⊤ C₀ = ⊤
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hCJ]
    change subspaceCommutator δ ⊤ (K.map q) = ⊤
    rw [←subspaceCommutator_comp_map]
    exact hm
  have hz' : fixedSpace α C₀ = ⊥ := by
    rw [fixedSpace_comp_map,map_subgroupOf_eq_of_le hCJ]
    exact (fixedSpace_actionSubgroup ρ K).trans hz
  exact naturalDual_of_source_distinct_simple_types α C₀ c hm' hz'
    (ρ.comp K.subtype) a I J hi hj hne
end CFSG.Quasithin.Chapter3.Section02.ChosenSource325

namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]

/-- Two simple summands with zero component-fixed space generate the whole
module by component commutators. -/
theorem moved_eq_top_of_simple_pair
    (ρ : Representation (ZMod 2) H E) (K : Subgroup H)
    (I J : Subrepresentation (ρ.comp K.subtype))
    (hi : IsIrreducible I.toRepresentation) (hj : IsIrreducible J.toRepresentation)
    (hspan : I.toSubmodule ⊔ J.toSubmodule = ⊤) (hz : fixedSpace ρ K = ⊥) :
    ChapterB.QuasisimpleSource.moved ρ K = ⊤ := by
  have hle (S : Subrepresentation (ρ.comp K.subtype))
      (hs : IsIrreducible S.toRepresentation) : S.toSubmodule ≤ subspaceCommutator ρ ⊤ K := by
    let Q : Subrepresentation (ρ.comp K.subtype) := {
      toSubmodule := subspaceCommutator ρ S.toSubmodule K
      apply_mem_toSubmodule := fun k v hv =>
        (subspaceCommutator_invariant ρ S.toSubmodule K k.property v).2 hv }
    have hQS : Q ≤ S := subspaceCommutator_le_of_invariant ρ
      (le_subspaceStabilizer ρ S.toSubmodule (fun k hk v hv => S.apply_mem_toSubmodule ⟨k,hk⟩ hv))
    have hn : Q ≠ ⊥ := by
      intro he
      have hh := (subspaceCommutator_eq_bot_iff ρ S.toSubmodule K).mp
        (congrArg Subrepresentation.toSubmodule he)
      rw [hz] at hh
      exact ((Subrepresentation.irreducible_iff_isAtom S).mp hs).ne_bot
        (Subrepresentation.toSubmodule_injective (bot_unique hh))
    have he : Q = S := by
      by_contra hh
      exact hn (((Subrepresentation.irreducible_iff_isAtom S).mp hs).2 Q
        (lt_of_le_of_ne hQS hh))
    rw [←congrArg Subrepresentation.toSubmodule he]
    exact subspaceCommutator_mono_left ρ le_top K
  exact top_unique (hspan ▸ sup_le (hle I hi) (hle J hj))
end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
