module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.Models
public import Theory.Representation.FirstCohomologyDuality
public import Theory.Representation.BinaryAlternatingNaturalCohomology
public import Theory.Representation.BinaryAlternatingNaturalCohomology.Even
public import Theory.Representation.BinaryPermutationNaturalDuality

/-!
# Central covers of the actual moved section in B.5.7

The literal projection from [V,L] to its quotient by C_[V,L](L) is a
commutator-generated central cover. The universal covering theorem bounds
its kernel by dual first cohomology. For the marked alternating natural
actions, this gives no kernel in degree seven and a one-dimensional kernel
in the nontrivial degree-six case. The latter moved space has dimension five.
When the kernel is zero, the quotient intertwiner lifts with exactly the
same actor isomorphism and alternating-subgroup marking.

`ReducedSymmetricModel` is an intermediate proof target, not an earlier
source input. It retains all six B.5.1 clauses and requires the cover/model
comparison to construct the marked quotient action. No model identification
of a nontrivial central extension follows from its dimension alone.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.7, printed
p.106; I.1.5–6(1), printed p.408. The projection argument also appears in
the private movedProjection helpers of B.5.1's CohomologyReduction module;
it is exposed here under narrow imports for the present consumer.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction
open QuasisimpleSource
universe u v w z
variable {D : Type u} [Group D]
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) D V} {L : Subgroup D}

/-- The marked natural action on the literal central quotient, before lifting it. -/
def ReducedSymmetricAction (s : MovedSection ρ L) : Prop :=
  ∃ n : ℕ, (n = 6 ∨ n = 7) ∧ Nonempty (MarkedActionEquiv s.action ⊤ L
    (BinaryPermutation.naturalRepresentation (Fin n)) (alternatingGroup (Fin n)))

/-- Output of the lifted-component/model comparison, retaining the full B.5.1 result. -/
structure ReducedSymmetricModel (ρ : Representation (ZMod 2) D V) (L A : Subgroup D) where
  classification : ProjectiveLine.QuasisimpleSourceConclusion
    (ρ.comp (L ⊔ A).subtype) (L.subgroupOf (L ⊔ A))
  action : ReducedSymmetricAction classification.sectionData

/-- The original moved-space projection, restricted to the actual component. -/
noncomputable def componentProjection (s : MovedSection ρ L) :
    Representation.IntertwiningMap (s.space.toRepresentation.comp L.subtype) (s.action.comp L.subtype) :=
  s.central.toSubmodule.mkQ.intertwiningMap_of_isIntertwiningMap _ _ (fun _ _ => rfl)

/-- Irr-plus supplies the commutator-generation required of a central cover. -/
theorem componentProjection_isCover (s : MovedSection ρ L)
    (hi : IsIrrPlus ρ L s.space.toSubmodule) : IsCover (componentProjection s) := by
  refine ⟨Submodule.mkQ_surjective _, ?_, ?_⟩
  · intro v hv g
    have hmem := (Submodule.Quotient.mk_eq_zero _).mp hv
    rw [s.central_eq] at hmem
    exact hmem g
  · let τ := s.space.toRepresentation.comp L.subtype
    have hm : s.space.toSubmodule ≤ (Coinvariants.ker τ).map s.space.toSubmodule.subtype := by
      conv_lhs => rw [← hi.choose_spec.1]
      apply Submodule.span_le.mpr
      rintro _ ⟨g, hg, v, hv, rfl⟩
      exact ⟨τ ⟨g, hg⟩ ⟨v, hv⟩ - ⟨v, hv⟩, Coinvariants.sub_mem_ker _ _, rfl⟩
    apply top_unique
    intro v _
    obtain ⟨w, hw, he⟩ := hm v.property
    rwa [show w = v from Subtype.ext he] at hw

/-- Irreducibility of the actual moved space kills its central denominator. -/
theorem central_eq_bot_of_irreducible (s : MovedSection ρ L)
    (hi : IsIrrPlus ρ L s.space.toSubmodule)
    [IsIrreducible (s.space.toRepresentation.comp L.subtype)] :
    s.central.toSubmodule = ⊥ := by
  let C : Subrepresentation (s.space.toRepresentation.comp L.subtype) :=
    ⟨s.central.toSubmodule, fun l _ hv => s.central.apply_mem_toSubmodule l hv⟩
  rcases eq_bot_or_eq_top C with hb | ht
  · exact congrArg Subrepresentation.toSubmodule hb
  · exfalso
    apply hi.not_le_fixedSpace ρ
    intro v hv l
    have hc : (⟨v, hv⟩ : s.space.toSubmodule) ∈ C := by rw [ht]; trivial
    change (⟨v, hv⟩ : s.space.toSubmodule) ∈ s.central.toSubmodule at hc
    rw [s.central_eq] at hc
    exact congrArg Subtype.val (hc l)

/-- A zero central denominator gives the actual full-actor quotient equivalence. -/
noncomputable def quotientEquiv (s : MovedSection ρ L)
    (hz : s.central.toSubmodule = ⊥) : ActionEquiv s.action s.space.toRepresentation where
  groupEquiv := MulEquiv.refl D
  linearEquiv := s.central.toSubmodule.quotEquivOfEqBot hz
  intertwines g v := by
    induction v using Submodule.Quotient.induction_on with | _ v => rfl

/-- Transfer a marking through the zero-kernel quotient without changing either group map. -/
noncomputable def liftMarking (s : MovedSection ρ L)
    (hz : s.central.toSubmodule = ⊥)
    {E : Type w} [Group E] {W : Type z} [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) E W} {M : Subgroup E}
    (e : MarkedActionEquiv s.action ⊤ L σ M) :
    MarkedActionEquiv s.space.toRepresentation ⊤ L σ M where
  action := {
    groupEquiv := e.action.groupEquiv
    linearEquiv := (quotientEquiv s hz).linearEquiv.symm.trans e.action.linearEquiv
    intertwines g v := by
      have hq : (quotientEquiv s hz).linearEquiv.symm (s.space.toRepresentation g v) =
          (MovedSection.action ρ s) g.val ((quotientEquiv s hz).linearEquiv.symm v) := by
        apply (quotientEquiv s hz).linearEquiv.injective
        simpa only [LinearEquiv.apply_symm_apply, quotientEquiv, MulEquiv.refl_apply] using
          ((quotientEquiv s hz).intertwines g
            ((quotientEquiv s hz).linearEquiv.symm v)).symm
      change e.action.linearEquiv ((quotientEquiv s hz).linearEquiv.symm
        (s.space.toRepresentation g v)) = _
      rw [hq]
      exact e.action.intertwines g _ }
  contained := e.contained
  subgroupEquiv := e.subgroupEquiv
  compatible := e.compatible

/-- The natural branch on the actual moved space, with its original subgroup marking. -/
theorem moved_action_of_central_eq_bot (s : MovedSection ρ L)
    (hr : ReducedSymmetricAction s) (hz : s.central.toSubmodule = ⊥) :
    SymmetricMovedAction ρ L s := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hr
  exact .natural n hn (liftMarking s hz e)

private noncomputable def dualEquiv
    {E : Type w} [Group E] {W : Type z} [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) E W} (e : ActionEquiv ρ σ) :
    ActionEquiv ρ.dual σ.dual where
  groupEquiv := e.groupEquiv
  linearEquiv := e.linearEquiv.symm.dualMap
  intertwines g f := by
    ext w
    change f (ρ g⁻¹ (e.linearEquiv.symm w)) = f (e.linearEquiv.symm (σ (e.groupEquiv g)⁻¹ w))
    congr 1
    apply e.linearEquiv.injective
    rw [e.intertwines, e.linearEquiv.apply_symm_apply, e.linearEquiv.apply_symm_apply,
      e.groupEquiv.map_inv]

/-- The same marking identifies the component action, including its dual cohomology. -/
theorem marked_dual_H1_finrank [Finite D] [FiniteDimensional (ZMod 2) V]
    (s : MovedSection ρ L) {n : ℕ} (hn : 0 < n)
    (e : MarkedActionEquiv s.action ⊤ L
      (BinaryPermutation.naturalRepresentation (Fin n)) (alternatingGroup (Fin n))) :
    Module.finrank (ZMod 2) (H1 (Representation.dual (s.action.comp L.subtype))) =
      Module.finrank (ZMod 2) (H1 (BinaryPermutation.alternatingNaturalRepresentation (Fin n))) := by
  let : NeZero n := ⟨by omega⟩
  let a : ActionEquiv (s.action.comp L.subtype)
      (BinaryPermutation.alternatingNaturalRepresentation (Fin n)) := {
    groupEquiv := e.subgroupEquiv
    linearEquiv := e.action.linearEquiv
    intertwines g v := by
      have he := e.action.intertwines ⟨g, e.contained g.property⟩ v
      rw [e.compatible] at he
      exact he }
  let d := dualEquiv a
  let b := H1Congr _ _ d.groupEquiv d.linearEquiv d.intertwines
  let c := H1Congr (BinaryPermutation.alternatingNaturalRepresentation (Fin n))
    (BinaryPermutation.alternatingNaturalRepresentation (Fin n)).dual (MulEquiv.refl _)
    (BinaryPermutation.naturalDualEquiv (Fin n))
    (fun g v => BinaryPermutation.naturalDualEquiv_equivariant (Fin n) g.val v)
  exact b.finrank_eq.trans c.finrank_eq.symm

private theorem cover_kernel_finrank_le [Finite D] [FiniteDimensional (ZMod 2) V]
    {W : Type w} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) D W} (p : σ.IntertwiningMap ρ) (hp : IsCover p) :
    Module.finrank (ZMod 2) p.toLinearMap.ker ≤ Module.finrank (ZMod 2) (H1 ρ.dual) := by
  let : FiniteDimensional (ZMod 2) (Module.Dual (ZMod 2) (cocycles ρ.dual)) :=
    Subspace.instModuleDualFiniteDimensional
  obtain ⟨q, hq, hqp⟩ := exists_universalCover_quotient p hp
  let u := universalCoverProjection ρ
  have hu : Function.Surjective u := by
    intro n
    obtain ⟨v, rfl⟩ := hp.1 n
    obtain ⟨x, rfl⟩ := hq v
    exact ⟨x, (hqp x).symm⟩
  have hU := u.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hu, finrank_top,
    finrank_ker_universalCoverProjection] at hU
  have hV := p.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hp.1, finrank_top] at hV
  have hle := LinearMap.finrank_le_finrank_of_surjective (f := q.toLinearMap) hq
  omega

/-- The size of the central denominator is bounded by the actual dual cohomology. -/
theorem central_finrank_le_dual_H1 [Finite D] [FiniteDimensional (ZMod 2) V]
    (s : MovedSection ρ L) (hi : IsIrrPlus ρ L s.space.toSubmodule) :
    Module.finrank (ZMod 2) s.central.toSubmodule ≤
      Module.finrank (ZMod 2) (H1 (Representation.dual (s.action.comp L.subtype))) := by
  have h := cover_kernel_finrank_le (componentProjection s) (componentProjection_isCover s hi)
  change Module.finrank (ZMod 2) s.central.toSubmodule.mkQ.ker ≤ _ at h
  rwa [Submodule.ker_mkQ] at h

/-- A seven-point reduced action has no central extension in its moved space. -/
theorem seven_central_eq_bot [Finite D] [FiniteDimensional (ZMod 2) V]
    (s : MovedSection ρ L) (hi : IsIrrPlus ρ L s.space.toSubmodule)
    (e : MarkedActionEquiv s.action ⊤ L
      (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7))) :
    s.central.toSubmodule = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  have h := central_finrank_le_dual_H1 s hi
  rw [marked_dual_H1_finrank s (by decide) e,
    BinaryPermutation.alternatingSeven_natural_finrank_H1] at h
  omega

/-- A nonzero central denominator in the six-point case has dimension exactly one. -/
theorem six_central_finrank [Finite D] [FiniteDimensional (ZMod 2) V]
    (s : MovedSection ρ L) (hi : IsIrrPlus ρ L s.space.toSubmodule)
    (e : MarkedActionEquiv s.action ⊤ L
      (BinaryPermutation.naturalRepresentation (Fin 6)) (alternatingGroup (Fin 6)))
    (hz : s.central.toSubmodule ≠ ⊥) :
    Module.finrank (ZMod 2) s.central.toSubmodule = 1 ∧
      Module.finrank (ZMod 2) s.space.toSubmodule = 5 := by
  have h := central_finrank_le_dual_H1 s hi
  rw [marked_dual_H1_finrank s (by decide) e,
    BinaryPermutation.alternatingSix_natural_finrank_H1] at h
  have hpos : Module.finrank (ZMod 2) s.central.toSubmodule ≠ 0 :=
    fun h => hz (Submodule.finrank_eq_zero.mp h)
  have hone : Module.finrank (ZMod 2) s.central.toSubmodule = 1 := by omega
  have hquot := e.action.linearEquiv.finrank_eq
  rw [BinaryPermutation.finrank_natural_even (Fin 6) (by decide)] at hquot
  have hdim := s.central.toSubmodule.finrank_quotient_add_finrank
  refine ⟨hone, ?_⟩
  simp only [Fintype.card_fin] at hquot
  omega

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction
