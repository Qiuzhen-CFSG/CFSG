module

public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceCoreExactSection
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.BinaryIdentification
public import Theory.Frattini.OmegaProducts

@[expose] public section

/-!
# The full marked component Frattini module

The exact sixteen-dimensional binary section identifies the component-core
Frattini quotient with the trace-zero adjoint module over `F₄`.  The quotient
transport is through the literal ambient core and the literal mapped core used
by the source section.  The resulting equivalence intertwines the original
component action with `projectiveSpecialAdjoint`.

This is a source-facing marking theorem; it does not infer a split diagonal
normal form for an outer cubic actor.
-/

open Subgroup Theory.GroupTheory Representation
open scoped commutatorElement MatrixGroups
open Representation.SL3.AdjointCubicCentralizer
open Representation.SL3.AdjointCubicCentralizer.GraphExtension.FrattiniDescent
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
open Nonblock.RootCoordinates
attribute [local instance] SecondaryActionData.normal
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {d : MSData c 2}
set_option backward.isDefEq.respectTransparency false

private theorem restriction_irred
    {A W : Type*} [Group A] [Finite A]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) [ρ.IsIrreducible]
    (H : Subgroup A) [H.Normal]
    (e : (H ⧸ pCore 2 H) ≃* Matrix.PSL3Four.PSL)
    (hd : Module.finrank (ZMod 2) W = 16) (hnt : ¬ H ≤ ρ.ker) :
    Representation.IsIrreducible (ρ.comp H.subtype) := by
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨J,hJ⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (ρ.comp H.subtype)
  let : J.toRepresentation.IsIrreducible := hJ
  have hjd := J.toSubmodule.finrank_le
  have hj := Representation.PSL3Four.core_simple_degree_le_twenty_two
    e J.toRepresentation (by omega)
  have hjne : Module.finrank (ZMod 2) J.toSubmodule ≠ 1 := by
    intro h1
    apply hnt
    apply le_ker_of_normal_invariants_ne_bot ρ H
    let : Nontrivial J.toSubmodule := Subrepresentation.irreducible_module_nontrivial J.toRepresentation
    obtain ⟨v,hv⟩ := exists_ne (0 : J.toSubmodule)
    have ht (g : H) : J.toRepresentation g v = v := by
      obtain ⟨a,ha⟩ := exists_smul_eq_of_finrank_eq_one h1 hv (J.toRepresentation g v)
      have ha0 : a ≠ 0 := by
        intro he
        have hh : J.toRepresentation g v = 0 := by simpa [he] using ha.symm
        apply hv
        simpa only [J.toRepresentation.inv_self_apply,map_zero] using
          congrArg (J.toRepresentation g⁻¹) hh
      have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha0
      simpa only [ha1,one_smul] using ha.symm
    intro hb
    have hm : (v : W) ∈ invariants (ρ.comp H.subtype) :=
      fun g => congrArg Subtype.val (ht g)
    rw [hb,Submodule.mem_bot] at hm
    exact hv (Subtype.ext hm)
  exact irreducible_restrict_of_large_constituent ρ H inferInstance J hJ (by omega)

theorem marking_of_section
    (s : SecondaryActionData c 2) (_D : Chapter12.Section02.ChosenModule T L V)
    (_h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (mark : (s.component ⧸ pCore 2 s.component) ≃* Matrix.PSL3Four.PSL)
    (X : Subgroup G) (hXr : X ≤ rootNormalizer c)
    (W : Type u) [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2)
      (s.component.map (rootNormalizer c).subtype ⊔ X : Subgroup G) W)
    (b : BinaryConjugationSection
      (s.component.map (rootNormalizer c).subtype ⊔ X)
      ((s.component.map (rootNormalizer c).subtype).pCoreIn 2)
      ((frattini ((s.component.map (rootNormalizer c).subtype).pCoreIn 2)).map
        ((s.component.map (rootNormalizer c).subtype).pCoreIn 2).subtype) ρ)
    [ρ.IsIrreducible] (hd : Module.finrank (ZMod 2) W = 16)
    (hnt : ¬ (s.component.map (rootNormalizer c).subtype).subgroupOf
      (s.component.map (rootNormalizer c).subtype ⊔ X) ≤ ρ.ker) :
    ∃ e : Frattini s.component ≃* Multiplicative (TraceZero Matrix.PSL3Four.F),
      ∀ (q : s.component) (v : Frattini s.component),
        (e (coreAction s.component (q : rootNormalizer c) v)).toAdd =
          projectiveSpecialAdjoint Matrix.PSL3Four.F
            (mark (QuotientGroup.mk' (pCore 2 s.component) q)) (e v).toAdd := by
  let M := s.component.map (rootNormalizer c).subtype
  let P := M.pCoreIn 2
  let E := M ⊔ X
  let H := M.subgroupOf E
  let f : H ≃* s.component :=
    (subgroupOfEquivOfLe (show M ≤ E from le_sup_left)).trans
      (s.component.equivMapOfInjective (rootNormalizer c).subtype
        (rootNormalizer c).subtype_injective).symm
  have hH : H.Normal := by
    apply normal_subgroupOf_of_le_normalizer
    have hn := s.component.le_normalizer_map (rootNormalizer c).subtype
    have hnr : rootNormalizer c ≤ normalizer (M : Set G) := by
      simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hn
    exact (sup_le (map_subtype_le _) hXr).trans hnr
  let eqH : (H ⧸ pCore 2 H) ≃* Matrix.PSL3Four.PSL :=
    (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans mark
  let ρH : Representation (ZMod 2) H W := ρ.comp H.subtype
  let : Finite W := Finite.of_surjective (fun a => (b.coordinates a).toAdd) b.onto
  let : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  have hntH : ¬ H ≤ ρ.ker := by
    simpa [H, E] using hnt
  have hirH : ρH.IsIrreducible := restriction_irred ρ H eqH hd hntH
  let hcore : pCore 2 H ≤ ρH.ker := normal_p_subgroup_le_ker ρH _ pCore_isPGroup
  let τ : Representation (ZMod 2) (H ⧸ pCore 2 H) W :=
    quotientOfLEKer ρH (pCore 2 H) hcore
  let σ : Representation (ZMod 2) Matrix.PSL3Four.PSL W :=
    τ.comp eqH.symm.toMonoidHom
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff eqH.symm.toMonoidHom eqH.symm.surjective τ).mpr
      ((quotientOfLEKer_irreducible_iff ρH (pCore 2 H) hcore).mpr hirH)
  let π : Matrix.PSL3Four.SL →* Matrix.PSL3Four.PSL :=
    QuotientGroup.mk' (Subgroup.center Matrix.PSL3Four.SL)
  let σSL : Representation (ZMod 2) Matrix.PSL3Four.SL W := σ.comp π
  let : σSL.IsIrreducible :=
    (irreducible_comp_surjective_iff π (QuotientGroup.mk'_surjective _) σ).mpr inferInstance
  obtain ⟨ea⟩ :=
    Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.equiv_adjointBinary
      σSL hd
  let eF : W ≃ₗ[ZMod 2] TraceZero Matrix.PSL3Four.F :=
    ea.toLinearEquiv.trans
      ((matrixAdjointEquiv Matrix.PSL3Four.F).restrictScalars (ZMod 2))
  have hcore : P = ((pCore 2 s.component).map s.component.subtype).map
      (rootNormalizer c).subtype := by
    dsimp only [P, M]
    rw [←map_pCoreIn_of_injective 2 s.component (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective]
    rfl
  let j0 : s.component.pCoreIn 2 ≃*
      (s.component.pCoreIn 2).map (rootNormalizer c).subtype :=
    Subgroup.equivMapOfInjective _ (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective
  let j : s.component.pCoreIn 2 ≃* P :=
    j0.trans (MulEquiv.subgroupCongr (by simpa only [pCoreIn, map_map] using hcore.symm))
  have hden : (frattini (s.component.pCoreIn 2)).map j.toMonoidHom =
      ((frattini P).map P.subtype).subgroupOf P := by
    rw [Subgroup.frattini_map_equiv j]
    ext x
    constructor
    · intro hx
      change (x : G) ∈ (frattini P).map P.subtype
      exact ⟨x, hx, rfl⟩
    · intro hx
      change (x : G) ∈ (frattini P).map P.subtype at hx
      obtain ⟨y, hy, heq⟩ := hx
      exact Subtype.ext heq.symm ▸ hy
  let c0 : s.component.pCoreIn 2 →* Multiplicative W :=
    b.coordinates.comp j.toMonoidHom
  have hc0 : c0.ker = frattini (s.component.pCoreIn 2) := by
    ext z
    change b.coordinates (j z) = 1 ↔ z ∈ frattini (s.component.pCoreIn 2)
    rw [b.coordinates_eq_one_iff]
    change (j z : G) ∈ (frattini P).map P.subtype ↔ _
    change j z ∈ ((frattini P).map P.subtype).subgroupOf P ↔ _
    rw [← hden]
    constructor
    · rintro ⟨z', hz', heq⟩
      have hzz' : z' = z := j.injective heq
      simpa [hzz'] using hz'
    · intro hz
      exact ⟨z, hz, rfl⟩
  have hc0_surj : Function.Surjective c0 := by
    intro w
    obtain ⟨p, hp⟩ := b.onto w
    obtain ⟨z, hz⟩ := j.surjective p
    refine ⟨z, ?_⟩
    change b.coordinates (j z) = w
    rw [hz, hp]
  let e0 : Frattini s.component ≃* Multiplicative W :=
    (QuotientGroup.quotientMulEquivOfEq hc0.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective c0 hc0_surj)
  let eMul : Multiplicative W ≃* Multiplicative (TraceZero Matrix.PSL3Four.F) :=
    eF.toAddEquiv.toMultiplicative
  let e : Frattini s.component ≃* Multiplicative (TraceZero Matrix.PSL3Four.F) :=
    e0.trans eMul
  refine ⟨e, ?_⟩
  intro q v
  obtain ⟨z, rfl⟩ :=
    QuotientGroup.mk'_surjective (frattini (s.component.pCoreIn 2)) v
  let hq : H := f.symm q
  let a' : P := ⟨(hq : G) * (j z : G) * (hq : G)⁻¹,
    (mem_normalizer_iff.mp (b.normalized hq.val.property) (j z)).mp (j z).property⟩
  have ha' : a' = j (MulAut.conjNormal (q : rootNormalizer c) z) := by
    apply Subtype.ext
    rfl
  have hb := b.equivariant hq (j z)
  change (b.coordinates a').toAdd = ρH hq (b.coordinates (j z)).toAdd at hb
  rw [ha'] at hb
  change (e (coreAction s.component (q : rootNormalizer c)
      (QuotientGroup.mk' (frattini (s.component.pCoreIn 2)) z))).toAdd = _
  rw [coreAction_eq, normalQuotientAction_apply_mk]
  have hρ (h' : H) :
      σ (eqH (QuotientGroup.mk' (pCore 2 H) h')) = ρH h' := by
    change τ (eqH.symm (eqH (QuotientGroup.mk' (pCore 2 H) h'))) = ρH h'
    rw [eqH.symm_apply_apply, quotientOfLEKer_apply]
  have hmark :
      eqH (QuotientGroup.mk' (pCore 2 H) hq) =
        mark (QuotientGroup.mk' (pCore 2 s.component) q) := by
    simp [eqH, hq]
  have hInt (r : Matrix.PSL3Four.PSL) (w : W) :
      eF (σ r w) = projectiveSpecialAdjoint Matrix.PSL3Four.F r (eF w) := by
    obtain ⟨g, rfl⟩ :=
      QuotientGroup.mk'_surjective (Subgroup.center Matrix.PSL3Four.SL) r
    have ha := Representation.IntertwiningMap.isIntertwining _ _ ea.toIntertwiningMap g w
    have hb' := Representation.IntertwiningMap.isIntertwining _ _
      (adjointRestrictionEquiv Matrix.PSL3Four.F).toIntertwiningMap g (ea w)
    change matrixAdjointEquiv Matrix.PSL3Four.F
        ((SL3.BinaryDefiningFactors.factorRep
          (RingHom.id Matrix.PSL3Four.F) .adjoint) g (ea w)) =
      projectiveAdjoint Matrix.PSL3Four.F (Matrix.SpecialLinearGroup.toPGL g)
        (matrixAdjointEquiv Matrix.PSL3Four.F (ea w)) at hb'
    have hh := (congrArg
      (fun z => (matrixAdjointEquiv Matrix.PSL3Four.F).restrictScalars (ZMod 2) z)
      ha).trans hb'
    change matrixAdjointEquiv Matrix.PSL3Four.F (ea (σ (g : Matrix.PSL3Four.PSL) w)) =
      adjointAction Matrix.PSL3Four.F
        (Matrix.SpecialLinearGroup.toGL g)
        (matrixAdjointEquiv Matrix.PSL3Four.F (ea w))
    exact hh
  change eF (b.coordinates (j (MulAut.conjNormal (q : rootNormalizer c) z))).toAdd =
    projectiveSpecialAdjoint Matrix.PSL3Four.F
      (mark (QuotientGroup.mk' (pCore 2 s.component) q))
      (eF (b.coordinates (j z)).toAdd)
  rw [← hmark, ← hInt (eqH (QuotientGroup.mk' (pCore 2 H) hq))
      (b.coordinates (j z)).toAdd, hρ]
  exact congrArg eF hb
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
