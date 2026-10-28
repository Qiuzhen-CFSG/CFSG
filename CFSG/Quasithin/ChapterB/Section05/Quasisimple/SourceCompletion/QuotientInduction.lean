module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.SocleInduction

/-!
# Strict quotient induction in the binary B.5.1 branch

A fixed vector modulo a natural submodule defines its actual connecting
cocycle. Vanishing first cohomology lifts it to an original fixed vector, so
fixed-point-freeness passes to that quotient. Full commutator generation and
failure of factorization also pass through the literal quotient map.

When F*(G)=G in the binary natural rows, the original center-free component
makes this nonzero quotient faithful. A best offender then normally generates
the whole actor. Thus all original B.5.1 hypotheses hold in strictly smaller
dimension, and its genuine induction conclusion makes the quotient semisimple.
Two disjoint natural kernels consequently make the original action semisimple.
The existence of those kernels is a separate splitting step, not an assumption
of the final source theorem.

Source: Aschbacher--Smith, B.5.1, printed p.102, case (B) and its quotients U/Ui.
-/

public section
open Representation Representation.BinaryOffender Representation.OneCohomology Theory.GroupTheory Subgroup
open scoped MonoidAlgebra MatrixGroups
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v
variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The vanishing connecting class lifts every fixed quotient vector; a
fixed-point-free original action therefore has fixed-point-free quotient. -/
theorem quotient_invariants_eq_bot_of_H1 (U : Subrepresentation ρ)
    [Subsingleton (H1 U.toRepresentation)] (hz : ρ.invariants = ⊥) :
    Representation.invariants U.quotientRepresentation = ⊥ := by
  apply bot_unique
  intro q hq
  obtain ⟨v,rfl⟩ := U.toSubmodule.mkQ_surjective q
  have hv (g : G) : ρ g v - v ∈ U :=
    (Submodule.Quotient.eq U.toSubmodule).mp (hq g)
  let f : cocycles U.toRepresentation := ⟨fun g => ⟨ρ g v - v,hv g⟩,by
    intro g t
    apply Subtype.ext
    change ρ (g*t) v - v = ρ g (ρ t v - v) + (ρ g v - v)
    rw [map_mul,Module.End.mul_apply,map_sub]
    abel⟩
  obtain ⟨w,hw⟩ := (classMap_eq_zero_iff _ f).mp (Subsingleton.elim _ _)
  have hfix : v - w.val ∈ ρ.invariants := by
    intro g
    have he := congrArg (fun c : cocycles U.toRepresentation => (c.val g).val) hw
    change ρ g w.val - w.val = ρ g v - v at he
    rw [map_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mp he.symm
  rw [hz] at hfix
  have hmem : v ∈ U := (sub_eq_zero.mp hfix) ▸ w.property
  exact (Submodule.Quotient.mk_eq_zero U.toSubmodule).mpr hmem

/-- Full commutator generation survives the literal quotient. -/
theorem quotient_coinvariants_top (U : Subrepresentation ρ)
    (hm : Coinvariants.ker ρ = ⊤) : Coinvariants.ker U.quotientRepresentation = ⊤ := by
  apply top_unique
  intro w _
  obtain ⟨v,rfl⟩ := U.toSubmodule.mkQ_surjective w
  have hle : Coinvariants.ker ρ ≤ (Coinvariants.ker U.quotientRepresentation).comap
      U.toSubmodule.mkQ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩,rfl⟩
    change U.toSubmodule.mkQ (ρ g v - v) ∈ Coinvariants.ker U.quotientRepresentation
    rw [map_sub]
    exact Coinvariants.sub_mem_ker g (U.toSubmodule.mkQ v)
  exact hle (hm ▸ Submodule.mem_top)

/-- Failure of factorization descends to an actual quotient with its original
actor; faithfulness is supplied separately by the source component argument. -/
theorem quotient_isFFModule [FiniteDimensional (ZMod 2) V]
    (U : Subrepresentation ρ) (hff : IsFFModule ρ) : IsFFModule U.quotientRepresentation := by
  obtain ⟨A,hA⟩ := hff
  refine ⟨A,hA.1,?_⟩
  exact (Nat.le_add_right _ _).trans ((fixedCodim_quotient_add_subrepresentation_le ρ U A).trans hA.2)

/-- A faithful FF action has the complete original B.5.1 hypothesis when its
quasisimple generalized Fitting subgroup is the whole actor. -/
theorem whole_source_hypothesis [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : CFSG.Quasithin.GroupClass.{u}}
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hwhole : generalizedFitting G = ⊤) (hcore : pCore 2 G = ⊥)
    (hf : Function.Injective ρ) (hff : IsFFModule ρ) :
    QuasisimpleSourceHypothesis ρ K (generalizedFitting G) := by
  obtain ⟨B,hB⟩ := (isFFModule_iff_exists_bestOffender ρ).mp hff
  let J := offenderSubgroup ρ
  let : J.Normal := offenderSubgroup_normal ρ
  have hBJ : B ≤ J := hB.le_offenderSubgroup ρ
  have hcomm := QuasisimpleSections.commutator_fitting_eq hcore
    (inferInstance : IsQuasisimple (generalizedFitting G)) hB.1.1 (hB.1.2.isPGroup 2 B)
  have hgen : J = ⊤ := by
    apply top_unique
    rw [← hwhole,← hcomm]
    exact (commutator_mono le_rfl hBJ).trans (commutator_le_right _ _)
  refine ⟨inferInstance,hf,inferInstance,hsq,?_,hcore,hgen⟩
  rw [hwhole,top_sup_eq]


/-- Removing a proper natural submodule in the binary branch gives a faithful,
fixed-point-free, fully moved source action of strictly smaller dimension.
The genuine induction conclusion then makes that literal quotient semisimple. -/
theorem recursive_binary_natural_quotient [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : CFSG.Quasithin.GroupClass.{u}}
    (ih : SmallerDimensionInput.{u,v} K (Module.finrank (ZMod 2) V))
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hwhole : generalizedFitting G = ⊤) (hcore : pCore 2 G = ⊥)
    (hm : Coinvariants.ker ρ = ⊤) (hz : ρ.invariants = ⊥)
    (hff : IsFFModule ρ) (U : Subrepresentation ρ) (hU : U.toSubmodule ≠ ⊤)
    {d : ℕ} (hd : 4 ≤ d) (hn : IsLinearNatural U.toRepresentation BinaryField.two d) :
    Nonempty (SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      U.quotientRepresentation (generalizedFitting G)) ∧
      IsSemisimpleRepresentation U.quotientRepresentation := by
  obtain ⟨a⟩ := hn
  let τ := U.quotientRepresentation
  let e : ActionEquiv (τ.comp (generalizedFitting G).subtype) τ :=
    ⟨(MulEquiv.subgroupCongr hwhole).trans Subgroup.topEquiv,
      LinearEquiv.refl _ _,fun _ _ => rfl⟩
  have hmove : moved τ (generalizedFitting G) = ⊤ := by
    have he : moved τ (generalizedFitting G) = Coinvariants.ker τ := by
      rw [hwhole]
      apply congrArg (Submodule.span (ZMod 2))
      ext v
      constructor
      · rintro ⟨g,_,w,_,rfl⟩
        exact ⟨(g,w),rfl⟩
      · rintro ⟨⟨g,w⟩,rfl⟩
        exact ⟨g,Subgroup.mem_top _,w,Submodule.mem_top,rfl⟩
    exact he.trans (quotient_coinvariants_top ρ U hm)
  have hcenter : center (generalizedFitting G) = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rw [Nat.card_congr (centerCongr (e.groupEquiv.trans a.groupEquiv)).toEquiv]
    change Nat.card (center SL(d,ZMod 2)) = 1
    rw [BinaryLinear.OuterCyclic.binary_center_eq_bot (by omega : 0 < d)]
    exact Subgroup.card_bot
  let : Nontrivial (V ⧸ U.toSubmodule) := Submodule.Quotient.nontrivial_iff.mpr hU
  have hfaith : Function.Injective τ := faithful_of_centerfree_fitting τ hcenter (by
    change moved τ (generalizedFitting G) ≠ ⊥
    rw [hmove]
    exact top_ne_bot)
  have hs := whole_source_hypothesis τ hsq hwhole hcore hfaith (quotient_isFFModule ρ U hff)
  let := H1_linearNatural_subsingleton hd
  let : Subsingleton (H1 U.toRepresentation) := a.H1_subsingleton
  have hzero := quotient_invariants_eq_bot_of_H1 ρ U hz
  let : IsIrreducible U.toRepresentation := ExtensionConsequences.irreducible_of_equiv a
    (ExtensionConsequences.linearNatural_irreducible _ (by omega))
  let : Nontrivial U.toSubmodule := Subrepresentation.irreducible_module_nontrivial U.toRepresentation
  have hdim := U.toSubmodule.finrank_quotient_add_finrank
  have hpos := Module.finrank_pos (R := ZMod 2) (M := U.toSubmodule)
  obtain ⟨c⟩ := ih G (V ⧸ U.toSubmodule) τ (generalizedFitting G) (by omega) hs
  refine ⟨⟨c⟩,?_⟩
  apply semisimple_of_actionEquiv τ (ExtensionConsequences.actionSymm e)
  exact semisimple_of_source_conclusion τ c hmove
    (ExtensionConsequences.invariants_of_equiv e hzero)

/-- Actual binary natural kernels discharge both quotient recursion inputs in
the diagonal semisimplicity argument. -/
theorem binary_semisimple_of_two_natural_kernels [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : CFSG.Quasithin.GroupClass.{u}}
    (ih : SmallerDimensionInput.{u,v} K (Module.finrank (ZMod 2) V))
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hwhole : generalizedFitting G = ⊤) (hcore : pCore 2 G = ⊥)
    (hm : Coinvariants.ker ρ = ⊤) (hz : ρ.invariants = ⊥)
    (hff : IsFFModule ρ) (U W : Subrepresentation ρ)
    (hdis : Disjoint U.toSubmodule W.toSubmodule)
    (hU : U.toSubmodule ≠ ⊤) (hW : W.toSubmodule ≠ ⊤)
    {d : ℕ} (hd : 4 ≤ d)
    (hnU : IsLinearNatural U.toRepresentation BinaryField.two d)
    (hnW : IsLinearNatural W.toRepresentation BinaryField.two d) :
    IsSemisimpleRepresentation ρ := by
  exact semisimple_of_disjoint_quotients ρ U W hdis
    (recursive_binary_natural_quotient ρ ih hsq hwhole hcore hm hz hff U hU hd hnU).2
    (recursive_binary_natural_quotient ρ ih hsq hwhole hcore hm hz hff W hW hd hnW).2

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
