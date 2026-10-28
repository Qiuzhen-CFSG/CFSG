module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoLineCosts
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoThreeNonsolvable
public import Theory.Representation.BinaryOffender.DualFixedSupplement

/-!
# The ordinary common-axis branch is a strong plane on the literal dual

Keep the same original actor A and the same canonical F/D action. When A
has rank two and its actual moved seed is a line, the ordinary cost-two
action becomes a strong minimal plane offender on the literal dual. This
uses finite-dimensional annihilator identities, not quotient FF inheritance.
The exact actor's normal closure is consequently nonsolvable.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
universe u v

private theorem dual_strong_of_two_cost_moved_line
    {J W : Type*} [Group J] [Finite J] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) J W)
    (hf : Function.Injective σ) (A : Subgroup J) (hA : IsElementaryTwo A)
    (hq : IsQuadratic σ A) (hr : rank A = 2) (hc : fixedCodim σ A = 2)
    (hm : Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ A) = 1) :
    fixedCodim σ.dual A = 1 ∧
      Module.finrank (ZMod 2) (subspaceCommutator σ.dual ⊤ A) = 2 ∧
      IsQuadratic σ.dual A ∧ IsStrongOffender σ.dual A ∧
      IsMinimalBestOffender σ.dual A ∧ Function.Injective σ.dual := by
  have hdc : fixedCodim σ.dual A = 1 := by
    rw [fixedCodim_dual_eq_moved_finrank,hm]
  have hdm : Module.finrank (ZMod 2) (subspaceCommutator σ.dual ⊤ A) = 2 := by
    rw [subspaceCommutator_top_eq_coinvariants]
    exact (Representation.finrank_quotient_invariants_eq_dual_commutator (σ.comp A.subtype)).symm.trans hc
  have hfaith : Function.Injective σ.dual := by
    intro x y he
    apply inv_injective
    apply hf
    apply LinearMap.ext
    intro w
    apply (Module.evalEquiv (ZMod 2) W).injective
    apply LinearMap.ext
    intro f
    exact congrArg (fun q : Module.End (ZMod 2) (Module.Dual (ZMod 2) W) => q f w) he
  have hstrong : IsStrongOffender σ.dual A := ⟨hA,by rw [hdc,hr]; omega⟩
  refine ⟨hdc,hdm,(isQuadratic_dual_iff σ A).mpr hq,hstrong,?_,hfaith⟩
  exact DecomposableQuinticControl.minimalBestOffender_of_moved_plane_exact_cost
    σ.dual hfaith A hA hdm.le (Or.inl ⟨hr,hdc⟩)

variable {G : Type u} [Group G] [Finite G]

/-- The same original rank-two actor with a one-dimensional marked seed
is a strong minimal plane offender on the exact canonical dual action. -/
theorem PreparedChosenModule.decomposable_five_partner_two_line_dual_strong
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 2 →
      let E := thompsonFixed T V
      let C := centralizer (localModule T Mc : Set G)
      let F := conjugateSpanBy E C
      let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
      let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
      V ≤ Mc.pCoreIn 2 ∨
        ∀ {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
          (ρ : Representation (ZMod 2) Mc W) (dF : BinaryConjugationSection Mc F D ρ),
          Nat.card (D ⊓ Z₁ : Subgroup G) = 2 →
          let σ := Representation.BinaryOffender.imageRepresentation ρ
          let A := actionSubgroup ρ (V.subgroupOf Mc)
          let P := dF.imageSpace E
          rank A = 2 → Module.finrank (ZMod 2) P = 1 →
          fixedCodim σ A = 2 ∧ fixedCodim σ.dual A = 1 ∧
            Module.finrank (ZMod 2) (subspaceCommutator σ.dual ⊤ A) = 2 ∧
            IsQuadratic σ.dual A ∧ IsStrongOffender σ.dual A ∧
            IsMinimalBestOffender σ.dual A ∧
            Function.Injective σ.dual ∧ pCore 2 (actionImage ρ) = ⊥ ∧
            ¬Group.IsSolvable (normalClosure (A : Set (actionImage ρ))) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc : Set G)
  let F := conjugateSpanBy E C
  let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  by_cases hVQ : V ≤ Mc.pCoreIn 2
  · exact Or.inl hVQ
  right
  intro W _ _ ρ dF hline
  let σ := Representation.BinaryOffender.imageRepresentation ρ
  let A := actionSubgroup ρ (V.subgroupOf Mc)
  let P := dF.imageSpace E
  change rank A = 2 → Module.finrank (ZMod 2) P = 1 → _
  intro hr hdP
  let : Finite W := Finite.of_surjective (fun x : F => (dF.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp dF.onto)
  obtain ⟨hoff,hquad,hP,_,_,_,_,hcases⟩ :=
    ((h.decomposable_five_partner_two_line_costs hG T hempty hM hmany hJ hu hfull
      c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ) ρ dF hline
  change rank A = 2 at hr
  change Module.finrank (ZMod 2) P = 1 at hdP
  have hc : fixedCodim σ A = 2 := by
    rcases hcases with hcase|hcase|hcase
    · have hh : rank A = 1 := hcase.1
      omega
    · have hh : Module.finrank (ZMod 2) P = 2 := hcase.2.2.1
      omega
    · exact hcase.2.1
  have hm : Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ A) = 1 := by
    change P = subspaceCommutator σ ⊤ A at hP
    rw [←hP]
    exact hdP
  obtain ⟨hdc,hdm,hdq,hstrong,hbest,hfaith⟩ := dual_strong_of_two_cost_moved_line
    σ (imageRepresentation_injective ρ) A hoff.1 hquad hr hc hm
  have hdimW : 0 < Module.finrank (ZMod 2) W := by
    have hh := Submodule.finrank_le P
    rw [hdP] at hh
    omega
  let : Nontrivial W := (Module.finrank_pos_iff (R := ZMod 2) (M := W)).mp hdimW
  have hirr : IsIrreducible ρ := (h.decomposable_five_canonical_section_irreducible
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2 ρ dF
  have hcore := actionImage_twoCore_eq_bot ρ hirr
  exact ⟨hc,hdc,hdm,hdq,hstrong,hbest,hfaith,hcore,
    DecomposableQuinticControl.normalClosure_not_solvable_of_strong σ.dual hfaith hcore A hstrong⟩

end CFSG.Quasithin.Chapter15.Section01
