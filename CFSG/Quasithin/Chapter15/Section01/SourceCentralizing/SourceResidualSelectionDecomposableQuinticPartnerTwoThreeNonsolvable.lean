module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoThreeStrong
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Glauberman
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.BinaryOffender.QuasisimpleImage
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# A nonsolvable normal closure on the actual three-dimensional seed

A strong offender in a faithful core-free binary action has nonsolvable
normal closure: actor restriction preserves the literal offender rank and
fixed codimension, while normal restriction preserves the trivial two-core.
Glauberman's solvable FF theorem then contradicts strongness.

The original quintic source supplies strongness on every specified canonical
F/D action with three-dimensional image of E. Its already proved
irreducibility supplies core-freeness for those same coordinates.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter15.DecomposableQuinticControl

/-- Strongness survives restriction to the actor's normal closure, whose
trivial two-core rules out a solvable FF action. -/
theorem normalClosure_not_solvable_of_strong
    {J W : Type*} [Group J] [Finite J] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) J W)
    (hfaith : Function.Injective σ) (hcore : pCore 2 J = ⊥)
    (A : Subgroup J) (hA : IsStrongOffender σ A) :
    ¬Group.IsSolvable (normalClosure (A : Set J)) := by
  let R := normalClosure (A : Set J)
  have hAR : A ≤ R := le_normalClosure
  have hcoreR : pCore 2 R = ⊥ := by
    rw [pCore_eq_comap_of_normal,hcore]
    exact R.subtype.ker_eq_bot R.subtype_injective
  have hoff : IsOffender σ A := ⟨hA.1,hA.2.le⟩
  have hstrong : IsStrongOffender (σ.comp R.subtype) (A.subgroupOf R) := by
    refine ⟨(hoff.subgroupOf σ hAR).1,?_⟩
    rw [fixedCodim_subgroupOf σ hAR,rank_subgroupOf hAR]
    exact hA.2
  intro hsolv
  exact (ChapterB.Glauberman.numerical_conclusions hsolv hcoreR
    (hfaith.comp R.subtype_injective)
    ⟨A.subgroupOf R,⟨hstrong.1,hstrong.2.le⟩⟩).2 _ hstrong

end CFSG.Quasithin.Chapter15.DecomposableQuinticControl

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- On every supplied canonical section with three-dimensional original seed,
the normal closure of the original V-image is nonsolvable. -/
theorem PreparedChosenModule.decomposable_five_partner_two_three_nonsolvable
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
      V ≤ Mc.pCoreIn 2 ∨
        ∀ {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
          (ρ : Representation (ZMod 2) Mc W) (dF : BinaryConjugationSection Mc F D ρ),
          Module.finrank (ZMod 2) (dF.imageSpace E) = 3 →
          ¬Group.IsSolvable (normalClosure
            (actionSubgroup ρ (V.subgroupOf Mc) : Set (Representation.BinaryOffender.actionImage ρ))) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc : Set G)
  let F := conjugateSpanBy E C
  let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  rcases h.decomposable_five_partner_two_three_strong
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU with
    hcore | hstrong
  · exact Or.inl hcore
  right
  intro W _ _ ρ dF hdim
  let : Finite W := Finite.of_surjective (fun x : F => (dF.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp dF.onto)
  have hdimW : 0 < Module.finrank (ZMod 2) W :=
    lt_of_lt_of_le (by decide : 0 < 3)
      (hdim ▸ Submodule.finrank_le (dF.imageSpace E))
  let : Nontrivial W := (Module.finrank_pos_iff (R := ZMod 2) (M := W)).mp hdimW
  have hirr : IsIrreducible ρ := (h.decomposable_five_canonical_section_irreducible
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2 ρ dF
  exact DecomposableQuinticControl.normalClosure_not_solvable_of_strong
    (Representation.BinaryOffender.imageRepresentation ρ) (imageRepresentation_injective ρ)
    (actionImage_twoCore_eq_bot ρ hirr) (actionSubgroup ρ (V.subgroupOf Mc))
    (hstrong ρ dF hdim).2

end CFSG.Quasithin.Chapter15.Section01
