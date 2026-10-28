module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerFourModule
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.BinaryActorCases
public import Theory.Representation.BinaryNaturalDual.SmallRepeatedEmbedding
public import Theory.Representation.SL5ExteriorSquare.InvolutionFixedBound

/-!
# Excluding the original constrained SL₅(2) star

The actual B.5.1 moved section contains the original natural-plus-dual
four-space, with its surjective residual action. Its literal central
projection is injective, and the original radical fixes its range.
The radical intersection has order sixteen.

Specialize B.5.1 on this same star. The natural row is too small. In the
natural-plus-dual row, counting displacement maps bounds the radical-fixed
space by seven. In the exterior row, the actual irreducible ten-dimensional
recognition and involution classes give the same bound. In every repeated
natural row, the inequivalent natural and dual four-dimensional simple
factors cannot both embed in repetitions of a five-dimensional restriction.
This last argument retains the original residual map and does not assume
that an arbitrary abstract GL₄ subgroup acts naturally.

Thus all rows contradict the original embedding. The chosen-orbit consumer
in DoubleNaturalExcludedFourOddNormalizers discharges 12.1.9(1); the earlier
ambient marked-omega premise remains with the pure-point/MS source owners.
Source: Aschbacher--Smith C.4.8 and 12.1.9, printed pp.154,793, with B.5.1
and the irreducible exterior recognition of I.1.6(7), printed pp.99,408.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion

private theorem source_five_exclusion
    {D F Y : Type*} [Group D] [Finite D] [Group F]
    [AddCommGroup Y] [Module (ZMod 2) Y] [FiniteDimensional (ZMod 2) Y]
    (ρ : Representation (ZMod 2) D Y) (C : Subgroup D)
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C)
    (mark : C ≃* SL(5,ZMod 2))
    (A : Subgroup C) (hA : Nat.card A = 16)
    (p : F →* BinaryLinear.OuterCyclic.LinearGroup 4) (hp : Function.Surjective p)
    (q : F →* C)
    (i : BinaryNaturalDual.CoordinateSpace 4 →ₗ[ZMod 2] c.sectionData.space.toSubmodule)
    (hg : Function.Injective (c.sectionData.central.toSubmodule.mkQ.comp i))
    (hiA : i.range ≤ fixedSpace (c.sectionData.space.toRepresentation.comp C.subtype) A)
    (he : ∀ x v, i (BinaryNaturalDual.naturalDualRepresentation (p x) v) =
      c.sectionData.space.toRepresentation (q x) (i v)) : False := by
  let s := c.sectionData
  let g := s.central.toSubmodule.mkQ.comp i
  have hi : Function.Injective i := fun x y hh => hg (congrArg s.central.toSubmodule.mkQ hh)
  have hdim : Module.finrank (ZMod 2) (BinaryNaturalDual.CoordinateSpace 4) = 8 := by
    simp [BinaryNaturalDual.CoordinateSpace,BinaryNaturalDual.Space,BinaryLinear.OuterCyclic.Space]
  have hgA : g.range ≤ fixedSpace (s.action.comp C.subtype) A := by
    rintro _ ⟨v,rfl⟩ a
    change s.central.toSubmodule.mkQ (s.space.toRepresentation a.val (i v)) =
      s.central.toSubmodule.mkQ (i v)
    exact congrArg s.central.toSubmodule.mkQ (hiA ⟨v,rfl⟩ a)
  have hfixed : 8 ≤ Module.finrank (ZMod 2) (fixedSpace (s.action.comp C.subtype) A) := by
    let f := g.codRestrict _ (fun v => hgA ⟨v,rfl⟩)
    have hf : Function.Injective f := fun x y hh => hg (congrArg Subtype.val hh)
    simpa only [hdim] using LinearMap.finrank_le_finrank_of_injective hf
  cases BinaryActor.actionCase ρ (Or.inr rfl) mark c.clause_one with
  | irreducible _ _ hir hs _ =>
    cases hs with
    | natural _ e _ =>
      have hd := LinearMap.finrank_le_finrank_of_injective hg
      rw [hdim,e.linearEquiv.finrank_eq] at hd
      change 8 ≤ Module.finrank (ZMod 2) (Fin 5 → ZMod 2) at hd
      norm_num [Module.finrank_pi] at hd
    | orthogonal hd => omega
    | symmetricEight hd => omega
    | exterior _ _ _ e hd _ _ =>
      let := hir
      have hb := Representation.SL5ExteriorSquare.fixed_finrank_le_seven_of_even
        (s.action.comp C.subtype) e hd A (by rw [hA]; decide)
      omega
  | naturalDual _ hnat =>
    obtain ⟨e⟩ := hnat
    let A' := A.map e.groupEquiv.toMonoidHom
    have hr : 2 ≤ rank A' := by
      rw [rank,card_map_of_injective e.groupEquiv.injective,hA]
      decide
    have hf : Function.Injective (linearNatural BinaryField.two 5) := by
      intro a b hab
      exact specialLinearNatural_injective 5 hab
    have hb := BinaryNaturalDual.three_le_fixedCodim_prod_dual
      (linearNatural BinaryField.two 5) hf A' hr
    have hs := fixedCodim_add_finrank (naturalPlusDual 5) A'
    have hpair : Module.finrank (ZMod 2)
        ((Fin 5 → BinaryField.two.Carrier) × Module.Dual (ZMod 2) (Fin 5 → BinaryField.two.Carrier)) = 10 := by
      change Module.finrank (ZMod 2) ((Fin 5 → ZMod 2) × Module.Dual (ZMod 2) (Fin 5 → ZMod 2)) = 10
      simp [Module.finrank_prod]
    rw [hpair] at hs
    let f := e.linearEquiv.toLinearMap.comp i
    have hfA : f.range ≤ fixedSpace (naturalPlusDual 5) A' := by
      rintro _ ⟨v,rfl⟩ ⟨_,a,ha,rfl⟩
      change naturalPlusDual 5 (e.groupEquiv a) (e.linearEquiv (i v)) = e.linearEquiv (i v)
      rw [←e.intertwines]
      exact congrArg e.linearEquiv (hiA ⟨v,rfl⟩ ⟨a,ha⟩)
    let j := f.codRestrict _ (fun v => hfA ⟨v,rfl⟩)
    have hj : Function.Injective j := fun x y hh =>
      hi (e.linearEquiv.injective (congrArg Subtype.val hh))
    have hd := LinearMap.finrank_le_finrank_of_injective hj
    rw [hdim] at hd
    change 3 ≤ fixedCodim (naturalPlusDual 5) A' at hb
    omega
  | repeatedNatural r _ _ _ hnat =>
    obtain ⟨e⟩ := hnat
    let a := e.groupEquiv.toMonoidHom.comp q
    let σ : Representation (ZMod 2) F (Fin 5 → BinaryField.two.Carrier) :=
      (linearNatural BinaryField.two 5).comp a
    let τ : Representation (ZMod 2) F (Fin r → Fin 5 → BinaryField.two.Carrier) :=
      (repeated (linearNatural BinaryField.two 5) r).comp a
    apply BinaryNaturalDual.no_small_repeated_embedding (by decide : 3 ≤ 4) p hp σ τ
      (fun _ _ _ => rfl) (by
        change Module.finrank (ZMod 2) (Fin 5 → ZMod 2) < 2*4
        norm_num [Module.finrank_pi])
      (e.linearEquiv.toLinearMap.comp i) (e.linearEquiv.injective.comp hi)
    intro x v
    change e.linearEquiv (i _) = _
    rw [he]
    exact e.intertwines (q x) (i v)

open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Chapter1.RadicalExclusions.ModelReduction Chapter12.Section01.DoubleNaturalSource

/-- The actual classified star module cannot contain the original doubled
module fixed by its order-sixteen radical. The residual and central projection
are the literal maps in the established coordinates. -/
theorem FourStarModuleCoordinates.not_classified_of_radical_card
    {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V J H : Subgroup G}
    {B : DoubledBranch T L V 4} {K : Subgroup H}
    (d : FourStarModuleCoordinates B J H K)
    (e : starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃* SL(5,ZMod 2))
    (hcard : Nat.card ((starImage (K.map H.subtype) (J.pCoreIn 2) (J.pCoreIn 2)).subgroupOf
      (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype))) = 16) :
    ¬ d.Classified := by
  rintro ⟨hCO,c,i,hi,hg,_,_⟩
  let C := starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype)
  let R := starImage (K.map H.subtype) (J.pCoreIn 2) (J.pCoreIn 2)
  let O := offenderSubgroup (starRepresentation (K.map H.subtype) (J.pCoreIn 2))
  let Q := (R.subgroupOf O).subgroupOf (C.subgroupOf O)
  let eQ : Q ≃* R.subgroupOf C := {
    toFun x := ⟨⟨x.val.val.val,x.val.property⟩,x.property⟩
    invFun x := ⟨⟨⟨x.val.val,hCO x.val.property⟩,x.val.property⟩,x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  have hQ : Nat.card Q = 16 := (Nat.card_congr eQ.toEquiv).trans hcard
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let q : F →* C.subgroupOf O := (subgroupOfEquivOfLe hCO).symm.toMonoidHom.comp
    ((toStarImage (K.map H.subtype) (J.pCoreIn 2)).comp (inclusion d.residual_le))
  apply source_five_exclusion _ _ c ((subgroupOfEquivOfLe hCO).trans e) Q hQ
    _ d.residual_surjective q i hg
  · rintro _ ⟨v,rfl⟩ a
    apply Subtype.ext
    change starRepresentation (K.map H.subtype) (J.pCoreIn 2) a.val.val.val
      (i v : Additive (starV (K.map H.subtype) (J.pCoreIn 2))) =
      (i v : Additive (starV (K.map H.subtype) (J.pCoreIn 2)))
    rw [hi]
    exact d.radical_fixed ⟨v,rfl⟩ ⟨a.val.val.val,a.property⟩
  · intro x v
    apply Subtype.ext
    change (i (BinaryNaturalDual.naturalDualRepresentation _ v) :
        Additive (starV (K.map H.subtype) (J.pCoreIn 2))) =
      starRepresentation (K.map H.subtype) (J.pCoreIn 2) _
        (i v : Additive (starV (K.map H.subtype) (J.pCoreIn 2)))
    rw [hi,hi]
    exact d.intertwines x v

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
