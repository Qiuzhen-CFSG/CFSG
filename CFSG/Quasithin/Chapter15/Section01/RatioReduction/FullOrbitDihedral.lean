module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.FullOrbitSingletonCyclic
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.DihedralResidual

/-!
# The original full-orbit dihedral alternative

The marked cyclic-three and cyclic-five endpoints on the literal Jhat
action give original case (1), with precisely the three prime/dimension
possibilities. Their kernel remains a normal cyclic subgroup of the actual
action image, equal to the intrinsic two-residual of Jhat and contained
in the ambient two-residual. The selected source supplies ambient
solvability and a trivial two-core. No ambient residual supplement is used.

The second theorem consumes the original singleton endpoint producer and
passes its unchanged E9 and extraspecial27 branches to their owners.
Source: Aschbacher–Smith 15.1.2(1), printed pp.1084 and1086.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

theorem source_localAction_full_orbit_dihedral
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    ∀ (l : CyclicSource.LocalGeneration (ρ.comp (Jhat ρ).subtype)) (p m : ℕ),
      CyclicSource.PrimeDimensionOptions p m → CyclicSource.DihedralMarking l p m →
    let P := l.kernel.map (Jhat ρ).subtype
    let t := (l.involution : D)
    Nonempty (Jhat ρ ≃* DihedralGroup p) ∧ Module.finrank (ZMod 2) (Additive V) = 2*m ∧
      Group.IsSolvable D ∧ pCore 2 D = ⊥ ∧ Nat.card (Jhat ρ) = 2*p ∧
      IsCyclic P ∧ Nat.card P = p ∧ P.Normal ∧ l.kernel = pResidual 2 (Jhat ρ) ∧
      P ≤ pResidual 2 D ∧ Jhat ρ = P ⊔ zpowers t ∧ orderOf t = 2 ∧
      (∀ x : P, t * (x : D) * t⁻¹ = (x : D)⁻¹) ∧
      subspaceCommutator ρ ⊤ P = ⊤ := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let : (Jhat ρ).Normal := Jhat_normal ρ
  dsimp only
  intro l p m hp hm
  exact ⟨hm.dihedral,hm.dimension,source_localAction_isSolvable hG T hempty hM,
    source_localAction_twoCore hG T hM,hm.ambient_marks (Jhat ρ) hp⟩

/-- The original full-orbit cyclic source gives case (1), or leaves precisely
its original marked E9 and extraspecial27 branches for their source consumers. -/
theorem source_localAction_full_orbit_cyclic_cases
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    ∀ (U : Submodule (ZMod 2) (Additive V))
      (c : FactorData ρ (Jhat ρ) U) (d : Decomposition c.representation), d.FittingFull →
    ∀ (i : d.Index), (∀ j : d.Index,j=i) → U=⊤ →
      (∀ A ∈ QhatStar (d.factor i).action, IsCyclic A) →
    (∃ p m, CyclicSource.PrimeDimensionOptions p m ∧
      Nonempty (Jhat ρ ≃* DihedralGroup p) ∧ Module.finrank (ZMod 2) (Additive V) = 2*m) ∨
    ∃ l : CyclicSource.LocalGeneration (ρ.comp (Jhat ρ).subtype),
      letI := BinaryGroupAction.action (ρ.comp (Jhat ρ).subtype)
      letI : Finite (Additive V) := Module.finite_of_finite (ZMod 2)
      letI : IsElementaryAbelian 2 (Multiplicative (Additive V)) := BinaryGroupAction.elementary
      letI := l.normal
      ChapterD.Section02.ElementaryNineEndpoint (V := Multiplicative (Additive V))
        l.kernel l.involution ∨
      ChapterD.Section02.ExtraspecialEndpoint (V := Multiplicative (Additive V))
        l.kernel l.involution := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  intro U c d hd i hi hU hc
  obtain ⟨l,hl⟩ := source_localAction_singleton_cyclic_endpoints hG T hempty hM hmany hJ
    U c d hd i hi hU hc
  rcases hl with ⟨p,m,hp,hm⟩ | hother
  · have h := source_localAction_full_orbit_dihedral hG T hempty hM l p m hp hm
    exact Or.inl ⟨p,m,hp,h.1,h.2.1⟩
  · exact Or.inr ⟨l,hother⟩
end CFSG.Quasithin.Chapter15.Section01
