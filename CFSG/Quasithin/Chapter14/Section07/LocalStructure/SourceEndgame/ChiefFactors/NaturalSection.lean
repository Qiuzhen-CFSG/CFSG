module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Normalizers
public import Theory.GroupTheory.NoncentralChiefRefinement

/-!
# The original natural chief section in 14.7.71

Compose the coordinates of U/V₁ with the original natural projection. Its
kernel is exactly the fixed-space preimage U₀. Transport to subgroups of H
gives equivariant coordinates on the literal relative quotient. The actual
SL₂(4) marking is transitive on nonzero vectors, hence this section is an
H-chief factor, binary and noncentral. No equality U₀=V₁ is used.

These coordinates supply the lower noncentral stratum for the chief-factor
accounting in 14.7.71 and preserve the natural quotient used in 14.7.72–73.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.63 and 14.7.71, printed pp.1069 and 1075.
-/

public section
noncomputable section
open Subgroup Representation NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W] (d : Data T L V F W)

@[expose] def naturalAction : Representation (ZMod 2) F.H SL2FourNatural.V :=
  d.naturalQuotient.action.comp d.qH

@[expose] def naturalMap : F.U →* Multiplicative SL2FourNatural.V :=
  (AddMonoidHom.toMultiplicative d.projection.toLinearMap.toAddMonoidHom).comp
    d.conjugationSection.coordinates

theorem naturalMap_surjective : Function.Surjective (naturalMap d) := by
  intro v
  obtain ⟨w, hw⟩ := d.projection_onto v.toAdd
  obtain ⟨a, ha⟩ := d.conjugationSection.onto (Multiplicative.ofAdd w)
  refine ⟨a, ?_⟩
  change Multiplicative.ofAdd (d.projection (d.conjugationSection.coordinates a).toAdd) = v
  rw [ha]
  exact hw

theorem naturalMap_ker : (naturalMap d).ker = d.U₀.subgroupOf F.U := by
  ext a
  change d.projection (d.conjugationSection.coordinates a).toAdd = 0 ↔ (a : G) ∈ d.U₀
  exact (d.mem_U₀ a).symm

@[expose] def naturalSection : BinaryConjugationSection F.H F.U d.U₀ (naturalAction d) where
  section_le := d.conjugationSection.section_le
  kernel_le := d.U₀_le_U
  normalized := d.conjugationSection.normalized
  coordinates := naturalMap d
  onto := naturalMap_surjective d
  kernel_eq := naturalMap_ker d
  equivariant h a := by
    change d.projection _ = d.naturalQuotient.action (d.qH h) _
    rw [d.conjugationSection.equivariant]
    exact LinearMap.congr_fun (d.projection.isIntertwining' h) _

@[expose] def uNode : NormalNode F.H :=
  ⟨F.U.subgroupOf F.H, normal_subgroupOf_of_le_normalizer d.conjugationSection.normalized⟩

@[expose] def fixedNode : NormalNode F.H :=
  ⟨d.U₀.subgroupOf F.H, normal_subgroupOf_of_le_normalizer d.H_normalizes_U₀⟩

theorem fixedNode_le_uNode : fixedNode d ≤ uNode d :=
  subgroupOf_mono F.H d.U₀_le_U

private def intrinsicMap : (uNode d).val →* Multiplicative SL2FourNatural.V :=
  (naturalMap d).comp (subgroupOfEquivOfLe d.conjugationSection.section_le).toMonoidHom

private theorem intrinsicMap_surjective : Function.Surjective (intrinsicMap d) :=
  (naturalMap_surjective d).comp (subgroupOfEquivOfLe d.conjugationSection.section_le).surjective

private theorem intrinsicMap_ker : (intrinsicMap d).ker =
    (fixedNode d).val.subgroupOf (uNode d).val := by
  ext a
  exact (d.mem_U₀ ((subgroupOfEquivOfLe d.conjugationSection.section_le) a)).symm

private def oneCopy : Multiplicative SL2FourNatural.V ≃*
    Multiplicative (Fin 1 → SL2FourNatural.V) where
  toFun v := Multiplicative.ofAdd (fun _ => v.toAdd)
  invFun v := Multiplicative.ofAdd (v.toAdd 0)
  left_inv _ := rfl
  right_inv v := by
    apply Multiplicative.toAdd.injective
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    rw [hi]
    rfl
  map_mul' _ _ := rfl

def naturalChiefCoordinates :
    SectionCoordinates (fixedNode d) (uNode d) (naturalAction d) 1 where
  equiv := ((QuotientGroup.quotientMulEquivOfEq (intrinsicMap_ker d).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (intrinsicMap d)
      (intrinsicMap_surjective d))).trans oneCopy
  equivariant h x i := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ x
    exact (naturalSection d).equivariant h
      ((subgroupOfEquivOfLe d.conjugationSection.section_le) a)

/-- Formula on original representatives, retaining the chosen projection. -/
theorem naturalChiefCoordinates_mk (a : (uNode d).val) (i : Fin 1) :
    ((naturalChiefCoordinates d).equiv
      (QuotientGroup.mk' ((fixedNode d).val.subgroupOf (uNode d).val) a)).toAdd i =
    (naturalMap d ((subgroupOfEquivOfLe d.conjugationSection.section_le) a)).toAdd := by rfl

theorem naturalAction_transitive (v w : SL2FourNatural.V) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ h : F.H, naturalAction d h v = w := by
  obtain ⟨g, hg⟩ := SL2FourNatural.transitive_nonzero v w hv hw
  obtain ⟨h, hh⟩ := d.qH_surjective (d.naturalQuotient.marking g)
  refine ⟨h, ?_⟩
  change d.naturalQuotient.action (d.qH h) v = w
  rw [hh, d.naturalQuotient.restriction]
  exact hg

theorem naturalAction_irreducible : IsIrreducible (naturalAction d) := by
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun A => ?_⟩
  by_cases hA : A = ⊥
  · exact Or.inl hA
  right
  have hn : ¬ A ≤ ⊥ := fun h => hA (le_antisymm h bot_le)
  obtain ⟨v, hv, hv0⟩ := SetLike.not_le_iff_exists.mp hn
  apply le_antisymm le_top
  intro w _
  by_cases hw : w = 0
  · rw [hw]
    exact A.toSubmodule.zero_mem
  obtain ⟨h, hh⟩ := naturalAction_transitive d v w hv0 hw
  rw [← hh]
  exact A.apply_mem_toSubmodule h hv

theorem naturalAction_nontrivial : ∃ h v, naturalAction d h v ≠ v := by
  let v : SL2FourNatural.V := ![0, 1]
  obtain ⟨h, hh⟩ := d.qH_surjective (d.naturalQuotient.marking (SL2FourNatural.upper 1))
  refine ⟨h, v, ?_⟩
  change d.naturalQuotient.action (d.qH h) v ≠ v
  rw [hh, d.naturalQuotient.restriction, SL2FourNatural.upper_action]
  intro he
  have hh0 := congrFun he 0
  change (0 : SL2FourNatural.F) + 1 * 1 = 0 at hh0
  simp at hh0

theorem natural_chief : ChiefFactor.IsChief (F.U.subgroupOf F.H)
    (d.U₀.subgroupOf F.H) := by
  let := naturalAction_irreducible d
  exact (covBy_iff_isChief _ _).mp
    ((naturalChiefCoordinates d).covBy (fixedNode_le_uNode d) (naturalAction_nontrivial d))

theorem natural_noncentral_two : IsNoncentralTwo (fixedNode d) (uNode d) :=
  ⟨(naturalChiefCoordinates d).isPGroup,
    (naturalChiefCoordinates d).not_isCentral (by decide) (naturalAction_nontrivial d)⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors
