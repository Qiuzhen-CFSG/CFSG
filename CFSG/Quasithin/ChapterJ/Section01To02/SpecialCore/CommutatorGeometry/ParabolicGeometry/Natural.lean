module

public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.CommutatorGeometry.Propagation
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.Basic
public import Theory.Representation.PSL3Two.SteinbergStructure.PointRadicalFixedSpace.NaturalParabolics

/-!
# The natural parabolic input to J.2.3

Transport a subgroup of V through its faithful natural coordinates. An adapted
basis supplies a Sylow stabilizer of the image. Its preimage under the common
Ru1 quotient marking is an actual Sylow subgroup of L, since the kernel is the
two-core. Equivariance then proves normalization of the original subgroup.

The final theorem applies the published commutator propagation argument with
this premise discharged. The independent full-commutator seed remains explicit.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.3(6), printed p.433 (PDF p.444).
-/

@[expose] public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.SpecialCore.CommutatorGeometry
variable {G : Type*} [Group G] [Finite G]
open BinaryLinearThree.SteinbergStructure.PointRadicalFixedSpace

omit [Finite G] in
/-- The natural Ru1 action supplies the parabolic input to commutator propagation. -/
theorem natural_parabolics {L V : Subgroup G} (r : RuOne L V) : NaturalParabolics L V := by
  intro W hWV _ _
  let A : Submodule (ZMod 2) BinaryLinearThree.Vector :=
    AddSubgroup.toZModSubmodule 2
      ((W.subgroupOf V).map r.natural.coordinates).toAddSubgroup'
  obtain ⟨P',hP'⟩ := natural_subspace_sylow A
  have hk : IsPGroup 2 r.quotientMap.ker := by
    rw [r.quotient_kernel]
    exact (isPGroup_pCoreIn 2 L).comap_subtype
  let P := P'.comapOfKerIsPGroup r.quotientMap hk (by
    rw [MonoidHom.range_eq_top_of_surjective _ r.quotient_surjective]
    exact le_top)
  have hinj : Function.Injective r.natural.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [r.natural.kernel_eq, bot_subgroupOf]
  have hstable (g : L) (hg : g ∈ (P : Subgroup L)) (w : G) (hw : w ∈ W) :
      (g : G) * w * (g : G)⁻¹ ∈ W := by
    let v : V := ⟨w,hWV hw⟩
    have hv : (r.natural.coordinates v).toAdd ∈ A := mem_map.mpr ⟨v,hw,rfl⟩
    have hgp : r.quotientMap g ∈ (P' : Subgroup BinaryLinearThree.Group) := hg
    obtain ⟨v',hv',he⟩ := hP' _ hgp _ hv
    let vconj : V := ⟨g*w*(g:G)⁻¹,
      (mem_normalizer_iff.mp (r.natural.normalized g.property) w).mp v.property⟩
    have heq : v' = vconj := hinj (he.trans
      (Multiplicative.toAdd.injective (r.natural.equivariant g v)).symm)
    have hvW : (v' : G) ∈ W := hv'
    have heG : (v' : G) = (g : G) * w * (g : G)⁻¹ := congrArg Subtype.val heq
    exact heG ▸ hvW
  refine ⟨P, fun g hg => ?_⟩
  apply mem_normalizer_iff.mpr
  intro w
  constructor
  · exact hstable g hg w
  · intro hw
    have h := hstable g⁻¹ ((P : Subgroup L).inv_mem hg) _ hw
    simpa only [coe_inv, inv_inv, inv_mul_cancel_left, mul_inv_cancel_right, mul_assoc, inv_mul_cancel, mul_one] using h

/-- Apply the published propagation argument with the natural parabolic premise discharged.
The independent full-commutator seed remains with its source assembly owner. -/
theorem full_commutator_of_seed {L V : Subgroup G} (r : RuOne L V)
    (P : Sylow 2 L) (hseed : SylowSeed r P) (t : L.pCoreIn 2) (ht : (t:G) ∉ V) :
    ⁅zpowers (t:G),L.pCoreIn 2⁆ = V :=
  full_commutator_of_one_seed r (natural_parabolics r) P hseed t ht

end CFSG.Quasithin.ChapterJ.SpecialCore.CommutatorGeometry
