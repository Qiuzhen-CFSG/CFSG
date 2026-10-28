module

public import CFSG.Quasithin.ChapterJ.Section04To05.SteinbergCommutator
public import CFSG.Quasithin.ChapterJ.Section04To05.Setup.CoreProduct
public import Theory.Representation.PSL3Two.SteinbergStructure.LineRadicalCommutator.Incident
public import Theory.Representation.BinaryOffender.MovedSpaceTransport

/-!
# The original U lies in the invariant second commutator preimage

The second core is normal in its parabolic, so its Steinberg commutator
and the full original preimage S₂ are parabolic-invariant. The original
R₁ image is the radical of the marked point parabolic and preserves the
selected natural plane. Its fixed endomorphisms, namely U/V by J.2.3(8),
have image in that plane and hence lie in the second commutator space.
This proves U≤S₂ without introducing a new flag or changing the quotient.

Source: Aschbacher–Smith, J.4.3(2), printed p.441.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open BinaryLinearThree
noncomputable section
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (p : Plane d)

/-- The original second core is normal in the actual second parabolic. -/
theorem Plane.R₂_normalized : p.parabolic ≤ normalizer (p.R₂ : Set G) := by
  rw [p.R₂_eq]
  simpa only [pCoreIn,normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype]
    using (pCore 2 p.parabolic).le_normalizer_map p.parabolic.subtype

/-- The full preimage S₂ is invariant under the original second parabolic. -/
theorem Plane.S₂_normalized : p.parabolic ≤ normalizer (p.S₂ : Set G) := by
  let A := p.parabolic.subgroupOf d.L
  let X := p.R₂.subgroupOf d.L
  have hn : A ≤ normalizer X := fun a ha =>
    le_normalizer_comap d.L.subtype (p.R₂_normalized ha)
  have hi := subspaceCommutator_invariant_normalizer (S.comp d.ru1.quotientMap)
    (D := ⊤) (X := X) (A := A) (fun _ _ _ => Iff.rfl) hn
  apply le_normalizer_iff.mpr
  intro l hl x hx
  let lL : d.L := ⟨l,((p.mem_parabolic _).mp hl).1⟩
  let xS : d.toTypeRuSetup.S := ⟨x,p.S₂_le_S hx⟩
  let yS : d.toTypeRuSetup.S := ⟨l*x*l⁻¹,
    (mem_normalizer_iff.mp (d.ru1.steinberg.normalized lL.property) x).mp xS.property⟩
  have hx' := (p.mem_S₂ xS).mp hx
  rw [p.steinbergCommutator_eq] at hx'
  have hy := (hi (show lL ∈ A from hl) (d.ru1.steinberg.coordinates xS).toAdd).2 hx'
  apply (p.mem_S₂ yS).mpr
  have he := d.ru1.steinberg.equivariant lL xS
  change (d.ru1.steinberg.coordinates yS).toAdd =
    S (d.ru1.quotientMap lL) (d.ru1.steinberg.coordinates xS).toAdd at he
  rw [he,p.steinbergCommutator_eq]
  exact hy

/-- The second image is the core of the actual natural plane stabilizer. -/
theorem Plane.secondImage_eq_core : p.secondImage =
    (NaturalPlaneStabilizer.stabilizer p.naturalSpace).pCoreIn 2 := by
  have hk : p.quotient.ker = p.parabolicMap.ker := by
    ext a
    change p.quotient a = 1 ↔ p.parabolicMap a = 1
    rw [Subtype.ext_iff]
    change (p.quotient a : BinaryLinearThree.Group) = 1 ↔ _
    rw [p.quotient_apply,p.parabolicMap_apply]
  have hp : IsPGroup 2 p.quotient.ker := by
    rw [hk,p.parabolicMap_kernel]
    exact (isPGroup_pCoreIn 2 d.L).comap_subtype
  have hm : (pCore 2 p.parabolic).map p.quotient =
      pCore 2 (NaturalPlaneStabilizer.stabilizer p.naturalSpace) := by
    rw [← p.quotient.comap_pCore_of_ker_isPGroup p.quotient_surjective hp,
      map_comap_eq_self]
    rw [MonoidHom.range_eq_top_of_surjective _ p.quotient_surjective]
    exact le_top
  have hf : (NaturalPlaneStabilizer.stabilizer p.naturalSpace).subtype.comp p.quotient =
      p.parabolicMap := by
    apply MonoidHom.ext
    intro a
    change (p.quotient a : BinaryLinearThree.Group) = p.parabolicMap a
    rw [p.quotient_apply,p.parabolicMap_apply]
  have he := congrArg (fun J : Subgroup (NaturalPlaneStabilizer.stabilizer p.naturalSpace) =>
    J.map (NaturalPlaneStabilizer.stabilizer p.naturalSpace).subtype) hm
  rw [map_map,hf] at he
  rw [p.secondImage_eq]
  exact he

private theorem first_core_eq (d : LocalSetup G) :
    d.toTypeRuSetup.R₁ = d.parabolic.pCoreIn 2 := by
  rw [← d.parabolic_core_eq_R₁,← d.H_inf_L]
  change (d.toTypeRuSetup.H ⊓ d.L).pCoreIn 2 = (d.L ⊓ d.toTypeRuSetup.H).pCoreIn 2
  rw [inf_comm]

private theorem first_core_le_T (d : LocalSetup G) :
    d.toTypeRuSetup.R₁ ≤ (d.T : Subgroup G) := by
  have ht : (d.T : Subgroup G) ≤ d.parabolic := le_inf d.T_le_L d.toTypeRuSetup.T_le_H
  rw [first_core_eq d]
  have h := pCoreIn_le_sylow d.parabolic (d.T.subtype ht)
  simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le ht] using h

private theorem naturalSpace_invariant (g : BinaryLinearThree.Group)
    (hg : d.parabolicMap.range =
      Matrix.PSL3Two.pointParabolicSL.map (MulAut.conj g).toMonoidHom) :
    Matrix.PSL3Two.MarkedAutomorphisms.pointV.map (MulAut.conj g).toMonoidHom ≤
      subspaceStabilizer W p.naturalSpace := by
  have hr := SpecialCore.CommutatorGeometry.R₁_image d (first_core_eq d) g hg
  intro a ha
  rw [← hr] at ha
  obtain ⟨b,hb,rfl⟩ := ha
  let bP : p.parabolic := ⟨b,p.sylow_le_parabolic (first_core_le_T d hb)⟩
  have he : (p.quotient bP : BinaryLinearThree.Group) = d.parabolicMap b := by
    rw [p.quotient_apply]
    rfl
  rw [← he]
  exact (NaturalPlaneStabilizer.mem_stabilizer _ _).mp (p.quotient bP).property

/-- The original subgroup U lies in the original second commutator preimage. -/
theorem Plane.U_le_S₂ : d.toTypeRuSetup.U ≤ p.S₂ := by
  obtain ⟨g,hg⟩ := d.parabolic_image
  intro u hu
  let uS : d.toTypeRuSetup.S := ⟨u,d.U_le_S hu⟩
  apply (p.mem_S₂ uS).mpr
  have huf : (d.ru1.steinberg.coordinates uS).toAdd ∈
      SpecialCore.CommutatorGeometry.uSpace d := ⟨uS,hu,rfl⟩
  rw [SpecialCore.CommutatorGeometry.uSpace_eq_point_fixed d g hg] at huf
  rw [p.steinbergCommutator_eq_image,p.secondImage_eq_core]
  apply SteinbergStructure.LineRadicalCommutator.image_in_plane_le_commutator
    p.naturalSpace p.finrank_naturalSpace
  exact SteinbergStructure.LineRadicalCommutator.fixed_image_in_plane g p.naturalSpace
    p.card_naturalSpace (naturalSpace_invariant p g hg) _ huf
end
end CFSG.Quasithin.ChapterJ.RuSubgroup
