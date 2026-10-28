module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.NaturalGeneration.Generation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.NaturalGeneration.Section

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.NaturalGeneration.TransportInput

/-!
# The selected seed in its actual natural quotient

The full single section gives genuine coordinates on V_alpha modulo B_alpha.
The intersection of D_alpha with V_alpha lies in B_alpha, so those coordinates
descend to G_alpha/D_alpha. The chosen element remains nonzero. Surjectivity
of the untilded local residual onto the marked parabolic converts its supplied
commutator bound into pointwise fixation of that coordinate.

There are no global fixed vectors in the natural three-space. Together with
the proved fixation of B modulo Z, this identifies the exact pairing
preimage C with generated(X) intersected with the B-image. Thus restricting
the natural coordinates to the opposite local closure will have exactly
the intrinsic kernel required by (1.7).

`naturalSeedData` constructs the inputs for the remaining matrix-orbit and
local-closure transport proofs. It is not itself a rank-one factor.
Source: Meierfrankenfeld--Stellmacher (1993), printed pp.847--848 and 883.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
open RankOnePairing NaturalGeneration
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : Geometry R} {a : Vertex R} {f : FrameAt a}

omit [Finite M] in
/-- B is the image of the literal fixed preimage in the finite stabilizer. -/
theorem B_subgroupOf :
    (B R a (geometry.Z_normal a)).subgroupOf (stabilizer R a) =
      letI := geometry.Z_normal a
      centralizerModulo ((V R a).subgroupOf (stabilizer R a))
        (pResidual 2 (stabilizer R a)) ((Z R a).subgroupOf (stabilizer R a)) := by
  let := geometry.Z_normal a
  exact comap_map_eq_self_of_injective (stabilizer R a).subtype_injective _

omit [Finite M] in
/-- The quotient denominator kills only fixed vectors of V. -/
theorem denominator_inf_V_le_B :
    (V R a).subgroupOf (stabilizer R a) ⊓ (quotientMap a).ker ≤
      (B R a (geometry.Z_normal a)).subgroupOf (stabilizer R a) := by
  let := geometry.Z_normal a
  rw [B_subgroupOf (geometry := geometry)]
  rintro x ⟨hx, hq⟩
  have hD : x ∈ denominator a := (QuotientGroup.eq_one_iff _).mp hq
  rw [denominator_eq] at hD
  apply mem_centralizerModulo_iff.mpr
  refine ⟨hx, ?_⟩
  intro l hl
  have he : ⁅l, x⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hD.2 l hl)
  rw [he]
  exact one_mem _

/-- The natural moving quotient of V descends with kernel exactly the B-image. -/
noncomputable def quotientNaturalV (source : LocalSource L R)
    (hb : 2 < geometry.b R) (ha : color R a = false) (f : FrameAt a) :
    NaturalFactor (projection f) ⊤ (quotientImage a (V R a))
      (quotientImage a (B R a (geometry.Z_normal a))) := by
  let := geometry.Z_normal a
  let A := stabilizer R a
  let := finite_stabilizer R a
  have hgen : pResidual 2 A ⊔ (Q R a).subgroupOf A = ⊤ := by
    apply Subgroup.map_injective (f := A.subtype) A.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le
      (show Q R a ≤ A from fun _ hx => hx.1)]
    change Ltilde R a ⊔ Q R a = (⊤ : Subgroup A).map A.subtype
    rw [source.local_generation a ha, ← MonoidHom.range_eq_map, range_subtype]
  let n := sectionCoordinates f.natural_section (isPPerfect_pResidual 2)
    (source.V_isPGroup geometry hb a ha).comap_subtype hgen
  have hn : NaturalFactor f.projection ⊤ ((V R a).subgroupOf A)
      ((B R a (geometry.Z_normal a)).subgroupOf A) :=
    { n with kernel := by rw [B_subgroupOf (geometry := geometry)]; exact n.kernel }
  exact mapNaturalFactor hn (quotientMap a) (QuotientGroup.mk'_surjective _)
    rfl (by rw [B_subgroupOf (geometry := geometry)]; exact centralizerModulo_le _ _ _)
    (denominator_inf_V_le_B (geometry := geometry))

@[simp] theorem quotientNaturalV_marking (source : LocalSource L R)
    (hb : 2 < geometry.b R) (ha : color R a = false) (f : FrameAt a) :
    (quotientNaturalV source hb ha f).marking = f.natural_section.natural.marking := rfl


namespace NaturalGeneration
open RankOnePairing.Incidence.FixedGeometry.ValueConstruction

/-- No nonzero vector of the natural three-space is fixed by a subgroup
covering SL3. Fixation modulo a smaller subgroup therefore lies in the kernel. -/
theorem natural_fixed_modulo_le_kernel {G : Type*} [Group G]
    {π : G →* SL} {H N K Z : Subgroup G} [Z.Normal]
    (n : NaturalFactor π ⊤ H N) (hK : K.map π = ⊤) (hZN : Z ≤ N) :
    centralizerModulo H K Z ≤ N := by
  intro x hx
  obtain ⟨hxH, hxfix⟩ := mem_centralizerModulo_iff.mp hx
  let x' : H := ⟨x, hxH⟩
  have hfixed : n.coordinates x' ∈ fixedSpace Matrix.PSL3Two.lineParabolicSL := by
    intro g _
    obtain ⟨l, hl, he⟩ :=
      (show n.marking.symm g ∈ K.map π from hK.symm ▸ mem_top _)
    let y : H := ⟨l * x * l⁻¹,
      (mem_normalizer_iff.mp (n.normalized (mem_top _)) _).mp hxH⟩
    have hker : y * x'⁻¹ ∈ n.coordinates.ker := by
      rw [n.kernel]
      exact hZN (hxfix l hl)
    have hc : n.coordinates y = n.coordinates x' := by
      apply mul_inv_eq_one.mp
      simpa only [MonoidHom.mem_ker, map_mul, map_inv] using hker
    have hact := n.action l (mem_top _) x' y rfl
    rw [hc, he, n.marking.apply_symm_apply] at hact
    exact hact.symm
  rw [ModelProof.line_fixed_bot] at hfixed
  have hk : x' ∈ n.coordinates.ker := mem_bot.mp hfixed
  rw [n.kernel] at hk
  exact hk

end NaturalGeneration

namespace SelectedSeed
variable (s : SelectedSeed geometry a f)

omit [Finite M] in
/-- The element outside B remains outside its image after quotienting by D. -/
theorem element_not_mem_B_image :
    quotientMap a s.element ∉ quotientImage a (B R a (geometry.Z_normal a)) := by
  let := geometry.Z_normal a
  rintro ⟨b, hb, he⟩
  have hbV : b ∈ (V R a).subgroupOf (stabilizer R a) := by
    rw [B_subgroupOf (geometry := geometry)] at hb
    exact (mem_centralizerModulo_iff.mp hb).1
  have hdiff : s.element * b⁻¹ ∈
      (V R a).subgroupOf (stabilizer R a) ⊓ (quotientMap a).ker := by
    refine ⟨((V R a).subgroupOf (stabilizer R a)).mul_mem
      (moving_Z_le_V s.moving s.element_mem)
      (((V R a).subgroupOf (stabilizer R a)).inv_mem hbV), ?_⟩
    change quotientMap a (s.element * b⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have h := (B R a (geometry.Z_normal a)).mul_mem
    (denominator_inf_V_le_B (geometry := geometry) hdiff) hb
  apply s.outside
  change ((s.element : FreeAmalgam R) * (b : FreeAmalgam R)⁻¹) *
    (b : FreeAmalgam R) ∈ B R a (geometry.Z_normal a) at h
  simpa only [inv_mul_cancel_right] using h

/-- The selected element has a genuinely nonzero natural coordinate. -/
theorem element_coordinate_ne_one (source : LocalSource L R)
    (hb : 2 < geometry.b R) (ha : color R a = false) :
    (quotientNaturalV source hb ha f).coordinates
      ⟨quotientMap a s.element, mem_map_of_mem _
        (moving_Z_le_V s.moving s.element_mem)⟩ ≠ 1 := by
  intro h
  apply s.element_not_mem_B_image
  have hk : (⟨quotientMap a s.element, mem_map_of_mem _
      (moving_Z_le_V s.moving s.element_mem)⟩ : quotientImage a (V R a)) ∈
      (quotientNaturalV source hb ha f).coordinates.ker := h
  rw [(quotientNaturalV source hb ha f).kernel] at hk
  exact hk


/-- The pairing's exact fixed preimage is the intersection with the B-image. -/
theorem C_eq_generated_inf_B (source : LocalSource L R)
    (hb : 2 < geometry.b R) (ha : color R a = false) :
    s.C = generated s.X ⊓ quotientImage a (B R a (geometry.Z_normal a)) := by
  let := quotientImage_normal a (Z R a) (Z_normalized R a)
  have hZB : quotientImage a (Z R a) ≤ quotientImage a (B R a (geometry.Z_normal a)) :=
    map_mono (comap_mono (EdgeTransfer.Z_le_B hb a ha))
  have hf := natural_fixed_modulo_le_kernel (quotientNaturalV source hb ha f)
    (component_map (projection f)
      (quotientProjection_surjective a _ f.natural_section.projection_surjective _) s.flag) hZB
  apply le_antisymm
  · intro x hx
    obtain ⟨hxU, hxfix⟩ := (mem_fixedPreimage _ _ _ x).mp hx
    exact ⟨hxU, hf (mem_centralizerModulo_iff.mpr ⟨s.generated_X_le_V hxU, hxfix⟩)⟩
  · rintro x ⟨hxU, hxB⟩
    exact (mem_fixedPreimage _ _ _ x).mpr ⟨hxU,
      (mem_centralizerModulo_iff.mp
        (quotientImage_B_le_fixed (geometry := geometry) source ha s.flag hxB)).2⟩

/-- In particular the coordinate kernel on the actual opposite closure is
precisely C restricted to that subgroup. -/
theorem C_subgroupOf_localGenerated (source : LocalSource L R)
    (hb : 2 < geometry.b R) (ha : color R a = false) :
    s.C.subgroupOf (localGenerated (parabolic (projection f) s.flag (!s.side)) s.X) =
      (quotientImage a (B R a (geometry.Z_normal a))).subgroupOf
        (localGenerated (parabolic (projection f) s.flag (!s.side)) s.X) := by
  rw [s.C_eq_generated_inf_B source hb ha]
  ext x
  exact ⟨fun h => h.2, fun h => ⟨localGenerated_le_generated _ _ x.property, h⟩⟩

/-- All input data for the opposite-parabolic coordinate transport are
constructed from the selected element and the full single natural section. -/
noncomputable def naturalSeedData (source : LocalSource L R)
    (hb : 2 < geometry.b R) (ha : color R a = false) :
    NaturalSeedData (projection f) s.flag s.side
      (quotientImage a (V R a)) (quotientImage a (B R a (geometry.Z_normal a)))
      (quotientImage a (Z R a)) (quotientMap a s.element) := by
  let n := quotientNaturalV source hb ha f
  have hV : quotientMap a s.element ∈ quotientImage a (V R a) :=
    mem_map_of_mem _ (moving_Z_le_V s.moving s.element_mem)
  have himage (j : Bool) :
      (localResidual (parabolic (projection f) s.flag j)).map (projection f) =
        modelParabolic s.flag j := by
    have hh := localResidual_map (s.extension source ha) j
    simpa only [s.localParabolic_extension source ha, s.extension_projection source ha,
      s.extension_flag source ha] using hh
  refine {
    natural := n
    projection_surjective := quotientProjection_surjective a _
      f.natural_section.projection_surjective _
    residual_image := himage
    fixed_le_group := ?_
    z_le_fixed := map_mono (comap_mono (EdgeTransfer.Z_le_B hb a ha))
    z_le_kernel := ?_
    element_mem := hV
    element_kernel := ?_
    nonzero := s.element_coordinate_ne_one source hb ha
    fixed := ?_ }
  · let := geometry.Z_normal a
    apply map_mono
    rw [B_subgroupOf (geometry := geometry)]
    exact centralizerModulo_le _ _ _
  · rw [projection, quotientProjection_kernel]
    exact map_mono (comap_mono ((Z_le_VBall R a 2).trans (geometry.V_le_Q hb a ha)))
  · rw [projection, quotientProjection_kernel]
    exact mem_map_of_mem _ (geometry.V_le_Q hb a ha
      (moving_Z_le_V s.moving s.element_mem))
  · intro g hg
    obtain ⟨l, hl, he⟩ := (show g ∈
        (localResidual (parabolic (projection f) s.flag s.side)).map (projection f) by
      rw [himage]; exact hg)
    let x : quotientImage a (V R a) := ⟨quotientMap a s.element, hV⟩
    let y : quotientImage a (V R a) := ⟨l * (x : LocalQuotient a) * l⁻¹,
      (mem_normalizer_iff.mp (n.normalized (mem_top _)) _).mp x.property⟩
    have hk : y * x⁻¹ ∈ n.coordinates.ker := by
      rw [n.kernel]
      apply s.fixes_seed
      rw [commutator_comm]
      exact commutator_mem_commutator hl (mem_zpowers _)
    have hc : n.coordinates y = n.coordinates x := by
      apply mul_inv_eq_one.mp
      simpa only [MonoidHom.mem_ker, map_mul, map_inv] using hk
    have hact := n.action l (mem_top _) x y rfl
    rw [hc, he] at hact
    exact hact.symm

@[simp] theorem naturalSeedData_seed (source : LocalSource L R)
    (hb : 2 < geometry.b R) (ha : color R a = false) :
    (s.naturalSeedData source hb ha).seed = s.X := rfl

end SelectedSeed
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
