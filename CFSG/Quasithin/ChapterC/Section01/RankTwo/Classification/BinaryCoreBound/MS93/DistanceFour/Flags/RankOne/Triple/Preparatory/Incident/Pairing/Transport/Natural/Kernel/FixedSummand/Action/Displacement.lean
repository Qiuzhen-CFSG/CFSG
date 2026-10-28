module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Natural.Kernel.FixedSummand.Transport

/-!
# Descending the bar action and identifying the seed image

The first two-core acts trivially on V_beta/Z_alpha. Its full-parabolic
representation therefore descends through the genuine rank-one quotient.
For any quotient marking in which the opposite core has image {1,t}, the
image of Z_alpha[V_beta,Q_delta] is exactly range(ρ(t) - 1): the denominator
vanishes, commutators map to displacements, and every displacement lifts
using the onto map from the original edge layer.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8)(3), printed p.906;
the intrinsic fixed denominator for (1.7) is on printed pp.847--848.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Natural.Kernel
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {i : Bool}

/-- Descend the literal bar action through the genuine first-parabolic
quotient. The action descends through its group of invertible linear maps. -/
theorem exists_descended_barRepresentation
    (b : FlagLayerModule source i (Z R (alpha R)))
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (hkernel : flagKernel source i = Q R (beta R))
    (π : flagParabolic source i →* BinaryS3.Actor) (hπ : Function.Surjective π)
    (hker : π.ker = (flagKernel source i).subgroupOf (flagParabolic source i)) :
    ∃ ρ : Representation (ZMod 2) BinaryS3.Actor b.Space,
      ∀ g v, b.representation g v = ρ (π g) v := by
  have hk : π.ker ≤ b.representation.asGroupHom.ker := by
    intro g hg
    apply MonoidHom.mem_ker.mpr
    apply Units.ext
    exact MonoidHom.mem_ker.mp (bar_core_le_kernel b geometry common early hkernel (hker ▸ hg))
  let σ := π.liftOfSurjective hπ ⟨b.representation.asGroupHom, hk⟩
  let ρ : Representation (ZMod 2) BinaryS3.Actor b.Space :=
    (Units.coeHom (b.Space →ₗ[ZMod 2] b.Space)).comp σ
  refine ⟨ρ, ?_⟩
  intro g v
  have he : σ (π g) = b.representation.asGroupHom g :=
    π.liftOfRightInverse_comp_apply _ _ _ g
  change b.representation g v = (σ (π g)).val v
  rw [he, Representation.asGroupHom_apply]

/-- The seed modulo Z_alpha is exactly the displacement range of the
reflection that is the image of the incident opposite core. -/
theorem seed_image_of_reflection
    (b : FlagLayerModule source i (Z R (alpha R)))
    (geometry : Geometry R) (hlarge : 2 < geometry.b R)
    (hkernel : flagKernel source i = Q R (beta R))
    (d : M) (hd : flagIncident source i 1 d)
    (π : flagParabolic source i →* BinaryS3.Actor)
    (ρ : Representation (ZMod 2) BinaryS3.Actor b.Space)
    (haction : ∀ g v, b.representation g v = ρ (π g) v)
    (t : BinaryS3.Actor)
    (himage : ∀ a, a ∈ ((localFlagKernel source (!i) d).subgroupOf
      (flagParabolic source i)).map π ↔ a = 1 ∨ a = t) :
    barImage b (Pairing.seed source i d) = BinaryS3.displacement ρ t := by
  let H := V R (beta R)
  let K := localFlagKernel source (!i) d
  let D := BinaryS3.displacement ρ t
  let N : Subgroup (FreeAmalgam R) :=
    (D.toAddSubgroup.toSubgroup.comap b.projection).map H.subtype
  have hcalc (g : flagParabolic source i) (x : H) :
      (b.projection (edgeRadiusAction source geometry hlarge i hkernel g x * x⁻¹)).toAdd =
        ρ (π g) (b.projection x).toAdd - (b.projection x).toAdd := by
    simp only [map_mul, map_inv, toAdd_mul, toAdd_inv,
      ← sub_eq_add_neg]
    rw [b.action g x _ (edgeRadiusAction_apply source geometry hlarge i hkernel g x), haction]
  have hcoe (g : flagParabolic source i) (x : H) :
      ((edgeRadiusAction source geometry hlarge i hkernel g x * x⁻¹ : H) : FreeAmalgam R) =
        ⁅(g : FreeAmalgam R), (x : FreeAmalgam R)⁆ := by
    change (edgeRadiusAction source geometry hlarge i hkernel g x : FreeAmalgam R) *
      (x : FreeAmalgam R)⁻¹ = _
    rw [edgeRadiusAction_apply]
    rfl
  apply le_antisymm
  · have hZ : Z R (alpha R) ≤ N := by
      intro z hz
      let x : H := ⟨z, Z_le_edgeRadius hz⟩
      have hx : x ∈ b.projection.ker := b.kernel ▸ hz
      refine ⟨x, ?_, rfl⟩
      change (b.projection x).toAdd ∈ D
      rw [MonoidHom.mem_ker.mp hx]
      exact D.zero_mem
    have hC : ⁅H, K⁆ ≤ N := by
      rw [commutator_comm]
      apply commutator_le.mpr
      intro g hg x hx
      let a : flagParabolic source i := ⟨g, incidentKernel_le_flagParabolic source i d hd hg⟩
      let v : H := ⟨x, hx⟩
      refine ⟨edgeRadiusAction source geometry hlarge i hkernel a v * v⁻¹, ?_, hcoe a v⟩
      change (b.projection _).toAdd ∈ D
      rw [hcalc]
      have hm := (himage (π a)).mp (mem_map_of_mem π (show a ∈ K.subgroupOf _ from hg))
      rcases hm with hm | hm
      · rw [hm, map_one]
        change (b.projection v).toAdd - (b.projection v).toAdd ∈ D
        simpa only [sub_self] using D.zero_mem
      · rw [hm]
        exact ⟨(b.projection v).toAdd, rfl⟩
    have hseed : Pairing.seed source i d ≤ N := sup_le hZ hC
    rintro v ⟨x, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := hseed hx
    have he' : y = x := Subtype.ext he
    subst y
    exact hy
  · rintro v ⟨w, rfl⟩
    obtain ⟨x, hx⟩ := b.onto (Multiplicative.ofAdd w)
    obtain ⟨g, hg, he⟩ := (himage t).mpr (Or.inr rfl)
    apply (mem_barImage b (Pairing.seed source i d) _).mpr
    refine ⟨edgeRadiusAction source geometry hlarge i hkernel g x * x⁻¹, ?_, ?_⟩
    · apply (le_sup_right : ⁅H,K⁆ ≤ Pairing.seed source i d)
      rw [commutator_comm, hcoe]
      exact commutator_mem_commutator hg x.property
    · rw [hcalc, he, hx]
      rfl

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Natural.Kernel
