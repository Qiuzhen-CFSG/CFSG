module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed.Contracts
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Normalizers
public import Theory.Representation.SL2FourNaturalOrbits.PlaneTransport

/-!
# The original natural coordinates and the V/V₁ plane

Compose the original U/V₁ coordinates with the original natural projection.
Its kernel is U₀; when U₀ = V₁ the projection itself is injective. The image
of V is a binary plane, and its full preimage is precisely V. Equivariance
then lifts every SL₂(4) actor preserving this plane through the original qH
to an element of N_H(V). These coordinates supply the ambient action in
`ParabolicSeed.LocalAction` without choosing a standard plane or changing qH.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.63–65, printed pp.1069–1070, and the proof of 14.7.72,
printed p.1076 (PDF p.1093), where UR/R = [UR/R,L₁] ≅ E₄.
-/

@[expose] public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed.LocalAction
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- The original section map followed by the original natural projection. -/
def naturalCoordinates : F.U →* Multiplicative SL2FourNatural.V :=
  d.projection.toLinearMap.toAddMonoidHom.toMultiplicative.comp d.conjugationSection.coordinates

theorem naturalCoordinates_surjective : Function.Surjective (naturalCoordinates d) := by
  intro w
  obtain ⟨v, hv⟩ := d.projection_onto w.toAdd
  obtain ⟨x, hx⟩ := d.conjugationSection.onto (Multiplicative.ofAdd v)
  refine ⟨x, ?_⟩
  change Multiplicative.ofAdd (d.projection (d.conjugationSection.coordinates x).toAdd) = w
  rw [hx]
  exact Multiplicative.toAdd.injective hv

theorem naturalCoordinates_ker : (naturalCoordinates d).ker = d.U₀.subgroupOf F.U := by
  ext x
  exact (d.mem_U₀ x).symm

/-- The original projection loses no further vectors when U₀ = V₁. -/
theorem projection_injective (hU₀ : d.U₀ = F.Vi 1) : Function.Injective d.projection := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro w hw
  obtain ⟨x, hx⟩ := d.conjugationSection.onto (Multiplicative.ofAdd w)
  have hx₀ : (x : G) ∈ d.U₀ := (d.mem_U₀ x).mpr (by rw [hx]; exact hw)
  have hx1 := (d.conjugationSection.coordinates_eq_one_iff x).mpr (hU₀ ▸ hx₀)
  change w = 0
  exact congrArg Multiplicative.toAdd (hx.symm.trans hx1)

/-- V/V₁ in the same natural coordinates, rather than a chosen standard plane. -/
def seedPlane : Submodule (ZMod 2) SL2FourNatural.V :=
  AddSubgroup.toZModSubmodule 2 (((V.subgroupOf F.U).map (naturalCoordinates d)).toAddSubgroup')

theorem coordinates_mem_seedPlane (hU₀ : d.U₀ = F.Vi 1) (u : F.U) :
    (naturalCoordinates d u).toAdd ∈ seedPlane d ↔ (u : G) ∈ V := by
  change u ∈ ((V.subgroupOf F.U).map (naturalCoordinates d)).comap (naturalCoordinates d) ↔ _
  rw [comap_map_eq, naturalCoordinates_ker, hU₀,
    sup_eq_left.mpr (subgroupOf_mono F.U (F.le_seed 1))]
  rfl

theorem card_seedPlane (hU₀ : d.U₀ = F.Vi 1) : Nat.card (seedPlane d) = 4 := by
  change Nat.card ((V.subgroupOf F.U).map (naturalCoordinates d)) = 4
  rw [← relIndex_ker, naturalCoordinates_ker, hU₀,
    relIndex_subgroupOf (Data.V_le_U F)]
  have h := ((F.Vi 1).subgroupOf V).index_mul_card
  change (F.Vi 1).relIndex V * Nat.card ((F.Vi 1).subgroupOf V) = Nat.card V at h
  have hV : Nat.card V = 8 := by
    rw [← F.last]
    exact F.card 3 (by decide)
  rw [Nat.card_congr (subgroupOfEquivOfLe (F.le_seed 1)).toEquiv,
    F.card 1 (by decide), hV] at h
  norm_num at h ⊢
  omega

theorem naturalCoordinates_equivariant (h : F.H) (u : F.U) :
    (naturalCoordinates d ⟨(h : G) * (u : G) * (h : G)⁻¹,
      (mem_normalizer_iff.mp (d.conjugationSection.normalized h.property) u).mp u.property⟩).toAdd =
    d.naturalQuotient.action (d.qH h) (naturalCoordinates d u).toAdd := by
  change d.projection (d.conjugationSection.coordinates _).toAdd = _
  rw [d.conjugationSection.equivariant]
  exact LinearMap.congr_fun (d.projection.isIntertwining' h) _

/-- A natural actor preserving the literal seed image lifts to N_H(V). -/
theorem lift_plane_stabilizer (hU₀ : d.U₀ = F.Vi 1) (g : SL2FourNatural.SL)
    (hg : ∀ v ∈ seedPlane d, SL2FourNatural.action g v ∈ seedPlane d) :
    ∃ h : F.H, (h : G) ∈ normalizer (V : Set G) ∧
      d.qH h = d.naturalQuotient.marking g := by
  obtain ⟨h, hh⟩ := d.qH_surjective (d.naturalQuotient.marking g)
  refine ⟨h, ?_, hh⟩
  apply mem_normalizer_fintype
  intro v hv
  let u : F.U := ⟨v, Data.V_le_U F hv⟩
  apply (coordinates_mem_seedPlane d hU₀ ⟨(h : G) * (u : G) * (h : G)⁻¹,
    (mem_normalizer_iff.mp (d.conjugationSection.normalized h.property) u).mp u.property⟩).mp
  rw [naturalCoordinates_equivariant, hh, d.naturalQuotient.restriction]
  exact hg _ ((coordinates_mem_seedPlane d hU₀ u).mpr hv)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed.LocalAction
