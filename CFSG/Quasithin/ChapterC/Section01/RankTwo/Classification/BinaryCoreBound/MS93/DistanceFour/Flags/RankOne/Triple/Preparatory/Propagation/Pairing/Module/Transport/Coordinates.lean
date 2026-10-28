module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Pairing.Module.Line
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof.Transport

/-!
# Faithful moving coordinates for the split seed section

The kernel commutator hypothesis makes the radical exactly N. Extend the
natural moving coordinates across the actual globally fixed summand. Although
the extended coordinates kill that summand, they detect commutators modulo N:
every displacement lies in the moving preimage, whose intersection with the
fixed preimage is N. Thus the seed may retain a fixed component throughout.
Its coordinate image is nonzero and has order at most two.

Source: Meierfrankenfeld--Stellmacher (1993), notation on p.881 and
(4.6.8)(2), printed p.906.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Pairing
open RankOnePairing
open RankOnePairing.Incidence.FixedGeometry.ValueConstruction
namespace SplitLineData
variable {G : Type*} [Group G] {π : G →* SL} {flag : SL} {j : Bool}
  {H N X : Subgroup G} (d : SplitLineData π flag j H N X)
include d

theorem radical_eq : Escape.radicalPreimage π.ker H N = N :=
  by
  exact sup_eq_left.mpr d.kernel_commutator

theorem seed_le_group : X ≤ H := by
  exact d.generation ▸ le_normalClosure

noncomputable def coordinates :
    letI := d.sectionData.normal_kernel
    NaturalFactor π ⊤ H (centralizerModulo H ⊤ N) := by
  letI := d.sectionData.normal_kernel
  letI := d.sectionData.normal_group
  letI : (centralizerModulo H ⊤ N).Normal := by
    unfold centralizerModulo
    rw [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    infer_instance
  have hn : NaturalFactor π ⊤ (N ⊔ ⁅H, (⊤ : Subgroup G)⁆) N := by
    simpa only [Escape.movingPreimage, d.radical_eq] using d.sectionData.natural
  have hc : H = (N ⊔ ⁅H, (⊤ : Subgroup G)⁆) ⊔ centralizerModulo H ⊤ N := by
    simpa only [Escape.movingPreimage, d.radical_eq] using d.sectionData.decomposition
  have hi : (N ⊔ ⁅H, (⊤ : Subgroup G)⁆) ⊓ centralizerModulo H ⊤ N = N := by
    simpa only [Escape.movingPreimage, d.radical_eq] using d.sectionData.intersection
  exact extendNaturalAcrossFixed hn hc hi le_normalizer_of_normal

theorem coordinates_conj (a : G) (x : H) :
    letI := d.sectionData.normal_group
    d.coordinates.coordinates (MulAut.conjNormal a x) =
      vectorAction (d.coordinates.marking (π a)) (d.coordinates.coordinates x) := by
  let := d.sectionData.normal_group
  exact d.coordinates.action a (mem_top a) x (MulAut.conjNormal a x) rfl

theorem commutator_mem_iff (a : G) (x : H) :
    ⁅a, (x : G)⁆ ∈ N ↔
      vectorAction (d.coordinates.marking (π a)) (d.coordinates.coordinates x) =
        d.coordinates.coordinates x := by
  let := d.sectionData.normal_group
  let := d.sectionData.normal_kernel
  let c : H := MulAut.conjNormal a x * x⁻¹
  have hc : (c : G) = ⁅a, (x : G)⁆ := rfl
  have he : d.coordinates.coordinates c = 1 ↔
      vectorAction (d.coordinates.marking (π a)) (d.coordinates.coordinates x) =
        d.coordinates.coordinates x := by
    dsimp only [c]
    rw [map_mul, map_inv, d.coordinates_conj, mul_inv_eq_one]
  rw [← he, ← MonoidHom.mem_ker, d.coordinates.kernel]
  change ⁅a, (x : G)⁆ ∈ N ↔ (c : G) ∈ centralizerModulo H ⊤ N
  have hi : (N ⊔ ⁅H, (⊤ : Subgroup G)⁆) ⊓ centralizerModulo H ⊤ N = N := by
    simpa only [Escape.movingPreimage, d.radical_eq] using d.sectionData.intersection
  have hcm : (c : G) ∈ N ⊔ ⁅H, (⊤ : Subgroup G)⁆ := by
    apply mem_sup_right
    rw [hc, commutator_comm]
    exact commutator_mem_commutator (mem_top a) x.property
  constructor
  · intro hn
    exact mem_centralizerModulo_iff.mpr ⟨c.property, fun b _ => by
      have hn' : (c : G) ∈ N := hc.symm ▸ hn
      exact commutator_le_right (⊤ : Subgroup G) N
        (commutator_mem_commutator (mem_top b) hn')⟩
  · intro hn
    rw [← hc, ← hi]
    exact ⟨hcm, hn⟩

noncomputable def image (A : Subgroup G) : Subgroup VectorGroup :=
  (A.subgroupOf H).map d.coordinates.coordinates

theorem image_fixed_iff (A K : Subgroup G) (hA : A ≤ H) :
    d.image A ≤ fixedSpace ((K.map π).map d.coordinates.marking.toMonoidHom) ↔
      ⁅A, K⁆ ≤ N := by
  rw [commutator_comm, commutator_le]
  constructor
  · intro h a ha x hx
    apply (d.commutator_mem_iff a ⟨x, hA hx⟩).mpr
    exact h (mem_map_of_mem _ hx) _
      (mem_map_of_mem _ (mem_map_of_mem _ ha))
  · intro h v hv a ha
    obtain ⟨x, hx, rfl⟩ := hv
    obtain ⟨b, ⟨a, ha, rfl⟩, rfl⟩ := ha
    exact (d.commutator_mem_iff a x).mp (h a ha x hx)

theorem image_conjugate (A : Subgroup G) (hA : A ≤ H) (a : G) :
    d.image (A.map (MulAut.conj a).toMonoidHom) =
      (d.image A).map (vectorAction (d.coordinates.marking (π a))).toMonoidHom := by
  let := d.sectionData.normal_group
  have he : (A.map (MulAut.conj a).toMonoidHom).subgroupOf H =
      (A.subgroupOf H).map (MulAut.conjNormal a).toMonoidHom := by
    ext x
    constructor
    · rintro ⟨y, hy, he⟩
      exact ⟨⟨y, hA hy⟩, hy, Subtype.ext he⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [image, he, map_map, image, map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  exact d.coordinates_conj a x

theorem image_seed_card_le [Finite G] : Nat.card (d.image X) ≤ 2 := by
  let := d.sectionData.normal_kernel
  have hNC : N ≤ centralizerModulo H ⊤ N := by
    intro x hx
    exact mem_centralizerModulo_iff.mpr ⟨d.sectionData.kernel_le hx, fun a ha =>
      commutator_le_right (⊤ : Subgroup G) N (commutator_mem_commutator ha hx)⟩
  rw [image, ← relIndex_ker, d.coordinates.kernel, relIndex_subgroupOf d.seed_le_group]
  exact (relIndex_le_of_le_left hNC (by rw [d.line_index]; decide)).trans_eq d.line_index

theorem image_seed_ne_bot : d.image X ≠ ⊥ := by
  intro he
  apply d.residual_moves
  apply (d.image_fixed_iff X (rankOne (parabolic π flag j)) d.seed_le_group).mp
  rw [he]
  exact bot_le

end SplitLineData
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Pairing
