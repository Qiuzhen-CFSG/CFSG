module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Consequences
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Propagation.Algebra
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Propagation.Cyclic.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Propagation.Cyclic.Orientation

/-!
# The marked cyclic seed for MS93 (4.6.12)(3)

The literal quotient transport constructs a cyclic vector from the local
midpoint line, with its two-dimensional second-parabolic orbit. The edge
fixed-plane calculation aligns the original frame with the dual of the
supplied natural marking. Conjugating the vector by that inner change of
flag gives all fields of MarkedCyclicSeed in every actual orbit LayerModule.

This proves the cyclic-witness contract from LocalConsequences and the
compatible frame. Containment of the orbit span in the midpoint kernel is
a separate geometric conclusion of the source propagation argument; the
cyclic witness itself needs no additional containment premise.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), notation p.905 and (4.6.12)(3), pp.910--911; application on p.912.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed
variable {M : Type*} [Group M] {L R : Subgroup M} {source : LocalSource L R}
  {geometry : Geometry R}

namespace CyclicTransport
open BinaryLinearThree.ParabolicCyclic
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

private theorem orbit_twist (ρ : Representation (ZMod 2) SL W)
    (a : SL ≃* SL) (H : Subgroup SL) (v : W) :
    BinaryLinearThree.ParabolicCyclic.orbitSpan (ρ.comp a.toMonoidHom) H v =
      BinaryLinearThree.ParabolicCyclic.orbitSpan ρ (H.map a.toMonoidHom) v := by
  apply congrArg (Submodule.span (ZMod 2))
  ext w
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨a g, mem_map_of_mem _ hg, rfl⟩
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, rfl⟩

private theorem orbit_translate (ρ : Representation (ZMod 2) SL W)
    (v : W) (k : SL) :
    BinaryLinearThree.ParabolicCyclic.orbitSpan ρ ⊤ (ρ k v) =
      BinaryLinearThree.ParabolicCyclic.orbitSpan ρ ⊤ v := by
  apply congrArg (Submodule.span (ZMod 2))
  ext w
  constructor
  · rintro ⟨g, _, rfl⟩
    exact ⟨g * k, mem_top _, by rw [map_mul, Module.End.mul_apply]⟩
  · rintro ⟨g, _, rfl⟩
    refine ⟨g * k⁻¹, mem_top _, ?_⟩
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

private theorem orbit_map (ρ : Representation (ZMod 2) SL W)
    (H : Subgroup SL) (v : W) (k : SL) :
    (BinaryLinearThree.ParabolicCyclic.orbitSpan ρ H v).map (ρ k) =
      BinaryLinearThree.ParabolicCyclic.orbitSpan ρ (H.map (MulAut.conj k).toMonoidHom)
        (ρ k v) := by
  unfold BinaryLinearThree.ParabolicCyclic.orbitSpan
  rw [Submodule.map_span]
  apply congrArg (Submodule.span (ZMod 2))
  ext w
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨k * g * k⁻¹, mem_map_of_mem (MulAut.conj k).toMonoidHom hg, ?_⟩
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨ρ g v, ⟨g, hg, rfl⟩, ?_⟩
    change ρ k (ρ g v) = ρ (k * g * k⁻¹) (ρ k v)
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

private theorem conj_inverse_map (H : Subgroup SL) (k : SL) :
    (H.map (MulAut.conj k).toMonoidHom).map (MulAut.conj k⁻¹).toMonoidHom = H := by
  rw [Subgroup.map_map]
  have he : (MulAut.conj k⁻¹).toMonoidHom.comp (MulAut.conj k).toMonoidHom =
      MonoidHom.id SL := by
    ext g : 1
    simp [mul_assoc]
  rw [he, Subgroup.map_id]

/-- An inner change of incident flag transports a cyclic line and its parabolic
plane while retaining the prescribed outer twist. -/
private theorem marked_seed_of_frame {c : Vertex R}
    (common : CommonFacts R source geometry) (dO : LayerModule source (DistanceFour.orbitSpan c))
    (f : Frame source) (k : SL)
    (hp : Matrix.PSL3Two.pointParabolicSL.map ((MulAut.conj k).trans
      (dualTwist common.natural.marking)).toMonoidHom =
        (f.parabolic false).map source.projection)
    (hl : Matrix.PSL3Two.lineParabolicSL.map ((MulAut.conj k).trans
      (dualTwist common.natural.marking)).toMonoidHom =
        (f.parabolic true).map source.projection)
    (v : dO.Space) (hv : v ≠ 0)
    (hfixed : ∀ g ∈ (f.parabolic false).map source.projection,
      dO.representation g v = v)
    (hgen : BinaryLinearThree.ParabolicCyclic.orbitSpan dO.representation ⊤ v = ⊤)
    (hdim : Module.finrank (ZMod 2) (BinaryLinearThree.ParabolicCyclic.orbitSpan
      dO.representation ((f.parabolic true).map source.projection) v) = 2) :
    Nonempty (MarkedCyclicSeed common c dO) := by
  let a := dualTwist common.natural.marking
  let σ : Representation (ZMod 2) SL dO.Space := dO.representation.comp a.toMonoidHom
  let w := σ k⁻¹ v
  have hw : w ≠ 0 := by
    intro hz
    exact hv ((σ.apply_bijective k⁻¹).1 (hz.trans (map_zero (σ k⁻¹)).symm))
  refine ⟨{
    vector := w
    nonzero := hw
    point_fixed := ?_
    generates := ?_
    plane_dimension := ?_ }⟩
  · intro g hg
    have hh : σ (k * g * k⁻¹) v = v := by
      change dO.representation (a (k * g * k⁻¹)) v = v
      apply hfixed
      rw [← hp]
      exact ⟨g, hg, rfl⟩
    have hh := congrArg (σ k⁻¹) hh
    change σ g (σ k⁻¹ v) = σ k⁻¹ v
    simpa only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel_left] using hh
  · change BinaryLinearThree.ParabolicCyclic.orbitSpan σ ⊤ (σ k⁻¹ v) = ⊤
    rw [orbit_translate, orbit_twist,
      map_top_of_surjective a.toMonoidHom a.surjective]
    exact hgen
  · have hd : Module.finrank (ZMod 2) (BinaryLinearThree.ParabolicCyclic.orbitSpan
        σ (Matrix.PSL3Two.lineParabolicSL.map (MulAut.conj k).toMonoidHom) v) = 2 := by
      rw [orbit_twist, Subgroup.map_map]
      change Module.finrank (ZMod 2) (BinaryLinearThree.ParabolicCyclic.orbitSpan
        dO.representation (Matrix.PSL3Two.lineParabolicSL.map
          ((MulAut.conj k).trans a).toMonoidHom) v) = 2
      rw [hl]
      exact hdim
    have he := orbit_map σ
      (Matrix.PSL3Two.lineParabolicSL.map (MulAut.conj k).toMonoidHom) v k⁻¹
    rw [conj_inverse_map] at he
    change Module.finrank (ZMod 2) (BinaryLinearThree.ParabolicCyclic.orbitSpan
      σ Matrix.PSL3Two.lineParabolicSL (σ k⁻¹ v)) = 2
    rw [← he]
    let E := LinearMap.GeneralLinearGroup.toLinearEquiv (σ.asGroupHom k⁻¹)
    exact (E.finrank_map_eq _).trans hd

end CyclicTransport

/-- The local seed determines a cyclic witness with exactly the supplied natural
marking in every genuine quotient realization of the full orbit span. -/
theorem exists_markedCyclicSeed [Finite M]
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    {d : LayerModule source (V R (alpha R))} {f : Frame source}
    (s : CriticalSegment geometry) (hf : Compatible f s)
    {x : Input (geometry := geometry) d f s.middle}
    (hlocal : LocalConsequences d f s.middle x)
    (dO : LayerModule source (orbitSpan s.middle)) :
    Nonempty (MarkedCyclicSeed common s.middle dO) := by
  obtain ⟨v, hv, hfixed, hgen, hdim⟩ := exists_frame_cyclic_seed s hlocal dO
  obtain ⟨k, hp, hl⟩ := exists_dual_frame common radius s f hf
  exact CyclicTransport.marked_seed_of_frame common dO f k hp hl v hv hfixed hgen hdim

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed
