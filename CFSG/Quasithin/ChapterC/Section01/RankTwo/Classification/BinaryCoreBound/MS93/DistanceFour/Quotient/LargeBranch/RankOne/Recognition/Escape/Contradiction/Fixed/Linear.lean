module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Escape.Contradiction.Fixed.Linear.Standard
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedProduct

/-!
# Full parabolic fixation from the binary displacement budget

For the actual marked parabolic P and its intrinsic core Q, the bound
`dim [W,Q] ≤ 2` together with a cubic in P moving at least four dimensions
implies `C_W(Q) ≤ C_W(P)`. The standard-point proof uses saturation of
transvection displacement spaces and elementary-matrix commutator relations.
Here the diagram automorphism and flag conjugation transport the parabolic,
its intrinsic core and the same cubic simultaneously.

The proof allows nonsplit extensions. Global fixed-point freeness is not
needed; `fixedSpace_core_le_parabolic` retains it in the requested source
interface. The final frame application uses the original projection and its
literal intrinsic core, discharging the finite representation step once the
starred core bound and cubic displacement bound have been obtained.

Source: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.12)(4), printed p.911, with notation on p.905 and the two
natural sections in (4.6.12)(1)–(2), p.910. The geometric production of the
bounds and the rest of source assembly remain with the parent development.
-/

public section

open Subgroup Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Escape.ParabolicLinear

private def flagEquiv (flag : SL) (side : Bool) : SL ≃* SL :=
  if side then diagram.trans (MulAut.conj flag) else MulAut.conj flag

private theorem parabolic_eq_map (flag : SL) (side : Bool) :
    modelParabolic flag side = pointParabolicSL.map (flagEquiv flag side).toMonoidHom := by
  cases side
  · rfl
  · change lineParabolicSL.map (MulAut.conj flag).toMonoidHom =
      pointParabolicSL.map ((MulAut.conj flag).toMonoidHom.comp diagram.toMonoidHom)
    rw [← map_map, pointParabolic_map_diagram]

private theorem core_eq_map (flag : SL) (side : Bool) :
    (modelParabolic flag side).pCoreIn 2 = pointV.map (flagEquiv flag side).toMonoidHom := by
  rw [parabolic_eq_map, ← map_pCoreIn_of_injective 2 _ _ (flagEquiv flag side).injective,
    MarkedProduct.pointParabolic_core]

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) SL W)

private theorem movedSpace_comp_map (e : SL ≃* SL) (H : Subgroup SL) :
    Seed.movedSpace (ρ.comp e.toMonoidHom) H ⊤ =
      Seed.movedSpace ρ (H.map e.toMonoidHom) ⊤ := by
  apply congrArg (Submodule.span (ZMod 2))
  ext w
  constructor
  · rintro ⟨g, hg, v, hv, rfl⟩
    exact ⟨e g, mem_map_of_mem _ hg, v, hv, rfl⟩
  · rintro ⟨_, ⟨g, hg, rfl⟩, v, hv, rfl⟩
    exact ⟨g, hg, v, hv, rfl⟩

private theorem fixedSpace_comp_map' (e : SL ≃* SL) (H : Subgroup SL) :
    fixedSpace (ρ.comp e.toMonoidHom) H = fixedSpace ρ (H.map e.toMonoidHom) := by
  ext v
  constructor
  · intro h
    rintro ⟨_, g, hg, rfl⟩
    exact h ⟨g, hg⟩
  · intro h g
    exact h ⟨e g, mem_map_of_mem _ g.property⟩

variable [FiniteDimensional (ZMod 2) W]

/-- The literal displacement bounds alone force fixation by the full marked
parabolic; no semisimplicity or dimension assumption beyond finiteness is used. -/
theorem fixedSpace_core_le_parabolic_of_displacement
    (flag : SL) (side : Bool) (c : SL)
    (hc : c ∈ modelParabolic flag side) (ho : orderOf c = 3)
    (hcore : Module.finrank (ZMod 2)
      (Seed.movedSpace ρ ((modelParabolic flag side).pCoreIn 2) ⊤) ≤ 2)
    (hcubic : 4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ c - LinearMap.id))) :
    fixedSpace ρ ((modelParabolic flag side).pCoreIn 2) ≤
      fixedSpace ρ (modelParabolic flag side) := by
  let e := flagEquiv flag side
  let σ := ρ.comp e.toMonoidHom
  have hP : modelParabolic flag side = pointParabolicSL.map e.toMonoidHom :=
    parabolic_eq_map flag side
  have hQ : (modelParabolic flag side).pCoreIn 2 = pointV.map e.toMonoidHom :=
    core_eq_map flag side
  have hc' : e.symm c ∈ pointParabolicSL := by
    rw [hP] at hc
    obtain ⟨g, hg, he⟩ := hc
    have hg' : e.symm c = g := by rw [← he]; exact e.symm_apply_apply g
    rwa [hg']
  have ho' : orderOf (e.symm c) = 3 := (e.symm.orderOf_eq c).trans ho
  have hcore' : Module.finrank (ZMod 2) (Seed.movedSpace σ pointV ⊤) ≤ 2 := by
    dsimp only [σ]
    rw [movedSpace_comp_map, ← hQ]
    exact hcore
  have hcubic' : 4 ≤ Module.finrank (ZMod 2)
      (LinearMap.range (σ (e.symm c) - LinearMap.id)) := by
    have he : σ (e.symm c) = ρ c := by
      change ρ (e (e.symm c)) = ρ c
      rw [e.apply_symm_apply]
    rwa [he]
  have h := standard_fixation σ hcore' (e.symm c) hc' ho' hcubic'
  change fixedSpace (ρ.comp e.toMonoidHom) pointV ≤
    fixedSpace (ρ.comp e.toMonoidHom) pointParabolicSL at h
  rwa [fixedSpace_comp_map', fixedSpace_comp_map', ← hQ, ← hP] at h

/-- The source-facing interface, retaining zero global invariants. -/
theorem fixedSpace_core_le_parabolic
    (flag : SL) (side : Bool) (c : SL)
    (hc : c ∈ modelParabolic flag side) (ho : orderOf c = 3)
    (_hfixed : fixedSpace ρ ⊤ = ⊥)
    (hcore : Module.finrank (ZMod 2)
      (Seed.movedSpace ρ ((modelParabolic flag side).pCoreIn 2) ⊤) ≤ 2)
    (hcubic : 4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ c - LinearMap.id))) :
    fixedSpace ρ ((modelParabolic flag side).pCoreIn 2) ≤
      fixedSpace ρ (modelParabolic flag side) :=
  fixedSpace_core_le_parabolic_of_displacement ρ flag side c hc ho hcore hcubic

/-- Application to the actual projected frame actors. This discharges full
parabolic fixation from the starred core budget and the marked cubic bound,
without replacing the full parabolic by its ordered residual. -/
theorem frame_fixedSpace_core_le_parabolic
    {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {source : LocalSource L R}
    (f : Seed.Frame source) (i : Bool) (c : SL)
    (hc : c ∈ (f.parabolic i).map source.projection) (ho : orderOf c = 3)
    (hcore : Module.finrank (ZMod 2)
      (Seed.movedSpace ρ ((f.core i).map source.projection) ⊤) ≤ 2)
    (hcubic : 4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ c - LinearMap.id))) :
    fixedSpace ρ ((f.core i).map source.projection) ≤
      fixedSpace ρ ((f.parabolic i).map source.projection) := by
  rw [Seed.frame_core_image, Seed.frame_parabolic_image] at hcore ⊢
  rw [Seed.frame_parabolic_image] at hc
  exact fixedSpace_core_le_parabolic_of_displacement ρ f.flag
    (if i then !f.first else f.first) c hc ho hcore hcubic


private theorem fixedPreimage_le_parabolic_of_pointwise_displacement
    (flag : SL) (side : Bool) (Y : Submodule (ZMod 2) W)
    (hYcore : Y ≤ fixedSpace ρ ((modelParabolic flag side).pCoreIn 2))
    (hpoint : ∀ t : SL, orderOf t = 2 →
      Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≤ 2)
    (c : SL) (hc : c ∈ modelParabolic flag side) (ho : orderOf c = 3)
    (hker : LinearMap.ker (ρ c - LinearMap.id) ≤ Y)
    (hcodim : 4 ≤ Module.finrank (ZMod 2) (W ⧸ Y)) :
    Y ≤ fixedSpace ρ (modelParabolic flag side) := by
  let e := flagEquiv flag side
  let σ := ρ.comp e.toMonoidHom
  have hP : modelParabolic flag side = pointParabolicSL.map e.toMonoidHom :=
    parabolic_eq_map flag side
  have hQ : (modelParabolic flag side).pCoreIn 2 = pointV.map e.toMonoidHom :=
    core_eq_map flag side
  have hc' : e.symm c ∈ pointParabolicSL := by
    rw [hP] at hc
    obtain ⟨g, hg, he⟩ := hc
    have hg' : e.symm c = g := by rw [← he]; exact e.symm_apply_apply g
    rwa [hg']
  have ho' : orderOf (e.symm c) = 3 := (e.symm.orderOf_eq c).trans ho
  have hYcore' : Y ≤ fixedSpace σ pointV := by
    change Y ≤ fixedSpace (ρ.comp e.toMonoidHom) pointV
    rwa [fixedSpace_comp_map', ← hQ]
  have hpoint' (t : SL) (ht : orderOf t = 2) :
      Module.finrank (ZMod 2) (LinearMap.range (σ t - LinearMap.id)) ≤ 2 :=
    hpoint (e t) ((e.orderOf_eq t).trans ht)
  have hker' : LinearMap.ker (σ (e.symm c) - LinearMap.id) ≤ Y := by
    change LinearMap.ker (ρ (e (e.symm c)) - LinearMap.id) ≤ Y
    rwa [e.apply_symm_apply]
  have h := standard_fixedPreimage_of_pointwise_displacement σ Y hYcore'
    hpoint' (e.symm c) hc' ho' hker' hcodim
  change Y ≤ fixedSpace (ρ.comp e.toMonoidHom) pointParabolicSL at h
  rwa [fixedSpace_comp_map', ← hP] at h

/-- The actual projected frame parabolic fixes the specified source subspace
using only pointwise involution displacement, its cubic fixed-kernel containment
and the source codimension bound. -/
theorem frame_fixedPreimage_of_pointwise_displacement
    {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {source : LocalSource L R}
    (f : Seed.Frame source) (i : Bool) (Y : Submodule (ZMod 2) W)
    (hYcore : Y ≤ fixedSpace ρ ((f.core i).map source.projection))
    (hpoint : ∀ t : SL, orderOf t = 2 →
      Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≤ 2)
    (c : SL) (hc : c ∈ (f.parabolic i).map source.projection) (ho : orderOf c = 3)
    (hker : LinearMap.ker (ρ c - LinearMap.id) ≤ Y)
    (hcodim : 4 ≤ Module.finrank (ZMod 2) (W ⧸ Y)) :
    Y ≤ fixedSpace ρ ((f.parabolic i).map source.projection) := by
  rw [Seed.frame_core_image, Seed.frame_parabolic_image] at hYcore
  rw [Seed.frame_parabolic_image] at hc ⊢
  exact fixedPreimage_le_parabolic_of_pointwise_displacement ρ f.flag
    (if i then !f.first else f.first) Y hYcore hpoint c hc ho hker hcodim

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Escape.ParabolicLinear
