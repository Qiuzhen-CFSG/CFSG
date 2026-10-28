module
public import Theory.Representation.SL2FourNaturalOrbits.PlaneOrbits
public import Theory.Representation.SL2FourNaturalOrbits.ElementaryActors
public import CFSG.Quasithin.ChapterG.Section10.InvariantGeometry
/-!
# Excluding the bare natural SL₂(4) action with a large marked actor

An invariant binary plane for a Sylow four-group in the natural module is
its fixed field-line: a vector outside that line has all its displacements
on the line. The G.10 fixed-space condition instead permits only the marked
point in the fixed part of its plane. Thus an elementary actor of order at
least four rules out the bare special-linear group.

The original HS consumer is SourceAction.NaturalOrder. Source:
Aschbacher--Smith 14.3.23(2)(ii), printed p.1000.
-/

public section
open Subgroup Module Representation
namespace Representation.SL2FourNatural
private theorem sylow_stable_plane_fixed (P : Sylow 2 SL)
    (W : Submodule (ZMod 2) V) (hc : Nat.card W=4)
    (hi : ∀ a∈P, ∀ w∈W, action a w∈W) :
    ∀ a∈P, ∀ w∈W, action a w=w := by
  obtain ⟨C,hC,hfix,hdisp⟩ := sylow_fixed_plane_displacements P
  have hWC : W≤C := by
    intro w hw
    by_contra hn
    have hCW : C≤W := by
      intro v hv
      obtain ⟨a,ha,he⟩ := hdisp w hn v hv
      exact he ▸ W.sub_mem (hi a ha w hw) hw
    exact hn ((PlaneGeometry.submodule_eq_of_card C W hCW (hC.trans hc.symm)).symm ▸ hw)
  intro a ha w hw
  exact (hfix w).mp (hWC hw) a ha
end Representation.SL2FourNatural

namespace CFSG.Quasithin.ChapterG.Section11.FourNatural
open SL2FourNatural
variable {G U : Type*} [Group G] [Finite G] [AddCommGroup U]
  [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  {ρ : Representation (ZMod 2) G U} {B : LinearMap.BilinForm (ZMod 2) U}
  {v : U} {W : Submodule (ZMod 2) U} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

theorem not_special_linear (h : Section10.Hypothesis ρ B v W X X₀)
    (hW : finrank (ZMod 2) W=2) (hX : 4≤Nat.card X)
    (e : G ≃* SL) (c : U ≃ₗ[ZMod 2] V)
    (he : ∀ a w, c (ρ a w)=action (e a) (c w)) : False := by
  obtain ⟨P,hP⟩ := ((IsElementaryAbelian.isPGroup 2 X).map e.toMonoidHom).exists_le_sylow
  have hSL : Nat.card SL=60 := by
    rw [Nat.card_congr alternatingFiveEquiv.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hPc : Nat.card P=4 := by rw [P.card_eq_multiplicity,hSL]; decide +kernel
  have hXP : X.map e.toMonoidHom=(P : Subgroup SL) :=
    Subgroup.eq_of_le_of_card_ge hP (by rw [card_map_of_injective e.injective,hPc]; exact hX)
  let W' := W.map c.toLinearMap
  have hc : Nat.card W'=4 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W')
    rw [c.finrank_map_eq W,hW,Nat.card_zmod] at hh
    exact hh
  have hs : ∀ a∈P, ∀ w∈W', action a w∈W' := by
    intro a ha w hw
    obtain ⟨b,hb,rfl⟩ := (show a∈X.map e.toMonoidHom from hXP.symm ▸ ha)
    obtain ⟨u,hu,rfl⟩ := hw
    exact ⟨ρ b u,h.stable_W ⟨b,hb⟩ u hu,he b u⟩
  have hfixed : W≤BinaryOffender.fixedSpace ρ X := by
    intro w hw x
    apply c.injective
    change c (ρ x.val w) = c w
    rw [he]
    exact SL2FourNatural.sylow_stable_plane_fixed P W' hc hs (e x.val)
      (hP (mem_map_of_mem e.toMonoidHom x.property)) (c w) ⟨w,hw,rfl⟩
  have hh := congrArg (fun Y : Submodule (ZMod 2) U => finrank (ZMod 2) Y) h.fixedSpace_in_W
  rw [inf_eq_left.mpr hfixed,hW,finrank_span_singleton h.point_ne_zero] at hh
  omega
end CFSG.Quasithin.ChapterG.Section11.FourNatural
