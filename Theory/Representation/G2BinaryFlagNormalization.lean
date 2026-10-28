module
public import Theory.Representation.G2BinaryPlaneKernel
/-!
# Normalization of the literal binary unitary flag

Positive-root coordinates preserve the plane and seed. The long Weyl
reflection also preserves the seed, so the full point parabolic does too.
The point-plane incidence and plane cardinality are computed in the same
six-coordinate frame. These facts provide original Sylow and local-residual
normalization in the unitary application of F.9.1.

Source: Aschbacher–Smith 13.3.18(1), printed p.894.
-/

public section
namespace Atlas.G2.Natural.BinaryPointFlag
open Atlas.G2.Restricted.NaturalCoordinates Atlas.G2.Explicit Subgroup
open Atlas.G2.LieParabolicSetup Representation.BinaryOffender

theorem pointLine_le_plane : pointLine≤plane := by
  intro v hv
  rw [mem_plane]
  exact ⟨(mem_pointLine v).mp hv 2 (by decide),(mem_pointLine v).mp hv 3 (by decide),
    (mem_pointLine v).mp hv 4 (by decide),(mem_pointLine v).mp hv 5 (by decide)⟩

theorem unipotent_preserves_plane (g:Model F) (hg:g∈unipotent) (v:W) (hv:v∈plane) :
    Restricted.NaturalCoordinates.action F g v∈plane := by
  rw [unipotent_eq_range] at hg
  obtain ⟨t,rfl⟩:=hg
  obtain ⟨h2,h3,h4,h5⟩:=(mem_plane v).mp hv
  rw [mem_plane]
  simp [unipotentProduct,map_mul,Module.End.mul_apply,h2,h3,h4,h5]

theorem unipotent_preserves_seed (g:Model F) (hg:g∈unipotent) (v:W) (hv:v∈seed) :
    Restricted.NaturalCoordinates.action F g v∈seed := by
  rw [unipotent_eq_range] at hg
  obtain ⟨t,rfl⟩:=hg
  obtain ⟨h3,h4,h5⟩:=(mem_seed v).mp hv
  rw [mem_seed]
  simp [unipotentProduct,map_mul,Module.End.mul_apply,h3,h4,h5]

theorem pointParabolic_preserves_seed (g:Model F) (hg:g∈parabolic) (v:W) (hv:v∈seed) :
    Restricted.NaturalCoordinates.action F g v∈seed := by
  have hh:parabolic≤subspaceStabilizer (Restricted.NaturalCoordinates.action F) seed := by
    change borel⊔closure {weylR}≤_
    rw [borel_eq_unipotent_of_card_two (by simp [Nat.card_eq_fintype_card])]
    refine sup_le (le_subspaceStabilizer (Restricted.NaturalCoordinates.action F) seed
      (fun g hg v hv=>unipotent_preserves_seed g hg v hv)) ?_
    apply (closure_le _).mpr
    rintro a (rfl: a=weylR)
    intro w
    simp [action_weylR,and_left_comm]
  exact ((hh hg) v).mpr hv

theorem card_plane : Nat.card plane=4 := by
  let e:plane≃(Fin 2→F):={
    toFun:=fun v=>![v.val 0,v.val 1]
    invFun:=fun a=>⟨![a 0,a 1,0,0,0,0],by rw [mem_plane];simp⟩
    left_inv:=by
      intro v
      obtain ⟨h2,h3,h4,h5⟩:=(mem_plane v.val).mp v.prop
      apply Subtype.ext
      ext i;fin_cases i <;>simp [h2,h3,h4,h5]
    right_inv:=by intro a;ext i;fin_cases i <;>rfl }
  rw [Nat.card_congr e,Nat.card_fun,Nat.card_fin]
  simp [F,Nat.card_eq_fintype_card]
end Atlas.G2.Natural.BinaryPointFlag
