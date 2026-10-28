module

public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PPerfectHom
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Centralization modulo a whole normal kernel

Suppose D and a p-subgroup generate G. If D centralizes a normal subgroup
B modulo N, every p-perfect subgroup does too. The inverse image of the
centralizer of B's image is normal and contains D, so its quotient is a
p-group. No part of N is discarded.

Source application: the whole original quintic residual in Aschbacher--Smith
6.1.4, printed pp.665--666, after its order-five supplement centralizes the
original module modulo O₂(KT). The argument needs no order-five assumption.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

/-- Centralization by a supplement passes to every p-perfect subgroup,
with the full original normal kernel retained. -/
theorem pPerfect_commutator_le_of_supplement_centralizes
    (X B D T N : Subgroup G) [B.Normal] [N.Normal]
    (hX : IsPPerfect p X) (hT : IsPGroup p T)
    (hgen : D ⊔ T = ⊤) (hDB : ⁅D,B⁆ ≤ N) : ⁅X,B⁆ ≤ N := by
  let q := QuotientGroup.mk' N
  let : (B.map q).Normal := (inferInstance : B.Normal).map q
    (QuotientGroup.mk'_surjective N)
  let C := (centralizer (B.map q : Set (G ⧸ N))).comap q
  have hDC : D ≤ C := by
    apply map_le_iff_le_comap.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
    exact hDB
  have hCT : C ⊔ T = ⊤ := top_unique (hgen.symm.le.trans
    (sup_le_sup_right hDC T))
  have hp := isPGroup_quotient_of_sup_eq_top C T hT hCT
  have hf := hX.hom_eq_one_of_isPGroup hp
    ((QuotientGroup.mk' C).comp X.subtype)
  have hXC : X ≤ C := by
    intro x hx
    apply (QuotientGroup.eq_one_iff (N := C) x).mp
    exact DFunLike.congr_fun hf ⟨x,hx⟩
  have he : ⁅X.map q,B.map q⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (map_le_iff_le_comap.mpr hXC)
  rwa [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at he

end Theory.GroupTheory
