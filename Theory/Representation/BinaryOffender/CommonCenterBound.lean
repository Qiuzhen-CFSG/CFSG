module

public import Theory.Representation.BinaryOffender.CommonCenterRank
public import Theory.Representation.BinaryOffender.SubspaceCodimensionLoss

/-!
# Codimension bounds for a common displacement line

Scalar displacement embeds the effective elementary actor in a dual space.
Without assuming faithfulness, the displacement image has dimension at most
the actor rank, so the common fixed space has at most that codimension.
The same bound on an invariant subspace loses at most its codimension in
the original module. A zero displacement line is handled separately.

Source application: Aschbacher--Smith, F.9.16(2), printed pp.323--324,
combined manuscript of 1 March 2004. The chapter consumer supplies the
actual critical denominator, central line and quotient conjugation action.
-/

public section
open Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.BinaryOffender.CommonCenter
variable {A V:Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem fixedCodim_top_le (ρ:Representation (ZMod 2) A V) (Z:Submodule (ZMod 2) V)
    (e:Z≃ₗ[ZMod 2]ZMod 2)
    (hd:∀a v,ρ a v-v∈Z) (hz:∀a z,z∈Z→ρ a z=z) :
    fixedCodim ρ ⊤≤Nat.log 2 (Nat.card A) := by
  have hn:=Subspace.finrank_add_finrank_dualCoannihilator_eq
    (LinearMap.range (displacementMap ρ Z e hd hz))
  rw [←fixedSpace_eq_annihilator ρ Z e hd hz] at hn
  have hr:=LinearMap.finrank_range_le (displacementMap ρ Z e hd hz)
  have hc:=fixedCodim_add_finrank ρ ⊤
  have hdim:Module.finrank (ZMod 2) (Additive A)=Nat.log 2 (Nat.card A) := by
    have hh:=Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive A)
    rw [Nat.card_zmod] at hh
    change _=Nat.log 2 (Nat.card (Additive A))
    rw [hh,Nat.log_pow Nat.one_lt_two]
  omega

theorem fixedCodim_top_le_of_center_dim_le_one (ρ:Representation (ZMod 2) A V)
    (Z:Submodule (ZMod 2) V) (hZ:Module.finrank (ZMod 2) Z≤1)
    (hd:∀a v,ρ a v-v∈Z) (hz:∀a z,z∈Z→ρ a z=z) :
    fixedCodim ρ ⊤≤Nat.log 2 (Nat.card A) := by
  by_cases hn:Z=⊥
  · have hf:fixedSpace ρ ⊤=⊤ := by
      apply top_unique
      intro v _ a
      have hh:=hd a v
      rw [hn,Submodule.mem_bot] at hh
      exact sub_eq_zero.mp hh
    have hc:=fixedCodim_add_finrank ρ ⊤
    rw [hf,finrank_top] at hc
    omega
  · have hdim:Module.finrank (ZMod 2) Z=1 := by
      have hp:0<Module.finrank (ZMod 2) Z := by
        by_contra hnot
        exact hn (Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_not_pos hnot))
      omega
    let e:Z≃ₗ[ZMod 2]ZMod 2:=LinearEquiv.ofFinrankEq _ _ (by simpa using hdim)
    exact fixedCodim_top_le ρ Z e hd hz

theorem fixedCodim_top_le_rank_add_codim (ρ:Representation (ZMod 2) A V)
    (W:Subrepresentation ρ) (Z:Submodule (ZMod 2) V)
    (hZ:Module.finrank (ZMod 2) Z≤1)
    (hd:∀a v,v∈W.toSubmodule→ρ a v-v∈Z)
    (hz:∀a z,z∈Z→ρ a z=z) :
    fixedCodim ρ ⊤≤Nat.log 2 (Nat.card A)+Module.finrank (ZMod 2) (V ⧸ W.toSubmodule) := by
  let Z':Submodule (ZMod 2) W.toSubmodule:=Z.comap W.toSubmodule.subtype
  have hZ':Module.finrank (ZMod 2) Z'≤1 := by
    have he:Module.finrank (ZMod 2) Z'=Module.finrank (ZMod 2) (W.toSubmodule⊓Z : Submodule (ZMod 2) V) := by
      rw [←Submodule.finrank_map_subtype_eq,Submodule.map_comap_subtype]
    exact he.le.trans ((Submodule.finrank_mono inf_le_right).trans hZ)
  have hc:=fixedCodim_top_le_of_center_dim_le_one W.toRepresentation Z' hZ'
    (fun a v=>hd a v v.property)
    (fun a z hz'=>Subtype.ext (hz a z hz'))
  exact (fixedCodim_le_subrepresentation_add_codim ρ W ⊤).trans (Nat.add_le_add_right hc _)

end Representation.BinaryOffender.CommonCenter
