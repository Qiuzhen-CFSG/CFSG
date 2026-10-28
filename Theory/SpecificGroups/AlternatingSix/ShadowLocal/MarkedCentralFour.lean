module
public import Theory.SpecificGroups.SymmetricSix.CentralFourPair
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.NormalElementaryPlacement
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.SylowGeometry
/-!
# The actual central four in a Sylow subgroup of Aut(A6)

The marked holomorph equivalence sends its central four to the explicit
permutation pair, with the same conjugating permutation. This subgroup
lies in natural S6 and centralizes the actual natural Sylow intersection.
Source: the binary symplectic paragraph of E.2.7, printed p.219.
-/

public section
open Subgroup
namespace AlternatingSix.ShadowLocal.Holomorph

theorem central_four_centralizes_natural :
    centralTwo ⊔ transpositionSubgroup ≤ centralizer (natural : Set Model) := by
  intro x hx y hy
  obtain ⟨i,rfl⟩ := (mem_centralTwo_sup_transposition x).mp hx
  obtain ⟨j,rfl⟩ := (mem_natural y).mp hy
  clear hx hy
  revert i j
  decide +kernel
end AlternatingSix.ShadowLocal.Holomorph

namespace AlternatingSix.ShadowLocal.BinaryWitness
open AlternatingSix.ShadowLocal
open AlternatingSix.ShadowLocal.Identification
open Theory.SpecificGroups.SymmetricSix.CentralFourPair hiding transposition
local notation "t0" => Theory.SpecificGroups.SymmetricSix.CentralFourPair.transposition

noncomputable def markedFour (P : Sylow 2 AutA6) : Subgroup AutA6 :=
  ((Holomorph.centralTwo ⊔ Holomorph.transpositionSubgroup).map
    (sylowEquiv P).toMonoidHom).map (P : Subgroup AutA6).subtype

theorem markedFour_def (P : Sylow 2 AutA6) :
    markedFour P = ((Holomorph.centralTwo ⊔ Holomorph.transpositionSubgroup).map
      (sylowEquiv P).toMonoidHom).map (P : Subgroup AutA6).subtype := by rfl

theorem markedFour_eq_permutation_pair (P : Sylow 2 AutA6) :
    markedFour P = four.map (permutationAction.comp
      (MulAut.conj (conjugatingPermutation P)).toMonoidHom) := by
  have hd : dihedralRotation.val ^ 2 = doubleTransposition := by
    rw [doubleTransposition_eq]
    decide +kernel
  rw [markedFour,Subgroup.map_sup,Subgroup.map_sup,
    Holomorph.centralTwo,Holomorph.transpositionSubgroup,
    MonoidHom.map_zpowers,MonoidHom.map_zpowers,
    MonoidHom.map_zpowers,MonoidHom.map_zpowers,
    four_eq_zpowers,Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
  change zpowers (sylowEquiv P (Holomorph.rotation^4) : AutA6) ⊔
    zpowers (sylowEquiv P Holomorph.transposition : AutA6) = _
  rw [sylowEquiv_rotation_four,sylowEquiv_transposition,hd]
  have ht : (MulAut.conj (conjugatingPermutation P)) t0 =
      Equiv.swap (conjugatingPermutation P 4) (conjugatingPermutation P 5) := by
    rw [transposition_eq]
    exact (Equiv.swap_apply_apply _ _ _).symm
  change _ = zpowers (permutationAction ((MulAut.conj (conjugatingPermutation P)) t0)) ⊔ _
  rw [ht,sup_comm]
  rfl

theorem markedFour_le_natural (P : Sylow 2 AutA6) : markedFour P ≤ natural := by
  rw [markedFour_eq_permutation_pair,←map_map]
  exact map_le_range _ _

theorem markedFour_le_sylow (P : Sylow 2 AutA6) : markedFour P ≤ (P : Subgroup AutA6) :=
  map_subtype_le _

theorem markedFour_centralizes_natural_intersection (P : Sylow 2 AutA6) :
    markedFour P ≤ centralizer ((P : Subgroup AutA6) ⊓ natural : Subgroup AutA6) := by
  intro x hx y hy
  obtain ⟨x,hx,rfl⟩ := hx
  obtain ⟨v,hv,rfl⟩ := hx
  let w : P := ⟨y,hy.1⟩
  have hw : (sylowEquiv P).symm w ∈ Holomorph.natural := by
    apply (mem_map_equiv).mp
    rw [sylowEquiv_natural]
    exact hy.2
  have hc := Holomorph.central_four_centralizes_natural hv _ hw
  have hh := congrArg (fun a:Holomorph.Model => ((sylowEquiv P a:P):AutA6)) hc
  simp only [map_mul,MulEquiv.apply_symm_apply] at hh
  exact hh
end AlternatingSix.ShadowLocal.BinaryWitness
