module

public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.LocalClassification.NativeOrders
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.Parabolics
public import Theory.SpecificGroups.SymmetricSix.Parabolics

/-!
# Native conjugacy of order-384 hexad subgroups in M₂₂

Every order-384 subgroup in a hexad stabilizer that contains an ambient Sylow
two-subgroup is an actual M₂₂-conjugate of the pair–hexad intersection or the
three-pair stabilizer.

Transport the hexad to the marked one and conjugate the Sylow subgroup inside
its stabilizer to the common Sylow subgroup of the two native candidates.
All three subgroups contain the kernel of the genuine six-point restriction
and are maximal in the hexad stabilizer. The A₆ quotient has exactly two
maximal overgroups of the Sylow image. The distinct native candidates therefore
exhaust the possibilities. Kernel containment lifts the quotient equalities;
composing the two ambient conjugators gives the asserted subgroup equalities.

Source: the local subgroup step of Aschbacher–Smith 13.8.21(2), printed p.956
(PDF p.973). This result takes the native order and hexad placement as inputs;
the source-theorem assembly discharges those inputs separately.
-/

public section

open Subgroup MulAction
open scoped Pointwise
namespace Sporadic.Mathieu.M22SolvableSylow.LocalClassification
open M22ValueBound.Concrete M22ValueBound.Concrete.PartitionStructure

private theorem coatom_image {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f)
    (X : Subgroup G) (hk : f.ker ≤ X) (hX : IsCoatom X) :
    IsCoatom (X.map f) := by
  refine ⟨?_, ?_⟩
  · intro he
    have he' := congrArg (Subgroup.comap f) he
    rw [comap_map_eq_self hk, comap_top] at he'
    exact hX.1 he'
  · intro Y hY
    have hl : X < Y.comap f := by
      rw [← comap_map_eq_self hk]
      exact (comap_lt_comap_of_surjective hf).mpr hY
    apply comap_injective hf
    rw [comap_top]
    exact hX.2 _ hl

private theorem two_coatoms {G : Type*} [Group G] [Finite G]
    (f : G →* alternatingGroup (Fin 6)) (hf : Function.Surjective f)
    (T : Sylow 2 G) (hk : f.ker ≤ (T : Subgroup G))
    (P Q X : Subgroup G) (hP : IsCoatom P) (hQ : IsCoatom Q) (hX : IsCoatom X)
    (hTP : (T : Subgroup G) ≤ P) (hTQ : (T : Subgroup G) ≤ Q)
    (hTX : (T : Subgroup G) ≤ X) (hne : P ≠ Q) : X = P ∨ X = Q := by
  obtain ⟨g, _, hg⟩ := Theory.SpecificGroups.SymmetricSix.a6_coatoms_over_sylow
    (T.mapSurjective hf)
  have hp := (hg (P.map f)).mp
    ⟨coatom_image f hf P (hk.trans hTP) hP, map_mono hTP⟩
  have hq := (hg (Q.map f)).mp
    ⟨coatom_image f hf Q (hk.trans hTQ) hQ, map_mono hTQ⟩
  have hx := (hg (X.map f)).mp
    ⟨coatom_image f hf X (hk.trans hTX) hX, map_mono hTX⟩
  have hpq : P.map f ≠ Q.map f := fun he => hne
    (map_injective_of_ker_le f (hk.trans hTP) (hk.trans hTQ) he)
  have hi : X.map f = P.map f ∨ X.map f = Q.map f := by
    rcases hp with hp | hp <;> rcases hq with hq | hq <;>
      rcases hx with hx | hx <;> simp_all
  exact hi.imp
    (map_injective_of_ker_le f (hk.trans hTX) (hk.trans hTP))
    (map_injective_of_ker_le f (hk.trans hTX) (hk.trans hTQ))

private theorem map_conj_subtype {G : Type*} [Group G]
    (H : Subgroup G) (h : H) (Y : Subgroup H) :
    (Y.map (MulAut.conj h).toMonoidHom).map H.subtype =
      (Y.map H.subtype).map (MulAut.conj h.val).toMonoidHom := by
  rw [map_map, map_map]
  rfl

private theorem standard_hexad_conjugacy (X : Subgroup M22)
    (hX : X ≤ stabilizer M22 m22Hexad123) (hc : Nat.card X = 384)
    (hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X) :
    ∃ g : M22, X = pairHexad.map (MulAut.conj g).toMonoidHom ∨
      X = second.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨U, hUX⟩ := hU
  obtain ⟨V, hV⟩ := exists_sylow_le_pairHexad_inf_second
  let H := stabilizer M22 m22Hexad123
  have hUH : (U : Subgroup M22) ≤ H := hUX.trans hX
  have hVP := hV.trans inf_le_left
  have hVQ := hV.trans inf_le_right
  have hVH : (V : Subgroup M22) ≤ H := hVP.trans inf_le_left
  let T := V.subtype hVH
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H T (U.subtype hUH)
  let e := (MulAut.conj h).mapSubgroup
  have he : e (T : Subgroup H) = ((U.subtype hUH) : Subgroup H) := by
    change ((h • T : Sylow 2 H) : Subgroup H) = _
    rw [hh]
  have hUX' : ((U.subtype hUH) : Subgroup H) ≤ X.subgroupOf H :=
    fun _ hx => hUX hx
  have hTY : (T : Subgroup H) ≤ e.symm (X.subgroupOf H) := by
    have hi := e.symm.monotone hUX'
    rwa [← he, e.symm_apply_apply] at hi
  have hk : (hexadRestriction m22Hexad123_mem).ker ≤ (T : Subgroup H) :=
    hexadRestriction_ker_le m22Hexad123_mem (V : Subgroup M22) hVH ⟨V, le_rfl⟩
  have hKX : m22HexadPointwiseKernel m22Hexad123 ≤ X :=
    (kernel_le_of_sylow m22Hexad123_mem U hUH).trans hUX
  have hcx := isCoatom_of_card_384 m22Hexad123_mem X hX hKX hc
  have hcy : IsCoatom (e.symm (X.subgroupOf H)) := (e.symm.isCoatom_iff _).mpr hcx
  have hne : pairHexad.subgroupOf H ≠ second.subgroupOf H := by
    intro heq
    have heq' := congrArg (Subgroup.map H.subtype) heq
    rw [map_subgroupOf_eq_of_le (show pairHexad ≤ H from inf_le_left),
      map_subgroupOf_eq_of_le second_le_hexad] at heq'
    apply second_not_conjugate_pairHexad 1
    rw [show (MulAut.conj (1 : M22)).toMonoidHom = MonoidHom.id M22 by
      ext x
      simp, map_id]
    exact heq'
  have hy := two_coatoms (hexadRestriction m22Hexad123_mem)
    (hexadRestriction_surjective m22Hexad123_mem) T hk
    (pairHexad.subgroupOf H) (second.subgroupOf H) (e.symm (X.subgroupOf H))
    pairHexad_isCoatom second_isCoatom hcy
    (fun _ hv => hVP hv) (fun _ hv => hVQ hv) hTY hne
  have lift (P : Subgroup M22) (hP : P ≤ H)
      (hy : e.symm (X.subgroupOf H) = P.subgroupOf H) :
      X = P.map (MulAut.conj h.val).toMonoidHom := by
    have heq : X.subgroupOf H = e (P.subgroupOf H) := by
      rw [← hy, e.apply_symm_apply]
    have hm := congrArg (Subgroup.map H.subtype) heq
    change (X.subgroupOf H).map H.subtype =
      ((P.subgroupOf H).map (MulAut.conj h).toMonoidHom).map H.subtype at hm
    rw [map_conj_subtype, map_subgroupOf_eq_of_le hX,
      map_subgroupOf_eq_of_le hP] at hm
    exact hm
  exact ⟨h.val, hy.imp (lift pairHexad inf_le_left) (lift second second_le_hexad)⟩

private theorem map_conj_map {G : Type*} [Group G]
    (P : Subgroup G) (g h : G) :
    (P.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      P.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

/-- Every order-384 ambient Sylow overgroup in a hexad stabilizer is an
actual M₂₂-conjugate of one of the two native parabolics. -/
theorem hexad_conjugacy {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (X : Subgroup M22) (hXB : X ≤ stabilizer M22 B) (hc : Nat.card X = 384)
    (hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X) :
    ∃ g : M22, X = pairHexad.map (MulAut.conj g).toMonoidHom ∨
      X = second.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := exists_smul_m22Hexad123_eq hB
  let e := (MulAut.conj g).mapSubgroup
  have hH : e (stabilizer M22 m22Hexad123) = stabilizer M22 B := by
    change (stabilizer M22 m22Hexad123).map (MulAut.conj g).toMonoidHom = _
    rw [← stabilizer_smul_eq_stabilizer_map_conj, hg]
  have hY : e.symm X ≤ stabilizer M22 m22Hexad123 := by
    have hi := e.symm.monotone hXB
    rwa [← hH, e.symm_apply_apply] at hi
  have hcard : Nat.card (e.symm X) = 384 := by
    change Nat.card (X.map (MulAut.conj g).symm.toMonoidHom) = _
    rwa [card_map_of_injective (MulAut.conj g).symm.injective]
  have hT : ∃ T : Sylow 2 M22, (T : Subgroup M22) ≤ e.symm X := by
    obtain ⟨U, hU⟩ := hU
    exact ⟨U.mapSurjective (MulAut.conj g).symm.surjective, map_mono hU⟩
  obtain ⟨h, hh⟩ := standard_hexad_conjugacy (e.symm X) hY hcard hT
  have lift (P : Subgroup M22)
      (he : e.symm X = P.map (MulAut.conj h).toMonoidHom) :
      X = P.map (MulAut.conj (g * h)).toMonoidHom := by
    have hm := congrArg e he
    rw [e.apply_symm_apply] at hm
    change X = (P.map (MulAut.conj h).toMonoidHom).map
      (MulAut.conj g).toMonoidHom at hm
    rwa [map_conj_map] at hm
  exact ⟨g * h, hh.imp (lift pairHexad) (lift second)⟩
end Sporadic.Mathieu.M22SolvableSylow.LocalClassification
