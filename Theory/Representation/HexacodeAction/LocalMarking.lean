module

public import Theory.Representation.HexacodeAction.Field
public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeZeroFibers
public import Mathlib.GroupTheory.Sylow

/-!
# The weight total on a Sylow-stable scalar hyperplane

A scalar-stable binary four-space is an `F₄` hyperplane. A nonzero
coordinate on it is onto the alphabet and has fibers of size four.
A Sylow two-subgroup cannot stabilize a coordinate-zero hyperplane:
its permutation image would fix one of six coordinates, contrary to the
odd index of a Sylow subgroup. All six coordinates are therefore onto,
and the sum of the weights of the sixteen vectors is `6 · 12 = 72`.

This is the concrete local calculation used with the two definite planes
on printed p.1155 of Aschbacher–Smith. The field interpretation is K.1.3,
printed p.453. Coordinate fibers and monomial formulas are reused from the
licensed ATLAS ports; no preferred plane or stabilizer quotient is chosen.
-/

@[expose] public section

open Atlas.Codes Subgroup
open scoped BigOperators
namespace Representation.Hexacode

theorem zeroCoordinate_finrank (i : HexIndex) : Module.finrank Bit (hexZeroCoordinate i) = 4 := by
  have h := Module.natCard_eq_pow_finrank (K := Bit) (V := hexZeroCoordinate i)
  rw [hexZeroCoordinate_card] at h
  norm_num [Bit] at h
  exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) h).symm

theorem scalar_coordinate_surjective (P : Submodule Bit hexacode)
    (hs : hexZ ∈ BinaryOffender.subspaceStabilizer action P) (i : HexIndex)
    (hn : ¬ P ≤ hexZeroCoordinate i) :
    Function.Surjective ((hexCoordinate i).comp P.subtype) := by
  classical
  obtain ⟨w, hw, hi⟩ : ∃ w ∈ P, w.val i ≠ 0 := by
    by_contra! h
    exact hn h
  intro u
  have hf : ∀ (i : HexIndex) (v u : K), v ≠ 0 →
      ∃ r : K, r.1 • v + r.2 •
        ((if i.2 = 0 then localKappa else localKappa⁻¹) v) = u := by decide
  obtain ⟨r, hr⟩ := hf i (w.val i) u hi
  refine ⟨⟨r.1 • w + r.2 • action hexZ w,
    P.add_mem (P.smul_mem _ hw) (P.smul_mem _ ((hs w).mpr hw))⟩, ?_⟩
  exact hr

theorem scalar_coordinate_fiber (P : Submodule Bit hexacode)
    (hd : Module.finrank Bit P = 4)
    (hs : hexZ ∈ BinaryOffender.subspaceStabilizer action P) (i : HexIndex)
    (hn : ¬ P ≤ hexZeroCoordinate i) (u : K) :
    let _ := Fintype.ofFinite P
    (Finset.univ.filter (fun w : P => w.val.val i = u)).card = 4 := by
  classical
  let _ := Fintype.ofFinite P
  let f := (hexCoordinate i).comp P.subtype
  have hf := scalar_coordinate_surjective P hs i hn
  have he (v : K) : (Finset.univ.filter (fun w : P => f w = v)).card =
      (Finset.univ.filter (fun w : P => f w = u)).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range f (hf v) (hf u)
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset P) (Finset.univ : Finset K) f
  simp only [he, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Finset.mem_univ, Finset.filter_true] at h
  have hc : Fintype.card P = 16 := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := Bit), hd]
    norm_num [Bit]
  norm_num [K, Letter, ZMod.card, hc] at h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) h

theorem scalar_four_weight_total (P : Submodule Bit hexacode)
    (hd : Module.finrank Bit P = 4)
    (hs : hexZ ∈ BinaryOffender.subspaceStabilizer action P)
    (hn : ∀ i : HexIndex, ¬ P ≤ hexZeroCoordinate i) :
    let _ := Fintype.ofFinite P
    ∑ w : P, hammingNorm w.val.val = 72 := by
  classical
  let _ := Fintype.ofFinite P
  simp only [hammingNorm, Finset.card_filter]
  rw [Finset.sum_comm]
  have hc : Fintype.card P = 16 := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := Bit), hd]
    norm_num [Bit]
  have hf (i : HexIndex) : (∑ w : P, if w.val.val i ≠ 0 then 1 else 0) = 12 := by
    rw [← Finset.card_filter]
    have h0 := scalar_coordinate_fiber P hd hs i (hn i) 0
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun w : P => w.val.val i = 0)
    rw [Finset.card_univ, hc, h0] at h
    change 4 + (Finset.univ.filter (fun w : P => w.val.val i ≠ 0)).card = 16 at h
    omega
  simp only [ite_not] at hf
  simp [hf, HexIndex]

theorem stabilizer_zeroCoordinate_le_point (i : HexIndex) :
    BinaryOffender.subspaceStabilizer action (hexZeroCoordinate i) ≤
      (MulAction.stabilizer (Equiv.Perm HexIndex) i).comap hexCoordinateHom := by
  intro g hg
  change hexCoordinateHom g i = i
  have he : g.val.perm.symm i = i := by
    by_contra hn
    obtain ⟨w, hw⟩ := hexZeroCoordinate_other_surjective i (g.val.perm.symm i) (Ne.symm hn) a
    have hzero := (hg w.val).mpr w.property
    change g.val.localMap i (w.val.val (g.val.perm.symm i)) = 0 at hzero
    rw [hw] at hzero
    have ha : a = 0 := (g.val.localMap i).map_eq_zero_iff.mp hzero
    exact (by decide : a ≠ 0) ha
  change g.val.perm i = i
  simpa using (congrArg g.val.perm he).symm

theorem sylow_four_not_zeroCoordinate (P : Submodule Bit hexacode)
    (hd : Module.finrank Bit P = 4) (S : Sylow 2 HexAutomorphisms)
    (hS : (S : Subgroup HexAutomorphisms) ≤ BinaryOffender.subspaceStabilizer action P)
    (i : HexIndex) : ¬ P ≤ hexZeroCoordinate i := by
  intro h
  have he : P = hexZeroCoordinate i :=
    Submodule.eq_of_le_of_finrank_eq h (hd.trans (zeroCoordinate_finrank i).symm)
  rw [he] at hS
  have hle := hS.trans (stabilizer_zeroCoordinate_le_point i)
  let S' := S.mapSurjective hexCoordinateHom_surjective
  have hS' : (S' : Subgroup (Equiv.Perm HexIndex)) ≤
      MulAction.stabilizer (Equiv.Perm HexIndex) i := by
    rintro _ ⟨g, hg, rfl⟩
    exact hle hg
  apply S'.not_dvd_index
  have hdvd := Subgroup.index_dvd_of_le hS'
  rw [MulAction.index_stabilizer_of_transitive] at hdvd
  exact dvd_trans (by norm_num [HexIndex, Nat.card_eq_fintype_card] :
    2 ∣ Nat.card HexIndex) hdvd

theorem sylow_scalar_four_weight_total (P : Submodule Bit hexacode)
    (hd : Module.finrank Bit P = 4)
    (hs : hexZ ∈ BinaryOffender.subspaceStabilizer action P)
    (S : Sylow 2 HexAutomorphisms)
    (hS : (S : Subgroup HexAutomorphisms) ≤ BinaryOffender.subspaceStabilizer action P) :
    let _ := Fintype.ofFinite P
    ∑ w : P, hammingNorm w.val.val = 72 :=
  scalar_four_weight_total P hd hs (sylow_four_not_zeroCoordinate P hd S hS)
end Representation.Hexacode
