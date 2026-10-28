module

public import CFSG.Quasithin.Chapter12.Section08.Setup.SourceData
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Basic
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Geometry

/-!
# Subspace transitivity and the source transporter

An isomorphism of equal-dimensional binary subspaces extends to the whole
seed. Full L action realizes it in G, with the inverse actor giving the
source's right conjugation. Independently, transitivity in one dimension
moves Vi^(g⁻¹) back to Vi; composing with g gives the required element of
Gi. This is the subgroup incidence argument of Appendix A.1.7(1).
The latter implication accepts actual transitivity, so the rank-two C₃
producer can use it without asserting full L action.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Notation 12.8.2 and
Lemma 12.8.3, printed pp.849–850, and Appendix A.1.7(1), printed p.21
of `refs/quasithin.pdf`.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.SetupFlagGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {n : ℕ}

/-- Equal-cardinality subgroups of an elementary abelian seed are conjugate
under an actor inducing every automorphism. The conjugation is right conjugation. -/
theorem subspace_transitive [IsElementaryAbelian 2 V]
    (hfull : ∀ a : MulAut V, ∃ l ∈ L, ∀ v : V, l * (v : G) * l⁻¹ = (a v : G))
    (A B : Subgroup G) (hA : A ≤ V) (hB : B ≤ V) (hc : Nat.card A = Nat.card B) :
    ∃ l ∈ L, conjugate A l = B := by
  let W := (AddSubgroup.toZModSubmodule 2) (A.subgroupOf V).toAddSubgroup
  let U := (AddSubgroup.toZModSubmodule 2) (B.subgroupOf V).toAddSubgroup
  have hcard : Nat.card W = Nat.card U := by
    change Nat.card (A.subgroupOf V) = Nat.card (B.subgroupOf V)
    rw [Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv, hc]
  have hd : Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) U := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have hw := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    have hu := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U)
    rw [Nat.card_zmod] at hw hu
    exact hw.symm.trans (hcard.trans hu)
  obtain ⟨f, hf⟩ := BinaryLinear.FourParabolicAction.exists_linearEquiv_map_eq W U hd
  let a : MulAut V := MulEquiv.toAdditive.symm f.toAddEquiv
  have ha : (A.subgroupOf V).map a.toMonoidHom = B.subgroupOf V := by
    ext v
    change (∃ w : V, (w : G) ∈ A ∧ a w = v) ↔ (v : G) ∈ B
    have hm := congrArg (fun S : Submodule (ZMod 2) (Additive V) => Additive.ofMul v ∈ S) hf
    exact iff_of_eq hm
  obtain ⟨l, hl, he⟩ := hfull a
  refine ⟨l⁻¹, L.inv_mem hl, ?_⟩
  have hmap := congrArg (fun S : Subgroup V => S.map V.subtype) ha
  have hf' : V.subtype.comp a.toMonoidHom = (MulAut.conj l).toMonoidHom.comp V.subtype := by
    ext v
    exact (he v).symm
  rw [map_map, hf', ← map_map, map_subgroupOf_eq_of_le hA,
    map_subgroupOf_eq_of_le hB] at hmap
  simpa only [conjugate, inv_inv] using hmap

omit [Finite G] in
private theorem right_conjugate_mul (A : Subgroup G) (a b : G) :
    conjugate A (a * b) = conjugate (conjugate A a) b := by
  unfold conjugate
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

omit [Finite G] in
/-- The subgroup version of Appendix A.1.7 used in 12.8.3(3).
Only transitivity in the relevant dimension is required. -/
theorem transporter_of_subspace_transitive (F : InvariantFlag T V n)
    (hLV : L ≤ normalizer (V : Set G)) (i : ℕ)
    (htrans : ∀ A : Subgroup G, A ≤ V → Nat.card A = Nat.card (F.Vi i) →
      ∃ l ∈ L, conjugate A l = F.Vi i)
    (g : G) (hg : F.Vi i ≤ conjugate V g) :
    ∃ k ∈ F.Gi i, conjugate V g = conjugate V k := by
  let A := conjugate (F.Vi i) g⁻¹
  have hA : A ≤ V := by
    have hh : A ≤ conjugate (conjugate V g) g⁻¹ := map_mono hg
    have he : conjugate (conjugate V g) g⁻¹ = V := by
      simpa only [inv_inv] using conjugate_conjugate_inv V g⁻¹
    rwa [he] at hh
  have hc : Nat.card A = Nat.card (F.Vi i) :=
    Subgroup.card_map_of_injective (MulAut.conj (g⁻¹)⁻¹).injective
  obtain ⟨l, hl, he⟩ := htrans A hA hc
  have hk : l⁻¹ * g ∈ F.Gi i := by
    have hh : g⁻¹ * l ∈ normalizer (F.Vi i : Set G) :=
      (conjugate_eq_iff _ _).mp ((right_conjugate_mul _ _ _).trans he)
    simpa only [mul_inv_rev, inv_inv, InvariantFlag.Gi] using (normalizer (F.Vi i : Set G)).inv_mem hh
  refine ⟨l⁻¹ * g, hk, ?_⟩
  rw [right_conjugate_mul, (conjugate_eq_iff V l⁻¹).mpr (hLV (L.inv_mem hl))]

end CFSG.Quasithin.Chapter12.Section08.SetupFlagGeometry
