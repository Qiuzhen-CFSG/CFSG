module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenSetup
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Calculus
public import Theory.GroupTheory.WreathTwoElementaryRank
public import Theory.GroupTheory.PrimeRankOrderBound

/-!
# Displacement at opposite chosen vertex stabilizers

For an elementary subgroup of H, its quotient by its intersection with O₂(H)
has rank at most two, using the actual S₃ wreath C₂ quotient. A subgroup of
that intersection acts on V through the literal M-image, whose two-rank is
at most one. Additivity of corank gives a displacement bound of three on the
whole H-span, after transporting by the actual conjugator.

This proves the numerical upper bound on printed p.1120 of Aschbacher--Smith.
The opposite-stabilizer containment must still come from the critical track;
the lower bound using both natural chief actions is a separate argument.
-/

public section

open Subgroup Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor ChapterE
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem corank_kernel_le_rank {D : Type*} [Group D] [Finite D]
    (H A : Subgroup G) [IsElementaryAbelian 2 A] (hAH : A ≤ H) (f : H →* D) :
    subgroupCorank A (A ⊓ f.ker.map H.subtype) ≤ primeRank 2 D := by
  let : IsElementaryAbelian 2 (A.subgroupOf H) := IsElementaryAbelian.subgroupOf hAH
  let : IsElementaryAbelian 2 ((A.subgroupOf H).map f) := IsElementaryAbelian.map f
  have he : (f.ker.map H.subtype).relIndex A = f.ker.relIndex (A.subgroupOf H) := by
    rw [← Subgroup.relIndex_map_map_of_injective f.ker (A.subgroupOf H) H.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hAH]
  rw [subgroupCorank, inf_relIndex_left, he, relIndex_ker]
  exact offender_rank_le_primeRank _

private theorem chosen_centralizer_corank_le_image_rank
    (M V A : Subgroup G) [IsElementaryAbelian 2 A]
    (hn : M ≤ normalizer (V : Set G)) (hAM : A ≤ M) :
    subgroupCorank A (A ⊓ centralizer (V : Set G)) ≤
      primeRank 2 (internalActionImage M V hn) := by
  let f := (actionHom M V hn).rangeRestrict
  have hk : f.ker.map M.subtype = M ⊓ centralizer (V : Set G) := by
    rw [MonoidHom.ker_rangeRestrict, actionHom_ker, subgroupOf_map_subtype, inf_comm]
  have he : A ⊓ f.ker.map M.subtype = A ⊓ centralizer (V : Set G) := by
    rw [hk, ← inf_assoc, inf_eq_left.mpr hAM]
  rw [← he]
  exact corank_kernel_le_rank M A hAM f

private theorem chosen_wreath_quotient_corank_le_two
    (H A : Subgroup G) [IsElementaryAbelian 2 A] (hAH : A ≤ H)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))) :
    subgroupCorank A (A ⊓ twoCoreIn H) ≤ 2 := by
  obtain ⟨e⟩ := he
  have hthree : primeRank 2 (Equiv.Perm (Fin 3)) ≤ 1 := by
    apply primeRank_le_of_prime_pow_not_dvd
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hw := WreathTwoElementaryRank.rank_bound hthree (by decide : 0 < 1)
  have hr : primeRank 2 (H ⧸ pCore 2 H) ≤ 2 := by
    rw [primeRank_equiv 2 e]
    exact hw
  have hh := corank_kernel_le_rank H A hAH (QuotientGroup.mk' (pCore 2 H))
  rw [QuotientGroup.ker_mk'] at hh
  exact hh.trans hr

private theorem corank_antitone (U A B : Subgroup G) (hAB : A ≤ B) :
    subgroupCorank U B ≤ subgroupCorank U A := by
  exact Nat.log_mono_right (relIndex_le_of_le_left hAB (Nat.ne_of_gt (Nat.card_pos (α := U ⧸ A.subgroupOf U))))

private theorem centralizer_displacement_add (U D W : Subgroup G)
    [IsElementaryAbelian 2 U] (hDU : D ≤ U) :
    subgroupCorank U (U ⊓ centralizer (W : Set G)) ≤
      subgroupCorank U D + subgroupCorank D (D ⊓ centralizer (W : Set G)) := by
  calc
    _ ≤ subgroupCorank U (D ⊓ centralizer (W : Set G)) :=
      corank_antitone U _ _ (inf_le_inf_right _ hDU)
    _ = _ := offender_corank_add inf_le_left hDU

omit [Finite G] in
private theorem corank_conjugate (A B : Subgroup G) (g : G) :
    subgroupCorank (A.map (MulAut.conj g).toMonoidHom)
      (B.map (MulAut.conj g).toMonoidHom) = subgroupCorank A B := by
  unfold subgroupCorank
  rw [relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]

/-- The bound on m(U_H/C_U_H(V^g)) from the actual opposite containment.
The only numerical input is the rank of the literal M-image. -/
theorem chosen_span_displacement_le_three
    (T : Sylow 2 G) {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hr : primeRank 2 (internalActionImage M V h.prepared.normalized) ≤ 1)
    (g : G)
    (hU : conjugateSpan H V ≤ H.map (MulAut.conj g).toMonoidHom) :
    subgroupCorank (conjugateSpan H V)
      (conjugateSpan H V ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G)) ≤ 3 := by
  let U := conjugateSpan H V
  let f := (MulAut.conj g).toMonoidHom
  let fi := (MulAut.conj g⁻¹).toMonoidHom
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hg.outside).1
  let : IsElementaryAbelian 2 (U.map fi) := IsElementaryAbelian.map fi
  have hback : (U.map fi).map f = U := by
    simpa only [inv_inv] using offender_map_conj_inverse U g⁻¹
  have hUH : U.map fi ≤ H := by
    have hh := map_mono (f := fi) hU
    rw [offender_map_conj_inverse H g] at hh
    exact hh
  have hQ : subgroupCorank (U.map fi) (U.map fi ⊓ twoCoreIn H) ≤ 2 :=
    chosen_wreath_quotient_corank_le_two H _ hUH hg.quotient
  have hQT : twoCoreIn H ≤ (T : Subgroup G) := by
    have hp : pCore 2 H ≤ (T : Subgroup G).subgroupOf H :=
      pCore_isPGroup.le_sylow_of_normal (T.subtype hg.outside.1.1.2)
    have hm := map_mono (f := H.subtype) hp
    rw [map_subgroupOf_eq_of_le hg.outside.1.1.2] at hm
    exact hm
  let D := U.map fi ⊓ twoCoreIn H
  let : IsElementaryAbelian 2 D := offender_elementary_of_le (show D ≤ U.map fi from inf_le_left)
  have hDC : subgroupCorank D (D ⊓ centralizer (V : Set G)) ≤ 1 :=
    (chosen_centralizer_corank_le_image_rank M V D h.prepared.normalized
      (inf_le_right.trans (hQT.trans h.maximal.1.2))).trans hr
  have hb := (centralizer_displacement_add (U.map fi) D V inf_le_left).trans
    (Nat.add_le_add hQ hDC)
  have he := corank_conjugate (U.map fi) (U.map fi ⊓ centralizer (V : Set G)) g
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hback,
    offender_centralizer_map] at he
  exact he.symm ▸ hb

end CFSG.Quasithin.Chapter15.Section02
