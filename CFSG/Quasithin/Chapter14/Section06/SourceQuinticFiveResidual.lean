module

public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticKernelStructure
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFiveCentralizer
public import Theory.GroupAction.CoprimeMovingQuotient
public import Theory.GroupAction.CoprimeFixedCardinality
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.SubgroupConjugation

/-!
# The five-residual inside the full order-1024 quintic core

The full centralizer kernel has order 64 and is abelian. An actual
five-subgroup fixes two elements in the derived subgroup of order 32.
The fixed subgroup of the whole core has order four, so coprime action
on the Frattini quotient gives an order-512 action commutator subgroup.
It contains the entire derived subgroup and meets the full kernel in
exactly that subgroup. The original core remains of order 1024.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

private theorem five_residual_card
    {K A : Type*} [Group K] [Finite K] [Group A] [Finite A]
    [MulDistribMulAction A K]
    (hK : IsPGroup 2 K) (hKcard : Nat.card K = 1024) (hA : Nat.card A = 5)
    (F : Subgroup K) [IsMulCommutative F] (hFcard : Nat.card F = 64)
    (hDcard : Nat.card (_root_.commutator K) = 32)
    (hDF : _root_.commutator K ≤ F)
    (hfixedF : FixedPoints.subgroup A K ≤ F)
    (hDfixed : Nat.card (_root_.commutator K ⊓ FixedPoints.subgroup A K : Subgroup K) = 2) :
    Nat.card (FixedPoints.subgroup A K) = 4 ∧
      Nat.card (commutatorAction A K) = 512 ∧
      _root_.commutator K ≤ commutatorAction A K ∧
      commutatorAction A K ⊔ F = ⊤ ∧
      commutatorAction A K ⊓ F = _root_.commutator K := by
  let D := _root_.commutator K
  let B := FixedPoints.subgroup A K
  let R := commutatorAction A K
  let : Group.IsNilpotent K := hK.isNilpotent
  let : R.Normal := commutatorAction_normal
  let : IsInvariant A K D := isInvariant_of_characteristic D
  let : MulDistribMulAction A (K ⧸ D) := quotientMulDistribMulAction D inferInstance
  let : IsMulCommutative (K ⧸ D) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
  have hcop : Nat.Coprime (Nat.card A) (Nat.card K) := by rw [hA, hKcard]; decide
  have hsplit : R ⊔ B = ⊤ := by
    rw [sup_comm]
    exact fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
      (inferInstance : Group.IsSolvable K) hcop
  have hBcomm : IsMulCommutative B := ⟨⟨fun x y => Subtype.ext
    (setLike_mul_comm (hfixedF x.property) (hfixedF y.property))⟩⟩
  have hDR : D ≤ R :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsplit hBcomm
  have hBcard : Nat.card B = 4 := by
    have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes D B
      (by rw [normalizer_eq_top]; exact le_top)
    have hbound : Nat.card (D ⊔ B : Subgroup K) ≤ 64 :=
      hFcard ▸ card_le_of_le (sup_le hDF hfixedF)
    change Nat.card D * Nat.card B = Nat.card (D ⊓ B : Subgroup K) *
      Nat.card (D ⊔ B : Subgroup K) at hp
    rw [hDcard, hDfixed] at hp
    have hle : Nat.card B ≤ 4 := by omega
    have hm := (IsPGroup.of_card (p := 5) (n := 1)
      (by simpa using hA)).card_modEq_card_fixedPoints K
    change Nat.card K % 5 = Nat.card B % 5 at hm
    rw [hKcard] at hm
    omega
  have hVcard : Nat.card (K ⧸ D) = 32 := by
    have hp := D.card_mul_index
    rw [index_eq_card, hDcard, hKcard] at hp
    omega
  have hVBcard : Nat.card (FixedPoints.subgroup A (K ⧸ D)) = 2 := by
    have hp := FixedPoints.card_eq_quotient_mul_kernel_of_coprime
      (inferInstance : Group.IsSolvable K) hcop D inferInstance
    rw [hBcard, hDfixed] at hp
    omega
  have hcompl := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (G := K ⧸ D) (A := A) (inferInstance : Group.IsSolvable (K ⧸ D))
    (by rw [hA, hVcard]; decide) (inferInstance : IsMulCommutative (K ⧸ D))
  have hmove : Nat.card (commutatorAction A (K ⧸ D)) = 16 := by
    have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes
      (FixedPoints.subgroup A (K ⧸ D)) (commutatorAction A (K ⧸ D))
      (by rw [normalizer_eq_top]; exact le_top)
    rw [hcompl.inf_eq_bot, hcompl.sup_eq_top, card_bot, card_top, hVcard, hVBcard] at hp
    omega
  have hRimage := Theory.GroupAction.commutatorAction_map_surjective
    (A := A) (QuotientGroup.mk' D) (QuotientGroup.mk'_surjective D) (fun _ _ => rfl)
  have hRcard : Nat.card R = 512 := by
    have hp := (D.subgroupOf R).card_mul_index
    rw [index_eq_card, Nat.card_congr (subgroupOfEquivOfLe hDR).toEquiv,
      hDcard, ← natCard_map_mk'_eq R D, hRimage, hmove] at hp
    omega
  have hRF : R ⊔ F = ⊤ := top_unique (hsplit ▸ sup_le_sup_left hfixedF R)
  have hinter : R ⊓ F = D := by
    apply (eq_of_le_of_card_ge (le_inf hDR hDF) ?_).symm
    have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes R F
      (by rw [normalizer_eq_top]; exact le_top)
    rw [hRcard, hFcard, hRF, card_top, hKcard] at hp
    rw [hDcard]
    omega
  exact ⟨hBcard, hRcard, hDR, hRF, hinter⟩

variable {G : Type*} [Group G] [Finite G]

/-- In the larger branch the actual five-residual has order 512 inside
the order-1024 core; it supplements the full kernel and intersects it in U. -/
theorem source_quintic_large_five_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5) :
    let U := conjugateSpanBy (localModule T M) H
    let Q := H.pCoreIn 2
    let C := H ⊓ centralizer (U : Set G)
    let B := Q ⊓ centralizer (A : Set G)
    let R := ⁅Q,A⁆
    Nat.card C = 64 ∧ Nat.card Q = 1024 ∧
      Nat.card B = 4 ∧ IsMulCommutative B ∧
      Nat.card R = 512 ∧ U ≤ R ∧ R ⊔ C = Q ∧ R ⊓ C = U := by
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  let B := Q ⊓ centralizer (A : Set G)
  let R := ⁅Q,A⁆
  obtain ⟨hCcomm, horders, _, hderived, _⟩ := source_quintic_full_kernel_structure
    hG T hempty hM hu hmany hcard e H hH hi
  let : IsMulCommutative C := hCcomm
  have hCcard : Nat.card C = 64 := by
    rcases horders with ⟨_, hq⟩ | ⟨hc, _⟩
    · omega
    · exact hc
  have hCQ : C ≤ Q := source_quintic_span_centralizer_le_core hG T hM H hH hi
  have hUQ : U ≤ Q := hderived.ge.trans (commutator_le_self Q)
  have hUC : U ≤ C := le_inf (hUQ.trans (pCoreIn_le 2 H)) (by
    let : IsElementaryAbelian 2 U :=
      (Section02.SolvableAmalgam.source_index_five_closure_structure
        hG T hempty hM hu hmany hcard e H hH.1 hi).1
    exact le_centralizer U)
  have hUcard : Nat.card U = 32 :=
    (source_quintic_span_card_and_core_radical hG T hempty hM hu hmany hcard e H hH hi).1
  obtain ⟨hUfixed, hQfixed⟩ := source_quintic_five_centralizers
    hG T hempty hM hu hmany hcard e H hH hi A hAH hA
  have hBC : B ≤ C := hQfixed.le.trans inf_le_left
  have hAQ : A ≤ normalizer (Q : Set G) := hAH.trans
    (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  let : Normalizes A Q := ⟨hAQ⟩
  let F := C.subgroupOf Q
  let D := _root_.commutator Q
  let BQ := FixedPoints.subgroup A Q
  let RQ := commutatorAction A Q
  have hDmap : D.map Q.subtype = U := by
    rw [map_subtype_commutator]
    exact hderived
  have hBQ : BQ = B.subgroupOf Q :=
    fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn Q A hAQ
  have hBmap : BQ.map Q.subtype = B := by
    rw [hBQ, map_subgroupOf_eq_of_le inf_le_left]
  have hRmap : RQ.map Q.subtype = R :=
    commutatorAction_subgroup_conj_map_eq_commutator Q A hAQ
  have hDF : D ≤ F := by
    intro d hd
    exact hUC (hDmap.le (mem_map_of_mem Q.subtype hd))
  have hBcomm : IsMulCommutative B := ⟨⟨fun x y => Subtype.ext
    (setLike_mul_comm (hBC x.property) (hBC y.property))⟩⟩
  let : IsMulCommutative F := ⟨⟨fun x y => Subtype.ext
    (Subtype.ext (setLike_mul_comm
      (show ((x : Q) : G) ∈ C from x.property)
      (show ((y : Q) : G) ∈ C from y.property)))⟩⟩
  have hDfixed : Nat.card (D ⊓ BQ : Subgroup Q) = 2 := by
    rw [← card_map_of_injective Q.subtype_injective,
      Subgroup.map_inf D BQ Q.subtype Q.subtype_injective, hDmap, hBmap]
    have hiUB : U ⊓ B = U ⊓ centralizer (A : Set G) := by
      dsimp [B]
      rw [← inf_assoc, inf_eq_left.mpr hUQ]
    rw [hiUB, hUfixed]
    exact plane_centralInvolutions_card T M hM.1.2 hcard e
  obtain ⟨hBfour, hR512, hDR, hRF, hcap⟩ := five_residual_card
    (isPGroup_pCoreIn 2 H) hlarge hA F
    ((Nat.card_congr (subgroupOfEquivOfLe hCQ).toEquiv).trans hCcard)
    (by rw [← card_map_of_injective Q.subtype_injective, hDmap]; exact hUcard)
    hDF (hBQ.le.trans (subgroupOf_mono Q hBC)) hDfixed
  have hBfour' : Nat.card B = 4 := by
    rw [← hBmap, card_map_of_injective Q.subtype_injective]
    exact hBfour
  have hR512' : Nat.card R = 512 := by
    rw [← hRmap, card_map_of_injective Q.subtype_injective]
    exact hR512
  refine ⟨hCcard, hlarge, hBfour', hBcomm, hR512', ?_, ?_, ?_⟩
  · have hm := map_mono (f := Q.subtype) hDR
    rw [hDmap, hRmap] at hm
    exact hm
  · have hm := congrArg (fun K : Subgroup Q => K.map Q.subtype) hRF
    rw [Subgroup.map_sup, hRmap, map_subgroupOf_eq_of_le hCQ,
      ← MonoidHom.range_eq_map, range_subtype] at hm
    exact hm
  · have hm := congrArg (fun K : Subgroup Q => K.map Q.subtype) hcap
    rw [Subgroup.map_inf RQ F Q.subtype Q.subtype_injective, hRmap,
      map_subgroupOf_eq_of_le hCQ, hDmap] at hm
    exact hm

end CFSG.Quasithin.Chapter14.Section06
