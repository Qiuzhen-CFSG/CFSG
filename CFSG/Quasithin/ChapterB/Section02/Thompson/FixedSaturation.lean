module
public import CFSG.Quasithin.ChapterB.Section02.Thompson.FixedAction

/-!
# Saturation of the near-maximum fixed-space bound

Equality in the relative fixed-rank bound makes C_V(C)C a maximum
elementary subgroup of the original S. If J(S) centralizes V, this
forces C to centralize V. Consequently a saturated restriction of a
near-maximum actor to C_V(K), with exact kernel K, has K trivial in
the faithful action quotient. All ranks and the replacement subgroup
are computed in the original cover.

Source: Aschbacher–Smith B.2.4, pp.75–76, used in the quintic branch
of 14.5.11, pp.1015–1016, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]

private theorem binary_card (E : Subgroup G) [IsElementaryAbelian 2 E] :
    Nat.card E = 2 ^ Nat.log 2 (Nat.card E) := by
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  rw [hn,Nat.log_pow (by decide : 1 < 2)]

/-- Equality makes the literal elementary replacement a maximum subgroup. -/
theorem near_maximum_relative_fixed_saturation
    (S V A C : Subgroup G) [IsElementaryAbelian 2 V]
    (hVS : V ≤ S) (hA : A ∈ thompsonFamily S 1) (hCA : C ≤ A)
    (heq : Nat.log 2 (Nat.card (V ⊓ centralizer (C : Set G) : Subgroup G)) -
      Nat.log 2 (Nat.card (V ⊓ centralizer (A : Set G) : Subgroup G)) =
      Nat.log 2 (Nat.card A) - Nat.log 2 (Nat.card C) + 1) :
    (V ⊓ centralizer (C : Set G)) ⊔ C ∈ elementaryAbelianMaxSubgroups S := by
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le hCA
  let U := V ⊓ centralizer (C : Set G)
  let Z := V ⊓ centralizer (A : Set G)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 (U ⊓ C : Subgroup G) := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 (U ⊔ C : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mpr (show U ≤ centralizer (C : Set G) from inf_le_right))
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes U C
    ((le_centralizer_iff.mp (show U ≤ centralizer (C : Set G) from inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _))
  rw [binary_card U,binary_card C,binary_card (U ⊓ C),binary_card (U ⊔ C),
    ←pow_add,←pow_add] at hc
  have hr := (Nat.pow_right_injective (by decide : 1 < 2)) hc
  have hmax := elementary_card_le_maxOrder S (U ⊔ C)
    (sup_le (inf_le_left.trans hVS) (hCA.trans hA.1)) inferInstance
  rw [binary_card (U ⊔ C),maxOrder_eq_two_pow_rank] at hmax
  have hmaxr := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hmax
  have hi : U ⊓ C ≤ Z :=
    le_inf (inf_le_left.trans inf_le_left)
      (inf_le_right.trans (hCA.trans (Subgroup.le_centralizer A)))
  have hir := Nat.log_mono_right (b := 2) (Nat.card_le_card_of_injective _ (inclusion_injective hi))
  have hcr := Nat.log_mono_right (b := 2) (Nat.card_le_card_of_injective _ (inclusion_injective hCA))
  have har := (mem_thompsonFamily_iff_rank S A 1).mp hA |>.2.2
  have he : Nat.log 2 (Nat.card (U ⊔ C : Subgroup G)) = twoRank S := by
    change Nat.log 2 (Nat.card U) - Nat.log 2 (Nat.card Z) = _ at heq
    omega
  refine ⟨sup_le (inf_le_left.trans hVS) (hCA.trans hA.1),inferInstance,?_⟩
  intro B hBS hB
  have hh := elementary_card_le_maxOrder S B hBS hB
  rwa [maxOrder_eq_two_pow_rank,←he,←binary_card (U ⊔ C)] at hh

end CFSG.Quasithin.ChapterB

namespace CFSG.Quasithin.ChapterB
open Representation Representation.BinaryOffender
variable {E D : Type*} [Group E] [Finite E] [Group D] [Finite D]

/-- Thompson centralization kills the exact kernel of a saturated fixed-space restriction. -/
theorem near_maximum_fixed_saturated_kernel
    (S V : Subgroup E) [V.Normal] [IsElementaryAbelian 2 V]
    (hVS : V ≤ S) (hJ : elementaryAbelianMaxJ S ≤ centralizer (V : Set E))
    (q : E →* D) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (V : Set E))
    {A : Subgroup E} (hA : A ∈ thompsonFamily S 1)
    (K : Subgroup D) (hKB : K ≤ A.map q)
    (hkernel : subspaceKernel (NormalElementaryQuotient.representation V q hq hk)
      (fixedSpace (NormalElementaryQuotient.representation V q hq hk) K) (A.map q) = K)
    (hsat : let ρ := NormalElementaryQuotient.representation V q hq hk
    let U := fixedSpace ρ K
    let I := restrictedSubgroup ρ U (A.map q)
    fixedCodim (subspaceImageRepresentation ρ U) I = rank I + 1) : K = ⊥ := by
  let ρ := NormalElementaryQuotient.representation V q hq hk
  let B := A.map q
  let U := fixedSpace ρ K
  let I := restrictedSubgroup ρ U B
  let C := A ⊓ K.comap q
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map q
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le inf_le_left
  have hBs : B ≤ subspaceStabilizer ρ U :=
    le_stabilizer_fixedSpace_of_commutator_eq_bot ρ B K
      (commutator_eq_bot_iff_le_centralizer.mpr
        ((Subgroup.le_centralizer B).trans (centralizer_le hKB)))
  have hCm : C.map q = K := by
    apply le_antisymm
    · rintro _ ⟨c,hc,rfl⟩; exact hc.2
    · intro k hk
      obtain ⟨a,ha,rfl⟩ := hKB hk
      exact ⟨a,⟨ha,hk⟩,rfl⟩
  have hfix (J : Subgroup E) :
      Module.finrank (ZMod 2) (fixedSpace ρ (J.map q)) =
        Nat.log 2 (Nat.card (V ⊓ centralizer (J : Set E) : Subgroup E)) := by
    have hc := Nat.card_congr (NormalElementaryQuotient.fixedSpaceEquiv V q hq hk J)
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
    rw [←hc,Nat.log_pow (by decide : 1 < 2)]
  have hdimU : Module.finrank (ZMod 2) U =
      Nat.log 2 (Nat.card (V ⊓ centralizer (C : Set E) : Subgroup E)) := by
    rw [←hfix C,hCm]
  have hdimB := hfix A
  have hcod := fixedCodim_restrictedSubgroup ρ U B hBs
  have hBU : fixedSpace ρ B ≤ U := fixedSpace_antitone ρ hKB
  rw [inf_eq_right.mpr hBU,hdimU,hdimB] at hcod
  have hrel : C.relIndex A = K.relIndex B := by
    change (A ⊓ K.comap q).relIndex A = K.relIndex (A.map q)
    rw [inf_relIndex_left,relIndex_comap]
  have hIcard := card_subspaceKernel_mul_image ρ U B hBs
  rw [hkernel] at hIcard
  have hKcard := relIndex_mul_relIndex (⊥ : Subgroup D) K B bot_le hKB
  simp only [relIndex_bot_left] at hKcard
  have hind : K.relIndex B = Nat.card I := by
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := K)) (hKcard.trans hIcard.symm)
  have hCcard := relIndex_mul_relIndex (⊥ : Subgroup E) C A bot_le inf_le_left
  simp only [relIndex_bot_left] at hCcard
  rw [hrel,hind] at hCcard
  have hIp : IsPGroup 2 I := by
    change IsPGroup 2 (restrictedSubgroup ρ U B)
    rw [←subgroupActionHom_range ρ U B hBs]
    exact (IsElementaryAbelian.isPGroup 2 B).of_surjective _
      (subgroupActionHom ρ U B hBs).rangeRestrict_surjective
  obtain ⟨n,hn⟩ := hIp.exists_card_eq
  have hIr : rank I = n := by rw [rank,hn,Nat.log_pow (by decide : 1 < 2)]
  rw [binary_card C,binary_card A,hn,←pow_add] at hCcard
  have hr := Nat.pow_right_injective (by decide : 1 < 2) hCcard
  have hs : (V ⊓ centralizer (C : Set E)) ⊔ C ∈ elementaryAbelianMaxSubgroups S := by
    apply near_maximum_relative_fixed_saturation S V A C hVS hA inf_le_left
    change fixedCodim (subspaceImageRepresentation ρ U) I = rank I + 1 at hsat
    rw [hcod,hIr] at hsat
    omega
  have hCker : C ≤ q.ker := by
    rw [hk]
    exact (le_sup_right.trans (le_sSup hs)).trans hJ
  rw [←hCm]
  exact (Subgroup.map_eq_bot_iff _).mpr hCker

end CFSG.Quasithin.ChapterB
