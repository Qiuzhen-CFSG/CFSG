module
public import CFSG.Quasithin.ChapterB.Section02.Thompson.NearMaximumAction
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.Representation.BinaryOffender.PrimeCentralizerFixed
public import Theory.GroupTheory.OddPrimeSectionCentralizers.ElementaryAction
public import Theory.Representation.BinaryOffender.FourDimensionalCubic
public import Theory.Representation.BinaryOffender.InvolutionRatio

/-!
# Near-maximum actors on a centralizer fixed space

For C ≤ A with A one rank below maximum in S, compare A with the
actual elementary subgroup C_V(C)C in S. Counting their orders bounds
the rank difference between C_V(C) and C_V(A) by m(A/C)+1.
This comparison transports through the original centralizer quotient
and an exact fixed-space kernel. Applied to C_B(R) for an odd normal
p-subgroup R, it gives a faithful R-action, an elementary image of order
at most four, fixed codimension at most three and cubic ratio at most two.
The prime-rank bound remains on the original covering group.

Source: Aschbacher–Smith B.2.4(1), A.1.18 and the representation step of
14.5.11, printed pp.75,1015–1016, refs/quasithin.pdf.
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

/-- The elementary replacement C_V(C)C gives the relative fixed-rank bound. -/
theorem near_maximum_relative_fixed_rank
    (S V A C : Subgroup G) [IsElementaryAbelian 2 V]
    (hVS : V ≤ S) (hA : A ∈ thompsonFamily S 1) (hCA : C ≤ A) :
    Nat.log 2 (Nat.card (V ⊓ centralizer (C : Set G) : Subgroup G)) -
      Nat.log 2 (Nat.card (V ⊓ centralizer (A : Set G) : Subgroup G)) ≤
      Nat.log 2 (Nat.card A) - Nat.log 2 (Nat.card C) + 1 := by
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
  change Nat.log 2 (Nat.card U) - Nat.log 2 (Nat.card Z) ≤ _
  omega
end CFSG.Quasithin.ChapterB

namespace CFSG.Quasithin.ChapterB
open Representation Representation.BinaryOffender
variable {E D : Type*} [Group E] [Finite E] [Group D] [Finite D]

/-- The exact fixed-space kernel cancels the rank lost in the original quotient. -/
theorem near_maximum_fixed_image_codimension
    (S V : Subgroup E) [V.Normal] [IsElementaryAbelian 2 V]
    (hVS : V ≤ S) (q : E →* D) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (V : Set E))
    {A : Subgroup E} (hA : A ∈ thompsonFamily S 1)
    (K : Subgroup D) (hKB : K ≤ A.map q)
    (hkernel : subspaceKernel (NormalElementaryQuotient.representation V q hq hk)
      (fixedSpace (NormalElementaryQuotient.representation V q hq hk) K) (A.map q) = K) :
    let ρ := NormalElementaryQuotient.representation V q hq hk
    let U := fixedSpace ρ K
    let I := restrictedSubgroup ρ U (A.map q)
    fixedCodim (subspaceImageRepresentation ρ U) I ≤ rank I + 1 := by
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
  have hb := near_maximum_relative_fixed_rank S V A C hVS hA inf_le_left
  dsimp only
  change fixedCodim (subspaceImageRepresentation ρ U) I ≤ rank I + 1
  rw [hcod,hIr]
  omega
end CFSG.Quasithin.ChapterB

namespace CFSG.Quasithin.ChapterB
open Representation Representation.BinaryOffender Theory.GroupTheory
variable {E D : Type*} [Group E] [Finite E] [Group D] [Finite D]

/-- The moved odd-prime action has a genuine small cubic actor after removing its kernel. -/
theorem near_maximum_prime_fixed_action
    (S V : Subgroup E) [V.Normal] [IsElementaryAbelian 2 V]
    (hVS : V ≤ S) (q : E →* D) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (V : Set E))
    {A : Subgroup E} (hA : A ∈ thompsonFamily S 1)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hrank : primeRank p E ≤ 2)
    (R : Subgroup D) [R.Normal] (hR : IsPGroup p R)
    (hm : ¬ A.map q ≤ centralizer (R : Set D)) :
    let ρ := NormalElementaryQuotient.representation V q hq hk
    let B := A.map q
    let K := B ⊓ centralizer (R : Set D)
    let U := fixedSpace ρ K
    let I := restrictedSubgroup ρ U B
    subspaceKernel ρ U R = ⊥ ∧ subspaceKernel ρ U B = K ∧
      IsElementaryTwo I ∧ Nat.card I ≤ 4 ∧
      fixedCodim (subspaceImageRepresentation ρ U) I ≤ rank I + 1 ∧
      fixedCodim (subspaceImageRepresentation ρ U) I ≤ 3 ∧
      IsCubic (subspaceImageRepresentation ρ U) I ∧
      cubicRatio (subspaceImageRepresentation ρ U) ≤ 2 := by
  let ρ := NormalElementaryQuotient.representation V q hq hk
  let B := A.map q
  let K := B ⊓ centralizer (R : Set D)
  let U := fixedSpace ρ K
  let I := restrictedSubgroup ρ U B
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map q
  have hf := NormalElementaryQuotient.representation_injective V q hq hk
  obtain ⟨hkR,hkB⟩ := prime_centralizer_fixed_kernel ρ hf hp R B hR
  have hcod := near_maximum_fixed_image_codimension S V hVS q hq hk hA K inf_le_left hkB
  have hc : Nat.card I ≤ 4 := by
    rw [prime_centralizer_fixed_image_card ρ hf hp R B hR]
    exact elementary_two_prime_action_card_le_four hp q hq hrank R hR B
  have hn := prime_centralizer_fixed_image_nontrivial ρ hf hp R B hR hm
  have hs : B ≤ subspaceStabilizer ρ U :=
    le_stabilizer_fixedSpace_of_commutator_eq_bot ρ B K
      (commutator_eq_bot_iff_le_centralizer.mpr
        ((Subgroup.le_centralizer B).trans (centralizer_le inf_le_left)))
  let : IsElementaryAbelian 2 (B.subgroupOf (subspaceStabilizer ρ U)) :=
    IsElementaryAbelian.subgroupOf hs
  have he : IsElementaryAbelian 2 I := IsElementaryAbelian.map _
  have hr : rank I ≤ 2 := by
    have hh := Nat.log_mono_right (b := 2) hc
    exact hh
  have hIe : IsElementaryTwo I := ⟨hn,he⟩
  let σ := subspaceImageRepresentation ρ U
  have hcub : IsCubic σ I := by
    have hpos := hIe.rank_pos
    have hcases : rank I = 1 ∨ rank I = 2 := by omega
    rcases hcases with hr1 | hr2
    · let : IsElementaryAbelian 2 I := he
      have hcard : Nat.card I = 2 := by rw [hIe.card_eq_two_pow_rank,hr1,pow_one]
      let : IsCyclic I := isCyclic_of_prime_card hcard
      obtain ⟨t,ht⟩ := I.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
      have ho : orderOf t = 2 := by rw [←Nat.card_zpowers,ht,hcard]
      rw [←ht]
      exact isCubic_of_isQuadratic (involution_actor_rank_and_fixedCodim σ t ho).2.2.1
    · apply isCubic_of_elementary_card_four σ I he
      rw [hIe.card_eq_two_pow_rank,hr2]
      rfl
  change fixedCodim σ I ≤ rank I + 1 at hcod
  refine ⟨hkR,hkB,hIe,hc,hcod,hcod.trans (by omega),hcub,?_⟩
  apply (cubicRatio_le_nat_iff σ 2).mpr
  refine ⟨I,hIe,hcub,?_⟩
  have hpos := hIe.rank_pos
  omega
end CFSG.Quasithin.ChapterB
