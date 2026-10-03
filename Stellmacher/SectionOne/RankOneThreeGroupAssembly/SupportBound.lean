module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Basic
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaGeneration
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Support
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.CyclicFixedIndices
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.SupportCentralizers

/-!
# The minimal-support bound

Full local fixed index two and the lost-factor witness prove the partner belongs to the source's maximal family. Global and local minimality plus exclusive-or counting then bound the distinguished support by two.

This module supports the rank-at-least-two case of Stellmacher (1.6).
The action is on an elementary abelian two-group; the local hypotheses and
minimal-offender conditions are explicit in the declarations that use them.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.18–19.
-/

open scoped Pointwise symmDiff

namespace Stellmacher.SectionOne.RankOneThreeGroupAssembly

universe u v

/-- The support-count conclusion of the generic p.18 argument, isolated from
the remaining module calculation proving that the selected order-two
subgroup is again in `oneAmax`. -/
public theorem omegaSupport_card_le_two_of_local_coordinate
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    [DecidableEq (Subgroup G)]
    (S A Aᵢ F : Subgroup G) (hS : IsElementaryAbelian 2 S)
    (hnorm : ∀ K : Subgroup G, oneOmega (G := G) (V := V) K →
      S ≤ Subgroup.normalizer K)
    (hcoreEq : oddCore G = oneOmegaGenerated (G := G) (V := V))
    (hdecomp : LemmaOneFourConclusion (G := G) (V := V)
      (oneOmegaGenerated (G := G) (V := V))
      (oneOmegaFinset (G := G) (V := V)))
    (hW : oddCore G = ⁅oddCore G, S⁆)
    (a : S) (hAeq : A = Subgroup.zpowers (a : G))
    (hAcard : Nat.card A = 2)
    (hAS : A ≤ Aᵢ) (hAᵢS : Aᵢ ≤ S)
    (hAᵢcard : Nat.card Aᵢ = 4)
    (hF : oneOmega (G := G) (V := V) F)
    (hFle : F ≤ ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆)
    (hcoordinate :
      ⁅⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆, Aᵢ⁆ = F)
    (hpoint : ∀ x : G, x ∈ Aᵢ → x ∉ A →
      ⁅F, Subgroup.zpowers x⁆ = F)
    (hBmax : ∀ x : S, (x : G) ∈ Aᵢ → (x : G) ∉ A →
      oneAmax (G := G) (V := V) S (Subgroup.zpowers (x : G)))
    (hminimal : ∀ x : S, x ≠ 1 →
      oneAmax (G := G) (V := V) S (Subgroup.zpowers (x : G)) →
      (omegaSupport (G := G) (V := V) S hnorm a).card ≤
        (omegaSupport (G := G) (V := V) S hnorm x).card) :
    (omegaSupport (G := G) (V := V) S hnorm a).card ≤ 2 := by
  obtain ⟨x, hxAᵢ, hxnotA, hpartner⟩ :=
    exists_outside_coordinate_with_minimal_partner_support
      S A Aᵢ hS hAS hAᵢS hAcard hAᵢcard a hAeq hnorm
  have hxne : x ≠ 1 := by
    intro hxone
    apply hxnotA
    rw [hxone]
    exact A.one_mem
  have hxmax := hBmax x hxAᵢ hxnotA
  have hglobal := hminimal x hxne hxmax
  have hFle' : F ≤ ⁅oddCore G ⊓
      Subgroup.centralizer (Subgroup.zpowers (a : G) : Set G), S⁆ := by
    rw [← hAeq]
    exact hFle
  have hFnot := oneOmega_not_mem_support_of_le_local_commutator
    S hS hnorm a F hF hFle'
  have hcoordinate' :
      ⁅⁅oddCore G ⊓
          Subgroup.centralizer (Subgroup.zpowers (a : G) : Set G), S⁆,
        Aᵢ⁆ = F := by
    rw [← hAeq]
    exact hcoordinate
  have hsdiff := support_sdiff_eq_singleton_of_local_coordinate
    S hnorm hcoreEq hdecomp hW a x Aᵢ F hxAᵢ hF hFnot
      (hpoint (x : G) hxAᵢ hxnotA) hcoordinate'
  apply card_le_two_of_minimal_symmDiff
    (omegaSupport (G := G) (V := V) S hnorm a)
    (omegaSupport (G := G) (V := V) S hnorm x)
  · rw [hsdiff]
    simp
  · exact hglobal
  · exact hpartner

/-- The unconditional support-count conclusion of the generic p.18
argument.  The local fixed-index statement and the factor lost from the old
support prove that the selected partner has no larger `m`-value.  Support
containment, coprime action on the odd core, and the original `oneAmax`
centralizer condition then prove the partner's remaining centralizer clause.
-/
public theorem omegaSupport_card_le_two_of_local_coordinate_full
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    [DecidableEq (Subgroup G)]
    (S A Aᵢ F : Subgroup G) (hS : IsElementaryAbelian 2 S)
    (hnorm : ∀ K : Subgroup G, oneOmega (G := G) (V := V) K →
      S ≤ Subgroup.normalizer K)
    (hcoreEq : oddCore G = oneOmegaGenerated (G := G) (V := V))
    (hdecomp : LemmaOneFourConclusion (G := G) (V := V)
      (oneOmegaGenerated (G := G) (V := V))
      (oneOmegaFinset (G := G) (V := V)))
    (hW : oddCore G = ⁅oddCore G, S⁆)
    (hWthree : IsPGroup 3 (oddCore G))
    (hmin : ∀ Y : Subgroup G, Y ≤ S → Y ≠ ⊥ →
      m (G := G) (V := V) S ≤ m (G := G) (V := V) Y)
    (a : S) (hAeq : A = Subgroup.zpowers (a : G))
    (hAmax : oneAmax (G := G) (V := V) S A)
    (hAcard : Nat.card A = 2)
    (hAS : A ≤ Aᵢ) (hAᵢS : Aᵢ ≤ S)
    (hAᵢcard : Nat.card Aᵢ = 4)
    (hF : oneOmega (G := G) (V := V) F)
    (hFle : F ≤ ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆)
    (hcoordinate :
      ⁅⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆, Aᵢ⁆ = F)
    (hpoint : ∀ x : G, x ∈ Aᵢ → x ∉ A →
      ⁅F, Subgroup.zpowers x⁆ = F ∧
      (Nat.card (FixedPoints.subgroup A V) : ℚ) /
        Nat.card (↥(FixedPoints.subgroup A V ⊓
          FixedPoints.subgroup (Subgroup.zpowers x) V)) = 2)
    (hminimal : ∀ x : S, x ≠ 1 →
      oneAmax (G := G) (V := V) S (Subgroup.zpowers (x : G)) →
      (omegaSupport (G := G) (V := V) S hnorm a).card ≤
        (omegaSupport (G := G) (V := V) S hnorm x).card) :
    (omegaSupport (G := G) (V := V) S hnorm a).card ≤ 2 := by
  classical
  let ZA := omegaSupport (G := G) (V := V) S hnorm a
  by_cases hdone : ZA.card ≤ 2
  · exact hdone
  have hgt : 2 < ZA.card := Nat.lt_of_not_ge hdone
  have hane : a ≠ 1 := by
    intro ha
    have hAbot : A = ⊥ := by rw [hAeq, ha]; simp
    rw [hAbot] at hAcard
    norm_num at hAcard
  obtain ⟨x, hxAᵢ, hxnotA, hpartner⟩ :=
    exists_outside_coordinate_with_minimal_partner_support
      S A Aᵢ hS hAS hAᵢS hAcard hAᵢcard a hAeq hnorm
  let X := omegaSupport (G := G) (V := V) S hnorm x
  let B : Subgroup G := Subgroup.zpowers (x : G)
  have hxne : x ≠ 1 := by
    intro hx
    apply hxnotA
    rw [hx]
    exact A.one_mem
  have hBcard : Nat.card B = 2 := by
    have hx2 : (x : G) ^ 2 = 1 := congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        hS.exponent_dvd_p x)
    dsimp only [B]
    rw [Nat.card_zpowers, orderOf_eq_prime hx2]
    exact fun hx1 => hxne (Subtype.ext hx1)
  have hFnot : F ∉ ZA := by
    have hFle' : F ≤ ⁅oddCore G ⊓
        Subgroup.centralizer (Subgroup.zpowers (a : G) : Set G), S⁆ := by
      rw [← hAeq]
      exact hFle
    exact oneOmega_not_mem_support_of_le_local_commutator
      S hS hnorm a F hF hFle'
  have hcoordinate' :
      ⁅⁅oddCore G ⊓
          Subgroup.centralizer (Subgroup.zpowers (a : G) : Set G), S⁆,
        Aᵢ⁆ = F := by
    rw [← hAeq]
    exact hcoordinate
  have hsdiff : X \ ZA = {F} := by
    exact support_sdiff_eq_singleton_of_local_coordinate
      S hnorm hcoreEq hdecomp hW a x Aᵢ F hxAᵢ hF hFnot
        (hpoint (x : G) hxAᵢ hxnotA).1 hcoordinate'
  obtain ⟨K, hKZA, hKnotX⟩ :=
    exists_mem_sdiff_of_card_pos_of_partner ZA X F hsdiff hpartner (by omega)
  have hK : oneOmega (G := G) (V := V) K :=
    (mem_oneOmegaFinset_iff (G := G) (V := V) K).mp
      (omegaSupport_subset_oneOmegaFinset S hnorm a hKZA)
  have hmBA : m (G := G) (V := V) B ≤ m (G := G) (V := V) A := by
    exact m_zpowers_le_of_support_witness S hnorm a x A hAeq hAcard
      hBcard K hK hKZA hKnotX (hpoint (x : G) hxAᵢ hxnotA).2
  have hmBS : m (G := G) (V := V) B ≤ m (G := G) (V := V) S :=
    hmBA.trans hAmax.2.1
  have hBS : B ≤ S := by
    rw [Subgroup.zpowers_le]
    exact x.property
  have hfixedB :
      S ⊓ fixingSubgroup G (FixedPoints.subgroup B V : Set V) = B :=
    fixed_centralizer_eq_of_card_two_of_m_le
      S B hBS hBcard hmin hmBS
  have hnorm_of_le (Y : Subgroup G) (hYS : Y ≤ S) :
      S ≤ Subgroup.normalizer (Y : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro s hs y hy
    have hsy : (s : G) * (y : G) = (y : G) * (s : G) := by
      exact congrArg Subtype.val
        (hS.toIsMulCommutative.is_comm.comm ⟨s, hs⟩ ⟨y, hYS hy⟩)
    rw [hsy]
    simpa [mul_assoc] using hy
  have hnormAeq : S ⊓ Subgroup.normalizer (A : Set G) = S :=
    le_antisymm inf_le_left (le_inf le_rfl (hnorm_of_le A hAmax.1))
  let C_A : Subgroup G :=
    ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
  have hAcentral : S ⊓ Subgroup.centralizer (C_A : Set G) = A := by
    have hdata := hAmax
    unfold oneAmax at hdata
    dsimp at hdata
    simpa only [hnormAeq, C_A] using hdata.2.2.1
  have hCAleFixed : C_A ≤
      oddCore G ⊓ Subgroup.centralizer (A : Set G) :=
    le_inf (local_commutator_le_oddCore S A)
      (local_commutator_le_centralizer S A hS hAmax.1)
  have mem_A_of_support_subset (z : S)
      (hzsub : omegaSupport (G := G) (V := V) S hnorm z ⊆ ZA) :
      (z : G) ∈ A := by
    have hzfixed :=
      zpowers_le_centralizer_oddCore_fixed_of_support_subset
        S hS hnorm hcoreEq hdecomp hWthree a z hane hzsub
    have hzcentFixed := Subgroup.zpowers_le.mp hzfixed
    have hzcentCA : (z : G) ∈ Subgroup.centralizer (C_A : Set G) :=
      Subgroup.centralizer_le
        (show (C_A : Set G) ⊆
          (oddCore G ⊓ Subgroup.centralizer
            (Subgroup.zpowers (a : G) : Set G) : Subgroup G) by
          rw [← hAeq]
          exact hCAleFixed)
        hzcentFixed
    exact hAcentral.le ⟨z.property, hzcentCA⟩
  let C_B : Subgroup G :=
    ⁅oddCore G ⊓ Subgroup.centralizer (B : Set G), S⁆
  have hcentralB : S ⊓ Subgroup.centralizer (C_B : Set G) = B := by
    apply le_antisymm
    · intro y hy
      let yS : S := ⟨y, hy.1⟩
      let Y := omegaSupport (G := G) (V := V) S hnorm yS
      have hYsub : Y ⊆ X := by
        intro L hLY
        by_contra hLX
        have hL : oneOmega (G := G) (V := V) L :=
          (mem_oneOmegaFinset_iff (G := G) (V := V) L).mp
            (omegaSupport_subset_oneOmegaFinset S hnorm yS hLY)
        have hLle : L ≤ C_B := by
          dsimp only [C_B, B]
          exact oneOmega_le_local_commutator_of_not_mem_support
            S hnorm hcoreEq hdecomp hW x L hL hLX
        have hycentL : y ∈ Subgroup.centralizer (L : Set G) :=
          Subgroup.centralizer_le
            (show (L : Set G) ⊆ (C_B : Set G) from hLle) hy.2
        exact (mem_omegaSupport_iff_not_mem_centralizer
          S hnorm yS L hL).mp hLY hycentL
      have hyAi : y ∈ Aᵢ := by
        by_cases hFy : F ∈ Y
        · let z : S := yS * x
          have hzsub : omegaSupport (G := G) (V := V) S hnorm z ⊆ ZA := by
            rw [show omegaSupport (G := G) (V := V) S hnorm z = Y ∆ X by
              simpa only [z, Y, X] using
                omegaSupport_mul_eq_symmDiff S hnorm yS x]
            intro L hL
            rw [Finset.mem_symmDiff] at hL
            rcases hL with ⟨hLY, hLX⟩ | ⟨hLX, hLY⟩
            · exact (hLX (hYsub hLY)).elim
            · by_contra hLZA
              have hLnew : L ∈ X \ ZA := Finset.mem_sdiff.mpr ⟨hLX, hLZA⟩
              rw [hsdiff, Finset.mem_singleton] at hLnew
              exact hLY (hLnew ▸ hFy)
          have hzA := mem_A_of_support_subset z hzsub
          have hzAi : (z : G) ∈ Aᵢ := hAS hzA
          have hxx : x * x = 1 := by
            simpa [pow_two] using
              (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
                hS.exponent_dvd_p x)
          have hxxG : (x : G) * (x : G) = 1 := congrArg Subtype.val hxx
          have hzximem := Aᵢ.mul_mem hzAi hxAᵢ
          simpa only [z, Subgroup.coe_mul, mul_assoc, hxxG, mul_one] using hzximem
        · have hYZA : Y ⊆ ZA := by
            intro L hLY
            have hLX := hYsub hLY
            by_contra hLZA
            have hLnew : L ∈ X \ ZA := Finset.mem_sdiff.mpr ⟨hLX, hLZA⟩
            rw [hsdiff, Finset.mem_singleton] at hLnew
            exact hFy (hLnew ▸ hLY)
          exact hAS (mem_A_of_support_subset yS hYZA)
      have hKnotY : K ∉ Y := fun hKY => hKnotX (hYsub hKY)
      have hKcommY : ⁅K, Subgroup.zpowers y⁆ = ⊥ := by
        simpa only [yS] using
          commutator_oneOmega_zpowers_eq_bot_of_not_mem_support
            S hnorm yS K hK hKnotY
      have hycentK : y ∈ Subgroup.centralizer (K : Set G) :=
        Subgroup.zpowers_le.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by
            simpa only [Subgroup.commutator_comm] using hKcommY))
      let C : Subgroup G := Aᵢ ⊓ Subgroup.centralizer (K : Set G)
      have hKcommB : ⁅K, B⁆ = ⊥ := by
        dsimp only [B]
        exact commutator_oneOmega_zpowers_eq_bot_of_not_mem_support
          S hnorm x K hK hKnotX
      have hBC : B ≤ C := le_inf
        ((Subgroup.zpowers_le).mpr hxAᵢ)
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by
          simpa only [Subgroup.commutator_comm] using hKcommB))
      have haA : (a : G) ∈ A := by
        rw [hAeq]
        exact Subgroup.mem_zpowers (a : G)
      have hanotK : (a : G) ∉ Subgroup.centralizer (K : Set G) :=
        (mem_omegaSupport_iff_not_mem_centralizer
          S hnorm a K hK).mp hKZA
      have hCneAi : C ≠ Aᵢ := by
        intro hCAi
        apply hanotK
        have haC : (a : G) ∈ C := by rw [hCAi]; exact hAS haA
        exact haC.2
      have hcardCle : Nat.card C ≤ 4 := by
        have := Subgroup.card_le_of_le (show C ≤ Aᵢ from inf_le_left)
        simpa only [hAᵢcard] using this
      have hcardCne : Nat.card C ≠ 4 := by
        intro hcardC
        apply hCneAi
        exact Subgroup.eq_of_le_of_card_ge inf_le_left (by
          rw [hAᵢcard, hcardC])
      have hcardClt : Nat.card C < 4 :=
        Nat.lt_of_le_of_ne hcardCle hcardCne
      have hdiv : 2 ∣ Nat.card C := by
        simpa only [hBcard] using Subgroup.card_dvd_of_le hBC
      have hcardC : Nat.card C = 2 := by
        have hCpos := Nat.card_pos (α := C)
        omega
      have hBCeq : B = C :=
        Subgroup.eq_of_le_of_card_ge hBC (by rw [hBcard, hcardC])
      rw [hBCeq]
      exact ⟨hyAi, hycentK⟩
    · refine le_inf hBS ?_
      apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      rw [Subgroup.commutator_comm]
      apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      dsimp only [C_B]
      exact local_commutator_le_centralizer S B hS hBS
  have hBmax : oneAmax (G := G) (V := V) S B := by
    unfold oneAmax
    dsimp
    have hnormBeq : S ⊓ Subgroup.normalizer (B : Set G) = S :=
      le_antisymm inf_le_left (le_inf le_rfl (hnorm_of_le B hBS))
    simpa only [hnormBeq, C_B] using
      (show B ≤ S ∧
          m (G := G) (V := V) B ≤ m (G := G) (V := V) S ∧
          S ⊓ Subgroup.centralizer (C_B : Set G) = B ∧
          S ⊓ fixingSubgroup G (FixedPoints.subgroup B V : Set V) = B from
        ⟨hBS, hmBS, hcentralB, hfixedB⟩)
  have hglobal := hminimal x hxne (by simpa only [B] using hBmax)
  apply card_le_two_of_minimal_symmDiff ZA X
  · rw [hsdiff]
    simp
  · exact hglobal
  · exact hpartner

end Stellmacher.SectionOne.RankOneThreeGroupAssembly
