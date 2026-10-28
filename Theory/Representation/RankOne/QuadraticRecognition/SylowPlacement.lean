module
public import Theory.Representation.RankOne.QuadraticRecognition.SourceTheorem
public import Theory.GroupTheory.PGroup.RankOneInvolution

/-!
# Quadratic actors in the original Sylow omega-center

Every involution of a binary Chapter 5 Sylow is central in that Sylow.
The proof uses the additive SL₂ root, the Suzuki root center, and the
Hermitian unitary root coordinates. Sz(2) has cyclic Sylows; the two small
unitary groups have two-rank one, so a central involution is the unique
involution in each Sylow. All transports preserve the prescribed Sylow
and its embedded center. Faithful quadratic actors are elementary, giving
the exact inclusion in Ω₁(Z(S)).

Source: DGS85, *Groups and Graphs*, (5.8)(b), (5.9)(b), pp.109–110.
The prime-two catalogue contains no odd-characteristic PSL₂ or Ree row,
so the exclusions in (5.9)(a) do not add branches here. The literal
critical-quotient application is in ModuleApplications.CriticalSupporting.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender BenderSuzuki.MatrixGroups
open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
open scoped MatrixGroups
namespace Representation.RankOne.QuadraticRecognition
private instance {F : Type*} [Field F] [Finite F] : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

variable {G : Type*} [Group G] [Finite G]

private theorem omega_le_center_of_rank_one (h : primeRank 2 G ≤ 1) (S : Sylow 2 G) :
    omegaOneAmbient (S : Subgroup G) ≤ (center S).map (S : Subgroup G).subtype := by
  apply (omegaOneAmbient_le_iff _ _).mpr
  intro x hx hx2
  by_cases hx1 : x = 1
  · simpa only [hx1] using (one_mem ((center S).map (S : Subgroup G).subtype))
  let : Nontrivial S := ⟨⟨⟨x,hx⟩,1,fun he => hx1 (congrArg Subtype.val he)⟩⟩
  have hfour (E : Subgroup S) (hE : IsElementaryAbelian 2 E) : Nat.card E ≠ 4 := by
    let := hE
    have hc := (primeRank_le_iff_elementary_card_le G).mp h
      (E.map (S : Subgroup G).subtype) (IsElementaryAbelian.map _)
    rw [card_map_of_injective (S : Subgroup G).subtype_injective] at hc
    norm_num at hc
    omega
  obtain ⟨z,_,hz,hu⟩ := S.isPGroup'.exists_central_involution_of_no_elementary_four hfour
  have he : (⟨x,hx⟩ : S) = z :=
    (hu ⟨x,hx⟩ (Subtype.ext hx2)).resolve_left (fun he => hx1 (congrArg Subtype.val he))
  exact ⟨⟨x,hx⟩,he ▸ hz,rfl⟩

omit [Finite G] in
private theorem omega_le_center_transport {H : Type*} [Group H]
    (e : G ≃* H) (S : Sylow 2 G)
    (h : omegaOneAmbient ((S : Subgroup G).map e.toMonoidHom) ≤
      (center ((S : Subgroup G).map e.toMonoidHom)).map
        ((S : Subgroup G).map e.toMonoidHom).subtype) :
    omegaOneAmbient (S : Subgroup G) ≤ (center S).map (S : Subgroup G).subtype := by
  rw [←map_omegaOneAmbient_injective e.toMonoidHom e.injective,
    ←map_embeddedCenter (S : Subgroup G) e.toMonoidHom e.injective] at h
  have hh := Subgroup.map_le_map_iff.mp h
  rwa [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective,sup_bot_eq] at hh

omit [Finite G] in
private theorem omega_le_center_of_comm (S : Sylow 2 G) [IsMulCommutative S] :
    omegaOneAmbient (S : Subgroup G) ≤ (center S).map (S : Subgroup G).subtype := by
  intro x hx
  exact ⟨⟨x,omegaOneAmbient_le _ hx⟩,by rw [center_eq_top]; trivial,rfl⟩

private theorem smallSuzuki_sylow_cyclic (S : Sylow 2 (SuzukiMatrixGroup 0)) : IsCyclic S := by
  let P : Sylow 2 (SuzukiMatrixGroup 0) := Sylow.ofCard (zpowers suzukiZeroRootGenerator) (by
    rw [Nat.card_zpowers,suzukiZeroRootGenerator_order,suzukiZero_card]
    rw [show (20 : ℕ) = 2^2 * 5 from rfl,
      Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
    norm_num [Nat.Prime.factorization Nat.prime_two,
      Nat.Prime.factorization (by decide : Nat.Prime 5)])
  let : IsCyclic P := inferInstanceAs (IsCyclic (zpowers suzukiZeroRootGenerator))
  exact (Sylow.equiv P S).isCyclic.mp inferInstance

/-- The involutions in every original Sylow of the complete binary Chapter 5
catalogue are central in that Sylow, including all small source parameters. -/
theorem binaryRankOne_omega_le_center (M : BinaryRankOneModel G) (S : Sylow 2 G) :
    omegaOneAmbient (S : Subgroup G) ≤ (center S).map (S : Subgroup G).subtype := by
  cases M with
  | sl2 F n hn hc e =>
    let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
    let : IsMulCommutative T := ⟨⟨fun x y =>
      (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T).symm.injective (by simp [mul_comm])⟩⟩
    exact omega_le_center_transport e S (omega_le_center_of_comm T)
  | suzuki m e =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
      let : IsCyclic T := smallSuzuki_sylow_cyclic T
      exact omega_le_center_transport e S (omega_le_center_of_comm T)
    · exact (suzukiSylow_omega_eq_center hm e S).le
  | su3 F J n hn hc hconj e =>
    by_cases hn2 : 2 ≤ n
    · have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hc hconj
      obtain ⟨C,hC⟩ := exists_standard_basis J (2^n) hc hfixed
      exact (HermitianForm.SylowOmega.omega_of_special_equiv (standardForm J)
        hn2 hc hfixed rfl (e.trans (specialEquiv J C hC)) S).1.le
    · have hn1 : n = 1 := by omega
      have hr : primeRank 2 G ≤ 1 := by
        rw [Theory.GroupTheory.primeRank_equiv 2 e,
          primeRank_eq_of_surjective_of_coprime 2 J.specialToProjective
            J.specialToProjective_surjective J.odd_card_specialToProjective_ker.coprime_two_left]
        simpa only [hn1] using (HermitianForm.EvenTwoRank.two_rank J hn hc hconj).le
      exact omega_le_center_of_rank_one hr S
  | psu3 F J n hn hc hconj e =>
    by_cases hn2 : 2 ≤ n
    · have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hc hconj
      obtain ⟨C,hC⟩ := exists_standard_basis J (2^n) hc hfixed
      exact (HermitianForm.SylowOmega.omega_of_projective_equiv (standardForm J)
        hn2 hc hfixed rfl (e.trans (projectiveEquiv J C hC)) S).1.le
    · have hn1 : n = 1 := by omega
      have hr : primeRank 2 G ≤ 1 := by
        rw [Theory.GroupTheory.primeRank_equiv 2 e]
        simpa only [hn1] using (HermitianForm.EvenTwoRank.two_rank J hn hc hconj).le
      exact omega_le_center_of_rank_one hr S

/-- DGS85 (5.9)(b) at prime two: the quadratic actor lies in the first omega
of the embedded center of the prescribed Sylow, not merely in some center. -/
theorem quadratic_actor_le_omega_center {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    (M : BinaryRankOneModel G) (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (S : Sylow 2 G) (A : Subgroup G)
    (hAS : A ≤ S) (hq : IsQuadratic ρ A) :
    A ≤ omegaOneAmbient ((center S).map (S : Subgroup G).subtype) := by
  let : IsElementaryAbelian 2 A := elementary_of_faithful_quadratic ρ hf A hq
  have hAC : A ≤ (center S).map (S : Subgroup G).subtype := by
    rw [←omegaOneAmbient_eq_self A]
    exact (omegaOneAmbient_mono hAS).trans (binaryRankOne_omega_le_center M S)
  rw [←omegaOneAmbient_eq_self A]
  exact omegaOneAmbient_mono hAC
end Representation.RankOne.QuadraticRecognition
