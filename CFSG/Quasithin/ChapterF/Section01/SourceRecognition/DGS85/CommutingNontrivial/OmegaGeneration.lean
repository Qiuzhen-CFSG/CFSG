module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.SylowCenters
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.SpecificGroups.PSL2.InvolutionFusion
public import Theory.SpecificGroups.Suzuki.InvolutionFusion
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.DegreeDivisibility.ModelTransitivity.Unitary

/-!
# Generation of the entire source Sylow omega-center

Fusion of involutions, followed by Burnside fusion, makes the actual Sylow
normalizer transitive on its nonidentity central omega elements. Thus every
nonzero elementary seed generates the full omega-center under that normalizer.
The linear and large Suzuki cases use concrete involution fusion; the unitary
cases use the fixed-field torus. Cyclic Sylows or two-rank one handle every
small parameter, including D₁₀, Sz(2), SU₃(2), and PSU₃(2).

The quotient preimage is the kernel joined with the original normalizer span.
`QuotientOmegaAction` applies this identity to the moving Chapter 8 seed and
proves the action of the entire quotient omega-center, not just that seed.
Source: DGS, *Groups and Graphs* (1985), 8.1(h), pp.132–134, using the
rank-one root geometry of 5.1 and 5.9. The prescribed quotient and Sylow
are retained throughout, without imposing simplicity on small models.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open Representation.RankOne.QuadraticRecognition
open BenderSuzuki.ZD.Source16ModelTransitivity
open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial

private instance {F : Type*} [Field F] [Finite F] : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

private theorem omega_fusion_of_rank_one {G : Type*} [Group G] [Finite G]
    (hr : primeRank 2 G ≤ 1) (S : Sylow 2 G) :
    ∀ x ∈ omegaCenterIn (S : Subgroup G), x ≠ 1 →
      ∀ y ∈ omegaCenterIn (S : Subgroup G), y ≠ 1 → IsConj x y := by
  intro x hx hx1 y hy hy1
  have he := commuting_involutions_eq_of_two_rank_one hr
    ⟨hx1, (mem_omegaCenterIn_iff _ _).mp hx |>.2.2⟩
    ⟨hy1, (mem_omegaCenterIn_iff _ _).mp hy |>.2.2⟩
    (show Commute x y from ((mem_omegaCenterIn_iff _ _).mp hx).2.1 y
      ((mem_omegaCenterIn_iff _ _).mp hy).1 |>.symm)
  exact isConj_iff.mpr ⟨1, by simpa using he⟩

private theorem omega_fusion_of_cyclic_sylow {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) [IsCyclic S] :
    ∀ x ∈ omegaCenterIn (S : Subgroup G), x ≠ 1 →
      ∀ y ∈ omegaCenterIn (S : Subgroup G), y ≠ 1 → IsConj x y := by
  intro x hx hx1 y hy hy1
  have hi (z : G) (hz : z ∈ omegaCenterIn (S : Subgroup G)) (hz1 : z ≠ 1) :
      orderOf (⟨z, ((mem_omegaCenterIn_iff _ _).mp hz).1⟩ : S) = 2 :=
    orderOf_eq_prime (Subtype.ext ((mem_omegaCenterIn_iff _ _).mp hz).2.2)
      (fun he => hz1 (congrArg Subtype.val he))
  have he := congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two (hi x hx hx1) (hi y hy hy1))
  exact isConj_iff.mpr ⟨1, by simpa using he⟩

private theorem omega_fusion_transport {G D : Type*} [Group G] [Finite G] [Group D]
    (e : G ≃* D)
    (hf : ∀ S : Sylow 2 D, ∀ x ∈ omegaCenterIn (S : Subgroup D), x ≠ 1 →
      ∀ y ∈ omegaCenterIn (S : Subgroup D), y ≠ 1 → IsConj x y)
    (S : Sylow 2 G) :
    ∀ x ∈ omegaCenterIn (S : Subgroup G), x ≠ 1 →
      ∀ y ∈ omegaCenterIn (S : Subgroup G), y ≠ 1 → IsConj x y := by
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hmem {x : G} (hx : x ∈ omegaCenterIn (S : Subgroup G)) :
      e x ∈ omegaCenterIn (T : Subgroup D) := by
    obtain ⟨hxs, hxc, hx2⟩ := (mem_omegaCenterIn_iff _ _).mp hx
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨mem_map_of_mem _ hxs, ?_, by rw [← map_pow, hx2, map_one]⟩
    rintro _ ⟨s, hs, rfl⟩
    change e s * e x = e x * e s
    simpa only [map_mul] using congrArg e (hxc s hs)
  intro x hx hx1 y hy hy1
  have hf' := e.symm.toMonoidHom.map_isConj
    (hf T (e x) (hmem hx) (fun he => hx1 (e.injective (he.trans e.map_one.symm)))
      (e y) (hmem hy) (fun he => hy1 (e.injective (he.trans e.map_one.symm))))
  simpa only [MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using hf'

private theorem omegaCenter_le_omega {D : Type*} [Group D] (S : Sylow 2 D) :
    omegaCenterIn (S : Subgroup D) ≤ omegaOneAmbient (S : Subgroup D) := by
  rw [omegaCenterIn_eq_omegaOneAmbient]
  exact omegaOneAmbient_mono (map_subtype_le _)

private theorem unitary_omega_fusion {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {n : ℕ} (hn : 0 < n)
    (hc : Nat.card F = (2^n)^2) (hf : ∀ x, J.conj x = x^(2^n)) :
    (∀ S : Sylow 2 J.specialSubgroup, ∀ x ∈ omegaCenterIn (S : Subgroup J.specialSubgroup), x ≠ 1 →
      ∀ y ∈ omegaCenterIn (S : Subgroup J.specialSubgroup), y ≠ 1 → IsConj x y) ∧
    (∀ S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      ∀ x ∈ omegaCenterIn (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)), x ≠ 1 →
      ∀ y ∈ omegaCenterIn (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)), y ≠ 1 → IsConj x y) := by
  by_cases hn2 : 2 ≤ n
  · have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hc hf
    obtain ⟨C, hC⟩ := exists_standard_basis J (2^n) hc hfixed
    constructor
    · intro S x hx hx1 y hy hy1
      exact unitary_special_omega_fusion (standardForm J) rfl hn2 hc hfixed
        (specialEquiv J C hC) S x ((omegaCenter_le_omega S) hx) hx1 y ((omegaCenter_le_omega S) hy) hy1
    · intro S x hx hx1 y hy hy1
      exact unitary_projective_omega_fusion (standardForm J) rfl hn2 hc hfixed
        (projectiveEquiv J C hC) S x ((omegaCenter_le_omega S) hx) hx1 y ((omegaCenter_le_omega S) hy) hy1
  · have hn1 : n = 1 := by omega
    have hp : primeRank 2 (ProjectiveSpecialUnitaryMatrixGroup J) ≤ 1 := by
      simpa only [hn1] using (HermitianForm.EvenTwoRank.two_rank J hn hc hf).le
    have hs : primeRank 2 J.specialSubgroup ≤ 1 := by
      rw [primeRank_eq_of_surjective_of_coprime 2 J.specialToProjective
        J.specialToProjective_surjective J.odd_card_specialToProjective_ker.coprime_two_left]
      exact hp
    exact ⟨omega_fusion_of_rank_one hs, omega_fusion_of_rank_one hp⟩

/-- All nonidentity elements of the marked Sylow omega-center fuse in every
source rank-one model, retaining the small unitary and dihedral cases. -/
theorem source_rank_one_omega_fusion {G : Type*} [Group G] [Finite G]
    (M : IsRankOneModel G) (S : Sylow 2 G) :
    ∀ x ∈ omegaCenterIn (S : Subgroup G), x ≠ 1 →
      ∀ y ∈ omegaCenterIn (S : Subgroup G), y ≠ 1 → IsConj x y := by
  cases M with
  | linear n hn hi =>
    obtain ⟨F, _, _, hc, ⟨e⟩⟩ := hi
    apply omega_fusion_transport e _ S
    intro T x hx hx1 y hy hy1
    exact Theory.PSL2.involutions_isConj x y
      (orderOf_eq_prime ((mem_omegaCenterIn_iff _ _).mp hx).2.2 hx1)
      (orderOf_eq_prime ((mem_omegaCenterIn_iff _ _).mp hy).2.2 hy1)
  | suzuki m hi =>
    obtain ⟨e⟩ := hi
    apply omega_fusion_transport e _ S
    intro T
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · let R : Sylow 2 (SuzukiMatrixGroup 0) := Sylow.ofCard (zpowers suzukiZeroRootGenerator) (by
        rw [Nat.card_zpowers, suzukiZeroRootGenerator_order, suzukiZero_card]
        rw [show (20 : ℕ) = 2^2 * 5 from rfl,
          Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
        norm_num [Nat.Prime.factorization Nat.prime_two,
          Nat.Prime.factorization (by decide : Nat.Prime 5)])
      let : IsCyclic R := inferInstanceAs (IsCyclic (zpowers suzukiZeroRootGenerator))
      let : IsCyclic T := (Sylow.equiv R T).isCyclic.mp inferInstance
      exact omega_fusion_of_cyclic_sylow T
    · intro x hx hx1 y hy hy1
      exact suzuki_involutions_isConj m hm x y
        (orderOf_eq_prime ((mem_omegaCenterIn_iff _ _).mp hx).2.2 hx1)
        (orderOf_eq_prime ((mem_omegaCenterIn_iff _ _).mp hy).2.2 hy1)
  | special_unitary n hn hi =>
    obtain ⟨F, _, _, J, hc, hf, ⟨e⟩⟩ := hi
    exact omega_fusion_transport e (unitary_omega_fusion J hn hc hf).1 S
  | projective_unitary n hn hi =>
    obtain ⟨F, _, _, J, hc, hf, ⟨e⟩⟩ := hi
    exact omega_fusion_transport e (unitary_omega_fusion J hn hc hf).2 S
  | dihedral hi =>
    obtain ⟨e⟩ := hi
    have hc : Nat.card S = 2 := by
      rw [S.card_eq_multiplicity, Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      rw [Nat.factorization_mul (by decide) (by decide),
        Nat.prime_two.factorization, Nat.prime_five.factorization]
      norm_num
    let : IsCyclic S := isCyclic_of_prime_card hc
    exact omega_fusion_of_cyclic_sylow S

/-- Burnside fusion places the conjugator in the normalizer of the original
Sylow, rather than just somewhere in the quotient model. -/
theorem source_rank_one_omega_normalizer_transitive {G : Type*} [Group G] [Finite G]
    (M : IsRankOneModel G) (S : Sylow 2 G) :
    ∀ x ∈ omegaCenterIn (S : Subgroup G), x ≠ 1 →
      ∀ y ∈ omegaCenterIn (S : Subgroup G), y ≠ 1 →
        ∃ g ∈ normalizer (S : Set G), MulAut.conj g x = y := by
  intro x hx hx1 y hy hy1
  obtain ⟨g, hg⟩ := isConj_iff.mp (source_rank_one_omega_fusion M S x hx hx1 y hy hy1)
  obtain ⟨a, ha, he⟩ := S.conj_eq_normalizer_conj_of_mem_centralizer x g⁻¹
    ((mem_omegaCenterIn_iff _ _).mp hx).2.1
    (by simpa only [inv_inv] using hg.symm ▸ ((mem_omegaCenterIn_iff _ _).mp hy).2.1)
  simp only [inv_inv] at he
  refine ⟨a⁻¹, (normalizer (S : Set G)).inv_mem ha, ?_⟩
  change a⁻¹ * x * (a⁻¹)⁻¹ = y
  simpa only [inv_inv] using he.symm.trans hg

/-- A nonzero elementary seed generates the full Sylow omega-center under
the literal normalizer. This includes all small source parameters. -/
theorem source_rank_one_omega_generated {G : Type*} [Group G] [Finite G]
    (M : IsRankOneModel G) (S : Sylow 2 G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAS : A ≤ S) (hne : A ≠ ⊥) :
    conjugateSpanBy A (normalizer (S : Set G)) = omegaCenterIn (S : Subgroup G) := by
  have hAZ := source_rank_one_elementary_le_sylow_omega M S A hAS
  apply le_antisymm (conjugateSpanBy_le hAZ (normalizer_le_normalizer_omegaCenterIn _))
  obtain ⟨x, hx, hx1⟩ := A.bot_or_exists_ne_one.resolve_left hne
  intro y hy
  by_cases hy1 : y = 1
  · exact hy1 ▸ one_mem _
  obtain ⟨g, hg, hxy⟩ := source_rank_one_omega_normalizer_transitive M S x (hAZ hx) hx1 y hy hy1
  rw [← hxy]
  exact (le_normalizer_iff.mp (le_normalizer_conjugateSpanBy A _) g hg x
    (le_conjugateSpanBy A _ hx))

/-- Lifting the full omega-center through its actual marked quotient gives
exactly the kernel joined with the normalizer span of the nonzero seed. -/
theorem source_rank_one_omega_preimage {L D : Type*} [Group L] [Finite L]
    [Group D] [Finite D] (q : L →* D) (hq : Function.Surjective q)
    (M : IsRankOneModel D) (S : Sylow 2 L) (hk : q.ker ≤ S)
    (A : Subgroup L) [IsElementaryAbelian 2 A] (hAS : A ≤ S)
    (hne : A.map q ≠ ⊥) :
    (omegaCenterIn (S.mapSurjective hq : Subgroup D)).comap q =
      conjugateSpanBy A (normalizer (S : Set L)) ⊔ q.ker := by
  let : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
  have hn : (normalizer (S : Set L)).map q = normalizer (S.map q : Set D) := by
    rw [← map_comap_eq_self_of_surjective hq (normalizer (S.map q : Set D)),
      comap_normalizer_eq_of_surjective _ hq, comap_map_eq_self hk]
    rfl
  have he := source_rank_one_omega_generated M (S.mapSurjective hq) (A.map q)
    (map_mono hAS) hne
  rw [← he]
  change (conjugateSpanBy (A.map q) (normalizer (S.map q : Set D))).comap q = _
  rw [← hn, ← map_conjugateSpanBy, comap_map_eq]

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
