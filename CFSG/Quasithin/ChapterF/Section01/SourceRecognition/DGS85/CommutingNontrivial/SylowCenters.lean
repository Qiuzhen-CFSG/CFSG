module
public import Theory.Representation.RankOne.QuadraticRecognition.SourceTheorem
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels

/-!
# Sylow-center displacement in the binary Chapter 8 models

Every involution in a Sylow two-subgroup of an actual binary rank-one
model is central in that Sylow. For SL₂ this follows from its additive
root coordinates; for Suzuki from its root omega-center and, at Sz(2),
its cyclic Sylow. Hermitian coordinates prove the unitary assertion at
every positive field degree, including SU₃(2) and PSU₃(2). The actual
scalar projection and a Hermitian basis change transport the result.
The source-specific extension includes D₁₀ through its order-two Sylows;
the separate corrected 5.12 catalogue remains unchanged.

Thus an elementary actor lies in the original Sylow omega-center.
Lifting through an arbitrary marked quotient gives the displacement
into its exact kernel, without faithfulness of an unrelated action.
`EdgeDisplacement` applies this to the Chapter 8 moving actor and
removes the displacement premise of its normality argument.

Source: DGS, *Groups and Graphs* (1985), 5.9(b) and the proof of 8.1(i),
pp.110,133; the root calculations are Huppert II.10.12 and
Huppert--Blackburn III, XI.3.1--3.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial

private instance {F : Type*} [Field F] [Finite F] : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

private theorem center_square_transport {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (h : ∀ x : H, x ^ 2 = 1 → x ∈ center H)
    (x : G) (hx : x ^ 2 = 1) : x ∈ center G := by
  apply mem_center_iff.mpr
  intro y
  apply e.injective
  simpa only [map_mul] using mem_center_iff.mp
    (h (e x) (by rw [← map_pow, hx, map_one])) (e y)

private theorem center_square_sylow_transport {G H : Type*} [Group G] [Finite G] [Group H]
    (e : G ≃* H)
    (h : ∀ S : Sylow 2 H, ∀ x : S, x ^ 2 = 1 → x ∈ center S)
    (S : Sylow 2 G) (x : S) (hx : x ^ 2 = 1) : x ∈ center S := by
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let f : S ≃* T := (S : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective
  exact center_square_transport f (h T) x hx

private theorem unitary_coord_square_central
    {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 3 F)
    (x : BenderSuzuki.External.hermitianUnipotentCoord J) (hx : x ^ 2 = 1) :
    x ∈ center (BenderSuzuki.External.hermitianUnipotentCoord J) := by
  have hx0 := (HermitianForm.EvenSemilinear.square_eq_one_iff_first_zero J x).mp hx
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  apply Prod.ext
  · change y.val.1 + x.val.1 = x.val.1 + y.val.1
    exact add_comm _ _
  · change y.val.2 + x.val.2 - y.val.1 * J.conj x.val.1 =
      x.val.2 + y.val.2 - x.val.1 * J.conj y.val.1
    simp only [hx0, map_zero, mul_zero, zero_mul, sub_zero, add_comm]

private theorem projective_unitary_square_central
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 0 < n) (hc : Nat.card F = (2^n)^2)
    (hf : ∀ x, J.conj x = x^(2^n))
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (x : S) (hx : x ^ 2 = 1) : x ∈ center S := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    (by simpa only [Nat.card_eq_fintype_card, pow_mul] using hc)
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    hn hc hf
  let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨e⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2^n) hc hfixed
  apply center_square_sylow_transport e _ S x hx
  intro T t ht
  let R := HermitianForm.EvenTwoRank.rootSylow J₀ rfl hn hc hfixed
  let f : T ≃* BenderSuzuki.External.hermitianUnipotentCoord J₀ :=
    (T.equiv R).trans
      (MonoidHom.ofInjective (HermitianForm.EvenInner.root_injective J₀ rfl)).symm
  exact center_square_transport f (unitary_coord_square_central J₀) t ht

private theorem special_unitary_square_central
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 0 < n) (hc : Nat.card F = (2^n)^2)
    (hf : ∀ x, J.conj x = x^(2^n))
    (S : Sylow 2 J.specialSubgroup) (x : S) (hx : x ^ 2 = 1) : x ∈ center S :=
  center_square_transport (HermitianForm.SylowOmega.specialSylowEquivProjective J S)
    (projective_unitary_square_central J hn hc hf _) x hx

private theorem small_suzuki_sylow_cyclic (S : Sylow 2 (SuzukiMatrixGroup 0)) : IsCyclic S := by
  let P : Sylow 2 (SuzukiMatrixGroup 0) := Sylow.ofCard (zpowers suzukiZeroRootGenerator) (by
    rw [Nat.card_zpowers, suzukiZeroRootGenerator_order, suzukiZero_card]
    rw [show (20 : ℕ) = 2^2 * 5 from rfl,
      Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
    norm_num [Nat.Prime.factorization Nat.prime_two,
      Nat.Prime.factorization (by decide : Nat.Prime 5)])
  let : IsCyclic P := inferInstanceAs (IsCyclic (zpowers suzukiZeroRootGenerator))
  exact (Sylow.equiv P S).isCyclic.mp inferInstance

/-- In every actual binary rank-one model, involutions in a Sylow group
are central in that same Sylow. All small source parameters are included. -/
theorem binary_rank_one_sylow_square_central {G : Type*} [Group G] [Finite G]
    (M : BinaryRankOneModel G) (S : Sylow 2 G)
    (x : S) (hx : x ^ 2 = 1) : x ∈ center S := by
  cases M with
  | sl2 F n hn hc e =>
    apply center_square_sylow_transport e _ S x hx
    intro T t ht
    exact center_square_transport (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T).symm
      (fun y _ => mem_center_iff.mpr (fun z => mul_comm z y)) t ht
  | suzuki m e =>
    apply center_square_sylow_transport e _ S x hx
    intro T t ht
    by_cases hm : m = 0
    · subst m
      let := small_suzuki_sylow_cyclic T
      exact mem_center_iff.mpr (fun y => mul_comm y t)
    · have hmem : (t : SuzukiMatrixGroup m) ∈ omegaOneAmbient (T : Subgroup _) :=
        (omegaOneAmbient_le_iff (T : Subgroup (SuzukiMatrixGroup m)) _).mp le_rfl (t : SuzukiMatrixGroup m) t.property (congrArg Subtype.val ht)
      rw [suzukiSylow_omega_eq_center (by omega) (MulEquiv.refl _) T] at hmem
      obtain ⟨y, hy, he⟩ := hmem
      exact (Subtype.ext he : y = t) ▸ hy
  | su3 F J n hn hc hf e =>
    exact center_square_sylow_transport e (special_unitary_square_central J hn hc hf) S x hx
  | psu3 F J n hn hc hf e =>
    exact center_square_sylow_transport e (projective_unitary_square_central J hn hc hf) S x hx

/-- The actual elementary actor lies in Ω₁(Z(S)), without any extra
faithfulness premise on a representation of the whole rank-one group. -/
theorem binary_rank_one_elementary_le_sylow_omega {G : Type*} [Group G] [Finite G]
    (M : BinaryRankOneModel G) (S : Sylow 2 G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAS : A ≤ S) :
    A ≤ omegaCenterIn (S : Subgroup G) := by
  intro x hx
  have hx2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx
  have hz := binary_rank_one_sylow_square_central M S ⟨x, hAS hx⟩ (Subtype.ext hx2)
  apply (mem_omegaCenterIn_iff _ _).mpr
  refine ⟨hAS hx, ?_, hx2⟩
  intro y hy
  exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩)

/-- The complete source local catalogue has the same involution-centrality
property, including the exceptional D₁₀ row of Hypothesis A′.
This does not add a row to the separate 5.12 module catalogue. -/
theorem source_rank_one_sylow_square_central {G : Type*} [Group G] [Finite G]
    (M : IsRankOneModel G) (S : Sylow 2 G) (x : S) (hx : x ^ 2 = 1) : x ∈ center S := by
  cases M with
  | linear n hn hi =>
    obtain ⟨F, _, _, hc, ⟨e⟩⟩ := hi
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hc)
    let f := e.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi F)
      ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩).symm
    exact center_square_sylow_transport f
      (binary_rank_one_sylow_square_central (.sl2 F n hn hc (MulEquiv.refl _))) S x hx
  | suzuki m hi =>
    obtain ⟨e⟩ := hi
    exact center_square_sylow_transport e
      (binary_rank_one_sylow_square_central (.suzuki m (MulEquiv.refl _))) S x hx
  | special_unitary n hn hi =>
    obtain ⟨F, _, _, J, hc, hf, ⟨e⟩⟩ := hi
    exact center_square_sylow_transport e (special_unitary_square_central J hn hc hf) S x hx
  | projective_unitary n hn hi =>
    obtain ⟨F, _, _, J, hc, hf, ⟨e⟩⟩ := hi
    exact center_square_sylow_transport e (projective_unitary_square_central J hn hc hf) S x hx
  | dihedral hi =>
    obtain ⟨e⟩ := hi
    have hc : Nat.card S = 2 := by
      rw [S.card_eq_multiplicity, Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      rw [Nat.factorization_mul (by decide) (by decide),
        Nat.prime_two.factorization, Nat.prime_five.factorization]
      norm_num
    let : IsCyclic S := isCyclic_of_prime_card hc
    exact mem_center_iff.mpr (fun y => mul_comm y x)

/-- Source 5.9(b)'s binary elementary placement includes the D₁₀ local
exception, on the literal Sylow subgroup. -/
theorem source_rank_one_elementary_le_sylow_omega {G : Type*} [Group G] [Finite G]
    (M : IsRankOneModel G) (S : Sylow 2 G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAS : A ≤ S) :
    A ≤ omegaCenterIn (S : Subgroup G) := by
  intro x hx
  have hx2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx
  have hz := source_rank_one_sylow_square_central M S ⟨x, hAS hx⟩ (Subtype.ext hx2)
  apply (mem_omegaCenterIn_iff _ _).mpr
  refine ⟨hAS hx, ?_, hx2⟩
  intro y hy
  exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩)

/-- Lifting Sylow centrality through the literal quotient map gives the
source displacement into its kernel. -/
theorem elementary_actor_displacement_le_kernel
    {G D : Type*} [Group G] [Group D] [Finite D]
    (L : Subgroup G) [Finite L] (q : L →* D) (hq : Function.Surjective q)
    (M : IsRankOneModel D) (S : Sylow 2 L)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAL : A ≤ L) (hAS : A ≤ (S : Subgroup L).map L.subtype) :
    ⁅(S : Subgroup L).map L.subtype, A⁆ ≤ q.ker.map L.subtype := by
  let A' := A.subgroupOf L
  let : IsElementaryAbelian 2 A' := IsElementaryAbelian.subgroupOf hAL
  let : IsElementaryAbelian 2 (A'.map q) := IsElementaryAbelian.map q
  let T := S.mapSurjective hq
  have hA'S : A' ≤ (S : Subgroup L) := by
    intro a ha
    obtain ⟨s, hs, he⟩ := hAS ha
    exact (Subtype.ext he : s = a) ▸ hs
  have hcent := source_rank_one_elementary_le_sylow_omega M T (A'.map q)
    (map_mono hA'S)
  have hcomm : ⁅(S : Subgroup L), A'⁆ ≤ q.ker := by
    rw [← Subgroup.map_eq_bot_iff, map_commutator]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    intro a ha
    exact ((mem_omegaCenterIn_iff _ _).mp (hcent ha)).2.1
  have hm := map_mono (f := L.subtype) hcomm
  rw [map_commutator, map_subgroupOf_eq_of_le hAL] at hm
  exact hm

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
