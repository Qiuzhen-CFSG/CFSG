module
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels
public import Theory.SpecificGroups.SL2.BorelIndex
public import Theory.GroupTheory.SylowNormalizerCentralQuotient

/-!
# Valences for the full characteristic-two rank-one catalogue

The Sylow normalizer has index q+1 in PSL₂(q), q²+1 in Sz(q), q³+1
in both SU₃(q) and PSU₃(q), and five in D₁₀. The linear case reuses the
matrix Borel index. The unitary case counts the actual isotropic points;
the central scalar quotient preserves the Sylow-normalizer index. Suzuki
ovoid transitivity gives the nondegenerate case, and prime index handles
Sz(2). All small parameters, including SU₃(2) and PSU₃(2), are retained.

Consequently every source model has two-power forward branching. The
DGS graph consumer transports this through the original starred quotient
and the full Borel product, without assuming enlargement recognition.

Source: Aschbacher--Smith, F.1.1--F.1.3, printed pp.259--260;
Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985), 6.7, p.123.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source
set_option backward.isDefEq.respectTransparency false in
private theorem normalizer_index_equiv {G H : Type*} [Group G] [Group H] [Finite G]
    (T : Sylow 2 G) (e : G ≃* H) :
    (normalizer (T.mapSurjective (f := e.toMonoidHom) e.surjective : Set H)).index =
      (normalizer (T : Set G)).index := by
  change (normalizer ((T : Subgroup G).map e.toMonoidHom : Set H)).index = _
  rw [←map_normalizer_eq_of_bijective _ e.bijective]
  exact index_map_of_bijective e.bijective _

private theorem normalizer_index_same {G : Type*} [Group G] [Finite G]
    (S T : Sylow 2 G) :
    (normalizer (S : Set G)).index = (normalizer (T : Set G)).index :=
  S.card_eq_index_normalizer.symm.trans T.card_eq_index_normalizer

private theorem normalizer_index_of_prime_index {G : Type*} [Group G]
    (T : Sylow 2 G) (hp : (T : Subgroup G).index = 5)
    (hn : normalizer (T : Set G) < ⊤) :
    (normalizer (T : Set G)).index = 5 := by
  have hd : (normalizer (T : Set G)).index ∣ 5 := by
    rw [←hp]
    exact index_dvd_of_le (T : Subgroup G).le_normalizer
  exact ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd).resolve_left
    (fun h => hn.ne (index_eq_one.mp h))

set_option backward.isDefEq.respectTransparency false in
/-- The original marked linear Sylow normalizer has index q+1, including q=2. -/
theorem linear_sylow_normalizer_index {F : Type*} [Field F] [Finite F] [CharP F 2]
    (T : Sylow 2 (BenderSuzuki.Converse.PSL2 F)) :
    (normalizer (T : Set (BenderSuzuki.Converse.PSL2 F))).index = Nat.card F + 1 := by
  let e : Matrix.SpecialLinearGroup (Fin 2) F ≃* BenderSuzuki.Converse.PSL2 F :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi F)
      ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩
  let U := Matrix.SpecialLinearGroup.upperUnipotentSylow F 2
  have hU : (normalizer (U : Set (Matrix.SpecialLinearGroup (Fin 2) F))).index =
      Nat.card F + 1 := by
    change (normalizer ((Matrix.SpecialLinearGroup.upperUnipotentSylow F 2 :
      Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) : Set (Matrix.SpecialLinearGroup (Fin 2) F))).index = _
    rw [Matrix.SpecialLinearGroup.coe_upperUnipotentSylow]
    exact Matrix.SpecialLinearGroup.rankOneBorel_index_even F
  exact (normalizer_index_same T
    (U.mapSurjective (f := e.toMonoidHom) e.surjective)).trans
      ((normalizer_index_equiv U e).trans hU)

/-- All Suzuki parameters have q²+1 neighbors, including Sz(2). -/
theorem suzuki_sylow_normalizer_index (m : ℕ) (T : Sylow 2 (SuzukiMatrixGroup m)) :
    (normalizer (T : Set (SuzukiMatrixGroup m))).index = (2^(2*m+1))^2+1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hc : Nat.card T = 4 := by
      rw [T.card_eq_multiplicity, suzukiZero_card]
      decide +kernel
    have hi : (T : Subgroup (SuzukiMatrixGroup 0)).index = 5 := by
      have he := (T : Subgroup (SuzukiMatrixGroup 0)).card_mul_index
      rw [hc, suzukiZero_card] at he
      omega
    simpa using normalizer_index_of_prime_index T hi (suzuki_rankOneSylowFacts 0 T).proper
  · obtain ⟨g,hg⟩ := suzuki_sylow_normalizer_eq_conjugate_borel m T
    rw [hg,index_map_of_bijective (MulAut.conj g).bijective,
      suzukiBorelSubgroup_eq_stabilizer m hm,
      MulAction.index_stabilizer_of_transitive,suzukiOvoid_card]

/-- The truncated Suzuki alternative has five neighbors. -/
theorem dihedral_sylow_normalizer_index {H : Type*} [Group H]
    (e : H ≃* DihedralGroup 5) (T : Sylow 2 H) :
    (normalizer (T : Set H)).index = 5 := by
  let : Finite H := Finite.of_injective e e.injective
  have hc : Nat.card T = 2 := by
    rw [T.card_eq_multiplicity, Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    change 2 ^ ((10 : ℕ).factorization 2) = 2
    decide +kernel
  have hi : (T : Subgroup H).index = 5 := by
    have he := (T : Subgroup H).card_mul_index
    rw [show Nat.card (T : Subgroup H) = 2 from hc,
      Nat.card_congr e.toEquiv,DihedralGroup.nat_card] at he
    omega
  exact normalizer_index_of_prime_index T hi (rankOneSylowFacts_of_dihedral_equiv e T).proper

open CFSG.Quasithin.ChapterF.Source.Unitary
open scoped Matrix LinearAlgebra.Projectivization
private theorem standard_psu_index {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    (normalizer (T : Set (ProjectiveSpecialUnitaryMatrixGroup J))).index = (2^n)^3+1 := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ (suProjection_surjective J)
  obtain ⟨rho,pinf,S,_,_,_,_,_,_,hN,_,htwo⟩ :=
    standard_psu_borel_data J n hn hcard hconj hJ
  let Ω := unitaryIsotropicPoints J
  have hc : Nat.card Ω = (2^n)^3+1 :=
    (BenderSuzuki.External.huppert_II_10_12 J (2^n) hcard
      (fixed_card J n hn hcard hconj) hJ).1
  let : Finite Ω := Nat.finite_of_card_ne_zero (by rw [hc]; omega)
  let : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hc]
    have hp : 0 < (2^n)^3 := by positivity
    omega)
  let : MulAction (ProjectiveSpecialUnitaryMatrixGroup J) Ω := MulAction.compHom Ω rho
  let : MulAction.IsPretransitive (ProjectiveSpecialUnitaryMatrixGroup J) Ω := ⟨by
    intro a c
    obtain ⟨b,hb⟩ := exists_ne a
    obtain ⟨d,hd⟩ := exists_ne c
    obtain ⟨g,hg,_⟩ := htwo a b c d hb.symm hd.symm
    exact ⟨g,hg⟩⟩
  simp only [Sylow.coe_coe] at hN
  rw [normalizer_index_same T S,hN]
  exact (MulAction.index_stabilizer_of_transitive
    (ProjectiveSpecialUnitaryMatrixGroup J) pinf).trans hc

/-- The projective unitary index uses the original Hermitian form and includes q=2. -/
theorem psu_sylow_normalizer_index {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    (normalizer (T : Set (ProjectiveSpecialUnitaryMatrixGroup J))).index = (2^n)^3+1 := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ (suProjection_surjective J)
  obtain ⟨C,hC⟩ := FormTransport.exists_standard_basis J n hn hcard hconj
  rw [←normalizer_index_equiv T (FormTransport.projectiveEquiv J C hC)]
  exact standard_psu_index (FormTransport.standardForm J) n hn hcard hconj rfl _

/-- The special unitary index descends through its actual central scalar kernel. -/
theorem su_sylow_normalizer_index {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (T : Sylow 2 J.specialSubgroup) :
    (normalizer (T : Set J.specialSubgroup)).index = (2^n)^3+1 := by
  rw [←T.normalizer_comap_of_central_kernel (suProjection J)
    (suProjection_surjective J) (suProjection_ker_central J),
    index_comap_of_surjective _ (suProjection_surjective J)]
  exact psu_sylow_normalizer_index J n hn hcard hconj _

/-- Every actual source model has a two-power branching number. -/
theorem IsRankOneModel.sylow_normalizer_branching {H : Type*} [Group H]
    (h : IsRankOneModel H) (T : Sylow 2 H) :
    ∃ k : ℕ, (normalizer (T : Set H)).index - 1 = 2^k := by
  let : Finite H := h.finite
  cases h with
  | linear n hn h =>
    obtain ⟨F,_,_,hc,⟨e⟩⟩ := h
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (by
      simpa only [Nat.card_eq_fintype_card] using hc)
    rw [←normalizer_index_equiv T e,linear_sylow_normalizer_index (F := F),Nat.add_sub_cancel,hc]
    exact ⟨n,rfl⟩
  | suzuki m h =>
    obtain ⟨e⟩ := h
    rw [←normalizer_index_equiv T e,suzuki_sylow_normalizer_index,Nat.add_sub_cancel,←pow_mul]
    exact ⟨(2*m+1)*2,rfl⟩
  | projective_unitary n hn h =>
    obtain ⟨F,_,_,J,hc,hconj,⟨e⟩⟩ := h
    rw [←normalizer_index_equiv T e,psu_sylow_normalizer_index J n hn hc hconj,
      Nat.add_sub_cancel,←pow_mul]
    exact ⟨n*3,rfl⟩
  | special_unitary n hn h =>
    obtain ⟨F,_,_,J,hc,hconj,⟨e⟩⟩ := h
    rw [←normalizer_index_equiv T e,su_sylow_normalizer_index J n hn hc hconj,
      Nat.add_sub_cancel,←pow_mul]
    exact ⟨n*3,rfl⟩
  | dihedral h =>
    obtain ⟨e⟩ := h
    rw [dihedral_sylow_normalizer_index e T]
    exact ⟨2,by decide⟩
end CFSG.Quasithin.ChapterF.Source
