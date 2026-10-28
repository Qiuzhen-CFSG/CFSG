module
public import ABG.ChapterII.Section2.Defs
public import ABG.ChapterII.Section1.WreathedUHighInvolutions
public import GorensteinWalter.GWLemma21Trichotomy
public import GorensteinWalter.NormalPComplementQuotientPGroup
public import GorensteinWalter.KleinFourMapInjective
public import Theory.GroupAction.NormalComplement

/-!
# A fused four-subgroup in every D-group or QD-group

Every finite D-group or QD-group contains an actual Klein-four subgroup
whose three nonidentity elements are all conjugate in the ambient group.
The enlarged D definition, including dihedral Sylow subgroups without a
normal two-complement, is retained.

The quasi-dihedral patterns have one involution class. In a wreathed pattern
the high base automizer fuses all involutions of the actual presentation
four-group inside that base. In the dihedral case, normalize the actual
Sylow parameter to a power of two; the cyclic case is excluded by Burnside
transfer. The unconditional dihedral trichotomy supplies a four-group with
strict C-prime normalizer containment. Its normalizer induces an automorphism
whose square is nontrivial, hence fixes no nonidentity four-group element;
the elementary four-group calculation gives the required fusion. The normal
complement alternative is excluded using the actual odd-core quotient.

This is the fusion witness used in ABG II.4 Lemma 17, article page 45,
from II.1 Propositions 1 and 2 and the dihedral fusion theorem. No minimal
counterexample, simple-group or characteristic-power hypothesis is imposed.
-/

namespace ABG
open scoped IsKleinFour
universe u

private theorem four_order {G : Type*} [Group G] (T : Subgroup G)
    [IsKleinFour T] (x : T) (hx : x ≠ 1) : orderOf (x : G) = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Subgroup.orderOf_coe]
  exact orderOf_eq_prime (by simpa only [pow_two] using IsKleinFour.mul_self x) hx

private theorem four_fusion_of_one_class {G : Type*} [Group G]
    (T : Subgroup G) (hT : IsKleinFour T) (hc : HasElementConjugacyClassCount G 2 1) :
    ∀ x y : T, x ≠ 1 → y ≠ 1 → IsConj (x : G) (y : G) := by
  let : IsKleinFour T := hT
  obtain ⟨r, _, _, hr⟩ := hc
  intro x y hx hy
  obtain ⟨i, hi⟩ := hr x (four_order T x hx)
  obtain ⟨j, hj⟩ := hr y (four_order T y hy)
  have hij : i = j := Subsingleton.elim _ _
  exact hi.trans (hij ▸ hj).symm

private theorem wreathed_fused_four
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (n : ℕ) (U V : Subgroup G)
    (hf : WreathedFusionFrame S n U V) (hU : automizerIndex U = 6) :
    ∃ T : Subgroup G, IsKleinFour T ∧
      ∀ x y : T, x ≠ 1 → y ≠ 1 → IsConj (x : G) (y : G) := by
  obtain ⟨P⟩ := Wreathed.nonempty_presentation hf.1
  have hPU : P.U = U.subgroupOf (S : Subgroup G) :=
    hf.2.2.2.2.1 P.U P.abelian_maximal_unique.1 P.U_isCoatom
  let T := P.T.map (S : Subgroup G).subtype
  have hT : IsKleinFour T := GorensteinWalter.isKleinFour_map_of_injective
    P.T P.T_isFourGroup (S : Subgroup G).subtype (S : Subgroup G).subtype_injective
  let : IsKleinFour T := hT
  have hTU : T ≤ U := by
    rintro _ ⟨x, hx, rfl⟩
    change x ∈ U.subgroupOf (S : Subgroup G)
    rw [← hPU]
    exact P.T_le_U hx
  refine ⟨T, hT, ?_⟩
  intro x y hx hy
  apply Wreathed.u_involutions_isConj S n U V hf hU
    ⟨x, hTU x.property⟩ ⟨y, hTU y.property⟩
  · rw [← Subgroup.orderOf_coe]
    exact four_order T x hx
  · rw [← Subgroup.orderOf_coe]
    exact four_order T y hy

private theorem four_fusion_of_cPrime
    {G : Type*} [Group G] (T : Subgroup G) (hT : IsKleinFour T)
    (hc : GorensteinWalter.NormalizerContainsCPrime T) :
    ∀ x y : T, x ≠ 1 → y ≠ 1 → IsConj (x : G) (y : G) := by
  let : IsKleinFour T := hT
  obtain ⟨a, ha, hac⟩ := Set.exists_of_ssubset hc
  let an : Subgroup.normalizer (T : Set G) := ⟨a, ha⟩
  let φ : MulAut T := T.normalizerMonoidHom an
  have hφsq : φ ^ 2 ≠ 1 := by
    intro h
    have hker : an ^ 2 ∈ T.normalizerMonoidHom.ker := by
      change T.normalizerMonoidHom (an ^ 2) = 1
      rw [map_pow]
      exact h
    rw [Subgroup.normalizerMonoidHom_ker] at hker
    exact hac ⟨ha, hker⟩
  have hfix (x : T) (hx : x ≠ 1) : φ x ≠ x := fun h =>
    hφsq (GorensteinWalter.mulAut_sq_eq_one_of_fixed_ne_one φ hx h)
  have hconj (x : T) : IsConj (x : G) (φ x : G) := isConj_iff.mpr ⟨a, rfl⟩
  intro x y hx hy
  by_cases hxy : x = y
  · subst y
    exact IsConj.refl _
  by_cases hφxy : φ x = y
  · exact hφxy ▸ hconj x
  have hφyx : φ y = x := by
    by_contra h
    have hφx1 : φ x ≠ 1 := by simpa using hx
    have hφy1 : φ y ≠ 1 := by simpa using hy
    have h1 := IsKleinFour.eq_mul_of_ne_all hx hy hxy hφx1 (hfix x hx) hφxy
    have h2 := IsKleinFour.eq_mul_of_ne_all hx hy hxy hφy1 h (hfix y hy)
    exact hxy (φ.injective (h1.trans h2.symm))
  exact (hφyx ▸ hconj y).symm

private theorem dihedral_fused_four
    {G : Type u} [Group G] [Finite G]
    (hd : HasDihedralSylowTwo G) (hn : ¬ HasNormalPComplement 2 G) :
    ∃ T : Subgroup G, IsKleinFour T ∧
      ∀ x y : T, x ≠ 1 → y ≠ 1 → IsConj (x : G) (y : G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, n, ⟨e⟩⟩ := hd
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  have hcard : 2 * n = 2 ^ k := by
    rw [← DihedralGroup.nat_card, ← Nat.card_congr e.toEquiv, hk]
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := by
    have hkpos : 0 < k := by
      by_contra h
      have hk0 : k = 0 := by omega
      simp only [hk0, pow_zero] at hcard
      omega
    exact ⟨k - 1, by omega⟩
  have hnmodel : n = 2 ^ k := by
    rw [pow_succ'] at hcard
    exact Nat.mul_left_cancel (by omega : 0 < 2) hcard
  have hkpos : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := by omega
    have hn1 : n = 1 := by simp [hnmodel, hk0]
    have hScard : Nat.card S = 2 := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hn1]
    have hS : IsCyclic S := e.isCyclic.mpr (DihedralGroup.isCyclic_iff.mpr hn1)
    have htwo : 2 ∣ Nat.card G := hScard ▸ S.card_subgroup_dvd_card
    have hNC : Subgroup.normalizer (S : Set G) ≤ Subgroup.centralizer (S : Set G) :=
      hS.normalizer_le_centralizer ((Nat.minFac_eq_two_iff _).mpr htwo)
    apply hn
    apply hasNormalPComplement_of_sylow_le_center_normalizer 2 S
    intro s hs
    refine ⟨Subgroup.le_normalizer hs, ?_⟩
    change s ∈ Subgroup.centralizer (Subgroup.normalizer (S : Set G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact (Subgroup.mem_centralizer_iff.mp (hNC hg) s hs).symm
  have hmodel : GorensteinWalter.HasDihedralSylowTwo G := by
    intro R
    refine ⟨k, hkpos, ⟨(Sylow.equiv R S).trans ?_⟩⟩
    exact hnmodel ▸ e
  rcases GorensteinWalter.gw_lemma_2_1 hmodel with h | h | h
  · obtain ⟨m, hm, ⟨eS⟩⟩ := hmodel S
    obtain ⟨T, hTS, hT⟩ := GorensteinWalter.exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
      (S : Subgroup G) hm eS
    exact ⟨T, hT, four_fusion_of_cPrime T hT (h.2.2 S T hTS hT)⟩
  · obtain ⟨R, _, T0, T1, _, _, hT0, hT1, _, _, hcases⟩ := h.2.2
    rcases hcases with ⟨h0, _⟩ | ⟨h1, _⟩
    · exact ⟨T0, hT0, four_fusion_of_cPrime T0 hT0 h0⟩
    · exact ⟨T1, hT1, four_fusion_of_cPrime T1 hT1 h1⟩
  · exact (hn ⟨pPrimeCore 2 G, inferInstance, pPrimeCore_coprime_card,
      GorensteinWalter.isPGroup_quotient_pPrimeCore_of_normalPComplement h.2⟩).elim

public theorem d_or_qd_exists_fused_four
    {G : Type u} [Group G] [Finite G] (hG : IsDGroup G ∨ IsQDGroup G) :
    ∃ T : Subgroup G, IsKleinFour T ∧
      ∀ x y : T, x ≠ 1 → y ≠ 1 → IsConj (x : G) (y : G) := by
  rcases hG with (hfull | ⟨hd, hn⟩) | hqd
  · rcases hfull with ⟨S, T, Q, hf, hp⟩ | ⟨S, n, U, V, hf, hp⟩
    · exact ⟨T, hf.2.2.2.1, four_fusion_of_one_class T hf.2.2.2.1 hp.2.1⟩
    · exact wreathed_fused_four S n U V hf hp.2.2.1
  · exact dihedral_fused_four hd hn
  · rcases hqd with ⟨S, T, Q, hf, hp⟩ | ⟨S, n, U, V, hf, hp⟩
    · exact ⟨T, hf.2.2.2.1, four_fusion_of_one_class T hf.2.2.2.1 hp.2.1⟩
    · exact wreathed_fused_four S n U V hf hp.2.2.1

end ABG
