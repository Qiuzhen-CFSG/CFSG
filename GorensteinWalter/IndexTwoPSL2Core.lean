module

public import GorensteinWalter.FinalTheorem
public import GorensteinWalter.NormalPSL2CoreUniqueness
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# The unique normal PSL2 core in the index-two dihedral case

Let H be an odd-core-free finite group with dihedral Sylow two-subgroups
and a normal subgroup K of index two which itself has no normal subgroup
of index two. Gorenstein-Walter supplies a two-group, alternating-seven,
or odd-index linear normal subgroup alternative. The first contradicts
the no-index-two property of the nontrivial two-group K; the second is
simple and cannot have an index-two subgroup. An odd-index PSL2 subgroup
would lie in K, contradicting index parity. In the PGL2 case its
characteristic derived subgroup gives a normal PSL2 model, including q=3.
The normal-core uniqueness theorem identifies every competing odd PSL2
model and its field order; the core also has no normal index-two subgroup.

This is the dihedral quotient step in ABG Chapter II, Section3,
Proposition2 (article p22), using the actual Gorenstein-Walter theorem.
No general automorphism-surjectivity hypothesis or perfectness at q=3
is imposed.
-/

public section
noncomputable section
namespace GorensteinWalter

universe u

private theorem four_le_card_of_hasDihedralSylowTwo
    {G : Type u} [Group G] [Finite G]
    (hG : HasDihedralSylowTwo G) : 4 ≤ Nat.card G := by
  let S : Sylow 2 G := Classical.choice Sylow.nonempty
  obtain ⟨m, hm, ⟨e⟩⟩ := hG S
  have hScard : Nat.card (S : Subgroup G) = 2 * 2 ^ m :=
    (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
  have h4S : 4 ≤ Nat.card (S : Subgroup G) := by
    rw [hScard]
    have h2pow : 2 ≤ 2 ^ m := by
      calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  exact h4S.trans (Nat.le_of_dvd Nat.card_pos S.card_subgroup_dvd_card)

private theorem nontrivial_two_group_has_normal_index_two
    {G : Type u} [Group G] [Finite G]
    (hG : IsPGroup 2 G) (hGne : Nontrivial G) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 G) := ⟨hG⟩
  obtain ⟨n, hn⟩ := hG.exists_card_eq
  have hnpos : 0 < n := by
    have hcardgt : 1 < Nat.card G := Finite.one_lt_card_iff_nontrivial.mpr hGne
    rw [hn] at hcardgt
    exact Nat.pos_of_ne_zero (by
      intro hn0
      subst n
      norm_num at hcardgt)
  obtain ⟨N, hNnormal, _hNle, hNcard⟩ :=
    exists_normal_subgroup_card_pow_of_normal
      (G := G) (p := 2) (⊤ : Subgroup G) inferInstance
      (by simpa only [Subgroup.card_top] using hn) (n - 1) (by omega)
  have hindex : N.index = 2 := by
    have hi := N.index_mul_card
    rw [hNcard, hn] at hi
    have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
      calc
        2 ^ n = 2 ^ (1 + (n - 1)) := by congr 1; omega
        _ = 2 * 2 ^ (n - 1) := by rw [pow_add]; simp
    rw [hpow] at hi
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) _) hi
  exact ⟨N, hNnormal, hindex⟩

private theorem no_normal_index_two_of_mulEquiv_aSeven
    {G : Type u} [Group G] [Finite G]
    (e : G ≃* alternatingGroup (Fin 7)) :
    ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  let : IsSimpleGroup G := e.isSimpleGroup
  intro N hNnormal hNindex
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N hNnormal with hbot | htop
  · rw [hbot, Subgroup.index_bot] at hNindex
    have hcard : Nat.card G = 2520 := by
      calc
        Nat.card G = Nat.card (alternatingGroup (Fin 7)) := Nat.card_congr e.toEquiv
        _ = 2520 := by rw [nat_card_alternatingGroup]; norm_num
    omega
  · rw [htop, Subgroup.index_top] at hNindex
    omega

/-- The unique normal odd PSL2 core in the index-two dihedral case. -/
theorem exists_unique_normal_psl2_of_index_two
    {H : Type u} [Group H] [Finite H]
    (hHd : HasDihedralSylowTwo H) (hO : pPrimeCore 2 H = ⊥)
    (K : Subgroup H) (hKnormal : K.Normal) (hKindex : K.index = 2)
    (hKno2 : ∀ N : Subgroup K, N.Normal → N.index ≠ 2) :
    ∃ (F : Type u) (instF : Field F) (_ : Finite F),
      let : Field F := instF
      IsOddPrimePower (Nat.card F) ∧
      ∃ L : Subgroup H,
        L.Normal ∧ Nonempty (L ≃* PSL2 F) ∧
        (∀ N : Subgroup L, N.Normal → N.index ≠ 2) ∧
        ∀ (E : Type u) (instE : Field E) (_ : Finite E),
          let : Field E := instE
          IsOddPrimePower (Nat.card E) →
          ∀ M : Subgroup H, M.Normal → Nonempty (M ≃* PSL2 E) →
            M = L ∧ Nat.card E = Nat.card F := by
  have hD : IsDGroup H := gorensteinWalter H hHd
  let qE : (H ⧸ pPrimeCore 2 H) ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq (G := H) hO).trans
      (QuotientGroup.quotientBot (G := H))
  rcases hD with ⟨_hSylow, htwo⟩ | ⟨_hSylow, eA⟩ |
      ⟨_hSylow, F, hF, Nq, hNqnormal, hNqindex, hNqmodel⟩
  · have hHp : IsPGroup 2 H := IsPGroup.of_equiv htwo qE
    have hKp : IsPGroup 2 K := hHp.to_subgroup K
    have hH4 : 4 ≤ Nat.card H := four_le_card_of_hasDihedralSylowTwo hHd
    have hKcard2 : 2 ≤ Nat.card K := by
      have hi := K.index_mul_card
      rw [hKindex] at hi
      omega
    let hKne : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨N, hNnormal, hNindex⟩ :=
      nontrivial_two_group_has_normal_index_two hKp hKne
    exact False.elim (hKno2 N hNnormal hNindex)
  · let eH : H ≃* alternatingGroup (Fin 7) := qE.symm.trans eA.some
    exact False.elim
      (no_normal_index_two_of_mulEquiv_aSeven eH K hKnormal hKindex)
  · let N : Subgroup H := Nq.map qE.toMonoidHom
    have hNnormal : N.Normal := by
      exact hNqnormal.map qE.toMonoidHom qE.surjective
    have hNindex : Odd N.index := by
      change Odd (Nq.map (qE : H ⧸ pPrimeCore 2 H →* H)).index
      rw [Subgroup.index_map_equiv]
      exact hNqindex
    let eN : Nq ≃* N :=
      Subgroup.equivMapOfInjective Nq qE.toMonoidHom qE.injective
    rcases hNqmodel with hPSL | hPGL
    · let ePSL : N ≃* PSL2 F := eN.symm.trans hPSL.some
      have hNno2 : ∀ A : Subgroup N, A.Normal → A.index ≠ 2 :=
        no_normal_index_two_of_mulEquiv_psl2 F hF ePSL
      let : K.Normal := hKnormal
      have hNleK : N ≤ K :=
        Subgroup.le_of_no_normal_index_two N K hKindex hNno2
      have h2dvd : 2 ∣ N.index := by
        rw [← hKindex]
        exact Subgroup.index_dvd_of_le hNleK
      exact False.elim (hNindex.not_two_dvd_nat h2dvd)
    · let ePGL : N ≃* PGL2 F := eN.symm.trans hPGL.some
      let C : Subgroup N := commutator N
      let L : Subgroup H := C.map N.subtype
      have hCchar : C.Characteristic := by dsimp [C]; infer_instance
      let : N.Normal := hNnormal
      have hLnormal : L.Normal := by
        exact ConjAct.normal_of_characteristic_of_normal
      have hLmodel : Nonempty (L ≃* PSL2 F) := by
        let eCL : C ≃* L :=
          Subgroup.equivMapOfInjective C N.subtype N.subtype_injective
        exact ⟨eCL.symm.trans
          (commutator_mulEquiv_psl2_of_mulEquiv_pgl2 F hF ePGL).some⟩
      have hLno2 : ∀ A : Subgroup L, A.Normal → A.index ≠ 2 :=
        no_normal_index_two_of_mulEquiv_psl2 F hF hLmodel.some
      refine ⟨F, inferInstance, inferInstance, hF, L, hLnormal,
        hLmodel, hLno2, ?_⟩
      intro E instE finE
      let : Field E := instE
      dsimp only
      intro hE M hMnormal hMmodel
      exact unique_normal_psl2_core hHd hO K hKnormal hKindex
        F hF L hLnormal hLmodel.some E hE M hMnormal hMmodel.some

end GorensteinWalter

