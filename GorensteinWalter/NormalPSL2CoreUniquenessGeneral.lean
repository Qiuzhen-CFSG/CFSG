module

public import GorensteinWalter.PSL2CoreModelFacts
public import GorensteinWalter.NormalCenterlessDihedral
public import GorensteinWalter.PSL2DihedralSylow
public import GorensteinWalter.PSL2Center
public import GorensteinWalter.AutAlternatingFour
public import GorensteinWalter.PGroupExtension
public import Theory.GroupTheory.NoNormalIndexTwoContainment
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# Uniqueness of normal odd PSL2 cores

In an odd-core-free finite group with dihedral Sylow two-subgroups, any
two normal odd PSL2 models coincide, and their defining fields have the
same order. No ambient subgroup of index two is required.

Both models are centerless with dihedral Sylow subgroups, so their ambient
centralizers are trivial. Large models are simple: their intersection forces
equality or makes them centralize, which is impossible. A field-three model
gives a faithful conjugation embedding into the proved Aut(A4)=S4, bounding
the ambient order by 24 and excluding larger models. When both models have
order 12, their ambient indices are one or two; the no-normal-index-two
property then forces containment, and equal cardinalities give equality.
The PSL2 order formula identifies the field orders.

This generalizes the uniqueness step in Alperin--Brauer--Gorenstein,
Chapter II, Section 3, Proposition 2 (article page 22), for characteristic
powers of the generalized Q-subgroups in Lemma 2 (article pages 23--24).
The q=3 case is retained without perfectness, and no general projective
semilinear automorphism recognition is assumed. The earlier index-two
theorem remains a wrapper in NormalPSL2CoreUniqueness.
The normal-core centralizer theorem is also public for prescribed-field
semilinear embeddings: it provides faithfulness of the actual conjugation
action without a further self-centralizing hypothesis.
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

public theorem normal_psl2_centralizer_eq_bot
    {G : Type u} [Group G] [Finite G]
    (hGd : HasDihedralSylowTwo G) (hO : pPrimeCore 2 G = ⊥)
    (L : Subgroup G) (hLnormal : L.Normal)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : L ≃* PSL2 K) :
    Subgroup.centralizer (L : Set G) = ⊥ := by
  exact centralizer_eq_bot_of_normal_centerless_dihedral_of_pPrimeCore_eq_bot
    hGd hO L hLnormal
      (center_eq_bot_of_mulEquiv e (psl2_center_eq_bot K))
      (hasDihedralSylowTwo_of_mulEquiv e
        (psl2_odd_hasDihedralSylowTwo_model K hK))

private theorem normal_simple_eq_of_centralizers_eq_bot
    {G : Type u} [Group G] [Finite G]
    (A B : Subgroup G) (hAnormal : A.Normal) (hBnormal : B.Normal)
    (hAne : A ≠ ⊥)
    (hAsimple : IsSimpleGroup A) (hBsimple : IsSimpleGroup B)
    (hCB : Subgroup.centralizer (B : Set G) = ⊥) :
    A = B := by
  let IA : Subgroup A := B.subgroupOf A
  have hIAnormal : IA.Normal := by
    exact Subgroup.Normal.subgroupOf hBnormal A
  rcases hAsimple.eq_bot_or_eq_top_of_normal IA hIAnormal with hIbot | hItop
  · have hcomm : ⁅A, B⁆ = ⊥ := by
      apply le_bot_iff.mp
      have hle : ⁅A, B⁆ ≤ A ⊓ B := by
        let : A.Normal := hAnormal
        let : B.Normal := hBnormal
        exact Subgroup.commutator_le_inf A B
      intro x hx
      have hxA : x ∈ A := hle hx |>.1
      have hxB : x ∈ B := hle hx |>.2
      have hxIA : (⟨x, hxA⟩ : A) ∈ IA := hxB
      rw [hIbot] at hxIA
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hxIA)
    have hAleC : A ≤ Subgroup.centralizer (B : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    rw [hCB] at hAleC
    exact False.elim (hAne (le_bot_iff.mp hAleC))
  · have hAleB : A ≤ B := by
      intro x hx
      have hxIA : (⟨x, hx⟩ : A) ∈ IA := by rw [hItop]; trivial
      exact hxIA
    let AB : Subgroup B := A.subgroupOf B
    have hABnormal : AB.Normal := by
      exact Subgroup.Normal.subgroupOf hAnormal B
    have hABne : AB ≠ ⊥ := by
      intro hbot
      apply hAne
      apply le_bot_iff.mp
      intro x hx
      have hxAB : (⟨x, hAleB hx⟩ : B) ∈ AB := hx
      rw [hbot] at hxAB
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hxAB)
    have hABtop : AB = ⊤ :=
      (hBsimple.eq_bot_or_eq_top_of_normal AB hABnormal).resolve_left hABne
    apply le_antisymm hAleB
    intro x hx
    have hxAB : (⟨x, hx⟩ : B) ∈ AB := by rw [hABtop]; trivial
    exact hxAB

theorem unique_normal_psl2_core_of_dihedral
    {H : Type u} [Group H] [Finite H]
    (hHd : HasDihedralSylowTwo H) (hO : pPrimeCore 2 H = ⊥)
    (F : Type u) [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F))
    (L : Subgroup H) (hLnormal : L.Normal) (eL : L ≃* PSL2 F)
    (E : Type u) [Field E] [Finite E]
    (hE : IsOddPrimePower (Nat.card E))
    (M : Subgroup H) (hMnormal : M.Normal) (eM : M ≃* PSL2 E) :
    M = L ∧ Nat.card E = Nat.card F := by
  have hLno2 : ∀ N : Subgroup L, N.Normal → N.index ≠ 2 :=
    no_normal_index_two_of_mulEquiv_psl2 F hF eL
  have hLcent : Subgroup.centralizer (L : Set H) = ⊥ :=
    normal_psl2_centralizer_eq_bot hHd hO L hLnormal F hF eL
  have hLne : L ≠ ⊥ := by
    intro hbot
    have hcardL : Nat.card L = Nat.card (PSL2 F) := Nat.card_congr eL.toEquiv
    have hfour : 4 ≤ Nat.card (PSL2 F) :=
      four_le_card_of_hasDihedralSylowTwo
        (psl2_odd_hasDihedralSylowTwo_model F hF)
    rw [hbot] at hcardL
    simp at hcardL
    omega
  have hMne : M ≠ ⊥ := by
    intro hbot
    have hcardM : Nat.card M = Nat.card (PSL2 E) := Nat.card_congr eM.toEquiv
    have hfour : 4 ≤ Nat.card (PSL2 E) :=
      four_le_card_of_hasDihedralSylowTwo
        (psl2_odd_hasDihedralSylowTwo_model E hE)
    rw [hbot] at hcardM
    simp at hcardM
    omega
  by_cases hF3 : Nat.card F = 3
  · have hLcard : Nat.card L = 12 := by
      rw [Nat.card_congr eL.toEquiv, psl2_card_formula F hF, hF3]
      norm_num
    have hLcent' := hLcent
    let : L.Normal := hLnormal
    rcases quotient_centralizer_mulAut_embedding L with ⟨phi, hphi⟩
    let q : H ≃* H ⧸ Subgroup.centralizer (L : Set H) :=
      ((QuotientGroup.quotientMulEquivOfEq (G := H) hLcent').trans
        (QuotientGroup.quotientBot (G := H))).symm
    let psi : H →* MulAut L := phi.comp q.toMonoidHom
    have hpsi : Function.Injective psi := hphi.comp q.injective
    let : Fintype F := Fintype.ofFinite F
    have hFcard' : Fintype.card F = 3 := by
      simpa [Nat.card_eq_fintype_card] using hF3
    let eF : ZMod 3 ≃+* F :=
      ZMod.ringEquivOfPrime F Nat.prime_three hFcard'
    let eLA : L ≃* alternatingGroup (Fin 4) :=
      (eL.trans (psl2RingEquiv eF).symm).trans psl2_three_equiv_alternatingGroup
    let c : Equiv.Perm (Fin 4) →* MulAut (alternatingGroup (Fin 4)) :=
      MulAut.conjNormal (H := alternatingGroup (Fin 4))
    have hc : Function.Bijective c :=
      GroupTheory.AutAlternating.aut_alternatingGroup_four_bijective_conj
    let eAut : Equiv.Perm (Fin 4) ≃* MulAut (alternatingGroup (Fin 4)) :=
      MulEquiv.ofBijective c hc
    have hAutLcard : Nat.card (MulAut L) = 24 := by
      calc
        Nat.card (MulAut L) = Nat.card (MulAut (alternatingGroup (Fin 4))) :=
          Nat.card_congr (MulAut.congr eLA).toEquiv
        _ = Nat.card (Equiv.Perm (Fin 4)) := Nat.card_congr eAut.symm.toEquiv
        _ = 24 := by rw [Nat.card_perm]; norm_num [Nat.card_eq_fintype_card]
    have hHle24 : Nat.card H ≤ 24 :=
      (Nat.card_le_card_of_injective psi hpsi).trans_eq hAutLcard
    by_cases hE3 : Nat.card E = 3
    · have hMcard : Nat.card M = 12 := by
        rw [Nat.card_congr eM.toEquiv, psl2_card_formula E hE, hE3]
        norm_num
      have hMindex : M.index ≤ 2 := by
        have hprod := M.card_mul_index
        rw [hMcard] at hprod
        omega
      have hMpos : 0 < M.index := Nat.pos_of_ne_zero M.index_ne_zero_of_finite
      have hLleM : L ≤ M := by
        by_cases hi : M.index = 1
        · rw [Subgroup.index_eq_one.mp hi]
          exact le_top
        · let : M.Normal := hMnormal
          exact Subgroup.le_of_no_normal_index_two L M (by omega) hLno2
      have hML : M = L :=
        (Subgroup.eq_of_le_of_card_ge hLleM (by rw [hLcard, hMcard])).symm
      exact ⟨hML, hE3.trans hF3.symm⟩
    · have hEgt : 3 < Nat.card E := by
        have hEge := odd_prime_power_three_le _ hE
        omega
      have hM60 : 60 ≤ Nat.card M := by
        rw [Nat.card_congr eM.toEquiv]
        exact psl2_card_ge_sixty_of_card_gt_three E hE hEgt
      have hMle24 : Nat.card M ≤ 24 :=
        (Nat.le_of_dvd Nat.card_pos M.card_subgroup_dvd_card).trans hHle24
      omega
  · have hFgt : 3 < Nat.card F := by
      have hFge := odd_prime_power_three_le _ hF
      omega
    have hLsimple : IsSimpleGroup L := by
      exact (MulEquiv.isSimpleGroup_congr eL).mpr
        (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega))
    by_cases hE3 : Nat.card E = 3
    · have hMcard : Nat.card M = 12 := by
        rw [Nat.card_congr eM.toEquiv, psl2_card_formula E hE, hE3]
        norm_num
      let I : Subgroup L := M.subgroupOf L
      have hInormal : I.Normal := Subgroup.Normal.subgroupOf hMnormal L
      rcases hLsimple.eq_bot_or_eq_top_of_normal I hInormal with hIbot | hItop
      · have hcomm : ⁅M, L⁆ = ⊥ := by
          apply le_bot_iff.mp
          have hle : ⁅M, L⁆ ≤ M ⊓ L := by
            let : M.Normal := hMnormal
            let : L.Normal := hLnormal
            exact Subgroup.commutator_le_inf M L
          intro x hx
          have hxM : x ∈ M := (hle hx).1
          have hxL : x ∈ L := (hle hx).2
          have hxI : (⟨x, hxL⟩ : L) ∈ I := hxM
          rw [hIbot] at hxI
          exact congrArg Subtype.val (Subgroup.mem_bot.mp hxI)
        have hMleC : M ≤ Subgroup.centralizer (L : Set H) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
        rw [hLcent] at hMleC
        exact False.elim (hMne (le_bot_iff.mp hMleC))
      · have hLleM : L ≤ M := by
          intro x hx
          have hxI : (⟨x, hx⟩ : L) ∈ I := by rw [hItop]; trivial
          exact hxI
        have hL60 : 60 ≤ Nat.card L := by
          rw [Nat.card_congr eL.toEquiv]
          exact psl2_card_ge_sixty_of_card_gt_three F hF hFgt
        have hLle12 : Nat.card L ≤ 12 := by
          rw [← hMcard]
          exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hLleM)
        omega
    · have hEgt : 3 < Nat.card E := by
        have hEge := odd_prime_power_three_le _ hE
        omega
      have hMsimple : IsSimpleGroup M := by
        exact (MulEquiv.isSimpleGroup_congr eM).mpr
          (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega))
      have hML : M = L :=
        normal_simple_eq_of_centralizers_eq_bot M L hMnormal hLnormal
          hMne hMsimple hLsimple hLcent
      have hfield : Nat.card E = Nat.card F := by
        apply psl2_field_card_eq_of_card_eq E F hE hF
        calc
          Nat.card (PSL2 E) = Nat.card M := (Nat.card_congr eM.toEquiv).symm
          _ = Nat.card L := by rw [hML]
          _ = Nat.card (PSL2 F) := Nat.card_congr eL.toEquiv
      exact ⟨hML, hfield⟩

end GorensteinWalter
