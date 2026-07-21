/-
Authors: OpenAI
-/

module

public import BenderSuzuki.MatrixGroups.PSL2
public import FeitThompson.ElementaryAbelian
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import BenderSuzuki.External.Huppert.II.theorem_6_11
import BenderSuzuki.External.Huppert.II.theorem_6_14
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Transfer

/-!
# Huppert II.8.27

Dickson's subgroup classification for subgroups of PSL(2,p^f).
-/

namespace BenderSuzuki
namespace External

open MatrixGroups
open scoped Pointwise
open scoped LinearAlgebra.Projectivization

universe u v

/-- The field exponent in Huppert II.8.27 is nonzero. -/
public theorem huppert_II_8_27_field_exponent_ne_zero
    {F : Type u} [Field F] [Finite F] {p f : ℕ}
    (hFcard : Nat.card F = p ^ f) :
    f ≠ 0 := by
  intro hf
  subst f
  have hcard : Nat.card F = 1 := by
    simpa using hFcard
  exact (Nat.ne_of_gt (Finite.one_lt_card (α := F))) hcard

/-- Huppert II.8.2(a): every Sylow `p`-subgroup of `PSL(2,p^f)` is
isomorphic to the additive group of the defining field. -/
public theorem huppert_II_8_2_a_sylow_equiv_additive
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f)
    (Q : Sylow p (PSL2MatrixGroup F)) :
    Nonempty (Multiplicative F ≃* Q) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F p :=
    charP_of_card_eq_prime_pow (by simpa using hFcard)
  have hf_ne_zero : f ≠ 0 :=
    huppert_II_8_27_field_exponent_ne_zero hFcard
  have hcard_roots :
        Nat.card (rootsOfUnity 2 F) =
          Nat.gcd (Nat.card F - 1) 2 := by
      let e :=
        Equiv.Set.image ((↑) : Fˣ → F) (rootsOfUnity 2 F : Set Fˣ)
          Units.val_injective
      have he :
          Nat.card (rootsOfUnity 2 F) =
            Nat.card (((↑) : Fˣ → F) '' (rootsOfUnity 2 F : Set Fˣ)) :=
        Nat.card_congr e
      rw [Units.val_set_image_rootsOfUnity_two] at he
      by_cases hp_two : p = 2
      · have htwo : (2 : F) = 0 := by
          subst p
          exact CharP.cast_eq_zero F 2
        have hneg_one : (-1 : F) = 1 := by
          apply (neg_eq_iff_add_eq_zero).2
          have hone_add_one : (1 : F) + 1 = 0 := by
            rw [show (1 : F) + 1 = 2 by norm_num, htwo]
          exact hone_add_one
        have hleft : Nat.card (rootsOfUnity 2 F) = 1 := by
          simpa [hneg_one] using he
        have hq_even : Even (Nat.card F) := by
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hf_ne_zero
          rw [hFcard, hp_two, hk, pow_succ]
          use 2 ^ k
          ring
        have hq_sub_one_odd : Odd (Nat.card F - 1) := by
          rw [← Nat.not_even_iff_odd]
          intro heven
          have hparity :=
            (Nat.even_sub (show 1 ≤ Nat.card F from (Finite.one_lt_card (α := F)).le)).mp
              heven
          exact Nat.not_even_one (hparity.mp hq_even)
        have hgcd : Nat.gcd (Nat.card F - 1) 2 = 1 :=
          Nat.coprime_iff_gcd_eq_one.mp hq_sub_one_odd.coprime_two_right
        rw [hleft, hgcd]
      · have hring_char_ne_two : ringChar F ≠ 2 := by
          rw [ringChar.eq F p]
          exact hp_two
        have hneg_one : (-1 : F) ≠ 1 :=
          Ring.neg_one_ne_one_of_char_ne_two hring_char_ne_two
        have hleft : Nat.card (rootsOfUnity 2 F) = 2 := by
          simpa [hneg_one, Ne.symm hneg_one] using he
        have hq_odd : Odd (Nat.card F) := by
          rw [hFcard]
          exact ((Fact.out : p.Prime).odd_of_ne_two hp_two).pow
        have htwo_dvd : 2 ∣ Nat.card F - 1 := by
          rcases hq_odd with ⟨k, hk⟩
          use k
          omega
        have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 :=
          Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
            (Nat.dvd_gcd htwo_dvd (dvd_refl 2))
        rw [hleft, hgcd]
  have hcard_psl :
      Nat.card (PSL2MatrixGroup F) * Nat.gcd (Nat.card F - 1) 2 =
        Nat.card F * (Nat.card F ^ 2 - 1) := by
    have hcard_sl :
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
          Nat.card F * (Nat.card F ^ 2 - 1) := by
      have hdet_range_top :
          (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)).range = ⊤ := by
        ext u
        constructor
        · intro _
          simp
        · intro _
          let diagonalGL : GL (Fin 2) F :=
            Matrix.GeneralLinearGroup.mkOfDetNeZero
              (Matrix.diagonal ![(u : F), 1]) (by
                simp [Matrix.det_diagonal, Fin.prod_univ_two])
          refine ⟨diagonalGL, ?_⟩
          ext
          simp [diagonalGL, Matrix.det_diagonal, Fin.prod_univ_two]
      have hGL :
          Nat.card (GL (Fin 2) F) =
            (Nat.card F ^ 2 - 1) * (Nat.card F ^ 2 - Nat.card F) := by
        simpa [Fin.prod_univ_two] using
          (Matrix.card_GL_field (𝔽 := F) 2)
      let detHom :=
        Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)
      have hRange :
          Nat.card detHom.range = Nat.card F - 1 := by
        rw [hdet_range_top]
        simpa using (Fintype.card_units (α := F))
      have hmul :
          Nat.card detHom.range * Nat.card detHom.ker =
            Nat.card (GL (Fin 2) F) := by
        rw [← Subgroup.index_ker detHom]
        exact detHom.ker.index_mul_card
      have hker :
          Nat.card detHom.ker =
            Nat.card F * (Nat.card F ^ 2 - 1) := by
        have hq : 1 < Nat.card F := Finite.one_lt_card
        have hdiff :
            Nat.card F ^ 2 - Nat.card F =
              Nat.card F * (Nat.card F - 1) := by
          rw [pow_two]
          calc
            Nat.card F * Nat.card F - Nat.card F =
                Nat.card F * Nat.card F - Nat.card F * 1 := by simp
            _ = Nat.card F * (Nat.card F - 1) :=
              (Nat.mul_sub_left_distrib _ _ _).symm
        have hcancel :
            (Nat.card F - 1) * Nat.card detHom.ker =
              (Nat.card F - 1) *
                (Nat.card F * (Nat.card F ^ 2 - 1)) := by
          calc
            (Nat.card F - 1) * Nat.card detHom.ker =
                Nat.card (GL (Fin 2) F) := by
              rw [hRange] at hmul
              exact hmul
            _ = (Nat.card F ^ 2 - 1) *
                (Nat.card F ^ 2 - Nat.card F) := hGL
            _ = (Nat.card F - 1) *
                (Nat.card F * (Nat.card F ^ 2 - 1)) := by
              rw [hdiff]
              ring
        exact Nat.eq_of_mul_eq_mul_left
          (Nat.sub_pos_iff_lt.mpr (Finite.one_lt_card (α := F))) hcancel
      calc
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
            Nat.card detHom.ker := by
          let slEquivDetKer :
              Matrix.SpecialLinearGroup (Fin 2) F ≃ detHom.ker := by
            refine Equiv.ofBijective
              (fun A => ⟨Matrix.SpecialLinearGroup.toGL A, by
                exact Matrix.SpecialLinearGroup.coeToGL_det A⟩) ?_
            constructor
            · intro A B h
              apply Matrix.SpecialLinearGroup.toGL_injective
              exact congrArg Subtype.val h
            · intro A
              refine ⟨⟨(A : GL (Fin 2) F), ?_⟩, ?_⟩
              · have hmem := A.property
                change
                  Matrix.GeneralLinearGroup.det
                    (A : GL (Fin 2) F) = 1 at hmem
                exact Units.ext_iff.mp hmem
              · apply Subtype.ext
                apply Matrix.GeneralLinearGroup.ext
                intro i j
                rfl
          exact Nat.card_congr slEquivDetKer
        _ = Nat.card F * (Nat.card F ^ 2 - 1) := hker

    have hcard_center :
        Nat.card
            (Subgroup.center
              (Matrix.SpecialLinearGroup (Fin 2) F)) =
          Nat.gcd (Nat.card F - 1) 2 := by
      rw [Nat.card_congr
        (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'
          (R := F) (n := Fin 2) 0).toEquiv]
      simpa using hcard_roots
    calc
      Nat.card (PSL2MatrixGroup F) *
          Nat.gcd (Nat.card F - 1) 2 =
          Nat.card (PSL2MatrixGroup F) *
            Nat.card
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F)) := by
            rw [hcard_center]
      _ = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) :=
        (Subgroup.card_eq_card_quotient_mul_card_subgroup
          (Subgroup.center
            (Matrix.SpecialLinearGroup (Fin 2) F))).symm
      _ = Nat.card F * (Nat.card F ^ 2 - 1) := hcard_sl
  let unipotentSL :
      AddChar F (Matrix.SpecialLinearGroup (Fin 2) F) :=
    { toFun := fun a => ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two]⟩
      map_zero_eq_one' := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      map_add_eq_mul' := by
        intro a b
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, add_comm]
    }
  let unipotent : AddChar F (PSL2MatrixGroup F) :=
    (QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).compAddChar
        unipotentSL
  have h_unipotent_injective : Function.Injective unipotent := by
    intro a b hab
    have hdiff : unipotent (a - b) = 1 := by
      rw [sub_eq_add_neg, unipotent.map_add_eq_mul,
        unipotent.map_neg_eq_inv, hab, mul_inv_cancel]
    have hcenter :
        unipotentSL (a - b) ∈
          Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      exact (QuotientGroup.eq_one_iff (unipotentSL (a - b))).mp hdiff
    have hscalar :=
      Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hcenter (0 : Fin 2)
    have hab0 := congrFun (congrFun hscalar (0 : Fin 2)) (1 : Fin 2)
    apply sub_eq_zero.mp
    simpa using hab0.symm
  let U : Subgroup (PSL2MatrixGroup F) := unipotent.toMonoidHom.range
  have hUcard : Nat.card U = Nat.card F := by
    let e : Multiplicative F ≃ U :=
      Equiv.ofInjective unipotent.toMonoidHom h_unipotent_injective
    exact Nat.card_congr e.symm
  have hU_isPGroup : IsPGroup p U := by
    apply IsPGroup.of_card
    rw [hUcard, hFcard]
  have hU_index_not_dvd : ¬ p ∣ U.index := by
    have hindex_card : U.index * Nat.card U = Nat.card (PSL2MatrixGroup F) :=
      U.index_mul_card
    have hindex_gcd :
        U.index * Nat.gcd (Nat.card F - 1) 2 = Nat.card F ^ 2 - 1 := by
      have hmul :
          Nat.card F * (U.index * Nat.gcd (Nat.card F - 1) 2) =
            Nat.card F * (Nat.card F ^ 2 - 1) := by
        calc
          Nat.card F * (U.index * Nat.gcd (Nat.card F - 1) 2) =
              (U.index * Nat.card U) * Nat.gcd (Nat.card F - 1) 2 := by
                rw [hUcard]
                ring
          _ = Nat.card (PSL2MatrixGroup F) *
                Nat.gcd (Nat.card F - 1) 2 := by rw [hindex_card]
          _ = Nat.card F * (Nat.card F ^ 2 - 1) := hcard_psl
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hmul
    intro hp_index
    have hp_bad : p ∣ Nat.card F ^ 2 - 1 := by
      rw [← hindex_gcd]
      exact dvd_mul_of_dvd_left hp_index _
    have hf_ne_zero : f ≠ 0 :=
      huppert_II_8_27_field_exponent_ne_zero hFcard
    have hp_card : p ∣ Nat.card F := by
      rw [hFcard]
      exact dvd_pow_self p hf_ne_zero
    have hp_sq : p ∣ Nat.card F ^ 2 := dvd_pow hp_card (by norm_num)
    have hp_one : p ∣ 1 := by
      have h := Nat.dvd_sub hp_sq hp_bad
      have hpos : 0 < Nat.card F ^ 2 := pow_pos Nat.card_pos 2
      have hsub : Nat.card F ^ 2 - (Nat.card F ^ 2 - 1) = 1 := by omega
      rw [hsub] at h
      exact h
    exact (Fact.out : p.Prime).not_dvd_one hp_one
  let ambientSylow : Sylow p (PSL2MatrixGroup F) :=
    hU_isPGroup.toSylow hU_index_not_dvd
  let eU : Multiplicative F ≃* U :=
    MulEquiv.ofBijective unipotent.toMonoidHom.rangeRestrict
      ⟨by
        intro a b hab
        exact h_unipotent_injective (congrArg Subtype.val hab),
        MonoidHom.rangeRestrict_surjective _⟩
  have hAmbient : (ambientSylow : Subgroup (PSL2MatrixGroup F)) = U := rfl
  let eAmbient : Multiplicative F ≃* ambientSylow :=
    eU.trans (MulEquiv.subgroupCongr hAmbient.symm)
  obtain ⟨g, hg⟩ :=
    MulAction.exists_smul_eq
      (α := Sylow p (PSL2MatrixGroup F))
      (PSL2MatrixGroup F) ambientSylow Q
  let eConj : ambientSylow ≃*
      (g • ambientSylow : Sylow p (PSL2MatrixGroup F)) :=
    (MulAut.conj g).subgroupMap ambientSylow
  rw [hg] at eConj
  exact ⟨eAmbient.trans eConj⟩
/-- Huppert II.8.17(b): a group of order twelve with four Sylow `3`-subgroups is `A₄`. -/
public theorem huppert_II_8_17_b_order_twelve_four_sylow_three
    {G : Type u} [Group G] [Finite G]
    (hGcard : Nat.card G = 12) (hSylow : Nat.card (Sylow 3 G) = 4) :
    Nonempty (G ≃* alternatingGroup (Fin 4)) := by
  classical
  let Ω := Sylow 3 G
  letI := Fintype.ofFinite Ω
  have hΩcard : Fintype.card Ω = 4 := by
    simpa [Ω, Nat.card_eq_fintype_card] using hSylow
  have hfac12 : (Nat.factorization 12) 3 = 1 := by
    rw [show 12 = 3 * 4 by norm_num,
      Nat.factorization_mul_apply_of_coprime (by norm_num : Nat.Coprime 3 4),
      Nat.prime_three.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 4)]
  have hnormalizer_eq :
      ∀ P : Ω, Subgroup.normalizer ((P : Subgroup G) : Set G) =
        (P : Subgroup G) := by
    intro P
    have hPcard : Nat.card P = 3 := by
      rw [P.card_eq_multiplicity, hGcard]
      rw [hfac12]
      norm_num
    have hindex :
        (Subgroup.normalizer ((P : Subgroup G) : Set G)).index = 4 := by
      rw [← P.card_eq_index_normalizer, hSylow]
    have hNcard :
        Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) = 3 := by
      have hmul :=
        (Subgroup.normalizer ((P : Subgroup G) : Set G)).card_mul_index
      rw [hindex, hGcard] at hmul
      omega
    exact
      (Subgroup.eq_of_le_of_card_ge Subgroup.le_normalizer (by omega)).symm
  let act := MulAction.toPermHom G Ω
  have hker_le : ∀ P : Ω, act.ker ≤ (P : Subgroup G) := by
    intro P x hx
    have hxperm : act x = 1 := hx
    have hxfix : x • P = P := by
      have h := DFunLike.congr_fun hxperm P
      simpa [act] using h
    have hxstab : x ∈ MulAction.stabilizer G P := hxfix
    rw [Sylow.stabilizer_eq_normalizer, hnormalizer_eq P] at hxstab
    exact hxstab
  have hact_inj : Function.Injective act := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    let P : Ω := default
    obtain ⟨Q, hQP⟩ :=
      Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card Ω) P
    have hxP : x ∈ (P : Subgroup G) := hker_le P hx
    have hxQ : x ∈ (Q : Subgroup G) := hker_le Q hx
    by_contra hxone
    let I : Subgroup G := (P : Subgroup G) ⊓ (Q : Subgroup G)
    have hxI : x ∈ I := ⟨hxP, hxQ⟩
    have hIcard_ne_one : Nat.card I ≠ 1 := by
      intro hIcard
      have hIbot : I = ⊥ := Subgroup.card_eq_one.mp hIcard
      rw [hIbot, Subgroup.mem_bot] at hxI
      exact hxone hxI
    have hPcard : Nat.card P = 3 := by
      rw [P.card_eq_multiplicity, hGcard]
      rw [hfac12]
      norm_num
    have hQcard : Nat.card Q = 3 := by
      rw [Q.card_eq_multiplicity, hGcard]
      rw [hfac12]
      norm_num
    have hIdivP : Nat.card I ∣ Nat.card P := by
      rw [← Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (show I ≤ (P : Subgroup G) from inf_le_left)).toEquiv]
      exact Subgroup.card_subgroup_dvd_card (I.subgroupOf (P : Subgroup G))
    have hIcard : Nat.card I = 3 := by
      have hdiv3 : Nat.card I ∣ 3 := by simpa [hPcard] using hIdivP
      rcases (Nat.dvd_prime Nat.prime_three).mp hdiv3 with h | h
      · exact (hIcard_ne_one h).elim
      · exact h
    have hIP : I = (P : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    have hIQ : I = (Q : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
    apply hQP
    exact Sylow.ext (hIQ.symm.trans hIP)
  let eΩ : Ω ≃ Fin 4 := Fintype.equivFinOfCardEq hΩcard
  let actFin : G →* Equiv.Perm (Fin 4) :=
    (Equiv.permCongrHom eΩ).toMonoidHom.comp act
  have hactFin_inj : Function.Injective actFin := by
    intro x y hxy
    apply hact_inj
    apply (Equiv.permCongrHom eΩ).injective
    simpa [actFin] using hxy
  let K : Subgroup (Equiv.Perm (Fin 4)) := actFin.range
  have hrange_inj : Function.Injective actFin.rangeRestrict := by
    intro x y hxy
    exact hactFin_inj (congrArg Subtype.val hxy)
  let eRange : G ≃* K :=
    MulEquiv.ofBijective actFin.rangeRestrict
      ⟨hrange_inj, MonoidHom.rangeRestrict_surjective actFin⟩
  have hKcard : Nat.card K = 12 := by
    rw [← Nat.card_congr eRange.toEquiv, hGcard]
  have hpermcard : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    rfl
  have hKindex : K.index = 2 := by
    have hmul := K.index_mul_card
    rw [hKcard, hpermcard] at hmul
    omega
  have hKalt : K = alternatingGroup (Fin 4) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hKindex
  exact ⟨eRange.trans (MulEquiv.subgroupCongr hKalt)⟩

/-- Huppert II.8.17(c): a group of order twenty-four with four Sylow
`3`-subgroups and trivial center is `S₄`. -/
public theorem huppert_II_8_17_c_order_twenty_four_four_sylow_three
    {G : Type u} [Group G] [Finite G]
    (hGcard : Nat.card G = 24) (hSylow : Nat.card (Sylow 3 G) = 4)
    (hcenter : Subgroup.center G = ⊥) :
    Nonempty (G ≃* Equiv.Perm (Fin 4)) := by
  classical
  let Ω := Sylow 3 G
  letI := Fintype.ofFinite Ω
  have hΩcard : Fintype.card Ω = 4 := by
    simpa [Ω, Nat.card_eq_fintype_card] using hSylow
  let act := MulAction.toPermHom G Ω
  have hnormalizer_card (P : Ω) :
      Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) = 6 := by
    have hindex :
        (Subgroup.normalizer ((P : Subgroup G) : Set G)).index = 4 := by
      rw [← P.card_eq_index_normalizer, hSylow]
    have hmul :=
      (Subgroup.normalizer ((P : Subgroup G) : Set G)).card_mul_index
    rw [hindex, hGcard] at hmul
    omega
  have hker_le_normalizer (P : Ω) :
      act.ker ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) := by
    intro x hx
    have hxperm : act x = 1 := hx
    have hxfix : x • P = P := by
      have h := DFunLike.congr_fun hxperm P
      simpa [act] using h
    exact Sylow.smul_eq_iff_mem_normalizer.mp hxfix
  have hthree_not_dvd_ker : ¬ 3 ∣ Nat.card act.ker := by
    intro hthree
    obtain ⟨x, hxorder⟩ := exists_prime_orderOf_dvd_card' 3 hthree
    have hxGorder : orderOf (x : G) = 3 :=
      (Subgroup.orderOf_coe x).trans hxorder
    have hXp : IsPGroup 3 (Subgroup.zpowers (x : G)) :=
      IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, hxGorder, pow_one])
    obtain ⟨P, hXP⟩ := hXp.exists_le_sylow
    obtain ⟨Q, hQP⟩ :=
      Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card Ω) P
    have hfac24 : (Nat.factorization 24) 3 = 1 := by
      have hle : 1 ≤ (Nat.factorization 24) 3 :=
        ((by decide : Nat.Prime 3).pow_dvd_iff_le_factorization
          (by norm_num)).mp (by norm_num)
      have hnle : ¬ 2 ≤ (Nat.factorization 24) 3 := by
        intro h
        have hdvd :=
          ((by decide : Nat.Prime 3).pow_dvd_iff_le_factorization
            (by norm_num)).mpr h
        norm_num at hdvd
      omega
    have hPcard : Nat.card P = 3 := by
      rw [P.card_eq_multiplicity, hGcard, hfac24]
      norm_num
    have hPker : (P : Subgroup G) ≤ act.ker := by
      have hXcard : Nat.card (Subgroup.zpowers (x : G)) = 3 := by
        rw [Nat.card_zpowers, hxGorder]
      have hXP_eq :
          Subgroup.zpowers (x : G) = (P : Subgroup G) :=
        Subgroup.eq_of_le_of_card_ge hXP (by rw [hXcard, hPcard])
      rw [← hXP_eq]
      intro y hy
      rcases hy with ⟨n, rfl⟩
      exact act.ker.zpow_mem x.2 n
    have hPnormalizesQ :
        (P : Subgroup G) ≤ Subgroup.normalizer ((Q : Subgroup G) : Set G) :=
      fun y hy => hker_le_normalizer Q (hPker hy)
    have hsupP :
        IsPGroup 3 ((P : Subgroup G) ⊔ (Q : Subgroup G) : Subgroup G) :=
      P.isPGroup'.to_sup_of_normal_right' Q.isPGroup' hPnormalizesQ
    have hsup_eq :
        (P : Subgroup G) ⊔ (Q : Subgroup G) = (Q : Subgroup G) :=
      Q.is_maximal' hsupP le_sup_right
    have hPleQ : (P : Subgroup G) ≤ Q := by
      rw [← hsup_eq]
      exact le_sup_left
    have hP_eq_Q : (P : Subgroup G) = Q :=
      Subgroup.eq_of_le_of_card_ge hPleQ (by
        rw [Nat.card_congr (Sylow.equiv P Q).toEquiv])
    exact hQP (Sylow.ext hP_eq_Q.symm)
  have hker_card_dvd_six : Nat.card act.ker ∣ 6 := by
    let P : Ω := default
    simpa [hnormalizer_card P] using
      Subgroup.card_dvd_of_le (hker_le_normalizer P)
  have hker_card_cases : Nat.card act.ker = 1 ∨ Nat.card act.ker = 2 := by
    have hpos : 0 < Nat.card act.ker := Nat.card_pos
    have hle : Nat.card act.ker ≤ 6 :=
      Nat.le_of_dvd (by norm_num) hker_card_dvd_six
    interval_cases Nat.card act.ker <;> norm_num at *
  have hker_bot : act.ker = ⊥ := by
    rcases hker_card_cases with hone | htwo
    · exact Subgroup.card_eq_one.mp hone
    · exfalso
      obtain ⟨z, hz_ne, hz_unique⟩ :=
        (Nat.card_eq_two_iff' (1 : act.ker)).mp htwo
      have hz_center : (z : G) ∈ Subgroup.center G := by
        rw [Subgroup.mem_center_iff]
        intro g
        let zg : act.ker :=
          ⟨g * (z : G) * g⁻¹,
            (inferInstance : act.ker.Normal).conj_mem (z : G) z.2 g⟩
        have hzg_ne : zg ≠ 1 := by
          intro hzg
          have hval := congrArg Subtype.val hzg
          change g * (z : G) * g⁻¹ = 1 at hval
          apply hz_ne
          apply Subtype.ext
          calc
            (z : G) = g⁻¹ * (g * (z : G) * g⁻¹) * g := by group
            _ = 1 := by rw [hval]; simp
        have hzg_eq : zg = z := hz_unique zg hzg_ne
        have hval := congrArg Subtype.val hzg_eq
        change g * (z : G) * g⁻¹ = (z : G) at hval
        calc
          g * (z : G) = (g * (z : G) * g⁻¹) * g := by group
          _ = (z : G) * g := by rw [hval]
      have hz_bot : (z : G) ∈ (⊥ : Subgroup G) := by
        rw [← hcenter]
        exact hz_center
      apply hz_ne
      apply Subtype.ext
      simpa using hz_bot
  have hact_inj : Function.Injective act := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact hker_bot
  let eΩ : Ω ≃ Fin 4 := Fintype.equivFinOfCardEq hΩcard
  let actFin : G →* Equiv.Perm (Fin 4) :=
    (Equiv.permCongrHom eΩ).toMonoidHom.comp act
  have hactFin_inj : Function.Injective actFin := by
    intro x y hxy
    apply hact_inj
    apply (Equiv.permCongrHom eΩ).injective
    simpa [actFin] using hxy
  let K : Subgroup (Equiv.Perm (Fin 4)) := actFin.range
  let eRange : G ≃* K :=
    MulEquiv.ofBijective actFin.rangeRestrict
      ⟨fun x y hxy => hactFin_inj (congrArg Subtype.val hxy),
        MonoidHom.rangeRestrict_surjective actFin⟩
  have hKcard : Nat.card K = 24 := by
    rw [← Nat.card_congr eRange.toEquiv, hGcard]
  have hpermcard : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    norm_num [Fintype.card_perm, Nat.factorial]
  have hKtop : K = ⊤ :=
    Subgroup.eq_top_of_card_eq (H := K) (hKcard.trans hpermcard.symm)
  exact ⟨eRange.trans (MulEquiv.subgroupCongr hKtop) |>.trans
    (Subgroup.topEquiv :
      (⊤ : Subgroup (Equiv.Perm (Fin 4))) ≃* Equiv.Perm (Fin 4))⟩
private theorem hsplit_matrix_diag_or_antidiag
    {F : Type u} [Field F]
    (A : Matrix.SpecialLinearGroup (Fin 2) F) (a b : Fˣ) (r : F)
    (ha_ne_inv : (a : F) ≠ (a⁻¹ : F))
    (heq :
      !![(b : F), 0; 0, (b⁻¹ : F)] * Matrix.scalar (Fin 2) r *
          (A : Matrix (Fin 2) (Fin 2) F) =
        (A : Matrix (Fin 2) (Fin 2) F) *
          !![(a : F), 0; 0, (a⁻¹ : F)]) :
    (A 0 1 = 0 ∧ A 1 0 = 0) ∨
      (A 0 0 = 0 ∧ A 1 1 = 0) := by
  have h00 := congrFun (congrFun heq (0 : Fin 2)) (0 : Fin 2)
  have h01 := congrFun (congrFun heq (0 : Fin 2)) (1 : Fin 2)
  have h10 := congrFun (congrFun heq (1 : Fin 2)) (0 : Fin 2)
  have h11 := congrFun (congrFun heq (1 : Fin 2)) (1 : Fin 2)
  simp [Matrix.mul_apply] at h00 h01 h10 h11
  by_cases hA00 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 0
  · right
    refine ⟨hA00, ?_⟩
    have hdet := A.property
    rw [Matrix.det_fin_two, hA00, zero_mul, zero_sub] at hdet
    have hA01 : A 0 1 ≠ 0 := by
      intro h
      rw [h, zero_mul, neg_zero] at hdet
      exact zero_ne_one hdet
    have hA10 : A 1 0 ≠ 0 := by
      intro h
      rw [h, mul_zero, neg_zero] at hdet
      exact zero_ne_one hdet
    have hbinvr_a : (b⁻¹ : F) * r = (a : F) := by
      apply mul_right_cancel₀ hA10
      simpa [mul_assoc, mul_comm] using h10
    by_contra hA11
    have hbinvr_ainv : (b⁻¹ : F) * r = (a⁻¹ : F) := by
      apply mul_right_cancel₀ hA11
      simpa [mul_assoc, mul_comm] using h11
    exact ha_ne_inv (hbinvr_a.symm.trans hbinvr_ainv)
  · left
    have hbr_a : (b : F) * r = (a : F) := by
      apply mul_right_cancel₀ hA00
      simpa [mul_assoc, mul_comm] using h00
    have hA01 : A 0 1 = 0 := by
      by_contra hA01
      have hbr_ainv : (b : F) * r = (a⁻¹ : F) := by
        apply mul_right_cancel₀ hA01
        simpa [mul_assoc, mul_comm] using h01
      exact ha_ne_inv (hbr_a.symm.trans hbr_ainv)
    refine ⟨hA01, ?_⟩
    have hdet := A.property
    rw [Matrix.det_fin_two, hA01, zero_mul, sub_zero] at hdet
    have hA11 : A 1 1 ≠ 0 := by
      intro h
      rw [h, mul_zero] at hdet
      exact zero_ne_one hdet
    have hbinvr_ainv : (b⁻¹ : F) * r = (a⁻¹ : F) := by
      apply mul_right_cancel₀ hA11
      simpa [mul_assoc, mul_comm] using h11
    by_contra hA10
    have hbinvr_a : (b⁻¹ : F) * r = (a : F) := by
      apply mul_right_cancel₀ hA10
      simpa [mul_assoc, mul_comm] using h10
    exact ha_ne_inv (hbinvr_a.symm.trans hbinvr_ainv)

set_option maxHeartbeats 800000 in
/-- Huppert II.8.3(a,c), retaining the Weyl reflection and its inversion
action on the standard split torus. -/
public theorem huppert_II_8_3_split_torus_reflection_data
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) :
    ∃ U : Subgroup (PSL2MatrixGroup F),
      ∃ w : PSL2MatrixGroup F,
      IsCyclic U ∧
      Nat.card U =
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      w ∈ Subgroup.normalizer (U : Set (PSL2MatrixGroup F)) ∧
      w ∉ U ∧
      w * w = 1 ∧
      (∀ t : PSL2MatrixGroup F, t ∈ U → w * t * w⁻¹ = t⁻¹) ∧
      Nat.card (U ⊔ Subgroup.zpowers w :
        Subgroup (PSL2MatrixGroup F)) = 2 * Nat.card U ∧
      ∀ R : Subgroup (PSL2MatrixGroup F), R ≤ U → R ≠ ⊥ →
        Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) =
          U ⊔ Subgroup.zpowers w := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F p :=
    charP_of_card_eq_prime_pow (by simpa using hFcard)
  have hf_ne_zero : f ≠ 0 :=
    huppert_II_8_27_field_exponent_ne_zero hFcard
  have hcard_roots :
        Nat.card (rootsOfUnity 2 F) =
          Nat.gcd (Nat.card F - 1) 2 := by
      let e :=
        Equiv.Set.image ((↑) : Fˣ → F) (rootsOfUnity 2 F : Set Fˣ)
          Units.val_injective
      have he :
          Nat.card (rootsOfUnity 2 F) =
            Nat.card (((↑) : Fˣ → F) '' (rootsOfUnity 2 F : Set Fˣ)) :=
        Nat.card_congr e
      rw [Units.val_set_image_rootsOfUnity_two] at he
      by_cases hp_two : p = 2
      · have htwo : (2 : F) = 0 := by
          subst p
          exact CharP.cast_eq_zero F 2
        have hneg_one : (-1 : F) = 1 := by
          apply (neg_eq_iff_add_eq_zero).2
          have hone_add_one : (1 : F) + 1 = 0 := by
            rw [show (1 : F) + 1 = 2 by norm_num, htwo]
          exact hone_add_one
        have hleft : Nat.card (rootsOfUnity 2 F) = 1 := by
          simpa [hneg_one] using he
        have hq_even : Even (Nat.card F) := by
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hf_ne_zero
          rw [hFcard, hp_two, hk, pow_succ]
          use 2 ^ k
          ring
        have hq_sub_one_odd : Odd (Nat.card F - 1) := by
          rw [← Nat.not_even_iff_odd]
          intro heven
          have hparity :=
            (Nat.even_sub (show 1 ≤ Nat.card F from (Finite.one_lt_card (α := F)).le)).mp
              heven
          exact Nat.not_even_one (hparity.mp hq_even)
        have hgcd : Nat.gcd (Nat.card F - 1) 2 = 1 :=
          Nat.coprime_iff_gcd_eq_one.mp hq_sub_one_odd.coprime_two_right
        rw [hleft, hgcd]
      · have hring_char_ne_two : ringChar F ≠ 2 := by
          rw [ringChar.eq F p]
          exact hp_two
        have hneg_one : (-1 : F) ≠ 1 :=
          Ring.neg_one_ne_one_of_char_ne_two hring_char_ne_two
        have hleft : Nat.card (rootsOfUnity 2 F) = 2 := by
          simpa [hneg_one, Ne.symm hneg_one] using he
        have hq_odd : Odd (Nat.card F) := by
          rw [hFcard]
          exact ((Fact.out : p.Prime).odd_of_ne_two hp_two).pow
        have htwo_dvd : 2 ∣ Nat.card F - 1 := by
          rcases hq_odd with ⟨k, hk⟩
          use k
          omega
        have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 :=
          Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
            (Nat.dvd_gcd htwo_dvd (dvd_refl 2))
        rw [hleft, hgcd]
  let splitTorusSL : Fˣ →* Matrix.SpecialLinearGroup (Fin 2) F :=
    { toFun := fun a => ⟨!![(a : F), 0; 0, (a⁻¹ : F)], by
        simp [Matrix.det_fin_two]⟩
      map_one' := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, mul_comm] }
  let splitTorus : Fˣ →* PSL2MatrixGroup F :=
    (QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).comp splitTorusSL
  have hsplit_mem_ker_iff (a : Fˣ) :
      a ∈ splitTorus.ker ↔ a ∈ rootsOfUnity 2 F := by
    rw [MonoidHom.mem_ker, mem_rootsOfUnity]
    constructor
    · intro ha
      have hcenter :
          splitTorusSL a ∈
            Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
        (QuotientGroup.eq_one_iff (splitTorusSL a)).mp ha
      have hscalar :=
        Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hcenter (0 : Fin 2)
      have ha_inv_val := congrFun (congrFun hscalar (1 : Fin 2)) (1 : Fin 2)
      have ha_inv : a = a⁻¹ := by
        apply Units.ext
        simpa [splitTorusSL] using ha_inv_val
      simpa [pow_two] using (eq_inv_iff_mul_eq_one.mp ha_inv)
    · intro ha
      apply (QuotientGroup.eq_one_iff (splitTorusSL a)).mpr
      rw [Matrix.SpecialLinearGroup.mem_center_iff]
      refine ⟨(a : F), ?_, ?_⟩
      · simpa using congrArg Units.val ha
      · have ha_inv : a = a⁻¹ :=
          eq_inv_iff_mul_eq_one.mpr (by simpa [pow_two] using ha)
        have ha_inv_val : (a : F) = (a⁻¹ : F) := by
          simpa using congrArg Units.val ha_inv
        change Matrix.scalar (Fin 2) (a : F) =
          !![(a : F), 0; 0, (a⁻¹ : F)]
        ext i j
        fin_cases i <;> fin_cases j
        · rfl
        · rfl
        · rfl
        · exact ha_inv_val
  have hsplit_ker_eq : splitTorus.ker = rootsOfUnity 2 F := by
    ext a
    exact hsplit_mem_ker_iff a
  have hsplit_ker_card :
      Nat.card splitTorus.ker = Nat.gcd (Nat.card F - 1) 2 := by
    rw [hsplit_ker_eq, hcard_roots]
  have hsplit_range_mul :
      Nat.card splitTorus.range * Nat.gcd (Nat.card F - 1) 2 =
        Nat.card F - 1 := by
    calc
      Nat.card splitTorus.range * Nat.gcd (Nat.card F - 1) 2 =
          splitTorus.ker.index * Nat.card splitTorus.ker := by
        rw [Subgroup.index_ker, hsplit_ker_card]
      _ = Nat.card Fˣ := splitTorus.ker.index_mul_card
      _ = Nat.card F - 1 := by
        simpa [Nat.card_eq_fintype_card] using (Fintype.card_units (α := F))
  have hsplit_range_card :
      Nat.card splitTorus.range =
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 := by
    apply Nat.eq_div_of_mul_eq_left
    · rw [← hcard_roots]
      exact Nat.ne_of_gt Nat.card_pos
    · exact hsplit_range_mul
  have hsplit_range_cyclic : IsCyclic splitTorus.range := by
    have hUnitsCyclic : IsCyclic Fˣ := by
      letI : IsCyclic (⊤ : Subgroup Fˣ) := isCyclic_subgroup_units ⊤
      exact isCyclic_of_surjective
        ((⊤ : Subgroup Fˣ).subtype) (by
          intro a
          exact ⟨⟨a, Subgroup.mem_top a⟩, rfl⟩)
    letI : IsCyclic Fˣ := hUnitsCyclic
    exact isCyclic_of_surjective splitTorus.rangeRestrict
      splitTorus.rangeRestrict_surjective
  let qSL : Matrix.SpecialLinearGroup (Fin 2) F →* PSL2MatrixGroup F :=
    QuotientGroup.mk' (Subgroup.center
      (Matrix.SpecialLinearGroup (Fin 2) F))
  let splitWeylSL : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
  let splitWeyl : PSL2MatrixGroup F := qSL splitWeylSL
  have hsplitWeylSL_inv :
      splitWeylSL⁻¹ =
        (⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩ :
          Matrix.SpecialLinearGroup (Fin 2) F) := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_inv]
    simp [splitWeylSL, Matrix.adjugate_fin_two]
  have hsplitWeylSL_conj (a : Fˣ) :
      splitWeylSL * splitTorusSL a * splitWeylSL⁻¹ =
        splitTorusSL a⁻¹ := by
    rw [hsplitWeylSL_inv]
    apply Subtype.ext
    change ((splitWeylSL : Matrix (Fin 2) (Fin 2) F) *
        (splitTorusSL a : Matrix (Fin 2) (Fin 2) F) *
          ((⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩ :
            Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) =
      (splitTorusSL a⁻¹ : Matrix (Fin 2) (Fin 2) F)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [splitWeylSL, splitTorusSL, Matrix.mul_apply]
  have hsplitWeylSL_sq_center :
      splitWeylSL * splitWeylSL ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨-1, by simp, ?_⟩
    change Matrix.scalar (Fin 2) (-1 : F) =
      ((splitWeylSL : Matrix (Fin 2) (Fin 2) F) *
        (splitWeylSL : Matrix (Fin 2) (Fin 2) F))
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [splitWeylSL, Matrix.mul_apply]
  have hsplitWeyl_sq : splitWeyl * splitWeyl = 1 := by
    change qSL splitWeylSL * qSL splitWeylSL = 1
    rw [← map_mul]
    change QuotientGroup.mk (splitWeylSL * splitWeylSL) =
      QuotientGroup.mk 1
    apply Quotient.sound
    change QuotientGroup.leftRel
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
        (splitWeylSL * splitWeylSL) 1
    rw [QuotientGroup.leftRel_eq]
    simpa using
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)).inv_mem
        hsplitWeylSL_sq_center
  have hsplitWeyl_inv : splitWeyl⁻¹ = splitWeyl := by
    calc
      splitWeyl⁻¹ = splitWeyl⁻¹ * 1 := (mul_one _).symm
      _ = splitWeyl⁻¹ * (splitWeyl * splitWeyl) := by
        rw [hsplitWeyl_sq]
      _ = splitWeyl := by
        rw [← mul_assoc]
        simp
  have hsplitWeyl_conj (a : Fˣ) :
      splitWeyl * splitTorus a * splitWeyl⁻¹ =
        splitTorus a⁻¹ := by
    have hqWsq : qSL (splitWeylSL * splitWeylSL) = 1 := by
      change QuotientGroup.mk (splitWeylSL * splitWeylSL) =
        QuotientGroup.mk 1
      apply Quotient.sound
      change QuotientGroup.leftRel
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
          (splitWeylSL * splitWeylSL) 1
      rw [QuotientGroup.leftRel_eq]
      simpa using
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)).inv_mem
          hsplitWeylSL_sq_center
    have hsource :
        splitWeylSL * splitTorusSL a * splitWeylSL =
          (splitWeylSL * splitTorusSL a * splitWeylSL⁻¹) *
            (splitWeylSL * splitWeylSL) := by
      group
    rw [hsplitWeyl_inv]
    change qSL splitWeylSL * qSL (splitTorusSL a) *
        qSL splitWeylSL = qSL (splitTorusSL a⁻¹)
    calc
      qSL splitWeylSL * qSL (splitTorusSL a) *
          qSL splitWeylSL =
          qSL (splitWeylSL * splitTorusSL a * splitWeylSL) := by
            rw [map_mul, map_mul]
      _ = qSL ((splitWeylSL * splitTorusSL a * splitWeylSL⁻¹) *
            (splitWeylSL * splitWeylSL)) :=
        congrArg qSL hsource
      _ = qSL (splitTorusSL a⁻¹ *
            (splitWeylSL * splitWeylSL)) := by
        rw [hsplitWeylSL_conj]
      _ = qSL (splitTorusSL a⁻¹) *
            qSL (splitWeylSL * splitWeylSL) := by rw [map_mul]
      _ = qSL (splitTorusSL a⁻¹) := by rw [hqWsq, mul_one]
  have hsplitWeyl_not_mem : splitWeyl ∉ splitTorus.range := by
    rintro ⟨a, ha⟩
    change qSL (splitTorusSL a) = qSL splitWeylSL at ha
    rcases (QuotientGroup.mk'_eq_mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).mp ha with
      ⟨z, hz, hzeq⟩
    have hscalar :=
      Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center
        hz (0 : Fin 2)
    have hmat := congrArg Subtype.val hzeq
    change (splitTorusSL a : Matrix (Fin 2) (Fin 2) F) *
        (z : Matrix (Fin 2) (Fin 2) F) =
      (splitWeylSL : Matrix (Fin 2) (Fin 2) F) at hmat
    rw [← hscalar] at hmat
    have h01 := congrFun (congrFun hmat (0 : Fin 2)) (1 : Fin 2)
    have hneg_one_zero : (-1 : F) = 0 := by
      simpa [splitTorusSL, splitWeylSL, Matrix.mul_apply] using h01.symm
    exact one_ne_zero (neg_eq_zero.mp hneg_one_zero)
  have hsplitWeyl_mem_normalizer :
      splitWeyl ∈
        Subgroup.normalizer (splitTorus.range : Set (PSL2MatrixGroup F)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a⁻¹, (hsplitWeyl_conj a).symm⟩
    · rintro ⟨a, ha⟩
      refine ⟨a⁻¹, ?_⟩
      calc
        splitTorus a⁻¹ =
            splitWeyl⁻¹ *
              (splitWeyl * splitTorus a⁻¹ * splitWeyl⁻¹) *
                splitWeyl := by group
        _ = splitWeyl⁻¹ * splitTorus a * splitWeyl := by
          rw [hsplitWeyl_conj]
          group
        _ = y := by rw [ha]; group
  have hreflection_candidate_data
      (T : Subgroup (PSL2MatrixGroup F)) (w : PSL2MatrixGroup F)
      (hw_normalizer : w ∈ Subgroup.normalizer (T : Set _))
      (hw_sq : w * w = 1) (hw_not_mem : w ∉ T) :
      Nat.card (Subgroup.zpowers w) = 2 ∧
        Disjoint T (Subgroup.zpowers w) ∧
        Nat.card (T ⊔ (Subgroup.zpowers w : Subgroup (PSL2MatrixGroup F)) : Subgroup (PSL2MatrixGroup F)) = 2 * Nat.card T := by
    dsimp
    let Z : Subgroup (PSL2MatrixGroup F) := Subgroup.zpowers w
    have hw_ne_one : w ≠ 1 := by
      intro hw_one
      apply hw_not_mem
      rw [hw_one]
      exact Subgroup.one_mem T
    have hw_zpowers_card : Nat.card Z = 2 := by
      change Nat.card (Subgroup.zpowers w) = 2
      rw [Nat.card_zpowers]
      have hw_pow : w ^ 2 = 1 := by
        simpa [pow_two] using hw_sq
      have hord_dvd : orderOf w ∣ 2 :=
        orderOf_dvd_of_pow_eq_one hw_pow
      rcases (Nat.dvd_prime Nat.prime_two).mp hord_dvd with hord | hord
      · exact False.elim (hw_ne_one (orderOf_eq_one_iff.mp hord))
      · exact hord
    have hdisjoint : Disjoint T Z := by
      let R : Subgroup Z := T.comap Z.subtype
      letI : Fact (Nat.card Z).Prime := ⟨by
        rw [show Nat.card Z = 2 by exact hw_zpowers_card]
        exact Nat.prime_two⟩
      rcases R.eq_bot_or_eq_top_of_prime_card with hR | hR
      · rw [disjoint_iff, eq_bot_iff]
        intro x hx
        have hxR : (⟨x, hx.2⟩ : Z) ∈ R := hx.1
        rw [hR] at hxR
        have hxone : (⟨x, hx.2⟩ : Z) = 1 := by simpa using hxR
        exact congrArg Subtype.val hxone
      · exfalso
        apply hw_not_mem
        have hwR : (⟨w, Subgroup.mem_zpowers w⟩ : Z) ∈ R := by
          rw [hR]
          simp
        exact hwR
    let D : Subgroup (PSL2MatrixGroup F) := T ⊔ Z
    have hD_le_normalizer : D ≤ Subgroup.normalizer (T : Set _) := by
      apply sup_le Subgroup.le_normalizer
      exact Subgroup.zpowers_le.2 hw_normalizer
    let TD : Subgroup D := T.subgroupOf D
    let ZD : Subgroup D := Z.subgroupOf D
    letI : TD.Normal := by
      change (T.subgroupOf D).Normal
      exact Subgroup.normal_subgroupOf_of_le_normalizer hD_le_normalizer
    have hTDZD : Disjoint TD ZD := by
      rw [disjoint_iff, eq_bot_iff]
      intro x hx
      have hxAmbient : (x : PSL2MatrixGroup F) ∈ T ⊓ Z := by
        change (x : PSL2MatrixGroup F) ∈ T ∧ (x : PSL2MatrixGroup F) ∈ Z
        exact ⟨hx.1, hx.2⟩
      have hxone : (x : PSL2MatrixGroup F) = 1 := by
        rw [hdisjoint.eq_bot] at hxAmbient
        simpa using hxAmbient
      apply Subtype.ext
      exact hxone
    have hsup : TD ⊔ ZD = ⊤ := by
      change T.subgroupOf D ⊔ Z.subgroupOf D = ⊤
      rw [← Subgroup.subgroupOf_sup (show T ≤ D from le_sup_left)
        (show Z ≤ D from le_sup_right)]
      exact Subgroup.subgroupOf_self D
    have hZD_le_normalizer : ZD ≤ Subgroup.normalizer (TD : Set D) := by
      rw [Subgroup.normalizer_eq_top TD]
      exact le_top
    have hmul : (ZD : Set D) * (TD : Set D) = Set.univ := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right ZD TD
        hZD_le_normalizer, sup_comm, hsup]
      rfl
    have hcomp : ZD.IsComplement' TD :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hTDZD.symm hmul
    have hZDcard : Nat.card ZD = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show Z ≤ D from le_sup_right)).toEquiv
    have hTDcard : Nat.card TD = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show T ≤ D from le_sup_left)).toEquiv
    refine ⟨hw_zpowers_card, hdisjoint, ?_⟩
    calc
      Nat.card (T ⊔ Z : Subgroup (PSL2MatrixGroup F)) = Nat.card D := rfl
      _ = Nat.card ZD * Nat.card TD := hcomp.card_mul.symm
      _ = 2 * Nat.card T := by
        rw [hZDcard, hTDcard, hw_zpowers_card]
  let splitWeylZ : Subgroup (PSL2MatrixGroup F) := Subgroup.zpowers splitWeyl
  rcases hreflection_candidate_data splitTorus.range splitWeyl
      hsplitWeyl_mem_normalizer hsplitWeyl_sq hsplitWeyl_not_mem with
    ⟨hsplitWeyl_zpowers_card, hsplit_torus_zpowers_disjoint,
      hsplitCandidate_card_raw⟩
  have hsplitCandidate_card :
      Nat.card (splitTorus.range ⊔ splitWeylZ : Subgroup (PSL2MatrixGroup F)) =
        2 * ((Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) := by
    have hraw :
        Nat.card (splitTorus.range ⊔ splitWeylZ : Subgroup (PSL2MatrixGroup F)) =
          2 * Nat.card splitTorus.range := by
      simpa [splitWeylZ] using hsplitCandidate_card_raw
    rw [hsplit_range_card] at hraw
    exact hraw
  have hsplit_normalizer_sub_candidate
      (R : Subgroup (PSL2MatrixGroup F))
      (hR_le : R ≤ splitTorus.range) (hR_ne : R ≠ ⊥) :
      Subgroup.normalizer (R : Set _) ≤
        splitTorus.range ⊔ splitWeylZ := by
    obtain ⟨r, hr_ne_one⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp hR_ne
    rcases hR_le r.property with ⟨a, ha⟩
    have ha_not_ker : a ∉ splitTorus.ker := by
      intro hak
      apply hr_ne_one
      apply Subtype.ext
      change (r : PSL2MatrixGroup F) = 1
      rw [← ha]
      exact hak
    have ha_ne_inv : (a : F) ≠ (a⁻¹ : F) := by
      intro hai
      apply ha_not_ker
      apply (hsplit_mem_ker_iff a).2
      rw [mem_rootsOfUnity]
      have haiU : a = a⁻¹ := by
        apply Units.ext
        simpa using hai
      simpa [pow_two] using (eq_inv_iff_mul_eq_one.mp haiU)
    intro g
    refine QuotientGroup.induction_on g ?_
    intro A hA_normalizes
    have hr_conj_R :
        qSL A * (r : PSL2MatrixGroup F) * (qSL A)⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hA_normalizes
        (r : PSL2MatrixGroup F)).mp r.property
    rcases hR_le hr_conj_R with ⟨b, hb⟩
    have hq :
        qSL (splitTorusSL b) = qSL (A * splitTorusSL a * A⁻¹) := by
      simpa [splitTorus, qSL, ← ha] using hb
    rcases (QuotientGroup.mk'_eq_mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).mp hq with
      ⟨z, hz, hzeq⟩
    have hzeqA :
        splitTorusSL b * z * A = A * splitTorusSL a := by
      calc
        splitTorusSL b * z * A =
            (A * splitTorusSL a * A⁻¹) * A := by rw [hzeq]
        _ = A * splitTorusSL a := by group
    have hscalar :=
      Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center
        hz (0 : Fin 2)
    have hmat := congrArg Subtype.val hzeqA
    change (!![(b : F), 0; 0, (b⁻¹ : F)] :
          Matrix (Fin 2) (Fin 2) F) *
        (z : Matrix (Fin 2) (Fin 2) F) *
          (A : Matrix (Fin 2) (Fin 2) F) =
      (A : Matrix (Fin 2) (Fin 2) F) *
        !![(a : F), 0; 0, (a⁻¹ : F)] at hmat
    rw [← hscalar] at hmat
    rcases hsplit_matrix_diag_or_antidiag A a b
        ((z : Matrix (Fin 2) (Fin 2) F) 0 0)
        ha_ne_inv hmat with hdiag | hanti
    · rcases hdiag with ⟨h01, h10⟩
      have hdet := A.property
      rw [Matrix.det_fin_two, h01, h10, zero_mul, sub_zero] at hdet
      have hA00 : A 0 0 ≠ 0 := by
        intro h
        rw [h, zero_mul] at hdet
        exact zero_ne_one hdet
      let u : Fˣ := Units.mk0 (A 0 0) hA00
      have hA11 : A 1 1 = (A 0 0)⁻¹ :=
        eq_inv_of_mul_eq_one_right hdet
      have hAeq : A = splitTorusSL u := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [splitTorusSL, u, h01, h10, hA11]
      rw [hAeq]
      exact (show splitTorus.range ≤
        splitTorus.range ⊔ splitWeylZ from le_sup_left)
          ⟨u, rfl⟩
    · rcases hanti with ⟨h00, h11⟩
      have hdet := A.property
      rw [Matrix.det_fin_two, h00, h11, zero_mul, zero_sub] at hdet
      have hA10 : A 1 0 ≠ 0 := by
        intro h
        rw [h, mul_zero, neg_zero] at hdet
        exact zero_ne_one hdet
      let u : Fˣ := Units.mk0 (A 1 0) hA10
      have hnegprod : (-A 0 1) * A 1 0 = 1 := by
        simpa using hdet
      have hneg : -A 0 1 = (A 1 0)⁻¹ :=
        eq_inv_of_mul_eq_one_left hnegprod
      have hA01 : A 0 1 = -(A 1 0)⁻¹ := by
        calc
          A 0 1 = -(-A 0 1) := by simp
          _ = -(A 1 0)⁻¹ := congrArg Neg.neg hneg
      have hAeq : A = splitWeylSL * splitTorusSL u := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [splitWeylSL, splitTorusSL, u, Matrix.mul_apply,
            h00, h11, hA01]
      have hw :
          splitWeyl ∈
            splitTorus.range ⊔ splitWeylZ :=
        (show splitWeylZ ≤
          splitTorus.range ⊔ splitWeylZ from le_sup_right)
            (Subgroup.mem_zpowers splitWeyl)
      have hu :
          splitTorus u ∈
            splitTorus.range ⊔ splitWeylZ :=
        (show splitTorus.range ≤
          splitTorus.range ⊔ splitWeylZ from le_sup_left)
            ⟨u, rfl⟩
      rw [hAeq]
      simpa [splitWeyl, splitTorus] using
        (splitTorus.range ⊔ splitWeylZ).mul_mem hw hu
  have hsplit_normalizer_eq_candidate
      (R : Subgroup (PSL2MatrixGroup F))
      (hR_le : R ≤ splitTorus.range) (hR_ne : R ≠ ⊥) :
      Subgroup.normalizer (R : Set _) =
        splitTorus.range ⊔ splitWeylZ := by
    apply le_antisymm
    · exact hsplit_normalizer_sub_candidate R hR_le hR_ne
    · apply sup_le
      · intro t ht
        have hsplit_comm {x y : PSL2MatrixGroup F}
            (hx : x ∈ splitTorus.range)
            (hy : y ∈ splitTorus.range) : Commute x y := by
          rcases hx with ⟨a, rfl⟩
          rcases hy with ⟨b, rfl⟩
          change splitTorus a * splitTorus b =
            splitTorus b * splitTorus a
          simp only [← map_mul]
          rw [mul_comm]
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          have hcomm := hsplit_comm ht (hR_le hy)
          simpa [hcomm.eq, mul_assoc] using hy
        · intro hy
          have hy' : y = t⁻¹ * (t * y * t⁻¹) * t := by
            simp [mul_assoc]
          have hconjR : t * y * t⁻¹ ∈ R := hy
          have hcomm := hsplit_comm
            (splitTorus.range.inv_mem ht) (hR_le hconjR)
          have hfixed :
              t⁻¹ * (t * y * t⁻¹) * t = t * y * t⁻¹ := by
            calc
              t⁻¹ * (t * y * t⁻¹) * t =
                  (t * y * t⁻¹) * t⁻¹ * t := by rw [hcomm.eq]
              _ = t * y * t⁻¹ := by group
          rw [hy', hfixed]
          exact hconjR
      · apply Subgroup.zpowers_le.2
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          rcases hR_le hy with ⟨a, ha⟩
          have hy_inv : y⁻¹ ∈ R := R.inv_mem hy
          have hconj :
              splitWeyl * y * splitWeyl⁻¹ = y⁻¹ := by
            rw [← ha]
            simpa using hsplitWeyl_conj a
          rw [hconj]
          exact hy_inv
        · intro hy
          have hyT :
              splitWeyl * y * splitWeyl⁻¹ ∈ splitTorus.range :=
            hR_le hy
          rcases hyT with ⟨a, ha⟩
          have hrecover : y = splitTorus a⁻¹ := by
            calc
              y = splitWeyl⁻¹ *
                  (splitWeyl * y * splitWeyl⁻¹) * splitWeyl := by
                    simp [mul_assoc]
              _ = splitWeyl⁻¹ * splitTorus a * splitWeyl := by
                    rw [← ha]
              _ = splitTorus a⁻¹ := by
                calc
                  splitWeyl⁻¹ * splitTorus a * splitWeyl =
                      splitWeyl⁻¹ *
                        (splitWeyl * splitTorus a⁻¹ * splitWeyl⁻¹) *
                          splitWeyl := by rw [hsplitWeyl_conj]; simp
                  _ = splitTorus a⁻¹ := by simp [mul_assoc]
          have hy_inv :
              (splitWeyl * y * splitWeyl⁻¹)⁻¹ ∈ R := R.inv_mem hy
          rw [hrecover]
          rw [← ha] at hy_inv
          simpa using hy_inv
  refine ⟨splitTorus.range, splitWeyl, hsplit_range_cyclic,
    hsplit_range_card, hsplitWeyl_mem_normalizer, hsplitWeyl_not_mem,
    hsplitWeyl_sq, ?_, ?_, ?_⟩
  · intro t ht
    rcases ht with ⟨a, rfl⟩
    simpa using hsplitWeyl_conj a
  · simpa [splitWeylZ] using hsplitCandidate_card_raw
  · intro R hR hRne
    simpa [splitWeylZ] using
      hsplit_normalizer_eq_candidate R hR hRne

/-- Huppert II.8.3(a,c), in the normalizer-card form used in II.8.22. -/
public theorem huppert_II_8_3_split_torus_normalizer_card
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) :
    ∃ U : Subgroup (PSL2MatrixGroup F),
      IsCyclic U ∧
      Nat.card U =
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      ∀ R : Subgroup (PSL2MatrixGroup F), R ≤ U → R ≠ ⊥ →
        Nat.card (Subgroup.normalizer (R : Set (PSL2MatrixGroup F))) =
          2 * Nat.card U := by
  obtain ⟨U, w, hUcyclic, hUcard, _hwN, _hwU, _hwsq, _hwinv,
      hcandidate_card, hnormalizer⟩ :=
    huppert_II_8_3_split_torus_reflection_data hFcard
  refine ⟨U, hUcyclic, hUcard, ?_⟩
  intro R hR hRne
  rw [hnormalizer R hR hRne, hcandidate_card]
set_option maxHeartbeats 1000000 in

private theorem h84_nonsplit_torus_data
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) :
    ∃ S : Subgroup (PSL2MatrixGroup F),
      IsCyclic S ∧
      Nat.card S =
        (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      Nat.card (Subgroup.normalizer (S : Set (PSL2MatrixGroup F))) =
        2 * Nat.card S ∧
      (∃ w : PSL2MatrixGroup F,
        w ∈ Subgroup.normalizer (S : Set (PSL2MatrixGroup F)) ∧
        w ∉ S ∧
        w * w = 1 ∧
        (∀ t : PSL2MatrixGroup F, t ∈ S → w * t * w⁻¹ = t⁻¹) ∧
        Nat.card (S ⊔ Subgroup.zpowers w :
          Subgroup (PSL2MatrixGroup F)) = 2 * Nat.card S ∧
        ∀ R : Subgroup (PSL2MatrixGroup F), R ≤ S → R ≠ ⊥ →
          Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) =
            S ⊔ Subgroup.zpowers w) ∧
      (∀ y : PSL2MatrixGroup F, y ∈ S → y ≠ 1 →
        ∀ g : PSL2MatrixGroup F,
          g * y * g⁻¹ ∈ S →
            g ∈ Subgroup.normalizer
              (S : Set (PSL2MatrixGroup F))) ∧
      ∀ A : Matrix.SpecialLinearGroup (Fin 2) F,
        Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ^ 2 ≠ (4 : F) →
        (¬ ∃ (μ : F) (v : Fin 2 → F), v ≠ 0 ∧
          (A : Matrix (Fin 2) (Fin 2) F).mulVec v = μ • v) →
        ∃ g : PSL2MatrixGroup F,
          (QuotientGroup.mk' (Subgroup.center
            (Matrix.SpecialLinearGroup (Fin 2) F))) A ∈
            S.map (MulAut.conj g).toMonoidHom := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F p :=
    charP_of_card_eq_prime_pow (by simpa using hFcard)
  have hf_ne_zero : f ≠ 0 :=
    huppert_II_8_27_field_exponent_ne_zero hFcard
  have hcard_roots :
        Nat.card (rootsOfUnity 2 F) =
          Nat.gcd (Nat.card F - 1) 2 := by
      let e :=
        Equiv.Set.image ((↑) : Fˣ → F) (rootsOfUnity 2 F : Set Fˣ)
          Units.val_injective
      have he :
          Nat.card (rootsOfUnity 2 F) =
            Nat.card (((↑) : Fˣ → F) '' (rootsOfUnity 2 F : Set Fˣ)) :=
        Nat.card_congr e
      rw [Units.val_set_image_rootsOfUnity_two] at he
      by_cases hp_two : p = 2
      · have htwo : (2 : F) = 0 := by
          subst p
          exact CharP.cast_eq_zero F 2
        have hneg_one : (-1 : F) = 1 := by
          apply (neg_eq_iff_add_eq_zero).2
          have hone_add_one : (1 : F) + 1 = 0 := by
            rw [show (1 : F) + 1 = 2 by norm_num, htwo]
          exact hone_add_one
        have hleft : Nat.card (rootsOfUnity 2 F) = 1 := by
          simpa [hneg_one] using he
        have hq_even : Even (Nat.card F) := by
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hf_ne_zero
          rw [hFcard, hp_two, hk, pow_succ]
          use 2 ^ k
          ring
        have hq_sub_one_odd : Odd (Nat.card F - 1) := by
          rw [← Nat.not_even_iff_odd]
          intro heven
          have hparity :=
            (Nat.even_sub (show 1 ≤ Nat.card F from (Finite.one_lt_card (α := F)).le)).mp
              heven
          exact Nat.not_even_one (hparity.mp hq_even)
        have hgcd : Nat.gcd (Nat.card F - 1) 2 = 1 :=
          Nat.coprime_iff_gcd_eq_one.mp hq_sub_one_odd.coprime_two_right
        rw [hleft, hgcd]
      · have hring_char_ne_two : ringChar F ≠ 2 := by
          rw [ringChar.eq F p]
          exact hp_two
        have hneg_one : (-1 : F) ≠ 1 :=
          Ring.neg_one_ne_one_of_char_ne_two hring_char_ne_two
        have hleft : Nat.card (rootsOfUnity 2 F) = 2 := by
          simpa [hneg_one, Ne.symm hneg_one] using he
        have hq_odd : Odd (Nat.card F) := by
          rw [hFcard]
          exact ((Fact.out : p.Prime).odd_of_ne_two hp_two).pow
        have htwo_dvd : 2 ∣ Nat.card F - 1 := by
          rcases hq_odd with ⟨k, hk⟩
          use k
          omega
        have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 :=
          Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
            (Nat.dvd_gcd htwo_dvd (dvd_refl 2))
        rw [hleft, hgcd]
  have hreflection_candidate_data
      (T : Subgroup (PSL2MatrixGroup F)) (w : PSL2MatrixGroup F)
      (hw_normalizer : w ∈ Subgroup.normalizer (T : Set _))
      (hw_sq : w * w = 1) (hw_not_mem : w ∉ T) :
      Nat.card (Subgroup.zpowers w) = 2 ∧
        Disjoint T (Subgroup.zpowers w) ∧
        Nat.card (T ⊔ (Subgroup.zpowers w : Subgroup (PSL2MatrixGroup F)) : Subgroup (PSL2MatrixGroup F)) = 2 * Nat.card T := by
    dsimp
    let Z : Subgroup (PSL2MatrixGroup F) := Subgroup.zpowers w
    have hw_ne_one : w ≠ 1 := by
      intro hw_one
      apply hw_not_mem
      rw [hw_one]
      exact Subgroup.one_mem T
    have hw_zpowers_card : Nat.card Z = 2 := by
      change Nat.card (Subgroup.zpowers w) = 2
      rw [Nat.card_zpowers]
      have hw_pow : w ^ 2 = 1 := by
        simpa [pow_two] using hw_sq
      have hord_dvd : orderOf w ∣ 2 :=
        orderOf_dvd_of_pow_eq_one hw_pow
      rcases (Nat.dvd_prime Nat.prime_two).mp hord_dvd with hord | hord
      · exact False.elim (hw_ne_one (orderOf_eq_one_iff.mp hord))
      · exact hord
    have hdisjoint : Disjoint T Z := by
      let R : Subgroup Z := T.comap Z.subtype
      letI : Fact (Nat.card Z).Prime := ⟨by
        rw [show Nat.card Z = 2 by exact hw_zpowers_card]
        exact Nat.prime_two⟩
      rcases R.eq_bot_or_eq_top_of_prime_card with hR | hR
      · rw [disjoint_iff, eq_bot_iff]
        intro x hx
        have hxR : (⟨x, hx.2⟩ : Z) ∈ R := hx.1
        rw [hR] at hxR
        have hxone : (⟨x, hx.2⟩ : Z) = 1 := by simpa using hxR
        exact congrArg Subtype.val hxone
      · exfalso
        apply hw_not_mem
        have hwR : (⟨w, Subgroup.mem_zpowers w⟩ : Z) ∈ R := by
          rw [hR]
          simp
        exact hwR
    let D : Subgroup (PSL2MatrixGroup F) := T ⊔ Z
    have hD_le_normalizer : D ≤ Subgroup.normalizer (T : Set _) := by
      apply sup_le Subgroup.le_normalizer
      exact Subgroup.zpowers_le.2 hw_normalizer
    let TD : Subgroup D := T.subgroupOf D
    let ZD : Subgroup D := Z.subgroupOf D
    letI : TD.Normal := by
      change (T.subgroupOf D).Normal
      exact Subgroup.normal_subgroupOf_of_le_normalizer hD_le_normalizer
    have hTDZD : Disjoint TD ZD := by
      rw [disjoint_iff, eq_bot_iff]
      intro x hx
      have hxAmbient : (x : PSL2MatrixGroup F) ∈ T ⊓ Z := by
        change (x : PSL2MatrixGroup F) ∈ T ∧ (x : PSL2MatrixGroup F) ∈ Z
        exact ⟨hx.1, hx.2⟩
      have hxone : (x : PSL2MatrixGroup F) = 1 := by
        rw [hdisjoint.eq_bot] at hxAmbient
        simpa using hxAmbient
      apply Subtype.ext
      exact hxone
    have hsup : TD ⊔ ZD = ⊤ := by
      change T.subgroupOf D ⊔ Z.subgroupOf D = ⊤
      rw [← Subgroup.subgroupOf_sup (show T ≤ D from le_sup_left)
        (show Z ≤ D from le_sup_right)]
      exact Subgroup.subgroupOf_self D
    have hZD_le_normalizer : ZD ≤ Subgroup.normalizer (TD : Set D) := by
      rw [Subgroup.normalizer_eq_top TD]
      exact le_top
    have hmul : (ZD : Set D) * (TD : Set D) = Set.univ := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right ZD TD
        hZD_le_normalizer, sup_comm, hsup]
      rfl
    have hcomp : ZD.IsComplement' TD :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hTDZD.symm hmul
    have hZDcard : Nat.card ZD = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show Z ≤ D from le_sup_right)).toEquiv
    have hTDcard : Nat.card TD = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show T ≤ D from le_sup_left)).toEquiv
    refine ⟨hw_zpowers_card, hdisjoint, ?_⟩
    calc
      Nat.card (T ⊔ Z : Subgroup (PSL2MatrixGroup F)) = Nat.card D := rfl
      _ = Nat.card ZD * Nat.card TD := hcomp.card_mul.symm
      _ = 2 * Nat.card T := by
        rw [hZDcard, hTDcard, hw_zpowers_card]
  let E := FiniteField.Extension F p 2
  letI : Fintype E := Fintype.ofFinite E
  let normUnits : Eˣ →* Fˣ := Units.map (Algebra.norm F)
  let K : Subgroup Eˣ := normUnits.ker
  have hnormUnits_surjective : Function.Surjective normUnits := by
    exact FiniteField.unitsMap_norm_surjective F E
  have hnormUnits_range : normUnits.range = ⊤ :=
    MonoidHom.range_eq_top.mpr hnormUnits_surjective
  have hK_index : K.index = Nat.card F - 1 := by
    calc
      K.index = Nat.card normUnits.range := Subgroup.index_ker normUnits
      _ = Nat.card Fˣ := by rw [hnormUnits_range]; simp
      _ = Nat.card F - 1 := by
        simpa [Nat.card_eq_fintype_card] using (Fintype.card_units (α := F))
  have hE_card : Nat.card E = Nat.card F ^ 2 := by
    exact FiniteField.natCard_extension F p 2
  have hK_mul_card :
      (Nat.card F - 1) * Nat.card K = Nat.card F ^ 2 - 1 := by
    calc
      (Nat.card F - 1) * Nat.card K = K.index * Nat.card K := by rw [hK_index]
      _ = Nat.card Eˣ := K.index_mul_card
      _ = Nat.card E - 1 := by
        simpa [Nat.card_eq_fintype_card] using (Fintype.card_units (α := E))
      _ = Nat.card F ^ 2 - 1 := by rw [hE_card]
  have hq_factor :
      (Nat.card F - 1) * (Nat.card F + 1) = Nat.card F ^ 2 - 1 := by
    simpa [mul_comm] using
      (Nat.pow_two_sub_pow_two (Nat.card F) 1).symm
  have hdegree_exp :
      (Nat.card E - 1) / (Nat.card F - 1) = Nat.card F + 1 := by
    rw [hE_card, ← hq_factor]
    simpa [mul_comm] using Nat.mul_div_left (Nat.card F + 1)
      (Nat.sub_pos_iff_lt.mpr (Finite.one_lt_card (α := F)))
  have hfrob_inv (x : K) :
      FiniteField.Extension.frob F p 2 (x.1 : E) = ((x.1 : E)⁻¹) := by
    have hxker := x.property
    change normUnits x.1 = 1 at hxker
    have hxnorm := congrArg Units.val hxker
    change Algebra.norm F (x.1 : E) = 1 at hxnorm
    have hpow : (x.1 : E) ^ (Nat.card F + 1) = 1 := by
      have h := FiniteField.algebraMap_norm_eq_pow
        (K := F) (K' := E) (x := (x.1 : E))
      rw [hxnorm, map_one, hdegree_exp] at h
      exact h.symm
    rw [FiniteField.Extension.frob_apply]
    apply mul_right_cancel₀ (x.1.ne_zero)
    calc
      (x.1 : E) ^ Nat.card F * (x.1 : E) =
          (x.1 : E) ^ (Nat.card F + 1) := (pow_succ _ _).symm
      _ = 1 := hpow
      _ = (x.1 : E)⁻¹ * (x.1 : E) := by
        rw [inv_mul_cancel₀ x.1.ne_zero]
  have hK_card : Nat.card K = Nat.card F + 1 := by
    apply Nat.eq_of_mul_eq_mul_left
      (Nat.sub_pos_iff_lt.mpr (Finite.one_lt_card (α := F)))
    exact hK_mul_card.trans hq_factor.symm
  have hK_cyclic : IsCyclic K := isCyclic_subgroup_units K
  have hidx :
      Fintype.card (Module.Free.ChooseBasisIndex F E) =
        Fintype.card (Fin 2) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, Fintype.card_fin]
    simpa [E] using (FiniteField.finrank_extension F p 2)
  let eidx : Module.Free.ChooseBasisIndex F E ≃ Fin 2 :=
    Fintype.equivOfCardEq hidx
  let b : Module.Basis (Fin 2) F E :=
    (Module.Free.chooseBasis F E).reindex eidx
  let nonsplitSL : K →* Matrix.SpecialLinearGroup (Fin 2) F :=
    { toFun := fun x =>
        ⟨Algebra.leftMulMatrix b (x.1 : E), by
          rw [← Algebra.norm_eq_matrix_det b]
          have hxker := x.property
          change normUnits x.1 = 1 at hxker
          simpa [normUnits] using congrArg Units.val hxker⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        simp }
  have hnonsplitSL_injective : Function.Injective nonsplitSL := by
    intro x y hxy
    apply Subtype.ext
    apply Units.ext
    apply Algebra.leftMulMatrix_injective b
    have hmat := congrArg
      (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
        (A : Matrix (Fin 2) (Fin 2) F)) hxy
    change Algebra.leftMulMatrix b (x.1 : E) =
      Algebra.leftMulMatrix b (y.1 : E) at hmat
    exact hmat
  let nonsplitTorus : K →* PSL2MatrixGroup F :=
    (QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).comp
        nonsplitSL
  have hnonsplit_mem_ker_iff (x : K) :
      x ∈ nonsplitTorus.ker ↔
        ∃ r : F, r ^ 2 = 1 ∧ algebraMap F E r = (x.1 : E) := by
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hcenter : nonsplitSL x ∈
          Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
        (QuotientGroup.eq_one_iff (nonsplitSL x)).mp hx
      rw [Matrix.SpecialLinearGroup.mem_center_iff] at hcenter
      rcases hcenter with ⟨r, hr, hscalar⟩
      refine ⟨r, by simpa using hr, ?_⟩
      apply Algebra.leftMulMatrix_injective b
      calc
        Algebra.leftMulMatrix b (algebraMap F E r) =
            algebraMap F (Matrix (Fin 2) (Fin 2) F) r :=
          (Algebra.leftMulMatrix b).commutes r
        _ = Matrix.scalar (Fin 2) r := rfl
        _ = (nonsplitSL x : Matrix.SpecialLinearGroup (Fin 2) F) := hscalar
        _ = Algebra.leftMulMatrix b (x.1 : E) := rfl
    · rintro ⟨r, hr, hxr⟩
      apply (QuotientGroup.eq_one_iff (nonsplitSL x)).mpr
      rw [Matrix.SpecialLinearGroup.mem_center_iff]
      refine ⟨r, by simpa using hr, ?_⟩
      change Matrix.scalar (Fin 2) r = Algebra.leftMulMatrix b (x.1 : E)
      rw [← hxr]
      calc
        Matrix.scalar (Fin 2) r =
            algebraMap F (Matrix (Fin 2) (Fin 2) F) r := rfl
        _ = Algebra.leftMulMatrix b (algebraMap F E r) :=
          ((Algebra.leftMulMatrix b).commutes r).symm
  let RootF := {r : F // r ^ 2 = 1}
  let kerScalar (x : nonsplitTorus.ker) : F :=
    Classical.choose ((hnonsplit_mem_ker_iff x.1).mp x.property)
  have hkerScalar_spec (x : nonsplitTorus.ker) :
      kerScalar x ^ 2 = 1 ∧
        algebraMap F E (kerScalar x) = (x.1.1 : E) :=
    Classical.choose_spec ((hnonsplit_mem_ker_iff x.1).mp x.property)
  let scalarK (r : RootF) : K :=
    ⟨Units.map (algebraMap F E)
        (Units.mk0 r.1 (by
          intro hr0
          have hr := r.property
          simp [hr0] at hr)), by
      change normUnits
        (Units.map (algebraMap F E)
          (Units.mk0 r.1 (by
            intro hr0
            have hr := r.property
            simp [hr0] at hr))) = 1
      apply Units.ext
      change Algebra.norm F (algebraMap F E r.1) = 1
      rw [Algebra.norm_algebraMap_of_basis b]
      simpa using r.property⟩
  let scalarKer (r : RootF) : nonsplitTorus.ker :=
    ⟨scalarK r, (hnonsplit_mem_ker_iff (scalarK r)).mpr
      ⟨r.1, r.property, by simp [scalarK]⟩⟩
  let eKerRoot : nonsplitTorus.ker ≃ RootF :=
    { toFun := fun x => ⟨kerScalar x, (hkerScalar_spec x).1⟩
      invFun := scalarKer
      left_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        apply Units.ext
        simpa [scalarKer, scalarK] using (hkerScalar_spec x).2
      right_inv := by
        intro r
        apply Subtype.ext
        apply (algebraMap F E).injective
        calc
          algebraMap F E (kerScalar (scalarKer r)) =
              ((scalarKer r).1.1 : E) :=
            (hkerScalar_spec (scalarKer r)).2
          _ = algebraMap F E r.1 := by simp [scalarKer, scalarK] }
  let rootVal : rootsOfUnity 2 F ≃ RootF :=
    { toFun := fun a =>
        ⟨(a.1 : F), by simpa using congrArg Units.val a.property⟩
      invFun := fun r =>
        ⟨Units.mk0 r.1 (by
            intro hr0
            have hr := r.property
            simp [hr0] at hr),
          by
            rw [mem_rootsOfUnity]
            apply Units.ext
            simpa using r.property⟩
      left_inv := by
        intro a
        apply Subtype.ext
        apply Units.ext
        rfl
      right_inv := by
        intro r
        apply Subtype.ext
        rfl }
  have hnonsplit_ker_card :
      Nat.card nonsplitTorus.ker =
        Nat.gcd (Nat.card F - 1) 2 := by
    calc
      Nat.card nonsplitTorus.ker = Nat.card RootF :=
        Nat.card_congr eKerRoot
      _ = Nat.card (rootsOfUnity 2 F) :=
        (Nat.card_congr rootVal).symm
      _ = Nat.gcd (Nat.card F - 1) 2 := hcard_roots
  have hnonsplit_range_mul :
      Nat.card nonsplitTorus.range * Nat.gcd (Nat.card F - 1) 2 =
        Nat.card F + 1 := by
    calc
      Nat.card nonsplitTorus.range * Nat.gcd (Nat.card F - 1) 2 =
          nonsplitTorus.ker.index * Nat.card nonsplitTorus.ker := by
        rw [Subgroup.index_ker, hnonsplit_ker_card]
      _ = Nat.card K := nonsplitTorus.ker.index_mul_card
      _ = Nat.card F + 1 := hK_card
  have hnonsplit_range_card :
      Nat.card nonsplitTorus.range =
        (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 := by
    apply Nat.eq_div_of_mul_eq_left
    · rw [← hcard_roots]
      exact Nat.ne_of_gt Nat.card_pos
    · exact hnonsplit_range_mul
  have hnonsplitTorus_cyclic : IsCyclic nonsplitTorus.range := by
    letI : IsCyclic K := hK_cyclic
    exact isCyclic_of_surjective nonsplitTorus.rangeRestrict
      nonsplitTorus.rangeRestrict_surjective
  let sigma : E ≃ₐ[F] E :=
    FiniteField.Extension.frob F p 2
  have hsigma_sq (x : E) : sigma (sigma x) = x := by
    change FiniteField.Extension.frob F p 2
      (FiniteField.Extension.frob F p 2 x) = x
    rw [FiniteField.Extension.frob_apply, FiniteField.Extension.frob_apply,
      ← pow_mul]
    have hcard : Nat.card F * Nat.card F = Fintype.card E := by
      rw [← pow_two, ← FiniteField.natCard_extension F p 2,
        Nat.card_eq_fintype_card]
    rw [hcard]
    exact FiniteField.pow_card x
  have hsigma_ne_one : sigma ≠ 1 := by
    intro hsigma
    change FiniteField.Extension.frob F p 2 = 1 at hsigma
    have hall : ∀ g : E ≃ₐ[F] E, g = 1 := by
      intro g
      obtain ⟨i, hi, hpow⟩ :=
        FiniteField.Extension.exists_frob_pow_eq
          (k := F) (p := p) (n := 2) g
      rw [← hpow, hsigma, one_pow]
    letI : Subsingleton (E ≃ₐ[F] E) :=
      ⟨fun a d => (hall a).trans (hall d).symm⟩
    have hone : Nat.card (E ≃ₐ[F] E) = 1 := Nat.card_unique
    have htwo : Nat.card (E ≃ₐ[F] E) = 2 :=
      FiniteField.natCard_algEquiv_extension F p 2
    omega
  let sigmaMat : Matrix (Fin 2) (Fin 2) F :=
    LinearMap.toMatrix b b sigma.toLinearEquiv
  have hsigma_inv (x : K) :
      sigma (x.1 : E) = ((x⁻¹ : K).1 : E) := by
    simpa [sigma] using hfrob_inv x
  have hsigmaMat_mul (x : E) :
      sigmaMat * Algebra.leftMulMatrix b x =
        Algebra.leftMulMatrix b (sigma x) * sigmaMat := by
    dsimp [sigmaMat]
    rw [Algebra.leftMulMatrix_apply, Algebra.leftMulMatrix_apply,
      ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp,
      (LinearMap.toMatrix b b).injective.eq_iff]
    ext y
    simp [LinearMap.comp_apply, Algebra.lmul]
  have hsigmaMat_sq : sigmaMat * sigmaMat = 1 := by
    dsimp [sigmaMat]
    rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_id b,
      (LinearMap.toMatrix b b).injective.eq_iff]
    ext x
    exact hsigma_sq x
  have hsigma_det_unit : IsUnit (Matrix.det sigmaMat) := by
    simpa [sigmaMat] using
      (LinearEquiv.isUnit_det sigma.toLinearEquiv b b)
  have hsigma_det_ne : Matrix.det sigmaMat ≠ 0 :=
    hsigma_det_unit.ne_zero
  obtain ⟨c, hc⟩ :=
    FiniteField.norm_surjective F E (Matrix.det sigmaMat)⁻¹
  have hc_ne : c ≠ 0 := by
    intro hc0
    subst c
    simp only [Algebra.norm_zero] at hc
    exact hsigma_det_ne (inv_eq_zero.mp hc.symm)
  let frobSL : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨Algebra.leftMulMatrix b c * sigmaMat, by
      rw [Matrix.det_mul, ← Algebra.norm_eq_matrix_det b, hc]
      exact inv_mul_cancel₀ hsigma_det_ne⟩
  have hc_sigma :
      c * sigma c = algebraMap F E (Algebra.norm F c) := by
    have h := FiniteField.algebraMap_norm_eq_pow
      (K := F) (K' := E) (x := c)
    rw [hdegree_exp] at h
    calc
      c * sigma c = c * c ^ Nat.card F := by
        change c * FiniteField.Extension.frob F p 2 c = _
        rw [FiniteField.Extension.frob_apply]
      _ = c ^ (Nat.card F + 1) := by rw [pow_succ, mul_comm]
      _ = algebraMap F E (Algebra.norm F c) := h.symm
  have hfrobSL_sq_matrix :
      ((frobSL * frobSL : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) =
        Algebra.leftMulMatrix b
          (algebraMap F E (Algebra.norm F c)) := by
    change (Algebra.leftMulMatrix b c * sigmaMat) *
        (Algebra.leftMulMatrix b c * sigmaMat) =
      Algebra.leftMulMatrix b
        (algebraMap F E (Algebra.norm F c))
    calc
      (Algebra.leftMulMatrix b c * sigmaMat) *
          (Algebra.leftMulMatrix b c * sigmaMat) =
          Algebra.leftMulMatrix b c *
            (sigmaMat * Algebra.leftMulMatrix b c) * sigmaMat := by
              simp only [Matrix.mul_assoc]
      _ = Algebra.leftMulMatrix b c *
            (Algebra.leftMulMatrix b (sigma c) * sigmaMat) *
              sigmaMat := by rw [hsigmaMat_mul]
      _ = (Algebra.leftMulMatrix b c *
            Algebra.leftMulMatrix b (sigma c)) *
              (sigmaMat * sigmaMat) := by
                simp only [Matrix.mul_assoc]
      _ = Algebra.leftMulMatrix b (c * sigma c) := by
            rw [hsigmaMat_sq, mul_one, ← map_mul]
      _ = Algebra.leftMulMatrix b
            (algebraMap F E (Algebra.norm F c)) := by rw [hc_sigma]
  have hfrobSL_sq_center :
      frobSL * frobSL ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨Algebra.norm F c, ?_, ?_⟩
    · have hdet := (frobSL * frobSL).property
      rw [hfrobSL_sq_matrix] at hdet
      have hscalar :
          Algebra.leftMulMatrix b
              (algebraMap F E (Algebra.norm F c)) =
            Matrix.scalar (Fin 2) (Algebra.norm F c) := by
        calc
          _ = algebraMap F (Matrix (Fin 2) (Fin 2) F)
              (Algebra.norm F c) :=
            (Algebra.leftMulMatrix b).commutes (Algebra.norm F c)
          _ = _ := rfl
      rw [hscalar] at hdet
      simpa [Matrix.det_fin_two, pow_two] using hdet
    · calc
        Matrix.scalar (Fin 2) (Algebra.norm F c) =
            algebraMap F (Matrix (Fin 2) (Fin 2) F)
              (Algebra.norm F c) := rfl
        _ = Algebra.leftMulMatrix b
            (algebraMap F E (Algebra.norm F c)) :=
          ((Algebra.leftMulMatrix b).commutes (Algebra.norm F c)).symm
        _ = ((frobSL * frobSL :
            Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) := hfrobSL_sq_matrix.symm
  have hleftMul_comm (a d : E) :
      Algebra.leftMulMatrix b a * Algebra.leftMulMatrix b d =
        Algebra.leftMulMatrix b d * Algebra.leftMulMatrix b a := by
    rw [← map_mul, ← map_mul, mul_comm]
  have hfrobSL_mul (x : K) :
      frobSL * nonsplitSL x = nonsplitSL x⁻¹ * frobSL := by
    apply Subtype.ext
    change (Algebra.leftMulMatrix b c * sigmaMat) *
          Algebra.leftMulMatrix b (x.1 : E) =
        Algebra.leftMulMatrix b ((x⁻¹ : K).1 : E) *
          (Algebra.leftMulMatrix b c * sigmaMat)
    calc
      (Algebra.leftMulMatrix b c * sigmaMat) *
          Algebra.leftMulMatrix b (x.1 : E) =
          Algebra.leftMulMatrix b c *
            (sigmaMat * Algebra.leftMulMatrix b (x.1 : E)) := by
              rw [Matrix.mul_assoc]
      _ = Algebra.leftMulMatrix b c *
            (Algebra.leftMulMatrix b (sigma (x.1 : E)) * sigmaMat) := by
              rw [hsigmaMat_mul]
      _ = (Algebra.leftMulMatrix b c *
            Algebra.leftMulMatrix b (sigma (x.1 : E))) * sigmaMat := by
              rw [Matrix.mul_assoc]
      _ = (Algebra.leftMulMatrix b (sigma (x.1 : E)) *
            Algebra.leftMulMatrix b c) * sigmaMat := by
              rw [hleftMul_comm]
      _ = Algebra.leftMulMatrix b (sigma (x.1 : E)) *
            (Algebra.leftMulMatrix b c * sigmaMat) := by
              rw [Matrix.mul_assoc]
      _ = Algebra.leftMulMatrix b ((x⁻¹ : K).1 : E) *
            (Algebra.leftMulMatrix b c * sigmaMat) := by
              rw [hsigma_inv]
  have hfrobSL_conj (x : K) :
      frobSL * nonsplitSL x * frobSL⁻¹ = nonsplitSL x⁻¹ := by
    calc
      frobSL * nonsplitSL x * frobSL⁻¹ =
          nonsplitSL x⁻¹ * (frobSL * frobSL⁻¹) := by
        rw [hfrobSL_mul, mul_assoc]
      _ = nonsplitSL x⁻¹ := by rw [mul_inv_cancel, mul_one]
  let frobPSL : PSL2MatrixGroup F :=
    QuotientGroup.mk' (Subgroup.center
      (Matrix.SpecialLinearGroup (Fin 2) F)) frobSL
  have hfrobPSL_sq : frobPSL ^ 2 = 1 := by
    change (QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) frobSL) ^ 2 = 1
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff (frobSL ^ 2)).mpr
    simpa [pow_two] using hfrobSL_sq_center
  have hfrobPSL_not_mem_torus :
      frobPSL ∉ nonsplitTorus.range := by
    rintro ⟨x, hx⟩
    change (QuotientGroup.mk'
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))
          (nonsplitSL x) =
      (QuotientGroup.mk'
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))
          frobSL at hx
    rcases (QuotientGroup.mk'_eq_mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).mp hx with
      ⟨z, hz_center, hz_eq⟩
    have hscalar :=
      Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center
        hz_center (0 : Fin 2)
    let r : F := (z : Matrix (Fin 2) (Fin 2) F) 0 0
    have hscalar' :
        Matrix.scalar (Fin 2) r =
          (z : Matrix.SpecialLinearGroup (Fin 2) F) := hscalar
    have hmat := congrArg Subtype.val hz_eq
    change Algebra.leftMulMatrix b (x.1 : E) *
        (z : Matrix (Fin 2) (Fin 2) F) =
      Algebra.leftMulMatrix b c * sigmaMat at hmat
    rw [← hscalar'] at hmat
    have hscalarLM :
        Matrix.scalar (Fin 2) r =
          Algebra.leftMulMatrix b (algebraMap F E r) := by
      calc
        _ = algebraMap F (Matrix (Fin 2) (Fin 2) F) r := rfl
        _ = _ := ((Algebra.leftMulMatrix b).commutes r).symm
    rw [hscalarLM, ← map_mul] at hmat
    rw [Algebra.leftMulMatrix_apply] at hmat
    change (LinearMap.toMatrix b b)
        (Algebra.lmul F E ((x.1 : E) * algebraMap F E r)) =
      Algebra.leftMulMatrix b c *
        (LinearMap.toMatrix b b) sigma.toLinearEquiv at hmat
    rw [Algebra.leftMulMatrix_apply, ← LinearMap.toMatrix_comp,
      (LinearMap.toMatrix b b).injective.eq_iff] at hmat
    have hone := LinearMap.congr_fun hmat (1 : E)
    have hxr : (x.1 : E) * algebraMap F E r = c := by
      simpa [LinearMap.comp_apply, Algebra.lmul] using hone
    have hall : ∀ y : E, sigma y = y := by
      intro y
      have hy := LinearMap.congr_fun hmat y
      change ((x.1 : E) * algebraMap F E r) * y =
        c * sigma y at hy
      rw [hxr] at hy
      exact (mul_left_cancel₀ hc_ne hy).symm
    apply hsigma_ne_one
    ext y
    exact hall y
  have hfrobPSL_conj (x : K) :
      frobPSL * nonsplitTorus x * frobPSL⁻¹ =
        nonsplitTorus x⁻¹ := by
    simpa [frobPSL, nonsplitTorus] using congrArg
      (QuotientGroup.mk' (Subgroup.center
        (Matrix.SpecialLinearGroup (Fin 2) F)))
      (hfrobSL_conj x)
  have hfrobPSL_mem_normalizer :
      frobPSL ∈ Subgroup.normalizer (nonsplitTorus.range : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x⁻¹, (hfrobPSL_conj x).symm⟩
    · rintro ⟨x, hx⟩
      refine ⟨x⁻¹, ?_⟩
      calc
        nonsplitTorus x⁻¹ =
            frobPSL⁻¹ *
              (frobPSL * nonsplitTorus x⁻¹ * frobPSL⁻¹) *
                frobPSL := by simp [mul_assoc]
        _ = frobPSL⁻¹ * nonsplitTorus x * frobPSL := by
          rw [hfrobPSL_conj]
          rw [inv_inv]
        _ = y := by rw [hx]; simp [mul_assoc]
  let nonsplitDihedralCandidate : Subgroup (PSL2MatrixGroup F) :=
    nonsplitTorus.range ⊔ Subgroup.zpowers frobPSL
  have hnonsplitCandidate_le_normalizer :
      nonsplitDihedralCandidate ≤
        Subgroup.normalizer (nonsplitTorus.range : Set _) := by
    apply sup_le Subgroup.le_normalizer
    exact Subgroup.zpowers_le.2 hfrobPSL_mem_normalizer
  rcases hreflection_candidate_data nonsplitTorus.range frobPSL
      hfrobPSL_mem_normalizer (by simpa [pow_two] using hfrobPSL_sq)
        hfrobPSL_not_mem_torus with
    ⟨hfrob_zpowers_card, hnonsplit_torus_zpowers_disjoint,
      hnonsplitCandidate_card_raw⟩
  have hnonsplitCandidate_card :
      Nat.card nonsplitDihedralCandidate =
        2 * ((Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2) := by
    have hraw :
        Nat.card nonsplitDihedralCandidate =
          2 * Nat.card nonsplitTorus.range := by
      simpa [nonsplitDihedralCandidate] using hnonsplitCandidate_card_raw
    rw [hnonsplit_range_card] at hraw
    exact hraw
  have hnonsplit_lift_classification_of_conj
      (A : Matrix.SpecialLinearGroup (Fin 2) F)
      (aK : K) (haK_not_ker : aK ∉ nonsplitTorus.ker)
      (hconj_mem :
        (QuotientGroup.mk' (Subgroup.center
            (Matrix.SpecialLinearGroup (Fin 2) F))) A *
              nonsplitTorus aK *
                ((QuotientGroup.mk' (Subgroup.center
                  (Matrix.SpecialLinearGroup (Fin 2) F))) A)⁻¹ ∈
          nonsplitTorus.range) :
      (∃ x : K, A = nonsplitSL x) ∨
        ∃ x : K, A = nonsplitSL x * frobSL := by
    have haK_not_scalar (r : F) :
        algebraMap F E r ≠ (aK.1 : E) := by
      intro hr
      apply haK_not_ker
      apply (hnonsplit_mem_ker_iff aK).2
      refine ⟨r, ?_, hr⟩
      have hker := aK.property
      change normUnits aK.1 = 1 at hker
      have hv := congrArg Units.val hker
      change Algebra.norm F (aK.1 : E) = 1 at hv
      rw [← hr, Algebra.norm_algebraMap_of_basis b] at hv
      simpa using hv
    rcases hconj_mem with ⟨bK, hbK⟩
    have hq :
        (QuotientGroup.mk' (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) F))) (nonsplitSL bK) =
        (QuotientGroup.mk' (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) F)))
            (A * nonsplitSL aK * A⁻¹) := by
      simpa [nonsplitTorus] using hbK
    rcases (QuotientGroup.mk'_eq_mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).mp hq with
      ⟨z, hz, hzeq⟩
    have hzeqA : nonsplitSL bK * z * A = A * nonsplitSL aK := by
      calc
        nonsplitSL bK * z * A = (A * nonsplitSL aK * A⁻¹) * A := by
          rw [hzeq]
        _ = A * nonsplitSL aK := by group
    have hscalar :=
      Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hz (0 : Fin 2)
    let rz : F := (z : Matrix (Fin 2) (Fin 2) F) 0 0
    have hscalarLM :
        Matrix.scalar (Fin 2) rz =
          Algebra.leftMulMatrix b (algebraMap F E rz) := by
      calc
        Matrix.scalar (Fin 2) rz =
            algebraMap F (Matrix (Fin 2) (Fin 2) F) rz := rfl
        _ = Algebra.leftMulMatrix b (algebraMap F E rz) :=
          ((Algebra.leftMulMatrix b).commutes rz).symm
    let yE : E := (bK.1 : E) * algebraMap F E rz
    have hmat :
        Algebra.leftMulMatrix b yE *
            (A : Matrix (Fin 2) (Fin 2) F) =
          (A : Matrix (Fin 2) (Fin 2) F) *
            Algebra.leftMulMatrix b (aK.1 : E) := by
      have hm := congrArg Subtype.val hzeqA
      change Algebra.leftMulMatrix b (bK.1 : E) *
            (z : Matrix (Fin 2) (Fin 2) F) *
              (A : Matrix (Fin 2) (Fin 2) F) =
          (A : Matrix (Fin 2) (Fin 2) F) *
            Algebra.leftMulMatrix b (aK.1 : E) at hm
      rw [← hscalar] at hm
      rw [hscalarLM, ← map_mul] at hm
      exact hm
    have hAunit :
        IsUnit (Matrix.det (A : Matrix (Fin 2) (Fin 2) F)) := by
      rw [A.property]
      exact isUnit_one
    let Aeq : E ≃ₗ[F] E :=
      Matrix.toLinearEquiv b (A : Matrix (Fin 2) (Fin 2) F) hAunit
    have hA_intertwine (x : E) :
        Aeq ((aK.1 : E) * x) = yE * Aeq x := by
      have hfun := congrArg
        (fun M : Matrix (Fin 2) (Fin 2) F => Matrix.toLin b b M x) hmat
      change Matrix.toLin b b (Algebra.leftMulMatrix b yE *
            (A : Matrix (Fin 2) (Fin 2) F)) x =
          Matrix.toLin b b ((A : Matrix (Fin 2) (Fin 2) F) *
            Algebra.leftMulMatrix b (aK.1 : E)) x at hfun
      rw [Matrix.toLin_mul_apply b b b (Algebra.leftMulMatrix b yE)
            (A : Matrix (Fin 2) (Fin 2) F) x,
        Matrix.toLin_mul_apply b b b (A : Matrix (Fin 2) (Fin 2) F)
            (Algebra.leftMulMatrix b (aK.1 : E)) x] at hfun
      simp only [Algebra.leftMulMatrix_apply, Matrix.toLin_toMatrix] at hfun
      change yE * Matrix.toLin b b (A : Matrix (Fin 2) (Fin 2) F) x =
          Matrix.toLin b b (A : Matrix (Fin 2) (Fin 2) F)
            ((aK.1 : E) * x) at hfun
      simpa [Aeq, Matrix.toLinearEquiv_apply] using hfun.symm
    have hfin : Module.finrank F E = 2 := by
      simpa [E] using FiniteField.finrank_extension F p 2
    have hcoeff : ∀ z : E, ∃ u v : F,
        u • (aK.1 : E) + v • (1 : E) = z := by
      have hLI : LinearIndependent F
          (![(aK.1 : E), 1] : Fin 2 → E) := by
        rw [linearIndependent_fin2]
        exact ⟨one_ne_zero, by
          intro r hr
          exact haK_not_scalar r (by simpa [Algebra.smul_def] using hr)⟩
      have hspan :
          Submodule.span F
              (Set.range (![(aK.1 : E), 1] : Fin 2 → E)) = ⊤ :=
        hLI.span_eq_top_of_card_eq_finrank (by simpa using hfin.symm)
      have hrange :
          Set.range (![(aK.1 : E), 1] : Fin 2 → E) =
            ({(aK.1 : E), 1} : Set E) := by
        ext z
        constructor
        · rintro ⟨i, rfl⟩
          fin_cases i <;> simp
        · intro hz
          rcases hz with (rfl | hz)
          · exact ⟨0, by simp⟩
          · have : z = 1 := hz
            exact ⟨1, by simpa [this]⟩
      intro z
      rw [hrange] at hspan
      apply Submodule.mem_span_pair.mp
      rw [hspan]
      exact Submodule.mem_top
    let d : E := Aeq 1
    have hd : d ≠ 0 := by
      intro hd0
      have h10 : (1 : E) = 0 := Aeq.injective (by simpa [d, hd0])
      exact one_ne_zero h10
    let du : Eˣ := Units.mk0 d hd
    let phiLin : E →ₗ[F] E :=
      (Aeq.trans ((du⁻¹).mulLeftLinearEquiv F E)).toLinearMap
    have hphi_apply (z : E) : phiLin z = d⁻¹ * Aeq z := by
      change ((du.mulLeftLinearEquiv F E).symm) (Aeq z) = _
      rw [Units.symm_mulLeftLinearEquiv_apply]
      rfl
    have hphi_one : phiLin 1 = 1 := by
      rw [hphi_apply]
      change d⁻¹ * d = 1
      exact inv_mul_cancel₀ hd
    have hphi_a : phiLin (aK.1 : E) = yE := by
      rw [hphi_apply]
      have ha1 := hA_intertwine 1
      simp only [mul_one] at ha1
      rw [ha1]
      change d⁻¹ * (yE * d) = yE
      calc
        d⁻¹ * (yE * d) = d⁻¹ * (d * yE) := by rw [mul_comm yE d]
        _ = (d⁻¹ * d) * yE := by rw [mul_assoc]
        _ = yE := by rw [inv_mul_cancel₀ hd, one_mul]
    have hphi_a_mul (z : E) :
        phiLin ((aK.1 : E) * z) = phiLin (aK.1 : E) * phiLin z := by
      rw [hphi_apply, hphi_a, hphi_apply, hA_intertwine]
      ac_rfl
    have hphi_mul (z w : E) :
        phiLin (z * w) = phiLin z * phiLin w := by
      obtain ⟨u, v, hz⟩ := hcoeff z
      rw [← hz]
      simp only [add_mul, smul_mul_assoc, map_add, map_smul, hphi_a_mul,
        one_mul, hphi_one]
    let phiHom : E →ₐ[F] E := AlgHom.ofLinearMap phiLin hphi_one hphi_mul
    have hbij : Function.Bijective phiHom := by
      change Function.Bijective phiLin
      exact (Aeq.trans ((du⁻¹).mulLeftLinearEquiv F E)).bijective
    let phi : E ≃ₐ[F] E := AlgEquiv.ofBijective phiHom hbij
    have hphi (z : E) : phi z = d⁻¹ * Aeq z := by
      simpa [phi, phiHom] using hphi_apply z
    obtain ⟨i, hi, hpow⟩ :=
      FiniteField.Extension.exists_frob_pow_eq
        (k := F) (p := p) (n := 2) phi
    have hphi_cases : phi = 1 ∨ phi = sigma := by
      have hi_cases : i = 0 ∨ i = 1 := by omega
      rcases hi_cases with rfl | rfl
      · left
        simpa using hpow.symm
      · right
        simpa [sigma] using hpow.symm
    have hAeq_linear : Aeq.toLinearMap =
        Matrix.toLin b b (A : Matrix (Fin 2) (Fin 2) F) := by
      ext z
      simp [Aeq, Matrix.toLinearEquiv_apply]
    have hAeq_matrix :
        LinearMap.toMatrix b b Aeq.toLinearMap =
          (A : Matrix (Fin 2) (Fin 2) F) := by
      rw [hAeq_linear]
      exact LinearMap.toMatrix_toLin b b _
    rcases hphi_cases with hphi_id | hphi_sigma
    · have hAeq_mul (z : E) : Aeq z = d * z := by
        calc
          Aeq z = d * (d⁻¹ * Aeq z) := by
            rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
          _ = d * phi z := by rw [hphi]
          _ = d * z := by rw [hphi_id]; rfl
      have hAmatrix :
          (A : Matrix (Fin 2) (Fin 2) F) =
            Algebra.leftMulMatrix b d := by
        rw [← hAeq_matrix, Algebra.leftMulMatrix_apply]
        apply congrArg (LinearMap.toMatrix b b)
        ext z
        simpa [Algebra.lmul] using hAeq_mul z
      have hd_norm : Algebra.norm F d = 1 := by
        have hdet := A.property
        rw [hAmatrix, ← Algebra.norm_eq_matrix_det b] at hdet
        exact hdet
      let x : K :=
        ⟨Units.mk0 d hd, by
          change normUnits (Units.mk0 d hd) = 1
          apply Units.ext
          simpa [normUnits] using hd_norm⟩
      left
      refine ⟨x, ?_⟩
      apply Subtype.ext
      simpa [x] using hAmatrix
    · have hAeq_mul_sigma (z : E) : Aeq z = d * sigma z := by
        calc
          Aeq z = d * (d⁻¹ * Aeq z) := by
            rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
          _ = d * phi z := by rw [hphi]
          _ = d * sigma z := by rw [hphi_sigma]
      have hAmatrix :
          (A : Matrix (Fin 2) (Fin 2) F) =
            Algebra.leftMulMatrix b d * sigmaMat := by
        apply (Matrix.toLin b b).injective
        ext z
        rw [Matrix.toLin_mul_apply b b b (Algebra.leftMulMatrix b d)
          sigmaMat z]
        simp only [Algebra.leftMulMatrix_apply, Matrix.toLin_toMatrix]
        change Matrix.toLin b b (A : Matrix (Fin 2) (Fin 2) F) z =
          d * Matrix.toLin b b sigmaMat z
        rw [show Matrix.toLin b b sigmaMat z = sigma z by
          simp [sigmaMat]]
        rw [← hAeq_mul_sigma z]
        rfl
      let u : E := d * c⁻¹
      have hu_ne : u ≠ 0 := mul_ne_zero hd (inv_ne_zero hc_ne)
      have hfactor :
          (A : Matrix (Fin 2) (Fin 2) F) =
            Algebra.leftMulMatrix b u *
              (frobSL : Matrix (Fin 2) (Fin 2) F) := by
        rw [hAmatrix]
        change Algebra.leftMulMatrix b d * sigmaMat =
          Algebra.leftMulMatrix b u *
            (Algebra.leftMulMatrix b c * sigmaMat)
        calc
          Algebra.leftMulMatrix b d * sigmaMat =
              Algebra.leftMulMatrix b ((d * c⁻¹) * c) * sigmaMat := by
                rw [show (d * c⁻¹) * c = d by
                  rw [mul_assoc, inv_mul_cancel₀ hc_ne, mul_one]]
          _ = (Algebra.leftMulMatrix b (d * c⁻¹) *
              Algebra.leftMulMatrix b c) * sigmaMat := by rw [map_mul]
          _ = Algebra.leftMulMatrix b (d * c⁻¹) *
              (Algebra.leftMulMatrix b c * sigmaMat) := by
                rw [Matrix.mul_assoc]
      have hu_norm : Algebra.norm F u = 1 := by
        have hdet := congrArg Matrix.det hfactor
        rw [Matrix.det_mul, ← Algebra.norm_eq_matrix_det b,
          A.property, frobSL.property, mul_one] at hdet
        exact hdet.symm
      let x : K :=
        ⟨Units.mk0 u hu_ne, by
          change normUnits (Units.mk0 u hu_ne) = 1
          apply Units.ext
          simpa [normUnits] using hu_norm⟩
      right
      refine ⟨x, ?_⟩
      apply Subtype.ext
      simpa [x] using hfactor
  have hnonsplit_normalizer_lift_classification
      (A : Matrix.SpecialLinearGroup (Fin 2) F)
      (hA :
        (QuotientGroup.mk' (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) F))) A ∈
            Subgroup.normalizer (nonsplitTorus.range : Set _)) :
      (∃ x : K, A = nonsplitSL x) ∨
        ∃ x : K, A = nonsplitSL x * frobSL := by
    have hnonsplit_range_one_lt : 1 < Nat.card nonsplitTorus.range := by
      rw [hnonsplit_range_card]
      have hq_one : 1 < Nat.card F := Finite.one_lt_card
      have hdpos : 0 < Nat.gcd (Nat.card F - 1) 2 :=
        Nat.gcd_pos_of_pos_right _ (by norm_num)
      by_cases hq2 : Nat.card F = 2
      · have hq2' : Fintype.card F = 2 := by
          simpa [Nat.card_eq_fintype_card] using hq2
        norm_num [hq2']
      · have hq3 : 3 ≤ Nat.card F := by omega
        have hdle : Nat.gcd (Nat.card F - 1) 2 ≤ 2 :=
          Nat.gcd_le_right _ (by norm_num)
        have hmul :
            2 * Nat.gcd (Nat.card F - 1) 2 ≤ Nat.card F + 1 := by omega
        have htwo :
            2 ≤ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 :=
          (Nat.le_div_iff_mul_le hdpos).2 hmul
        omega
    letI : IsCyclic nonsplitTorus.range := hnonsplitTorus_cyclic
    obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := nonsplitTorus.range)
    have ht_ne : t ≠ 1 := by
      intro ht_one
      have hall_one : ∀ u : nonsplitTorus.range, u = 1 := by
        intro u
        simpa [ht_one] using ht u
      haveI : Subsingleton nonsplitTorus.range :=
        ⟨fun u v => (hall_one u).trans (hall_one v).symm⟩
      have hcard_one : Nat.card nonsplitTorus.range = 1 := Nat.card_unique
      omega
    rcases t.property with ⟨aK, haK⟩
    have haK_not_ker : aK ∉ nonsplitTorus.ker := by
      intro hak
      apply ht_ne
      apply Subtype.ext
      change (t : PSL2MatrixGroup F) = 1
      rw [← haK]
      exact hak
    have hconj_mem :
        (QuotientGroup.mk' (Subgroup.center
            (Matrix.SpecialLinearGroup (Fin 2) F))) A *
              nonsplitTorus aK *
                ((QuotientGroup.mk' (Subgroup.center
                  (Matrix.SpecialLinearGroup (Fin 2) F))) A)⁻¹ ∈
          nonsplitTorus.range :=
      (Subgroup.mem_normalizer_iff.mp hA (nonsplitTorus aK)).mp
        ⟨aK, rfl⟩
    exact hnonsplit_lift_classification_of_conj
      A aK haK_not_ker hconj_mem
  have hnonsplit_normalizer_sub_candidate :
      Subgroup.normalizer (nonsplitTorus.range : Set _) ≤
        nonsplitDihedralCandidate := by
    intro g hg
    refine QuotientGroup.induction_on g ?_ hg
    intro A hA
    rcases hnonsplit_normalizer_lift_classification A hA with
      ⟨x, hx⟩ | ⟨x, hx⟩
    · have hxT : nonsplitTorus x ∈ nonsplitTorus.range := ⟨x, rfl⟩
      change (QuotientGroup.mk' (Subgroup.center
        (Matrix.SpecialLinearGroup (Fin 2) F))) A ∈
          nonsplitDihedralCandidate
      rw [hx]
      exact (show nonsplitTorus.range ≤ nonsplitDihedralCandidate from
        le_sup_left) hxT
    · have hxT : nonsplitTorus x ∈ nonsplitTorus.range := ⟨x, rfl⟩
      have hfrob : frobPSL ∈ Subgroup.zpowers frobPSL :=
        Subgroup.mem_zpowers frobPSL
      change (QuotientGroup.mk' (Subgroup.center
        (Matrix.SpecialLinearGroup (Fin 2) F))) A ∈
          nonsplitDihedralCandidate
      rw [hx]
      change nonsplitTorus x * frobPSL ∈ nonsplitDihedralCandidate
      exact nonsplitDihedralCandidate.mul_mem
        ((show nonsplitTorus.range ≤ nonsplitDihedralCandidate from
          le_sup_left) hxT)
        ((show Subgroup.zpowers frobPSL ≤ nonsplitDihedralCandidate from
          le_sup_right) hfrob)
  have hnonsplit_normalizer_eq_candidate :
      Subgroup.normalizer (nonsplitTorus.range : Set _) =
        nonsplitDihedralCandidate :=
    le_antisymm hnonsplit_normalizer_sub_candidate
      hnonsplitCandidate_le_normalizer
  have hnonsplit_weakTI :
      ∀ y : PSL2MatrixGroup F, y ∈ nonsplitTorus.range → y ≠ 1 →
        ∀ g : PSL2MatrixGroup F,
          g * y * g⁻¹ ∈ nonsplitTorus.range →
            g ∈ Subgroup.normalizer
              (nonsplitTorus.range : Set (PSL2MatrixGroup F)) := by
    intro y hy hy_ne g hgy
    rcases hy with ⟨aK, rfl⟩
    have haK_not_ker : aK ∉ nonsplitTorus.ker := by
      intro haK
      apply hy_ne
      exact haK
    refine QuotientGroup.induction_on g ?_ hgy
    intro A hAconj
    rcases hnonsplit_lift_classification_of_conj
        A aK haK_not_ker hAconj with ⟨x, hx⟩ | ⟨x, hx⟩
    · change (QuotientGroup.mk' (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) F))) A ∈
        Subgroup.normalizer (nonsplitTorus.range : Set _)
      rw [hx]
      change nonsplitTorus x ∈
        Subgroup.normalizer (nonsplitTorus.range : Set _)
      exact Subgroup.le_normalizer ⟨x, rfl⟩
    · change (QuotientGroup.mk' (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) F))) A ∈
        Subgroup.normalizer (nonsplitTorus.range : Set _)
      rw [hx]
      change nonsplitTorus x * frobPSL ∈
        Subgroup.normalizer (nonsplitTorus.range : Set _)
      have hxT : nonsplitTorus x ∈ nonsplitTorus.range := ⟨x, rfl⟩
      have hxN : nonsplitTorus x ∈
          Subgroup.normalizer
            (nonsplitTorus.range : Set (PSL2MatrixGroup F)) :=
        Subgroup.le_normalizer hxT
      have hfrobN : frobPSL ∈ Subgroup.normalizer
          (nonsplitTorus.range : Set (PSL2MatrixGroup F)) :=
        hfrobPSL_mem_normalizer
      exact (Subgroup.normalizer
          (nonsplitTorus.range : Set (PSL2MatrixGroup F))).mul_mem
        hxN hfrobN
  have hnonsplit_comm {x y : PSL2MatrixGroup F}
      (hx : x ∈ nonsplitTorus.range)
      (hy : y ∈ nonsplitTorus.range) : Commute x y := by
    rcases hx with ⟨a, rfl⟩
    rcases hy with ⟨b, rfl⟩
    change nonsplitTorus a * nonsplitTorus b =
      nonsplitTorus b * nonsplitTorus a
    simp only [← map_mul]
    rw [mul_comm]
  have hnonsplit_normalizer_eq_candidate_of_le
      (R : Subgroup (PSL2MatrixGroup F))
      (hR_le : R ≤ nonsplitTorus.range) (hR_ne : R ≠ ⊥) :
      Subgroup.normalizer (R : Set _) =
        nonsplitDihedralCandidate := by
    apply le_antisymm
    · intro g hg
      apply hnonsplit_normalizer_sub_candidate
      obtain ⟨r, hr_ne_one⟩ :=
        Subgroup.ne_bot_iff_exists_ne_one.mp hR_ne
      have hr_ne_one' : (r : PSL2MatrixGroup F) ≠ 1 := by
        intro hr
        apply hr_ne_one
        apply Subtype.ext
        exact hr
      have hgr : g * (r : PSL2MatrixGroup F) * g⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp hg (r : PSL2MatrixGroup F)).mp
          r.property
      exact hnonsplit_weakTI (r : PSL2MatrixGroup F)
        (hR_le r.property) hr_ne_one' g (hR_le hgr)
    · apply sup_le
      · intro t ht
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          have hcomm := hnonsplit_comm ht (hR_le hy)
          simpa [hcomm.eq, mul_assoc] using hy
        · intro hy
          have hy' : y = t⁻¹ * (t * y * t⁻¹) * t := by
            simp [mul_assoc]
          have hconjR : t * y * t⁻¹ ∈ R := hy
          have hcomm := hnonsplit_comm
            (nonsplitTorus.range.inv_mem ht) (hR_le hconjR)
          have hfixed :
              t⁻¹ * (t * y * t⁻¹) * t = t * y * t⁻¹ := by
            calc
              t⁻¹ * (t * y * t⁻¹) * t =
                  (t * y * t⁻¹) * t⁻¹ * t := by rw [hcomm.eq]
              _ = t * y * t⁻¹ := by group
          rw [hy', hfixed]
          exact hconjR
      · apply Subgroup.zpowers_le.2
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          rcases hR_le hy with ⟨a, ha⟩
          have hy_inv : y⁻¹ ∈ R := R.inv_mem hy
          have hconj : frobPSL * y * frobPSL⁻¹ = y⁻¹ := by
            rw [← ha]
            simpa using hfrobPSL_conj a
          rw [hconj]
          exact hy_inv
        · intro hy
          have hyT : frobPSL * y * frobPSL⁻¹ ∈
              nonsplitTorus.range := hR_le hy
          rcases hyT with ⟨a, ha⟩
          have hrecover : y = nonsplitTorus a⁻¹ := by
            calc
              y = frobPSL⁻¹ *
                  (frobPSL * y * frobPSL⁻¹) * frobPSL := by
                    simp [mul_assoc]
              _ = frobPSL⁻¹ * nonsplitTorus a * frobPSL := by
                    rw [← ha]
              _ = nonsplitTorus a⁻¹ := by
                have hfrob_inv : frobPSL⁻¹ = frobPSL :=
                  (eq_inv_of_mul_eq_one_left
                    (by simpa [pow_two] using hfrobPSL_sq)).symm
                simpa [hfrob_inv] using hfrobPSL_conj a
          have hy_inv : (frobPSL * y * frobPSL⁻¹)⁻¹ ∈ R :=
            R.inv_mem hy
          rw [hrecover]
          rw [← ha] at hy_inv
          simpa using hy_inv
  refine ⟨nonsplitTorus.range, hnonsplitTorus_cyclic,
    hnonsplit_range_card, ?_, ?_, hnonsplit_weakTI, ?_⟩
  · rw [hnonsplit_normalizer_eq_candidate, hnonsplitCandidate_card,
      hnonsplit_range_card]
  · refine ⟨frobPSL, hfrobPSL_mem_normalizer,
      hfrobPSL_not_mem_torus, ?_, ?_, ?_, ?_⟩
    · simpa [pow_two] using hfrobPSL_sq
    · intro t ht
      rcases ht with ⟨a, rfl⟩
      simpa using hfrobPSL_conj a
    · simpa [nonsplitDihedralCandidate] using
        hnonsplitCandidate_card_raw
    · intro R hR hRne
      simpa [nonsplitDihedralCandidate] using
        hnonsplit_normalizer_eq_candidate_of_le R hR hRne
  · intro A _hdisc_nonzero heigen
    let qSL : Matrix.SpecialLinearGroup (Fin 2) F →* PSL2MatrixGroup F :=
      QuotientGroup.mk' (Subgroup.center
        (Matrix.SpecialLinearGroup (Fin 2) F))
    let M : Matrix (Fin 2) (Fin 2) F := A
    let χ : Polynomial F := M.charpoly
    have hχdeg : χ.natDegree = 2 := by
      simpa [χ, M] using Matrix.charpoly_natDegree_eq_dim M
    have hχne : χ ≠ 0 := by
      exact (Matrix.charpoly_monic M).ne_zero
    have hno_root (μ : F) : ¬ χ.IsRoot μ := by
      intro hroot
      have hdet_zero :
          (Matrix.scalar (Fin 2) μ - M).det = 0 := by
        rw [← Matrix.eval_charpoly]
        exact hroot
      obtain ⟨v, hv_ne, hv⟩ :=
        Matrix.exists_mulVec_eq_zero_iff.mpr hdet_zero
      apply heigen
      refine ⟨μ, v, hv_ne, ?_⟩
      have hscalar :
          (Matrix.scalar (Fin 2) μ).mulVec v = μ • v := by
        ext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct]
      rw [Matrix.sub_mulVec, hscalar] at hv
      exact (sub_eq_zero.mp hv).symm
    have hχroots : χ.roots = 0 := by
      apply Multiset.eq_zero_of_forall_notMem
      intro μ hμ
      exact hno_root μ ((Polynomial.mem_roots hχne).mp hμ)
    have hχirreducible : Irreducible χ := by
      apply ((Matrix.charpoly_monic M).irreducible_iff_roots_eq_zero_of_degree_le_three
        (by rw [hχdeg]) (by rw [hχdeg]; norm_num)).mpr
      exact hχroots
    haveI : Fact (Irreducible χ) := ⟨hχirreducible⟩
    letI : Algebra F (AdjoinRoot χ) := AdjoinRoot.instAlgebra χ
    letI : Module F (AdjoinRoot χ) := Algebra.toModule
    have hfinrankL : Module.finrank F (AdjoinRoot χ) = 2 := by
      calc
        Module.finrank F (AdjoinRoot χ) =
            (AdjoinRoot.powerBasis hχne).dim :=
          (AdjoinRoot.powerBasis hχne).finrank
        _ = χ.natDegree := AdjoinRoot.powerBasis_dim hχne
        _ = 2 := hχdeg
    let eL : AdjoinRoot χ ≃ₐ[F] E :=
      FiniteField.algEquivExtension F p 2 (AdjoinRoot χ) hfinrankL
    let α : E := eL (AdjoinRoot.root χ)
    have hα_root : (χ.map (algebraMap F E)).IsRoot α := by
      have hrootL := AdjoinRoot.isRoot_root χ
      have hrootE :
          ((χ.map (AdjoinRoot.of χ)).map eL.toRingEquiv.toRingHom).IsRoot
            (eL (AdjoinRoot.root χ)) := hrootL.map
      rw [Polynomial.map_map] at hrootE
      convert hrootE using 1
      congr 1
      ext r
      simp [eL]
    have hα_not_scalar (r : F) : algebraMap F E r ≠ α := by
      intro hr
      apply hno_root r
      apply (Polynomial.isRoot_map_iff
        ((algebraMap F E).injective)).mp
      rw [hr]
      exact hα_root
    have hdetA : M.det = 1 := by
      exact A.property
    have hα_poly : α ^ 2 - algebraMap F E (Matrix.trace M) * α + 1 = 0 := by
      have h := hα_root
      simpa [Polynomial.IsRoot, χ, Matrix.charpoly_fin_two, hdetA] using h
    have hα_sq : α * α = algebraMap F E (Matrix.trace M) * α - 1 := by
      rw [pow_two] at hα_poly
      linear_combination hα_poly
    let αfamily : Fin 2 → E := ![α, 1]
    have hαLI : LinearIndependent F αfamily := by
      rw [linearIndependent_fin2]
      refine ⟨one_ne_zero, ?_⟩
      intro r hr
      exact hα_not_scalar r (by
        simpa [αfamily, Algebra.smul_def] using hr)
    have hfinrankE : Module.finrank F E = 2 := by
      simpa [E] using FiniteField.finrank_extension F p 2
    let bα : Module.Basis (Fin 2) F E :=
      basisOfLinearIndependentOfCardEqFinrank hαLI (by
        simpa [hfinrankE])
    let v : Fin 2 → F := ![1, 0]
    let w : Fin 2 → F := M.mulVec v
    have hv_ne : v ≠ 0 := by
      intro hv
      have := congrFun hv 0
      simpa [v] using this
    let Afamily : Fin 2 → (Fin 2 → F) := ![w, v]
    have hALI : LinearIndependent F Afamily := by
      rw [linearIndependent_fin2]
      refine ⟨hv_ne, ?_⟩
      intro μ hμ
      apply heigen
      refine ⟨μ, v, hv_ne, ?_⟩
      simpa [Afamily, w] using hμ.symm
    let bA : Module.Basis (Fin 2) F (Fin 2 → F) :=
      basisOfLinearIndependentOfCardEqFinrank hALI (by simp)
    have hbα_zero : bα 0 = α := by
      simp [bα, αfamily]
    have hbα_one : bα 1 = 1 := by
      simp [bα, αfamily]
    have hbA_zero : bA 0 = w := by
      simp [bA, Afamily]
    have hbA_one : bA 1 = v := by
      simp [bA, Afamily]
    let H : E ≃ₗ[F] (Fin 2 → F) := bα.equiv bA (Equiv.refl (Fin 2))
    have hH_basis (i : Fin 2) : H (bα i) = bA i := by
      simp [H]
    have hH_alpha : H α = w := by
      rw [← hbα_zero, hH_basis, hbA_zero]
    have hH_one : H 1 = v := by
      rw [← hbα_one, hH_basis, hbA_one]
    have hdet_coord :
        M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
      simpa [Matrix.det_fin_two] using hdetA
    have hAw : M.mulVec w = Matrix.trace M • w - v := by
      ext i
      fin_cases i
      · simp [w, v, Matrix.mulVec, dotProduct, Matrix.trace_fin_two]
        linear_combination -hdet_coord
      · simp [w, v, Matrix.mulVec, dotProduct, Matrix.trace_fin_two]
        ring
    have hlin :
        H.toLinearMap.comp (Algebra.lmul F E α) =
          M.mulVecLin.comp H.toLinearMap := by
      apply Module.Basis.ext bα
      intro i
      fin_cases i
      · change H (α * bα 0) = M.mulVec (H (bα 0))
        rw [hbα_zero, hH_alpha]
        calc
          H (α * α) = H (algebraMap F E (Matrix.trace M) * α - 1) :=
            congrArg H hα_sq
          _ = Matrix.trace M • H α - H 1 := by
            change H (Matrix.trace M • α - 1) = _
            rw [map_sub, map_smul]
          _ = Matrix.trace M • w - v := by rw [hH_alpha, hH_one]
          _ = M.mulVec w := hAw.symm
      · change H (α * bα 1) = M.mulVec (H (bα 1))
        rw [hbα_one, mul_one, hH_alpha, hH_one]
    let std : Module.Basis (Fin 2) F (Fin 2 → F) := Pi.basisFun F (Fin 2)
    let D : Matrix (Fin 2) (Fin 2) F :=
      LinearMap.toMatrix b std H.toLinearMap
    let B : Matrix (Fin 2) (Fin 2) F := Algebra.leftMulMatrix b α
    have hMmatrix : LinearMap.toMatrix std std M.mulVecLin = M := by
      change LinearMap.toMatrix' (Matrix.toLin' M) = M
      exact LinearMap.toMatrix'_toLin' M
    have hMD : M * D = D * B := by
      calc
        M * D =
            LinearMap.toMatrix std std M.mulVecLin *
              LinearMap.toMatrix b std H.toLinearMap := by rw [hMmatrix]
        _ = LinearMap.toMatrix b std
            (M.mulVecLin.comp H.toLinearMap) :=
          (LinearMap.toMatrix_comp b std std M.mulVecLin H.toLinearMap).symm
        _ = LinearMap.toMatrix b std
            (H.toLinearMap.comp (Algebra.lmul F E α)) := by rw [hlin]
        _ = LinearMap.toMatrix b std H.toLinearMap *
            LinearMap.toMatrix b b (Algebra.lmul F E α) :=
          LinearMap.toMatrix_comp b b std H.toLinearMap (Algebra.lmul F E α)
        _ = D * B := by rfl
    have hDunit : IsUnit D.det := by
      change IsUnit (LinearMap.toMatrix b std H.toLinearMap).det
      exact H.isUnit_det b std
    have hDne : D.det ≠ 0 := hDunit.ne_zero
    have hdet_eq := congrArg Matrix.det hMD
    rw [Matrix.det_mul, Matrix.det_mul] at hdet_eq
    have hBdet : B.det = 1 := by
      apply mul_left_cancel₀ hDne
      calc
        D.det * B.det = M.det * D.det := hdet_eq.symm
        _ = 1 * D.det := by rw [hdetA]
        _ = D.det * 1 := by simp
    have hnormα : Algebra.norm F α = 1 := by
      calc
        Algebra.norm F α = B.det := by
          simpa [B] using Algebra.norm_eq_matrix_det b α
        _ = 1 := hBdet
    have hαne : α ≠ 0 := by
      intro hα
      have := hnormα
      rw [hα, Algebra.norm_zero] at this
      exact zero_ne_one this
    let αunit : Eˣ := Units.mk0 α hαne
    let xK : K := ⟨αunit, by
      change normUnits αunit = 1
      apply Units.ext
      simpa [normUnits, αunit] using hnormα⟩
    obtain ⟨d, hd⟩ := hDunit
    obtain ⟨c, hc⟩ := hnormUnits_surjective d⁻¹
    have hcval : Algebra.norm F (c : E) = (d⁻¹ : Fˣ) := by
      have hc' := congrArg Units.val hc
      simpa [normUnits] using hc'
    let Lc : Matrix (Fin 2) (Fin 2) F := Algebra.leftMulMatrix b (c : E)
    let Gmat : Matrix (Fin 2) (Fin 2) F := D * Lc
    have hGdet : Gmat.det = 1 := by
      change (D * Lc).det = 1
      rw [Matrix.det_mul]
      change D.det * (Algebra.leftMulMatrix b (c : E)).det = 1
      rw [← Algebra.norm_eq_matrix_det b, hcval, ← hd]
      exact Units.mul_inv d
    let G : Matrix.SpecialLinearGroup (Fin 2) F := ⟨Gmat, hGdet⟩
    have hBLc : B * Lc = Lc * B := by
      calc
        B * Lc = Algebra.leftMulMatrix b (α * (c : E)) := by
          simp [B, Lc]
        _ = Algebra.leftMulMatrix b ((c : E) * α) := by rw [mul_comm]
        _ = Lc * B := by simp [B, Lc]
    have hMG : M * Gmat = Gmat * B := by
      calc
        M * Gmat = (M * D) * Lc := by simp [Gmat, Matrix.mul_assoc]
        _ = (D * B) * Lc := by rw [hMD]
        _ = D * (B * Lc) := by rw [Matrix.mul_assoc]
        _ = D * (Lc * B) := by rw [hBLc]
        _ = (D * Lc) * B := by rw [Matrix.mul_assoc]
        _ = Gmat * B := rfl
    have hxB :
        (nonsplitSL xK : Matrix.SpecialLinearGroup (Fin 2) F) =
          ⟨B, hBdet⟩ := by
      apply Subtype.ext
      rfl
    have hMGsl : A * G = G * nonsplitSL xK := by
      apply Subtype.ext
      change M * Gmat = Gmat * (nonsplitSL xK : Matrix.SpecialLinearGroup (Fin 2) F).1
      rw [hxB]
      exact hMG
    have hA_factor : A = G * nonsplitSL xK * G⁻¹ := by
      calc
        A = (A * G) * G⁻¹ := by simp
        _ = (G * nonsplitSL xK) * G⁻¹ := by rw [hMGsl]
    refine ⟨qSL G, ?_⟩
    refine ⟨nonsplitTorus xK, ⟨xK, rfl⟩, ?_⟩
    change qSL G * nonsplitTorus xK * (qSL G)⁻¹ = qSL A
    rw [hA_factor]
    simp [nonsplitTorus, qSL]
set_option maxHeartbeats 1000000 in

/-- Huppert II.8.4(a,b), retaining the Frobenius reflection and its inversion
action on the standard nonsplit torus. -/
public theorem huppert_II_8_4_nonsplit_torus_reflection_data
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) :
    ∃ S : Subgroup (PSL2MatrixGroup F),
      ∃ w : PSL2MatrixGroup F,
      IsCyclic S ∧
      Nat.card S =
        (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      w ∈ Subgroup.normalizer (S : Set (PSL2MatrixGroup F)) ∧
      w ∉ S ∧
      w * w = 1 ∧
      (∀ t : PSL2MatrixGroup F, t ∈ S → w * t * w⁻¹ = t⁻¹) ∧
      Nat.card (S ⊔ Subgroup.zpowers w :
        Subgroup (PSL2MatrixGroup F)) = 2 * Nat.card S ∧
      ∀ R : Subgroup (PSL2MatrixGroup F), R ≤ S → R ≠ ⊥ →
        Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) =
          S ⊔ Subgroup.zpowers w := by
  obtain ⟨S, hS_cyclic, hS_card, _hS_normalizer,
      ⟨w, hwN, hwS, hwsq, hwinv, hcandidate_card, hnormalizer⟩,
      _hweakTI, _hcover⟩ := h84_nonsplit_torus_data hFcard
  exact ⟨S, w, hS_cyclic, hS_card, hwN, hwS, hwsq, hwinv,
    hcandidate_card, hnormalizer⟩

/-- Huppert II.8.4(a,b), for the canonical nonsplit torus and its normalizer. -/
public theorem huppert_II_8_4_nonsplit_torus_normalizer_card
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) :
    ∃ S : Subgroup (PSL2MatrixGroup F),
      IsCyclic S ∧
      Nat.card S =
        (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      Nat.card (Subgroup.normalizer (S : Set (PSL2MatrixGroup F))) =
        2 * Nat.card S := by
  obtain ⟨S, hS_cyclic, hS_card, hS_normalizer, _, _, _⟩ :=
    h84_nonsplit_torus_data hFcard
  exact ⟨S, hS_cyclic, hS_card, hS_normalizer⟩
private theorem hmem_eq_one_of_coprime_card
    {G : Type u} [Group G] [Finite G]
    (A B : Subgroup G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card B))
    {x : G} (hxA : x ∈ A) (hxB : x ∈ B) :
    x = 1 := by
  have horder_A : orderOf x ∣ Nat.card A := by
    simpa [Subgroup.orderOf_coe] using
      (orderOf_dvd_natCard (⟨x, hxA⟩ : A))
  have horder_B : orderOf x ∣ Nat.card B := by
    simpa [Subgroup.orderOf_coe] using
      (orderOf_dvd_natCard (⟨x, hxB⟩ : B))
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcoprime horder_A horder_B)

private theorem hq_coprime_split_order (q : ℕ) (hq : 1 ≤ q) :
    Nat.Coprime q ((q - 1) / Nat.gcd (q - 1) 2) := by
  apply ((Nat.coprime_self_sub_right hq).mpr (Nat.coprime_one_right q)).coprime_dvd_right
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left (q - 1) 2)

private theorem hq_coprime_nonsplit_order (q : ℕ) (hq : 1 ≤ q) :
    Nat.Coprime q ((q + 1) / Nat.gcd (q - 1) 2) := by
  apply ((Nat.coprime_self_add_right).mpr (Nat.coprime_one_right q)).coprime_dvd_right
  apply Nat.div_dvd_of_dvd
  convert Nat.dvd_add (Nat.gcd_dvd_left (q - 1) 2)
    (Nat.gcd_dvd_right (q - 1) 2) using 1 <;> omega

private theorem hsplit_nonsplit_order_coprime (q : ℕ) (hq : 2 ≤ q) :
    Nat.Coprime
      ((q - 1) / Nat.gcd (q - 1) 2)
      ((q + 1) / Nat.gcd (q - 1) 2) := by
  by_cases hq_even : Even q
  · have hq_sub_one_odd : Odd (q - 1) := by
      rw [← Nat.not_even_iff_odd]
      intro heven
      have hparity := (Nat.even_sub (by omega : 1 ≤ q)).mp heven
      exact Nat.not_even_one (hparity.mp hq_even)
    have hgcd : Nat.gcd (q - 1) 2 = 1 :=
      Nat.coprime_iff_gcd_eq_one.mp hq_sub_one_odd.coprime_two_right
    rw [hgcd]
    simp only [Nat.div_one]
    have hcop : Nat.Coprime (q - 1) ((q - 1) + 2) :=
      (Nat.coprime_self_add_right).mpr hq_sub_one_odd.coprime_two_right
    convert hcop using 1 <;> omega
  · have hq_odd : Odd q := Nat.not_even_iff_odd.mp hq_even
    have htwo_dvd : 2 ∣ q - 1 := by
      rcases hq_odd with ⟨k, hk⟩
      use k
      omega
    have hgcd : Nat.gcd (q - 1) 2 = 2 :=
      Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
        (Nat.dvd_gcd htwo_dvd (dvd_refl 2))
    rcases hq_odd with ⟨k, hk⟩
    rw [hgcd]
    have hsub : q - 1 = 2 * k := by omega
    have hadd : q + 1 = 2 * (k + 1) := by omega
    rw [hsub, hadd]
    rw [Nat.mul_div_cancel_left k (by omega),
      Nat.mul_div_cancel_left (k + 1) (by omega)]
    exact (Nat.coprime_self_add_right).mpr (Nat.coprime_one_right k)
private theorem hconjugate_family_unique_of_weak_ti
    {G : Type u} [Group G] (U : Subgroup G)
    (hweakTI : ∀ y : G, y ∈ U → y ≠ 1 → ∀ g : G,
      g * y * g⁻¹ ∈ U → g ∈ Subgroup.normalizer (U : Set G)) :
    ∀ x : G, x ≠ 1 → ∀ g₁ g₂,
      x ∈ U.map (MulAut.conj g₁).toMonoidHom →
      x ∈ U.map (MulAut.conj g₂).toMonoidHom →
      U.map (MulAut.conj g₁).toMonoidHom =
        U.map (MulAut.conj g₂).toMonoidHom := by
  intro x hx g₁ g₂ hx₁ hx₂
  rcases hx₁ with ⟨a, haU, ha⟩
  rcases hx₂ with ⟨b, hbU, hb⟩
  have ha' : g₁ * a * g₁⁻¹ = x := by
    simpa [MulAut.conj_apply] using ha
  have hb' : g₂ * b * g₂⁻¹ = x := by
    simpa [MulAut.conj_apply] using hb
  have ha_ne : a ≠ 1 := by
    intro ha_one
    apply hx
    rw [← ha']
    simp [ha_one]
  have hb_ne : b ≠ 1 := by
    intro hb_one
    apply hx
    rw [← hb']
    simp [hb_one]
  let g : G := g₁⁻¹ * g₂
  have hconj : g * b * g⁻¹ = a := by
    change (g₁⁻¹ * g₂) * b * (g₁⁻¹ * g₂)⁻¹ = a
    calc
      (g₁⁻¹ * g₂) * b * (g₁⁻¹ * g₂)⁻¹ =
          g₁⁻¹ * (g₂ * b * g₂⁻¹) * g₁ := by group
      _ = g₁⁻¹ * x * g₁ := by rw [hb']
      _ = a := by rw [← ha']; group
  have hgN : g ∈ Subgroup.normalizer (U : Set G) :=
    hweakTI b hbU hb_ne g (by simpa [hconj] using haU)
  have hmapg :
      U.map (MulAut.conj g).toMonoidHom = U := by
    rw [← Subgroup.conjAct_pointwise_smul_iff] at hgN
    change U.map (MulAut.conj g).toMonoidHom = U at hgN
    exact hgN
  have hgprod : g₁ * g = g₂ := by
    simp [g]
  calc
    U.map (MulAut.conj g₁).toMonoidHom =
        (U.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj g₁).toMonoidHom := by rw [hmapg]
    _ = U.map (MulAut.conj (g₁ * g)).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext y
      simp [MulAut.conj_apply, mul_assoc]
    _ = U.map (MulAut.conj g₂).toMonoidHom := by rw [hgprod]
private theorem hthree_family_unique_of_same_family
    {G : Type u} [Group G] [Finite G]
    (P U S : Subgroup G)
    (hPU : Nat.Coprime (Nat.card P) (Nat.card U))
    (hPS : Nat.Coprime (Nat.card P) (Nat.card S))
    (hUS : Nat.Coprime (Nat.card U) (Nat.card S))
    (hsameP : ∀ x : G, x ≠ 1 → ∀ g₁ g₂,
      x ∈ P.map (MulAut.conj g₁).toMonoidHom →
      x ∈ P.map (MulAut.conj g₂).toMonoidHom →
      P.map (MulAut.conj g₁).toMonoidHom =
        P.map (MulAut.conj g₂).toMonoidHom)
    (hsameU : ∀ x : G, x ≠ 1 → ∀ g₁ g₂,
      x ∈ U.map (MulAut.conj g₁).toMonoidHom →
      x ∈ U.map (MulAut.conj g₂).toMonoidHom →
      U.map (MulAut.conj g₁).toMonoidHom =
        U.map (MulAut.conj g₂).toMonoidHom)
    (hsameS : ∀ x : G, x ≠ 1 → ∀ g₁ g₂,
      x ∈ S.map (MulAut.conj g₁).toMonoidHom →
      x ∈ S.map (MulAut.conj g₂).toMonoidHom →
      S.map (MulAut.conj g₁).toMonoidHom =
        S.map (MulAut.conj g₂).toMonoidHom) :
    ∀ x : G, x ≠ 1 →
      ∀ T₁ T₂ : Subgroup G, x ∈ T₁ → x ∈ T₂ →
      ((∃ g, T₁ = P.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, T₁ = U.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, T₁ = S.map (MulAut.conj g).toMonoidHom)) →
      ((∃ g, T₂ = P.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, T₂ = U.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, T₂ = S.map (MulAut.conj g).toMonoidHom)) →
      T₁ = T₂ := by
  intro x hx T₁ T₂ hx₁ hx₂ hT₁ hT₂
  rcases hT₁ with ⟨g₁, rfl⟩ | ⟨g₁, rfl⟩ | ⟨g₁, rfl⟩ <;>
    rcases hT₂ with ⟨g₂, rfl⟩ | ⟨g₂, rfl⟩ | ⟨g₂, rfl⟩
  · exact hsameP x hx g₁ g₂ hx₁ hx₂
  · exact (hx (hmem_eq_one_of_coprime_card _ _ (by
      rw [Subgroup.card_map_of_injective (K := P)
          (f := (MulAut.conj g₁).toMonoidHom) (MulAut.conj g₁).injective,
        Subgroup.card_map_of_injective (K := U)
          (f := (MulAut.conj g₂).toMonoidHom) (MulAut.conj g₂).injective]
      exact hPU) hx₁ hx₂)).elim
  · exact (hx (hmem_eq_one_of_coprime_card _ _ (by
      rw [Subgroup.card_map_of_injective (K := P)
          (f := (MulAut.conj g₁).toMonoidHom) (MulAut.conj g₁).injective,
        Subgroup.card_map_of_injective (K := S)
          (f := (MulAut.conj g₂).toMonoidHom) (MulAut.conj g₂).injective]
      exact hPS) hx₁ hx₂)).elim
  · exact (hx (hmem_eq_one_of_coprime_card _ _ (by
      rw [Subgroup.card_map_of_injective (K := U)
          (f := (MulAut.conj g₁).toMonoidHom) (MulAut.conj g₁).injective,
        Subgroup.card_map_of_injective (K := P)
          (f := (MulAut.conj g₂).toMonoidHom) (MulAut.conj g₂).injective]
      exact hPU.symm) hx₁ hx₂)).elim
  · exact hsameU x hx g₁ g₂ hx₁ hx₂
  · exact (hx (hmem_eq_one_of_coprime_card _ _ (by
      rw [Subgroup.card_map_of_injective (K := U)
          (f := (MulAut.conj g₁).toMonoidHom) (MulAut.conj g₁).injective,
        Subgroup.card_map_of_injective (K := S)
          (f := (MulAut.conj g₂).toMonoidHom) (MulAut.conj g₂).injective]
      exact hUS) hx₁ hx₂)).elim
  · exact (hx (hmem_eq_one_of_coprime_card _ _ (by
      rw [Subgroup.card_map_of_injective (K := S)
          (f := (MulAut.conj g₁).toMonoidHom) (MulAut.conj g₁).injective,
        Subgroup.card_map_of_injective (K := P)
          (f := (MulAut.conj g₂).toMonoidHom) (MulAut.conj g₂).injective]
      exact hPS.symm) hx₁ hx₂)).elim
  · exact (hx (hmem_eq_one_of_coprime_card _ _ (by
      rw [Subgroup.card_map_of_injective (K := S)
          (f := (MulAut.conj g₁).toMonoidHom) (MulAut.conj g₁).injective,
        Subgroup.card_map_of_injective (K := U)
          (f := (MulAut.conj g₂).toMonoidHom) (MulAut.conj g₂).injective]
      exact hUS.symm) hx₁ hx₂)).elim
  · exact hsameS x hx g₁ g₂ hx₁ hx₂

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Huppert II.8.5(a), with the covering and TI uniqueness clauses tied to
the same standard split and nonsplit tori. -/
public theorem huppert_II_8_5_a_psl2_cover
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f)
    (P : Sylow p (PSL2MatrixGroup F)) :
    ∃ U S : Subgroup (PSL2MatrixGroup F),
      IsCyclic U ∧
      Nat.card U =
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      IsCyclic S ∧
      Nat.card S =
        (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      ∀ x : PSL2MatrixGroup F, x ≠ 1 →
        ∃! T : Subgroup (PSL2MatrixGroup F),
          x ∈ T ∧
            ((∃ g, T = (P : Subgroup (PSL2MatrixGroup F)).map
              (MulAut.conj g).toMonoidHom) ∨
            (∃ g, T = U.map (MulAut.conj g).toMonoidHom) ∨
            (∃ g, T = S.map (MulAut.conj g).toMonoidHom)) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F p :=
    charP_of_card_eq_prime_pow (by simpa using hFcard)
  let qSL : Matrix.SpecialLinearGroup (Fin 2) F →* PSL2MatrixGroup F :=
    QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
  let unipotentSL :
      AddChar F (Matrix.SpecialLinearGroup (Fin 2) F) :=
    { toFun := fun a => ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two]⟩
      map_zero_eq_one' := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      map_add_eq_mul' := by
        intro a b
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, add_comm] }
  let unipotent : AddChar F (PSL2MatrixGroup F) :=
    qSL.compAddChar unipotentSL
  have h_unipotent_injective : Function.Injective unipotent := by
    intro a b hab
    have hdiff : unipotent (a - b) = 1 := by
      rw [sub_eq_add_neg, unipotent.map_add_eq_mul,
        unipotent.map_neg_eq_inv, hab, mul_inv_cancel]
    have hcenter :
        unipotentSL (a - b) ∈
          Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
      (QuotientGroup.eq_one_iff (unipotentSL (a - b))).mp hdiff
    have hscalar :=
      Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hcenter (0 : Fin 2)
    have hab0 := congrFun (congrFun hscalar (0 : Fin 2)) (1 : Fin 2)
    apply sub_eq_zero.mp
    simpa using hab0.symm
  let U₀ : Subgroup (PSL2MatrixGroup F) := unipotent.toMonoidHom.range
  have hU₀card : Nat.card U₀ = Nat.card F := by
    let e : Multiplicative F ≃ U₀ :=
      Equiv.ofInjective unipotent.toMonoidHom h_unipotent_injective
    exact Nat.card_congr e.symm
  have hU₀_isPGroup : IsPGroup p U₀ := by
    apply IsPGroup.of_card
    rw [hU₀card, hFcard]
  obtain ⟨Q, hU₀_le_Q⟩ := hU₀_isPGroup.exists_le_sylow
  have hQcard : Nat.card (Q : Subgroup (PSL2MatrixGroup F)) = Nat.card F := by
    rcases huppert_II_8_2_a_sylow_equiv_additive hFcard Q with ⟨eQ⟩
    exact (Nat.card_congr eQ.toEquiv).symm
  have hU₀_eq_Q : U₀ = (Q : Subgroup (PSL2MatrixGroup F)) :=
    Subgroup.eq_of_le_of_card_ge hU₀_le_Q (by rw [hQcard, hU₀card])
  obtain ⟨kP, hkP⟩ := MulAction.exists_smul_eq
    (α := Sylow p (PSL2MatrixGroup F)) (PSL2MatrixGroup F) P Q
  have hP_to_U₀ :
      (P : Subgroup (PSL2MatrixGroup F)).map
        (MulAut.conj kP).toMonoidHom = U₀ := by
    have hkP' := congrArg
      (fun R : Sylow p (PSL2MatrixGroup F) =>
        (R : Subgroup (PSL2MatrixGroup F))) hkP
    simpa [hU₀_eq_Q] using hkP'
  have hupper_unipotent_conj
      (A : Matrix.SpecialLinearGroup (Fin 2) F)
      (hA10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
      (t : F) :
      A * unipotentSL t * A⁻¹ =
        unipotentSL
          ((A : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * t) := by
    have hdet :
        (A : Matrix (Fin 2) (Fin 2) F) 0 0 *
            (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
      have h := A.property
      rw [Matrix.det_fin_two, hA10, mul_zero, sub_zero] at h
      exact h
    have hdet' :
        (A : Matrix (Fin 2) (Fin 2) F) 1 1 *
            (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
      rw [mul_comm, hdet]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [unipotentSL, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.adjugate_fin_two, Matrix.mul_apply, hA10, hdet, hdet',
        pow_two] <;>
      ring
  have hU₀_weakTI :
      ∀ y : PSL2MatrixGroup F, y ∈ U₀ → y ≠ 1 →
        ∀ g : PSL2MatrixGroup F,
          g * y * g⁻¹ ∈ U₀ →
            g ∈ Subgroup.normalizer (U₀ : Set (PSL2MatrixGroup F)) := by
    intro y hy hy_ne g hgy
    rcases hy with ⟨a, rfl⟩
    have ha_ne_zero : a.toAdd ≠ 0 := by
      intro ha_zero
      apply hy_ne
      change unipotent a.toAdd = 1
      rw [ha_zero]
      exact unipotent.map_zero_eq_one
    refine QuotientGroup.induction_on g ?_ hgy
    intro A hAconj
    rcases hAconj with ⟨b, hb⟩
    have hq :
        qSL (unipotentSL b.toAdd) =
          qSL (A * unipotentSL a.toAdd * A⁻¹) := by
      simpa [qSL, unipotent] using hb
    rcases (QuotientGroup.mk'_eq_mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).mp hq with
      ⟨z, hz, hzeq⟩
    have hzeqA :
        unipotentSL b.toAdd * z * A =
          A * unipotentSL a.toAdd := by
      calc
        unipotentSL b.toAdd * z * A =
            (A * unipotentSL a.toAdd * A⁻¹) * A := by rw [hzeq]
        _ = A * unipotentSL a.toAdd := by group
    let r : F := (z : Matrix (Fin 2) (Fin 2) F) 0 0
    have hscalar :
        Matrix.scalar (Fin 2) r =
          (z : Matrix.SpecialLinearGroup (Fin 2) F) := by
      simpa [r] using
        Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hz (0 : Fin 2)
    have hmat := congrArg Subtype.val hzeqA
    change (unipotentSL b.toAdd : Matrix (Fin 2) (Fin 2) F) *
        (z : Matrix (Fin 2) (Fin 2) F) *
          (A : Matrix (Fin 2) (Fin 2) F) =
      (A : Matrix (Fin 2) (Fin 2) F) *
        (unipotentSL a.toAdd : Matrix (Fin 2) (Fin 2) F) at hmat
    rw [← hscalar] at hmat
    have h10 := congrFun (congrFun hmat (1 : Fin 2)) (0 : Fin 2)
    have h11 := congrFun (congrFun hmat (1 : Fin 2)) (1 : Fin 2)
    simp [unipotentSL, Matrix.mul_apply] at h10 h11
    have hr_one : r = 1 := by
      by_cases hA10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
      · have hA11_ne :
            (A : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
          intro hA11
          have hdet := A.property
          rw [Matrix.det_fin_two, hA10, hA11, mul_zero, mul_zero,
            sub_zero] at hdet
          exact zero_ne_one hdet
        apply mul_right_cancel₀ hA11_ne
        simpa [hA10, mul_assoc] using h11
      · apply mul_right_cancel₀ hA10
        simpa [mul_assoc] using h10
    have hA10 :
        (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      have hprod :
          (A : Matrix (Fin 2) (Fin 2) F) 1 0 * a.toAdd = 0 := by
        simpa [hr_one, mul_comm, mul_left_comm, mul_assoc] using h11
      exact (mul_eq_zero.mp hprod).resolve_right ha_ne_zero
    have hmap_le :
        U₀.map (MulAut.conj (qSL A)).toMonoidHom ≤ U₀ := by
      intro v hv
      rcases hv with ⟨w, hw, rfl⟩
      rcases hw with ⟨t, rfl⟩
      refine ⟨Multiplicative.ofAdd
        ((A : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * t.toAdd), ?_⟩
      change unipotent
          ((A : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * t.toAdd) =
        (MulAut.conj (qSL A)).toMonoidHom (unipotent t.toAdd)
      have hc := congrArg qSL
        (hupper_unipotent_conj A hA10 t.toAdd)
      simpa [qSL, unipotent, MulAut.conj_apply] using hc.symm
    have hmap_eq :
        U₀.map (MulAut.conj (qSL A)).toMonoidHom = U₀ := by
      apply Subgroup.eq_of_le_of_card_ge hmap_le
      rw [Subgroup.card_map_of_injective
        (K := U₀) (f := (MulAut.conj (qSL A)).toMonoidHom)
          (MulAut.conj (qSL A)).injective]
    rw [← Subgroup.conjAct_pointwise_smul_iff]
    exact hmap_eq
  have hU₀_same_family :=
    hconjugate_family_unique_of_weak_ti U₀ hU₀_weakTI
  have hprojective_TI_P :
      ∀ x : PSL2MatrixGroup F, x ≠ 1 → ∀ g₁ g₂,
        x ∈ (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g₁).toMonoidHom →
        x ∈ (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g₂).toMonoidHom →
        (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g₁).toMonoidHom =
          (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g₂).toMonoidHom := by
    have hmap (g : PSL2MatrixGroup F) :
        (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g).toMonoidHom =
          U₀.map (MulAut.conj (g * kP⁻¹)).toMonoidHom := by
      rw [← hP_to_U₀, Subgroup.map_map]
      congr 1
      ext y
      simp [MulAut.conj_apply, mul_assoc]
    intro x hx g₁ g₂ hx₁ hx₂
    rw [hmap g₁] at hx₁ ⊢
    rw [hmap g₂] at hx₂ ⊢
    exact hU₀_same_family x hx (g₁ * kP⁻¹) (g₂ * kP⁻¹) hx₁ hx₂
  let splitTorusSL : Fˣ →* Matrix.SpecialLinearGroup (Fin 2) F :=
    { toFun := fun a => ⟨!![(a : F), 0; 0, (a⁻¹ : F)], by
          simp [Matrix.det_fin_two]⟩
      map_one' := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, mul_comm] }
  let splitTorus : Fˣ →* PSL2MatrixGroup F :=
    qSL.comp splitTorusSL
  have hsplit_props :
      IsCyclic splitTorus.range ∧
        Nat.card splitTorus.range =
          (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 := by
    have hf_ne_zero : f ≠ 0 :=
      huppert_II_8_27_field_exponent_ne_zero hFcard
    have hcard_roots :
          Nat.card (rootsOfUnity 2 F) =
            Nat.gcd (Nat.card F - 1) 2 := by
        let e :=
          Equiv.Set.image ((↑) : Fˣ → F) (rootsOfUnity 2 F : Set Fˣ)
            Units.val_injective
        have he :
            Nat.card (rootsOfUnity 2 F) =
              Nat.card (((↑) : Fˣ → F) '' (rootsOfUnity 2 F : Set Fˣ)) :=
          Nat.card_congr e
        rw [Units.val_set_image_rootsOfUnity_two] at he
        by_cases hp_two : p = 2
        · have htwo : (2 : F) = 0 := by
            subst p
            exact CharP.cast_eq_zero F 2
          have hneg_one : (-1 : F) = 1 := by
            apply (neg_eq_iff_add_eq_zero).2
            have hone_add_one : (1 : F) + 1 = 0 := by
              rw [show (1 : F) + 1 = 2 by norm_num, htwo]
            exact hone_add_one
          have hleft : Nat.card (rootsOfUnity 2 F) = 1 := by
            simpa [hneg_one] using he
          have hq_even : Even (Nat.card F) := by
            obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hf_ne_zero
            rw [hFcard, hp_two, hk, pow_succ]
            use 2 ^ k
            ring
          have hq_sub_one_odd : Odd (Nat.card F - 1) := by
            rw [← Nat.not_even_iff_odd]
            intro heven
            have hparity :=
              (Nat.even_sub (show 1 ≤ Nat.card F from (Finite.one_lt_card (α := F)).le)).mp
                heven
            exact Nat.not_even_one (hparity.mp hq_even)
          have hgcd : Nat.gcd (Nat.card F - 1) 2 = 1 :=
            Nat.coprime_iff_gcd_eq_one.mp hq_sub_one_odd.coprime_two_right
          rw [hleft, hgcd]
        · have hring_char_ne_two : ringChar F ≠ 2 := by
            rw [ringChar.eq F p]
            exact hp_two
          have hneg_one : (-1 : F) ≠ 1 :=
            Ring.neg_one_ne_one_of_char_ne_two hring_char_ne_two
          have hleft : Nat.card (rootsOfUnity 2 F) = 2 := by
            simpa [hneg_one, Ne.symm hneg_one] using he
          have hq_odd : Odd (Nat.card F) := by
            rw [hFcard]
            exact ((Fact.out : p.Prime).odd_of_ne_two hp_two).pow
          have htwo_dvd : 2 ∣ Nat.card F - 1 := by
            rcases hq_odd with ⟨k, hk⟩
            use k
            omega
          have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 :=
            Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
              (Nat.dvd_gcd htwo_dvd (dvd_refl 2))
          rw [hleft, hgcd]
    have hsplit_mem_ker_iff (a : Fˣ) :
        a ∈ splitTorus.ker ↔ a ∈ rootsOfUnity 2 F := by
      rw [MonoidHom.mem_ker, mem_rootsOfUnity]
      constructor
      · intro ha
        have hcenter :
            splitTorusSL a ∈
              Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
          (QuotientGroup.eq_one_iff (splitTorusSL a)).mp ha
        have hscalar :=
          Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hcenter (0 : Fin 2)
        have ha_inv_val := congrFun (congrFun hscalar (1 : Fin 2)) (1 : Fin 2)
        have ha_inv : a = a⁻¹ := by
          apply Units.ext
          simpa [splitTorusSL] using ha_inv_val
        simpa [pow_two] using (eq_inv_iff_mul_eq_one.mp ha_inv)
      · intro ha
        apply (QuotientGroup.eq_one_iff (splitTorusSL a)).mpr
        rw [Matrix.SpecialLinearGroup.mem_center_iff]
        refine ⟨(a : F), ?_, ?_⟩
        · simpa using congrArg Units.val ha
        · have ha_inv : a = a⁻¹ :=
            eq_inv_iff_mul_eq_one.mpr (by simpa [pow_two] using ha)
          have ha_inv_val : (a : F) = (a⁻¹ : F) := by
            simpa using congrArg Units.val ha_inv
          change Matrix.scalar (Fin 2) (a : F) =
            !![(a : F), 0; 0, (a⁻¹ : F)]
          ext i j
          fin_cases i <;> fin_cases j
          · rfl
          · rfl
          · rfl
          · exact ha_inv_val
    have hsplit_ker_eq : splitTorus.ker = rootsOfUnity 2 F := by
      ext a
      exact hsplit_mem_ker_iff a
    have hsplit_ker_card :
        Nat.card splitTorus.ker = Nat.gcd (Nat.card F - 1) 2 := by
      rw [hsplit_ker_eq, hcard_roots]
    have hsplit_range_mul :
        Nat.card splitTorus.range * Nat.gcd (Nat.card F - 1) 2 =
          Nat.card F - 1 := by
      calc
        Nat.card splitTorus.range * Nat.gcd (Nat.card F - 1) 2 =
            splitTorus.ker.index * Nat.card splitTorus.ker := by
          rw [Subgroup.index_ker, hsplit_ker_card]
        _ = Nat.card Fˣ := splitTorus.ker.index_mul_card
        _ = Nat.card F - 1 := by
          simpa [Nat.card_eq_fintype_card] using (Fintype.card_units (α := F))
    have hsplit_range_card :
        Nat.card splitTorus.range =
          (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 := by
      apply Nat.eq_div_of_mul_eq_left
      · rw [← hcard_roots]
        exact Nat.ne_of_gt Nat.card_pos
      · exact hsplit_range_mul
    have hsplit_range_cyclic : IsCyclic splitTorus.range := by
      have hUnitsCyclic : IsCyclic Fˣ := by
        letI : IsCyclic (⊤ : Subgroup Fˣ) := isCyclic_subgroup_units ⊤
        exact isCyclic_of_surjective
          ((⊤ : Subgroup Fˣ).subtype) (by
            intro a
            exact ⟨⟨a, Subgroup.mem_top a⟩, rfl⟩)
      letI : IsCyclic Fˣ := hUnitsCyclic
      exact isCyclic_of_surjective splitTorus.rangeRestrict
        splitTorus.rangeRestrict_surjective
    exact ⟨hsplit_range_cyclic, hsplit_range_card⟩
  have h85_split_semisimple
    (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (hdisc_nonzero :
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ^ 2 ≠ (4 : F))
    (heigen : ∃ (μ : F) (v : Fin 2 → F), v ≠ 0 ∧
      (A : Matrix (Fin 2) (Fin 2) F).mulVec v = μ • v) :
    ∃ g : PSL2MatrixGroup F,
      qSL A ∈ splitTorus.range.map (MulAut.conj g).toMonoidHom := by
    classical
    let trA : F := Matrix.trace (A : Matrix (Fin 2) (Fin 2) F)
    change trA ^ 2 ≠ (4 : F) at hdisc_nonzero
    rcases heigen with ⟨μ, v, hv_ne, hAv⟩
    have hμ_ne : μ ≠ 0 := by
      intro hμ
      subst μ
      have hzero :
          (A : Matrix (Fin 2) (Fin 2) F).mulVec v = 0 := by
        simpa using hAv
      have hrecover :
          ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F).mulVec
              ((A : Matrix (Fin 2) (Fin 2) F).mulVec v) = v := by
        calc
          _ = (((A⁻¹ * A : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F).mulVec v) :=
            Matrix.mulVec_mulVec v _ _
          _ = v := by rw [inv_mul_cancel]; simp
      apply hv_ne
      calc
        v = ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F).mulVec
                ((A : Matrix (Fin 2) (Fin 2) F).mulVec v) := hrecover.symm
        _ = ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F).mulVec 0 := by rw [hzero]
        _ = 0 := by simp
    let a : Fˣ := Units.mk0 μ hμ_ne
    have hdetA :
        Matrix.det (A : Matrix (Fin 2) (Fin 2) F) = 1 := A.property
    have hkernel :
        (Matrix.scalar (Fin 2) μ -
          (A : Matrix (Fin 2) (Fin 2) F)).mulVec v = 0 := by
      rw [Matrix.sub_mulVec]
      have hscalar :
          (Matrix.scalar (Fin 2) μ).mulVec v = μ • v := by
        ext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct]
      rw [hscalar, hAv, sub_self]
    have hdet_zero :
        (Matrix.scalar (Fin 2) μ -
          (A : Matrix (Fin 2) (Fin 2) F)).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv_ne, hkernel⟩
    have hdet_formula (x : F) :
        (Matrix.scalar (Fin 2) x -
          (A : Matrix (Fin 2) (Fin 2) F)).det =
            x ^ 2 - trA * x + 1 := by
      calc
        _ = x ^ 2 - trA * x +
            Matrix.det (A : Matrix (Fin 2) (Fin 2) F) := by
              simp [Matrix.det_fin_two, Matrix.trace_fin_two, trA]
              have hdetCoord := hdetA
              rw [Matrix.det_fin_two] at hdetCoord
              linear_combination hdetCoord
        _ = _ := by rw [hdetA]
    have hpoly : μ ^ 2 - trA * μ + 1 = 0 := by
      rw [← hdet_formula]
      exact hdet_zero
    have htrace_mu : trA = μ + μ⁻¹ := by
      apply mul_right_cancel₀ hμ_ne
      calc
        trA * μ = μ ^ 2 + 1 := by
          linear_combination -hpoly
        _ = (μ + μ⁻¹) * μ := by
          field_simp [hμ_ne]
          <;> ring
    have hμ_ne_inv : μ ≠ μ⁻¹ := by
      intro hμ
      apply hdisc_nonzero
      have hμ_sq : μ ^ 2 = 1 := by
        calc
          μ ^ 2 = μ * μ := by rw [pow_two]
          _ = μ * μ⁻¹ := congrArg (fun z : F => μ * z) hμ
          _ = 1 := mul_inv_cancel₀ hμ_ne
      rw [htrace_mu, ← hμ]
      calc
        (μ + μ) ^ 2 = 4 * μ ^ 2 := by ring
        _ = 4 := by rw [hμ_sq, mul_one]
    have hother_eigen :
        ∃ w : Fin 2 → F, w ≠ 0 ∧
          (A : Matrix (Fin 2) (Fin 2) F).mulVec w = μ⁻¹ • w := by
      have hpoly_inv : (μ⁻¹) ^ 2 - trA * μ⁻¹ + 1 = 0 := by
        rw [htrace_mu]
        field_simp [hμ_ne]
        <;> ring
      have hdet_inv :
          (Matrix.scalar (Fin 2) μ⁻¹ -
            (A : Matrix (Fin 2) (Fin 2) F)).det = 0 := by
        rw [hdet_formula]
        exact hpoly_inv
      obtain ⟨w, hw_ne, hw⟩ :=
        Matrix.exists_mulVec_eq_zero_iff.mpr hdet_inv
      refine ⟨w, hw_ne, ?_⟩
      have hscalar :
          (Matrix.scalar (Fin 2) μ⁻¹).mulVec w = μ⁻¹ • w := by
        ext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct]
      rw [Matrix.sub_mulVec, hscalar] at hw
      exact (sub_eq_zero.mp hw).symm
    rcases hother_eigen with ⟨w, hw_ne, hAw⟩
    have hbasis_conjugates :
        ∃ G : Matrix.SpecialLinearGroup (Fin 2) F,
          A = G * splitTorusSL a * G⁻¹ := by
      let fA : Module.End F (Fin 2 → F) :=
        Matrix.mulVecLin (A : Matrix (Fin 2) (Fin 2) F)
      let eigenvalue : Fin 2 → F := ![μ, μ⁻¹]
      let eigenvector : Fin 2 → (Fin 2 → F) := ![v, w]
      have heigenvalue_injective : Function.Injective eigenvalue := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · exact (hμ_ne_inv (by simpa [eigenvalue] using hij)).elim
        · exact (hμ_ne_inv (by simpa [eigenvalue] using hij.symm)).elim
        · rfl
      have heigenvector :
          ∀ i, fA.HasEigenvector (eigenvalue i) (eigenvector i) := by
        intro i
        fin_cases i
        · refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
          · simpa [fA, eigenvalue, eigenvector,
              Matrix.mulVecLin_apply] using hAv
          · simpa [eigenvector] using hv_ne
        · refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
          · simpa [fA, eigenvalue, eigenvector,
              Matrix.mulVecLin_apply] using hAw
          · simpa [eigenvector] using hw_ne
      have hlinearIndependent :
          LinearIndependent F eigenvector :=
        Module.End.eigenvectors_linearIndependent' fA eigenvalue
          heigenvalue_injective eigenvector heigenvector
      let δ : F := v 0 * w 1 - w 0 * v 1
      have hδ_ne : δ ≠ 0 := by
        intro hδ
        have hcoeff := Fintype.linearIndependent_iff.mp hlinearIndependent
        by_cases hv1 : v 1 = 0
        · have hv0 : v 0 ≠ 0 := by
            intro hv0
            apply hv_ne
            funext i
            fin_cases i <;> assumption
          have hw1 : w 1 = 0 := by
            apply mul_left_cancel₀ hv0
            have : v 0 * w 1 = 0 := by
              simpa [δ, hv1] using hδ
            simpa using this
          let c : Fin 2 → F := ![w 0, -v 0]
          have hsum : ∑ i, c i • eigenvector i = 0 := by
            funext j
            fin_cases j <;>
              simp [Fin.sum_univ_two, c, eigenvector, hv1, hw1,
                mul_comm] <;> ring
          have hc := hcoeff c hsum 1
          exact hv0 (by simpa [c] using neg_eq_zero.mp hc)
        · let c : Fin 2 → F := ![w 1, -v 1]
          have hsum : ∑ i, c i • eigenvector i = 0 := by
            funext j
            fin_cases j
            · simpa [Fin.sum_univ_two, c, eigenvector, δ,
                sub_eq_add_neg, mul_comm] using hδ
            · simp [Fin.sum_univ_two, c, eigenvector, mul_comm] <;> ring
          have hc := hcoeff c hsum 1
          exact hv1 (by simpa [c] using neg_eq_zero.mp hc)
      let G : Matrix.SpecialLinearGroup (Fin 2) F :=
        ⟨!![v 0, δ⁻¹ * w 0; v 1, δ⁻¹ * w 1], by
          rw [Matrix.det_fin_two]
          change v 0 * (δ⁻¹ * w 1) -
            (δ⁻¹ * w 0) * v 1 = 1
          calc
            _ = δ⁻¹ * δ := by simp [δ]; ring
            _ = 1 := inv_mul_cancel₀ hδ_ne⟩
      have hAG : A * G = G * splitTorusSL a := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j
        · simpa [G, splitTorusSL, Matrix.mul_apply, Matrix.mulVec,
            dotProduct, a, mul_comm] using congrFun hAv 0
        · have hw := congrFun hAw 0
          simp [Matrix.mulVec, dotProduct] at hw
          simp [G, splitTorusSL, Matrix.mul_apply, a]
          linear_combination δ⁻¹ * hw
        · simpa [G, splitTorusSL, Matrix.mul_apply, Matrix.mulVec,
            dotProduct, a, mul_comm] using congrFun hAv 1
        · have hw := congrFun hAw 1
          simp [Matrix.mulVec, dotProduct] at hw
          simp [G, splitTorusSL, Matrix.mul_apply, a]
          linear_combination δ⁻¹ * hw
      refine ⟨G, ?_⟩
      apply mul_right_cancel (b := G)
      calc
        A * G = G * splitTorusSL a := hAG
        _ = (G * splitTorusSL a * G⁻¹) * G := by group
    rcases hbasis_conjugates with ⟨G, hG⟩
    refine ⟨qSL G, ?_⟩
    refine ⟨splitTorus a, ⟨a, rfl⟩, ?_⟩
    change qSL G * splitTorus a * (qSL G)⁻¹ = qSL A
    rw [hG]
    simp [splitTorus, qSL]
  have h85_repeated_root
    (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (hA_one : qSL A ≠ 1)
    (hdisc_zero :
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ^ 2 = (4 : F)) :
    (∃ g : PSL2MatrixGroup F,
      qSL A ∈ U₀.map (MulAut.conj g).toMonoidHom) ∨
    (∃ g : PSL2MatrixGroup F,
      qSL A ∈ splitTorus.range.map (MulAut.conj g).toMonoidHom) := by
    classical
    let trA : F := Matrix.trace (A : Matrix (Fin 2) (Fin 2) F)
    change trA ^ 2 = (4 : F) at hdisc_zero
    by_cases hA_split : qSL A ∈ splitTorus.range
    · right
      refine ⟨1, ?_⟩
      exact ⟨qSL A, hA_split, by simp⟩
    · have hA_parabolic :
          ((A : Matrix (Fin 2) (Fin 2) F).IsParabolic) := by
        refine ⟨?_, ?_⟩
        · rintro ⟨r, hr⟩
          apply hA_one
          apply (QuotientGroup.eq_one_iff A).mpr
          rw [Matrix.SpecialLinearGroup.mem_center_iff]
          refine ⟨r, ?_, ?_⟩
          · have hdet := A.property
            rw [← hr, Matrix.det_fin_two] at hdet
            change r ^ 2 = 1
            simpa [pow_two] using hdet
          · exact hr
        · have hdisc : (A : Matrix (Fin 2) (Fin 2) F).discr = trA ^ 2 - (4 : F) := by
            simp [Matrix.discr_fin_two, trA, A.property]
          rw [hdisc, hdisc_zero, sub_self]
      have h85_repeated_root_fixed_line :
          ∃ v : Fin 2 → F, v ≠ 0 ∧
            ∃ μ : F, ((A : Matrix (Fin 2) (Fin 2) F).mulVec v = μ • v) := by
        have htrace :
            Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) = (2 : F) ∨
              Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) = -(2 : F) := by
          apply (sq_eq_sq_iff_eq_or_eq_neg).mp
          calc
            _ = (4 : F) := hdisc_zero
            _ = (2 : F) ^ 2 := by norm_num
        have hdet_coord :
            (A : Matrix (Fin 2) (Fin 2) F) 0 0 *
                (A : Matrix (Fin 2) (Fin 2) F) 1 1 -
              (A : Matrix (Fin 2) (Fin 2) F) 0 1 *
                (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
          have hdetA := A.property
          change Matrix.det (A : Matrix (Fin 2) (Fin 2) F) = 1 at hdetA
          rw [Matrix.det_fin_two] at hdetA
          exact hdetA
        rcases htrace with htrace | htrace
        · have htrace_coord :
              (A : Matrix (Fin 2) (Fin 2) F) 0 0 +
                (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 2 := by
            simpa [Matrix.trace_fin_two] using htrace
          have hdet_zero :
              (Matrix.scalar (Fin 2) (1 : F) -
                (A : Matrix (Fin 2) (Fin 2) F)).det = 0 := by
            calc
              _ = 1 -
                  ((A : Matrix (Fin 2) (Fin 2) F) 0 0 +
                    (A : Matrix (Fin 2) (Fin 2) F) 1 1) +
                  ((A : Matrix (Fin 2) (Fin 2) F) 0 0 *
                      (A : Matrix (Fin 2) (Fin 2) F) 1 1 -
                    (A : Matrix (Fin 2) (Fin 2) F) 0 1 *
                      (A : Matrix (Fin 2) (Fin 2) F) 1 0) := by
                        simp [Matrix.det_fin_two]
                        ring
              _ = 0 := by rw [htrace_coord, hdet_coord]; ring
          obtain ⟨v, hv_ne, hv⟩ :=
            Matrix.exists_mulVec_eq_zero_iff.mpr hdet_zero
          refine ⟨v, hv_ne, 1, ?_⟩
          have hscalar :
              (Matrix.scalar (Fin 2) (1 : F)).mulVec v = (1 : F) • v := by
            ext i
            fin_cases i <;> simp [Matrix.mulVec, dotProduct]
          rw [Matrix.sub_mulVec, hscalar] at hv
          exact (sub_eq_zero.mp hv).symm
        · have htrace_coord :
              (A : Matrix (Fin 2) (Fin 2) F) 0 0 +
                (A : Matrix (Fin 2) (Fin 2) F) 1 1 = -2 := by
            simpa [Matrix.trace_fin_two] using htrace
          have hdet_zero :
              (Matrix.scalar (Fin 2) (-1 : F) -
                (A : Matrix (Fin 2) (Fin 2) F)).det = 0 := by
            calc
              _ = 1 +
                  ((A : Matrix (Fin 2) (Fin 2) F) 0 0 +
                    (A : Matrix (Fin 2) (Fin 2) F) 1 1) +
                  ((A : Matrix (Fin 2) (Fin 2) F) 0 0 *
                      (A : Matrix (Fin 2) (Fin 2) F) 1 1 -
                    (A : Matrix (Fin 2) (Fin 2) F) 0 1 *
                      (A : Matrix (Fin 2) (Fin 2) F) 1 0) := by
                        simp [Matrix.det_fin_two]
                        ring
              _ = 0 := by rw [htrace_coord, hdet_coord]; ring
          obtain ⟨v, hv_ne, hv⟩ :=
            Matrix.exists_mulVec_eq_zero_iff.mpr hdet_zero
          refine ⟨v, hv_ne, -1, ?_⟩
          have hscalar :
              (Matrix.scalar (Fin 2) (-1 : F)).mulVec v = (-1 : F) • v := by
            ext i
            fin_cases i <;> simp [Matrix.mulVec, dotProduct]
          rw [Matrix.sub_mulVec, hscalar] at hv
          exact (sub_eq_zero.mp hv).symm
      have h85_repeated_root_jordan_basis :
          ∃ (G : Matrix.SpecialLinearGroup (Fin 2) F) (t : F),
            qSL A = qSL (G * unipotentSL t * G⁻¹) := by
        rcases h85_repeated_root_fixed_line with ⟨v, hv_ne, μ, heigen⟩
        have hw :
            ∃ w : Fin 2 → F, v 0 * w 1 - w 0 * v 1 = 1 := by
          by_cases hv0 : v 0 = 0
          · have hv1 : v 1 ≠ 0 := by
              intro hv1
              apply hv_ne
              funext i
              fin_cases i <;> assumption
            refine ⟨![(-(v 1)⁻¹), 0], ?_⟩
            simp [hv0, hv1]
          · refine ⟨![0, (v 0)⁻¹], ?_⟩
            simp [hv0]
        rcases hw with ⟨w, hw⟩
        let G : Matrix.SpecialLinearGroup (Fin 2) F :=
          ⟨!![v 0, w 0; v 1, w 1], by
            simpa [Matrix.det_fin_two] using hw⟩
        let e0 : Fin 2 → F := ![1, 0]
        have hG_e0 :
            (G : Matrix (Fin 2) (Fin 2) F).mulVec e0 = v := by
          ext i
          fin_cases i <;>
            simp [G, e0, Matrix.mulVec, dotProduct]
        let B : Matrix.SpecialLinearGroup (Fin 2) F :=
          G⁻¹ * A * G
        have hGinv_v :
            (G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1.mulVec v =
              e0 := by
          calc
            _ = (G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1.mulVec
                ((G : Matrix (Fin 2) (Fin 2) F).mulVec e0) := by
                  rw [hG_e0]
            _ = (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1 *
                (G : Matrix (Fin 2) (Fin 2) F)).mulVec e0) :=
                  Matrix.mulVec_mulVec e0 _ _
            _ = e0 := by
              change (((G⁻¹ * G : Matrix.SpecialLinearGroup (Fin 2) F) :
                Matrix (Fin 2) (Fin 2) F).mulVec e0) = e0
              rw [inv_mul_cancel]
              simp
        have hB_e0 :
            (B : Matrix (Fin 2) (Fin 2) F).mulVec e0 =
              μ • e0 := by
          calc
            _ = (G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1.mulVec
                ((A : Matrix (Fin 2) (Fin 2) F).mulVec
                  ((G : Matrix (Fin 2) (Fin 2) F).mulVec e0)) := by
                    simp only [B, Matrix.SpecialLinearGroup.coe_mul]
                    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
            _ = (G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1.mulVec
                ((A : Matrix (Fin 2) (Fin 2) F).mulVec v) := by
                  rw [hG_e0]
            _ = (G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1.mulVec
                (μ • v) := by rw [heigen]
            _ = μ •
                (G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1.mulVec v :=
                  Matrix.mulVec_smul _ _ _
            _ = μ • e0 := by rw [hGinv_v]
        have hB10 :
            (B : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
          have h := congrFun hB_e0 1
          simpa [e0, Matrix.mulVec, dotProduct] using h
        have hB_parabolic :
            (B : Matrix (Fin 2) (Fin 2) F).IsParabolic := by
          have h := (Matrix.isParabolic_conj'_iff
            (Matrix.SpecialLinearGroup.toGL G)
            (m := (A : Matrix (Fin 2) (Fin 2) F))).mpr
              hA_parabolic
          rw [← Matrix.coe_units_inv] at h
          have hcoe_inv :
              ((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
                  Matrix (Fin 2) (Fin 2) F) =
                (((Matrix.SpecialLinearGroup.toGL G)⁻¹ :
                    GL (Fin 2) F) :
                  Matrix (Fin 2) (Fin 2) F) := by
            exact congrArg
              (fun X : GL (Fin 2) F =>
                (X : Matrix (Fin 2) (Fin 2) F))
              (map_inv
                (Matrix.SpecialLinearGroup.toGL
                  (n := Fin 2) (R := F)) G)
          rw [← hcoe_inv] at h
          simpa [B] using h
        have hBdiag :
            (B : Matrix (Fin 2) (Fin 2) F) 0 0 =
              (B : Matrix (Fin 2) (Fin 2) F) 1 1 :=
          (Matrix.isParabolic_iff_of_upperTriangular hB10).mp
            hB_parabolic |>.1
        let a : F := (B : Matrix (Fin 2) (Fin 2) F) 0 0
        have ha_sq : a ^ 2 = 1 := by
          have hdetB := B.property
          change Matrix.det (B : Matrix (Fin 2) (Fin 2) F) = 1
            at hdetB
          rw [Matrix.det_fin_two, hB10, mul_zero, sub_zero,
            ← hBdiag] at hdetB
          simpa [a, pow_two] using hdetB
        have ha_ne : a ≠ 0 := by
          intro ha
          rw [ha, zero_pow (by norm_num)] at ha_sq
          exact zero_ne_one ha_sq
        let t : F :=
          a⁻¹ * (B : Matrix (Fin 2) (Fin 2) F) 0 1
        let z : Matrix.SpecialLinearGroup (Fin 2) F :=
          ⟨Matrix.scalar (Fin 2) a, by
            simpa [Matrix.det_fin_two, pow_two] using ha_sq⟩
        have hz_center :
            z ∈ Subgroup.center
              (Matrix.SpecialLinearGroup (Fin 2) F) := by
          rw [Matrix.SpecialLinearGroup.mem_center_iff]
          exact ⟨a, ha_sq, rfl⟩
        have hB_factor : B = z * unipotentSL t := by
          apply Subtype.ext
          ext i j
          fin_cases i <;> fin_cases j
          · simp [z, t, unipotentSL, Matrix.mul_apply, a]
          · simp [z, t, unipotentSL, Matrix.mul_apply, a, ha_ne]
          · simp [z, t, unipotentSL, Matrix.mul_apply, hB10]
          · simp [z, t, unipotentSL, Matrix.mul_apply, a, hBdiag]
        have hqz : qSL z = 1 :=
          (QuotientGroup.eq_one_iff z).mpr hz_center
        have hqB : qSL B = qSL (unipotentSL t) := by
          rw [hB_factor, map_mul, hqz, one_mul]
        refine ⟨G, t, ?_⟩
        calc
          qSL A = qSL (G * B * G⁻¹) := by
            simp [B, mul_assoc]
          _ = qSL G * qSL B * qSL G⁻¹ := by simp
          _ = qSL G * qSL (unipotentSL t) * qSL G⁻¹ := by
            rw [hqB]
          _ = qSL (G * unipotentSL t * G⁻¹) := by simp
      have h85_repeated_root_nonsplit_unipotent :
          ∃ g : PSL2MatrixGroup F,
            qSL A ∈ U₀.map (MulAut.conj g).toMonoidHom := by
        rcases h85_repeated_root_jordan_basis with ⟨G, t, hG⟩
        refine ⟨qSL G, ?_⟩
        refine ⟨unipotent t, ⟨Multiplicative.ofAdd t, rfl⟩, ?_⟩
        change (MulAut.conj (qSL G)).toMonoidHom (unipotent t) = qSL A
        rw [hG]
        change qSL G * qSL (unipotentSL t) * (qSL G)⁻¹ =
          qSL (G * unipotentSL t * G⁻¹)
        simp [qSL, unipotent]
      exact Or.inl h85_repeated_root_nonsplit_unipotent
  obtain ⟨S, hS_cyclic, hS_card, _hS_normalizer, _hS_reflection,
      hS_weakTI,
      hS_noEigen⟩ :=
    h84_nonsplit_torus_data hFcard
  refine ⟨splitTorus.range, S, hsplit_props.1, hsplit_props.2,
    hS_cyclic, hS_card, ?_⟩
  have hprojective_cover :
      ∀ x : PSL2MatrixGroup F, x ≠ 1 →
        (∃ g, x ∈ (P : Subgroup (PSL2MatrixGroup F)).map
          (MulAut.conj g).toMonoidHom) ∨
        (∃ g, x ∈ splitTorus.range.map
          (MulAut.conj g).toMonoidHom) ∨
        (∃ g, x ∈ S.map (MulAut.conj g).toMonoidHom) := by
    intro x hx
    refine QuotientGroup.induction_on x ?_ hx
    intro A hxA
    have hA_ne : qSL A ≠ 1 := by
      simpa [qSL] using hxA
    by_cases hdisc_zero :
        Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ^ 2 = (4 : F)
    · rcases h85_repeated_root A hA_ne hdisc_zero with hU₀ | hsplit
      · rcases hU₀ with ⟨g, hg⟩
        left
        refine ⟨g * kP, ?_⟩
        have hmap :
            U₀.map (MulAut.conj g).toMonoidHom =
              (P : Subgroup (PSL2MatrixGroup F)).map
                (MulAut.conj (g * kP)).toMonoidHom := by
          rw [← hP_to_U₀, Subgroup.map_map]
          congr 1
          ext y
          simp [MulAut.conj_apply, mul_assoc]
        rw [← hmap]
        exact hg
      · exact Or.inr (Or.inl hsplit)
    · by_cases heigen : ∃ (μ : F) (v : Fin 2 → F), v ≠ 0 ∧
          (A : Matrix (Fin 2) (Fin 2) F).mulVec v = μ • v
      · exact Or.inr (Or.inl (h85_split_semisimple A hdisc_zero heigen))
      · exact Or.inr (Or.inr (by
          simpa [qSL] using hS_noEigen A hdisc_zero heigen))
  have hPcard :
      Nat.card (P : Subgroup (PSL2MatrixGroup F)) = Nat.card F := by
    obtain ⟨eP⟩ := huppert_II_8_2_a_sylow_equiv_additive hFcard P
    exact (Nat.card_congr eP.toEquiv).symm
  have hP_split_coprime :
      Nat.Coprime (Nat.card (P : Subgroup (PSL2MatrixGroup F)))
        (Nat.card splitTorus.range) := by
    rw [hPcard, hsplit_props.2]
    exact hq_coprime_split_order (Nat.card F) Nat.card_pos
  have hP_nonsplit_coprime :
      Nat.Coprime (Nat.card (P : Subgroup (PSL2MatrixGroup F)))
        (Nat.card S) := by
    rw [hPcard, hS_card]
    exact hq_coprime_nonsplit_order (Nat.card F) Nat.card_pos
  have hsplit_nonsplit_coprime :
      Nat.Coprime (Nat.card splitTorus.range) (Nat.card S) := by
    rw [hsplit_props.2, hS_card]
    exact hsplit_nonsplit_order_coprime (Nat.card F)
      (Finite.one_lt_card (α := F))
  have hsplit_weakTI :
      ∀ y : PSL2MatrixGroup F, y ∈ splitTorus.range → y ≠ 1 →
        ∀ g : PSL2MatrixGroup F,
          g * y * g⁻¹ ∈ splitTorus.range →
            g ∈ Subgroup.normalizer
              (splitTorus.range : Set (PSL2MatrixGroup F)) := by
    intro y hy hy_ne g hgy
    rcases hy with ⟨a, rfl⟩
    have ha_ne_inv : (a : F) ≠ (a⁻¹ : F) := by
      intro hai
      apply hy_ne
      change qSL (splitTorusSL a) = 1
      apply (QuotientGroup.eq_one_iff (splitTorusSL a)).mpr
      rw [Matrix.SpecialLinearGroup.mem_center_iff]
      have haiU : a = a⁻¹ := by
        apply Units.ext
        simpa using hai
      have ha_sq : (a : F) ^ 2 = 1 := by
        have hsqU := congrArg (fun u : Fˣ => (u : F))
          (eq_inv_iff_mul_eq_one.mp haiU)
        simpa [pow_two] using hsqU
      refine ⟨(a : F), ha_sq, ?_⟩
      change Matrix.scalar (Fin 2) (a : F) =
        !![(a : F), 0; 0, (a⁻¹ : F)]
      ext i j
      fin_cases i <;> fin_cases j
      · rfl
      · rfl
      · rfl
      · exact hai
    refine QuotientGroup.induction_on g ?_ hgy
    intro A hAconj
    rcases hAconj with ⟨b, hb⟩
    have hq :
        qSL (splitTorusSL b) =
          qSL (A * splitTorusSL a * A⁻¹) := by
      simpa [qSL, splitTorus] using hb
    rcases (QuotientGroup.mk'_eq_mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).mp hq with
      ⟨z, hz, hzeq⟩
    have hzeqA :
        splitTorusSL b * z * A = A * splitTorusSL a := by
      calc
        splitTorusSL b * z * A =
            (A * splitTorusSL a * A⁻¹) * A := by rw [hzeq]
        _ = A * splitTorusSL a := by group
    have hscalar :=
      Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center
        hz (0 : Fin 2)
    have hmat := congrArg Subtype.val hzeqA
    change (!![(b : F), 0; 0, (b⁻¹ : F)] :
          Matrix (Fin 2) (Fin 2) F) *
        (z : Matrix (Fin 2) (Fin 2) F) *
          (A : Matrix (Fin 2) (Fin 2) F) =
      (A : Matrix (Fin 2) (Fin 2) F) *
        !![(a : F), 0; 0, (a⁻¹ : F)] at hmat
    rw [← hscalar] at hmat
    rcases hsplit_matrix_diag_or_antidiag A a b
        ((z : Matrix (Fin 2) (Fin 2) F) 0 0)
        ha_ne_inv hmat with hdiag | hanti
    · rcases hdiag with ⟨h01, h10⟩
      have hmap_le :
          splitTorus.range.map
              (MulAut.conj (qSL A)).toMonoidHom ≤
            splitTorus.range := by
        intro v hv
        rcases hv with ⟨w, hw, rfl⟩
        rcases hw with ⟨c, rfl⟩
        refine ⟨c, ?_⟩
        have hcomm :
            A * splitTorusSL c = splitTorusSL c * A := by
          apply Subtype.ext
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [splitTorusSL, Matrix.mul_apply, h01, h10, mul_comm]
        have hconj :
            A * splitTorusSL c * A⁻¹ = splitTorusSL c := by
          rw [hcomm]
          simp [mul_assoc]
        simpa [qSL, splitTorus, MulAut.conj_apply] using
          (congrArg qSL hconj).symm
      have hmap_eq :
          splitTorus.range.map
              (MulAut.conj (qSL A)).toMonoidHom =
            splitTorus.range := by
        apply Subgroup.eq_of_le_of_card_ge hmap_le
        rw [Subgroup.card_map_of_injective
          (K := splitTorus.range)
          (f := (MulAut.conj (qSL A)).toMonoidHom)
          (MulAut.conj (qSL A)).injective]
      rw [← Subgroup.conjAct_pointwise_smul_iff]
      exact hmap_eq
    · rcases hanti with ⟨h00, h11⟩
      have hmap_le :
          splitTorus.range.map
              (MulAut.conj (qSL A)).toMonoidHom ≤
            splitTorus.range := by
        intro v hv
        rcases hv with ⟨w, hw, rfl⟩
        rcases hw with ⟨c, rfl⟩
        refine ⟨c⁻¹, ?_⟩
        have hcomm :
            A * splitTorusSL c = splitTorusSL c⁻¹ * A := by
          apply Subtype.ext
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [splitTorusSL, Matrix.mul_apply, h00, h11, mul_comm]
        have hconj :
            A * splitTorusSL c * A⁻¹ = splitTorusSL c⁻¹ := by
          rw [hcomm]
          simp [mul_assoc]
        simpa [qSL, splitTorus, MulAut.conj_apply] using
          (congrArg qSL hconj).symm
      have hmap_eq :
          splitTorus.range.map
              (MulAut.conj (qSL A)).toMonoidHom =
            splitTorus.range := by
        apply Subgroup.eq_of_le_of_card_ge hmap_le
        rw [Subgroup.card_map_of_injective
          (K := splitTorus.range)
          (f := (MulAut.conj (qSL A)).toMonoidHom)
          (MulAut.conj (qSL A)).injective]
      rw [← Subgroup.conjAct_pointwise_smul_iff]
      exact hmap_eq
  have hprojective_TI_split :=
    hconjugate_family_unique_of_weak_ti splitTorus.range hsplit_weakTI
  have hprojective_TI_nonsplit :=
    hconjugate_family_unique_of_weak_ti S hS_weakTI
  have hprojective_TI_same_family :
      (∀ x : PSL2MatrixGroup F, x ≠ 1 → ∀ g₁ g₂,
        x ∈ (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g₁).toMonoidHom →
        x ∈ (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g₂).toMonoidHom →
        (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g₁).toMonoidHom =
          (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g₂).toMonoidHom) ∧
      (∀ x : PSL2MatrixGroup F, x ≠ 1 → ∀ g₁ g₂,
        x ∈ splitTorus.range.map (MulAut.conj g₁).toMonoidHom →
        x ∈ splitTorus.range.map (MulAut.conj g₂).toMonoidHom →
        splitTorus.range.map (MulAut.conj g₁).toMonoidHom =
          splitTorus.range.map (MulAut.conj g₂).toMonoidHom) ∧
      (∀ x : PSL2MatrixGroup F, x ≠ 1 → ∀ g₁ g₂,
        x ∈ S.map (MulAut.conj g₁).toMonoidHom →
        x ∈ S.map (MulAut.conj g₂).toMonoidHom →
        S.map (MulAut.conj g₁).toMonoidHom =
          S.map (MulAut.conj g₂).toMonoidHom) := by
    exact ⟨hprojective_TI_P, hprojective_TI_split,
      hprojective_TI_nonsplit⟩
  have hprojective_TI :
      ∀ x : PSL2MatrixGroup F, x ≠ 1 →
        ∀ T₁ T₂ : Subgroup (PSL2MatrixGroup F),
          x ∈ T₁ → x ∈ T₂ →
          ((∃ g, T₁ = (P : Subgroup (PSL2MatrixGroup F)).map
              (MulAut.conj g).toMonoidHom) ∨
            (∃ g, T₁ = splitTorus.range.map
              (MulAut.conj g).toMonoidHom) ∨
            (∃ g, T₁ = S.map (MulAut.conj g).toMonoidHom)) →
          ((∃ g, T₂ = (P : Subgroup (PSL2MatrixGroup F)).map
              (MulAut.conj g).toMonoidHom) ∨
            (∃ g, T₂ = splitTorus.range.map
              (MulAut.conj g).toMonoidHom) ∨
            (∃ g, T₂ = S.map (MulAut.conj g).toMonoidHom)) →
          T₁ = T₂ := by
    rcases hprojective_TI_same_family with
      ⟨hsameP, hsameSplit, hsameS⟩
    exact hthree_family_unique_of_same_family
      (P : Subgroup (PSL2MatrixGroup F)) splitTorus.range S
      hP_split_coprime hP_nonsplit_coprime hsplit_nonsplit_coprime
      hsameP hsameSplit hsameS
  intro x hx
  rcases hprojective_cover x hx with hP | hU | hS
  · let T := (P : Subgroup (PSL2MatrixGroup F)).map
      (MulAut.conj hP.choose).toMonoidHom
    refine ⟨T, ⟨hP.choose_spec, Or.inl ⟨hP.choose, rfl⟩⟩, ?_⟩
    intro T' hT'
    exact hprojective_TI x hx T' T hT'.1 hP.choose_spec
      hT'.2 (Or.inl ⟨hP.choose, rfl⟩)
  · let T := splitTorus.range.map
      (MulAut.conj hU.choose).toMonoidHom
    refine ⟨T, ⟨hU.choose_spec, Or.inr (Or.inl ⟨hU.choose, rfl⟩)⟩, ?_⟩
    intro T' hT'
    exact hprojective_TI x hx T' T hT'.1 hU.choose_spec
      hT'.2 (Or.inr (Or.inl ⟨hU.choose, rfl⟩))
  · let T := S.map (MulAut.conj hS.choose).toMonoidHom
    refine ⟨T, ⟨hS.choose_spec, Or.inr (Or.inr ⟨hS.choose, rfl⟩)⟩, ?_⟩
    intro T' hT'
    exact hprojective_TI x hx T' T hT'.1 hS.choose_spec
      hT'.2 (Or.inr (Or.inr ⟨hS.choose, rfl⟩))

/-- Huppert II.8.5(a): the nonidentity elements of PSL(2,p^f) are
partitioned by the conjugates of a Sylow p-subgroup and the split and
nonsplit cyclic tori. -/
public theorem huppert_II_8_5_a_psl2_partition
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f)
    (P : Sylow p (PSL2MatrixGroup F)) :
    ∃ U S : Subgroup (PSL2MatrixGroup F),
      IsCyclic U ∧
      Nat.card U =
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      IsCyclic S ∧
      Nat.card S =
        (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      ∀ x : PSL2MatrixGroup F, x ≠ 1 →
        ∃! T : Subgroup (PSL2MatrixGroup F),
          x ∈ T ∧
            ((∃ g, T = (P : Subgroup (PSL2MatrixGroup F)).map
              (MulAut.conj g).toMonoidHom) ∨
            (∃ g, T = U.map (MulAut.conj g).toMonoidHom) ∨
            (∃ g, T = S.map (MulAut.conj g).toMonoidHom)) := by
  exact huppert_II_8_5_a_psl2_cover hFcard P
/-- The conjugacy-class representative step in Huppert II.8.22. -/
public theorem huppert_II_8_22_maximal_cyclic_representatives
    {H : Type u} [Group H] [Finite H] (p : ℕ) :
    ∃ (r : ℕ) (Z : Fin r → Subgroup H),
      (∀ i, IsCyclic (Z i)) ∧
      (∀ i, 1 < Nat.card (Z i)) ∧
      (∀ i, Nat.Coprime p (Nat.card (Z i))) ∧
      (∀ i (W : Subgroup H), IsCyclic W → Z i ≤ W → W = Z i) ∧
      (∀ W : Subgroup H, IsCyclic W → 1 < Nat.card W →
        Nat.Coprime p (Nat.card W) →
        (∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) →
        ∃ i g, W = (Z i).map (MulAut.conj g).toMonoidHom) ∧
      (∀ i j g,
        (Z i).map (MulAut.conj g).toMonoidHom = Z j → i = j) := by
  classical
  letI : MulAction H (Subgroup H) :=
    { smul := fun g W => W.map (MulAut.conj g).toMonoidHom
      one_smul := by
        intro W
        change W.map (MulAut.conj (1 : H)).toMonoidHom = W
        have h :
            (MulAut.conj (1 : H)).toMonoidHom = MonoidHom.id H := by
          ext x
          simp
        rw [h, Subgroup.map_id]
      mul_smul := by
        intro g h W
        change W.map (MulAut.conj (g * h)).toMonoidHom =
          (W.map (MulAut.conj h).toMonoidHom).map
            (MulAut.conj g).toMonoidHom
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp [MulAut.conj_apply, mul_assoc] }
  have hcyclic_smul (g : H) (W : Subgroup H)
      (hW : IsCyclic W) : IsCyclic ↥(g • W : Subgroup H) := by
    let e : W ≃* ↥(g • W : Subgroup H) :=
      (MulAut.conj g).subgroupMap W
    letI : IsCyclic W := hW
    rcases IsCyclic.exists_zpow_surjective (G := W) with ⟨x, hx⟩
    apply IsCyclic.mk
    refine ⟨e x, ?_⟩
    intro y
    obtain ⟨n, hn⟩ := hx (e.symm y)
    refine ⟨n, ?_⟩
    change (e x) ^ n = y
    rw [← map_zpow]
    simpa using congrArg e hn
  have hcard_smul (g : H) (W : Subgroup H) :
      Nat.card ↥(g • W : Subgroup H) = Nat.card W := by
    let e : W ≃* ↥(g • W : Subgroup H) :=
      (MulAut.conj g).subgroupMap W
    exact (Nat.card_congr e.toEquiv).symm
  have helig_smul (g : H) (W : Subgroup H)
      (hW : IsCyclic W ∧ 1 < Nat.card W ∧
        Nat.Coprime p (Nat.card W) ∧
        ∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) :
      IsCyclic ↥(g • W : Subgroup H) ∧
        1 < Nat.card ↥(g • W : Subgroup H) ∧
        Nat.Coprime p (Nat.card ↥(g • W : Subgroup H)) ∧
        ∀ V : Subgroup H, IsCyclic V →
          (g • W : Subgroup H) ≤ V → V = (g • W : Subgroup H) := by
    refine ⟨hcyclic_smul g W hW.1, ?_, ?_, ?_⟩
    · simpa [hcard_smul g W] using hW.2.1
    · simpa [hcard_smul g W] using hW.2.2.1
    · intro V hV hle
      have hback_cyclic : IsCyclic ↥(g⁻¹ • V : Subgroup H) :=
        hcyclic_smul g⁻¹ V hV
      have hback_le : W ≤ (g⁻¹ • V : Subgroup H) := by
        have hmap := Subgroup.map_mono
          (f := (MulAut.conj g⁻¹).toMonoidHom) hle
        change (g⁻¹ • (g • W) : Subgroup H) ≤
          (g⁻¹ • V : Subgroup H) at hmap
        simpa using hmap
      have heq : (g⁻¹ • V : Subgroup H) = W :=
        hW.2.2.2 (g⁻¹ • V : Subgroup H) hback_cyclic hback_le
      have hfront := congrArg (fun T : Subgroup H => g • T) heq
      simpa using hfront
  let C := {W : Subgroup H //
    IsCyclic W ∧ 1 < Nat.card W ∧ Nat.Coprime p (Nat.card W) ∧
      ∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W}
  letI : MulAction H C :=
    { smul := fun g W =>
        ⟨g • (W : Subgroup H), helig_smul g W W.property⟩
      one_smul := by
        intro W
        apply Subtype.ext
        exact one_smul H (W : Subgroup H)
      mul_smul := by
        intro g h W
        apply Subtype.ext
        exact mul_smul g h (W : Subgroup H) }
  let O := Quotient (MulAction.orbitRel H C)
  letI : Fintype O := Fintype.ofFinite O
  let r := Fintype.card O
  let e : Fin r ≃ O := (Fintype.equivFin O).symm
  let Z : Fin r → Subgroup H := fun i => ((e i).out : C)
  refine ⟨r, Z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ((e i).out : C).property.1
  · intro i
    exact ((e i).out : C).property.2.1
  · intro i
    exact ((e i).out : C).property.2.2.1
  · intro i W hW hle
    exact ((e i).out : C).property.2.2.2 W hW hle
  · intro W hW hWcard hWcop hWmax
    let c : C := ⟨W, hW, hWcard, hWcop, hWmax⟩
    let q : O := Quotient.mk (MulAction.orbitRel H C) c
    let i : Fin r := e.symm q
    have heq : e i = q := by simp [i]
    have hquot :
        Quotient.mk (MulAction.orbitRel H C) (e i).out =
          Quotient.mk (MulAction.orbitRel H C) c := by
      rw [Quotient.out_eq, heq]
    have hrel :
        (e i).out ∈ MulAction.orbit H c :=
      Quotient.exact hquot
    rcases MulAction.mem_orbit_iff.mp hrel with ⟨g, hg⟩
    refine ⟨i, g⁻¹, ?_⟩
    have hgval :
        (g • W : Subgroup H) = Z i := by
      simpa [c, Z] using congrArg Subtype.val hg
    have hback :=
      congrArg (fun T : Subgroup H => g⁻¹ • T) hgval
    change W = (g⁻¹ • Z i : Subgroup H)
    simpa using hback
  · intro i j g hg
    let ci : C := (e i).out
    let cj : C := (e j).out
    have hgc : g • ci = cj := by
      apply Subtype.ext
      exact hg
    have hrel : ci ∈ MulAction.orbit H cj := by
      rw [MulAction.mem_orbit_iff]
      refine ⟨g⁻¹, ?_⟩
      rw [← hgc]
      simp
    have hq : e i = e j := by
      calc
        e i = Quotient.mk (MulAction.orbitRel H C) ci :=
          (Quotient.out_eq (e i)).symm
        _ = Quotient.mk (MulAction.orbitRel H C) cj :=
          Quotient.sound hrel
        _ = e j := Quotient.out_eq (e j)
    exact e.injective hq

private theorem cyclic_le_unique_partition_family
    {G : Type*} [Group G]
    (Family : Subgroup G → Prop)
    (hpartition : ∀ x : G, x ≠ 1 →
      ∃! T : Subgroup G, x ∈ T ∧ Family T)
    {x : G} (hx : x ≠ 1)
    {T V : Subgroup G}
    (hxT : x ∈ T) (hTfamily : Family T)
    (hxV : x ∈ V) (hVcyclic : IsCyclic V) :
    V ≤ T := by
  letI : IsCyclic V := hVcyclic
  rcases IsCyclic.exists_zpow_surjective (G := V) with ⟨v, hv⟩
  have hv_ne : (v : G) ≠ 1 := by
    intro hv_one
    obtain ⟨n, hn⟩ := hv ⟨x, hxV⟩
    have hnval : (v ^ n : V) = ⟨x, hxV⟩ := hn
    have hnval' := congrArg Subtype.val hnval
    change ((v : G) ^ n) = x at hnval'
    simp [hv_one] at hnval'
    exact hx hnval'.symm
  obtain ⟨Tv, hvTv, _hTv_unique⟩ := hpartition (v : G) hv_ne
  have hxTv : x ∈ Tv := by
    obtain ⟨n, hn⟩ := hv ⟨x, hxV⟩
    have hnval : (v : G) ^ n = x := congrArg Subtype.val hn
    have hvpow : (v : G) ^ n ∈ Tv := Tv.zpow_mem hvTv.1 n
    rwa [hnval] at hvpow
  have hTvT : Tv = T :=
    (hpartition x hx).unique ⟨hxTv, hvTv.2⟩ ⟨hxT, hTfamily⟩
  intro y hyV
  obtain ⟨n, hn⟩ := hv ⟨y, hyV⟩
  have hnval : (v : G) ^ n = y := congrArg Subtype.val hn
  have hypow : (v : G) ^ n ∈ Tv := Tv.zpow_mem hvTv.1 n
  rw [hTvT, hnval] at hypow
  exact hypow

private theorem equiv_torus_reflection_data
    {G : Type u} [Group G] [Finite G]
    (T0 : Subgroup G) (w0 : G)
    (hcyclic0 : IsCyclic T0)
    (hw0_normalizer : w0 ∈ Subgroup.normalizer (T0 : Set G))
    (hw0_not_mem : w0 ∉ T0) (hw0_sq : w0 * w0 = 1)
    (hw0_inv : ∀ t : G, t ∈ T0 → w0 * t * w0⁻¹ = t⁻¹)
    (hcard0 : Nat.card (T0 ⊔ Subgroup.zpowers w0 : Subgroup G) =
      2 * Nat.card T0)
    (hnormalizer0 : ∀ R : Subgroup G, R ≤ T0 → R ≠ ⊥ →
      Subgroup.normalizer (R : Set G) = T0 ⊔ Subgroup.zpowers w0)
    (e : G ≃* G) :
    let T := T0.map e.toMonoidHom
    let w := e w0
    IsCyclic T ∧
      w ∈ Subgroup.normalizer (T : Set G) ∧
      w ∉ T ∧
      w * w = 1 ∧
      (∀ t : G, t ∈ T → w * t * w⁻¹ = t⁻¹) ∧
      Nat.card (T ⊔ Subgroup.zpowers w : Subgroup G) = 2 * Nat.card T ∧
      ∀ R : Subgroup G, R ≤ T → R ≠ ⊥ →
        Subgroup.normalizer (R : Set G) = T ⊔ Subgroup.zpowers w := by
  dsimp only
  have hcyclic : IsCyclic (T0.map e.toMonoidHom) := by
    letI : IsCyclic T0 := hcyclic0
    exact isCyclic_of_surjective (e.subgroupMap T0).toMonoidHom
      (e.subgroupMap T0).surjective
  have hw_normalizer :
      e w0 ∈ Subgroup.normalizer (T0.map e.toMonoidHom : Set G) := by
    have hw_map : e w0 ∈
        (Subgroup.normalizer (T0 : Set G)).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom hw0_normalizer
    rwa [Subgroup.map_equiv_normalizer_eq T0 e] at hw_map
  have hw_not_mem : e w0 ∉ T0.map e.toMonoidHom := by
    rw [Subgroup.mem_map_equiv]
    simpa using hw0_not_mem
  have hw_sq : e w0 * e w0 = 1 := by
    simpa using congrArg e hw0_sq
  have hw_inv : ∀ t : G, t ∈ T0.map e.toMonoidHom →
      e w0 * t * (e w0)⁻¹ = t⁻¹ := by
    intro t ht
    have ht0 : e.symm t ∈ T0 :=
      Subgroup.mem_map_equiv.mp ht
    simpa using congrArg e (hw0_inv (e.symm t) ht0)
  have hcard : Nat.card
      (T0.map e.toMonoidHom ⊔ Subgroup.zpowers (e w0) : Subgroup G) =
      2 * Nat.card (T0.map e.toMonoidHom) := by
    have heq : (T0 ⊔ Subgroup.zpowers w0).map e.toMonoidHom =
        T0.map e.toMonoidHom ⊔ Subgroup.zpowers (e w0) := by
      simpa using
        (Subgroup.map_sup T0 (Subgroup.zpowers w0) e.toMonoidHom).trans
          (congrArg (fun K : Subgroup G => T0.map e.toMonoidHom ⊔ K)
            (MonoidHom.map_zpowers e.toMonoidHom w0))
    calc
      Nat.card (T0.map e.toMonoidHom ⊔ Subgroup.zpowers (e w0) : Subgroup G) =
          Nat.card ((T0 ⊔ Subgroup.zpowers w0).map e.toMonoidHom) :=
        congrArg (fun K : Subgroup G => Nat.card K) heq.symm
      _ = Nat.card (T0 ⊔ Subgroup.zpowers w0 : Subgroup G) := by
        rw [Subgroup.card_map_of_injective e.injective]
      _ = 2 * Nat.card (T0 : Subgroup G) := hcard0
      _ = 2 * Nat.card (T0.map e.toMonoidHom) := by
        rw [Subgroup.card_map_of_injective e.injective]
  refine ⟨hcyclic, hw_normalizer, hw_not_mem, hw_sq, hw_inv, hcard, ?_⟩
  intro R hR_le hR_ne
  let R0 : Subgroup G := R.map e.symm.toMonoidHom
  have hR0_le : R0 ≤ T0 := by
    intro x hx
    have hex : e x ∈ R := by
      change x ∈ R.map e.symm.toMonoidHom at hx
      rwa [Subgroup.mem_map_equiv] at hx
    have hexT : e x ∈ T0.map e.toMonoidHom := hR_le hex
    rw [Subgroup.mem_map_equiv] at hexT
    simpa using hexT
  have hR0_ne : R0 ≠ ⊥ := by
    intro hR0
    apply hR_ne
    apply (Subgroup.map_eq_bot_iff_of_injective R
      (f := e.symm.toMonoidHom) e.symm.injective).mp
    exact hR0
  have hR0_map : R0.map e.toMonoidHom = R := by
    apply (Subgroup.map_symm_eq_iff_map_eq (K := R0) (e := e)).mp
    rfl
  have hmap := congrArg
    (fun K : Subgroup G => K.map e.toMonoidHom)
    (hnormalizer0 R0 hR0_le hR0_ne)
  change (Subgroup.normalizer (R0 : Set G)).map e.toMonoidHom =
    (T0 ⊔ Subgroup.zpowers w0).map e.toMonoidHom at hmap
  rw [Subgroup.map_equiv_normalizer_eq R0 e, hR0_map,
    Subgroup.map_sup, MonoidHom.map_zpowers] at hmap
  exact hmap

private theorem conjugate_torus_reflection_data
    {G : Type u} [Group G] [Finite G]
    (T0 : Subgroup G) (w0 : G)
    (hcyclic0 : IsCyclic T0)
    (hw0_normalizer : w0 ∈ Subgroup.normalizer (T0 : Set G))
    (hw0_not_mem : w0 ∉ T0) (hw0_sq : w0 * w0 = 1)
    (hw0_inv : ∀ t : G, t ∈ T0 → w0 * t * w0⁻¹ = t⁻¹)
    (hcard0 : Nat.card (T0 ⊔ Subgroup.zpowers w0 : Subgroup G) =
      2 * Nat.card T0)
    (hnormalizer0 : ∀ R : Subgroup G, R ≤ T0 → R ≠ ⊥ →
      Subgroup.normalizer (R : Set G) = T0 ⊔ Subgroup.zpowers w0)
    (g : G) :
    let T := T0.map (MulAut.conj g).toMonoidHom
    let w := MulAut.conj g w0
    IsCyclic T ∧
      w ∈ Subgroup.normalizer (T : Set G) ∧
      w ∉ T ∧
      w * w = 1 ∧
      (∀ t : G, t ∈ T → w * t * w⁻¹ = t⁻¹) ∧
      Nat.card (T ⊔ Subgroup.zpowers w : Subgroup G) = 2 * Nat.card T ∧
      ∀ R : Subgroup G, R ≤ T → R ≠ ⊥ →
        Subgroup.normalizer (R : Set G) = T ⊔ Subgroup.zpowers w := by
  exact equiv_torus_reflection_data T0 w0 hcyclic0 hw0_normalizer hw0_not_mem
    hw0_sq hw0_inv hcard0 hnormalizer0 (MulAut.conj g)

private theorem relIndex_le_two_of_inter_eq
    {G : Type u} [Group G] [Finite G]
    (T B N A : Subgroup G)
    (hB_le : B ≤ N) (hinter : T ⊓ B = A)
    (hindex : T.relIndex N = 2) :
    A.relIndex B ≤ 2 := by
  rw [← hinter, Subgroup.inf_relIndex_right]
  rw [← hindex]
  exact Subgroup.relIndex_le_of_le_right hB_le (by
    rw [Subgroup.relIndex]
    exact Nat.card_pos.ne')

private theorem relIndex_eq_two_of_card_eq_two_mul
    {G : Type u} [Group G] [Finite G]
    (T N : Subgroup G) (hT_le : T ≤ N)
    (hcard : Nat.card N = 2 * Nat.card T) :
    T.relIndex N = 2 := by
  rw [Subgroup.relIndex]
  have hsubcard : Nat.card (T.subgroupOf N) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT_le).toEquiv
  have hmul := (T.subgroupOf N).index_mul_card
  rw [hsubcard, hcard] at hmul
  exact Nat.mul_right_cancel Nat.card_pos hmul

private theorem mulEquiv_dihedral_of_cyclic_reflection
    {G : Type u} [Group G] [Finite G]
    (C : Subgroup G) (hC : IsCyclic C) (w : G)
    (hw_not_mem : w ∉ C) (hw_sq : w * w = 1)
    (hw_inv : ∀ c : G, c ∈ C → w * c * w⁻¹ = c⁻¹)
    (hindex : C.index = 2) :
    Nonempty (G ≃* DihedralGroup (Nat.card C)) := by
  classical
  let e : Multiplicative (ZMod (Nat.card C)) ≃* C :=
    zmodCyclicMulEquiv hC
  let rot : ZMod (Nat.card C) → G := fun i =>
    (e (Multiplicative.ofAdd i) : C)
  have hrot_mem (i : ZMod (Nat.card C)) : rot i ∈ C :=
    (e (Multiplicative.ofAdd i)).property
  have hrot_add (i j : ZMod (Nat.card C)) :
      rot (i + j) = rot i * rot j := by
    exact congrArg Subtype.val (e.map_mul
      (Multiplicative.ofAdd i) (Multiplicative.ofAdd j))
  have hrot_neg (i : ZMod (Nat.card C)) :
      rot (-i) = (rot i)⁻¹ := by
    exact congrArg Subtype.val (e.map_inv (Multiplicative.ofAdd i))
  have hrot_zero : rot 0 = 1 := by
    exact congrArg Subtype.val e.map_one
  have hw_inv_eq : w⁻¹ = w :=
    (eq_inv_of_mul_eq_one_left hw_sq).symm
  have hw_mul_rot (i : ZMod (Nat.card C)) :
      w * rot i = rot (-i) * w := by
    calc
      w * rot i = (w * rot i * w⁻¹) * w := by
        rw [hw_inv_eq, mul_assoc, hw_sq, mul_one]
      _ = (rot i)⁻¹ * w := by rw [hw_inv (rot i) (hrot_mem i)]
      _ = rot (-i) * w := by rw [hrot_neg]
  have hrot_mul_w (i : ZMod (Nat.card C)) :
      rot i * w = w * rot (-i) := by
    calc
      rot i * w = rot (-(-i)) * w := by rw [neg_neg]
      _ = w * rot (-i) := (hw_mul_rot (-i)).symm
  let hom : DihedralGroup (Nat.card C) →* G :=
    { toFun := fun x => match x with
        | DihedralGroup.r i => rot i
        | DihedralGroup.sr i => w * rot i
      map_one' := hrot_zero
      map_mul' := by
        rintro (i | i) (j | j)
        · change rot (i + j) = rot i * rot j
          exact hrot_add i j
        · change w * rot (j - i) = rot i * (w * rot j)
          calc
            w * rot (j - i) = w * rot (-i + j) := by
              rw [sub_eq_add_neg, add_comm]
            _ = w * (rot (-i) * rot j) := by rw [hrot_add]
            _ = (w * rot (-i)) * rot j := by rw [mul_assoc]
            _ = (rot i * w) * rot j := by rw [hrot_mul_w]
            _ = rot i * (w * rot j) := by rw [mul_assoc]
        · change w * rot (i + j) = (w * rot i) * rot j
          rw [hrot_add, mul_assoc]
        · change rot (j - i) = (w * rot i) * (w * rot j)
          calc
            rot (j - i) = rot (-i + j) := by
              rw [sub_eq_add_neg, add_comm]
            _ = rot (-i) * rot j := hrot_add (-i) j
            _ = (w * rot i) * (w * rot j) := by
              calc
                rot (-i) * rot j = (w * w) * (rot (-i) * rot j) := by
                  rw [hw_sq, one_mul]
                _ = (w * (w * rot (-i))) * rot j := by
                  simp only [mul_assoc]
                _ = (w * (rot i * w)) * rot j := by
                  rw [hrot_mul_w]
                _ = (w * rot i) * (w * rot j) := by
                  simp only [mul_assoc] }
  have hhom_injective : Function.Injective hom := by
    rintro (i | i) (j | j) hij
    · apply congrArg DihedralGroup.r
      change rot i = rot j at hij
      have heq : Multiplicative.ofAdd i = Multiplicative.ofAdd j := by
        apply e.injective
        apply Subtype.ext
        exact hij
      exact congrArg Multiplicative.toAdd heq
    · exfalso
      apply hw_not_mem
      change rot i = w * rot j at hij
      have hwrj : w * rot j ∈ C := by
        rw [← hij]
        exact hrot_mem i
      exact (C.mul_mem_cancel_right (hrot_mem j)).mp hwrj
    · exfalso
      apply hw_not_mem
      change w * rot i = rot j at hij
      have hwri : w * rot i ∈ C := by
        rw [hij]
        exact hrot_mem j
      exact (C.mul_mem_cancel_right (hrot_mem i)).mp hwri
    · apply congrArg DihedralGroup.sr
      change w * rot i = w * rot j at hij
      have heq : Multiplicative.ofAdd i = Multiplicative.ofAdd j := by
        apply e.injective
        apply Subtype.ext
        exact mul_left_cancel hij
      exact congrArg Multiplicative.toAdd heq
  have hhom_surjective : Function.Surjective hom := by
    intro x
    by_cases hx : x ∈ C
    · obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      refine ⟨DihedralGroup.r i.toAdd, ?_⟩
      exact congrArg Subtype.val hi
    · have hxw : w * x ∈ C := by
        rw [Subgroup.mul_mem_iff_of_index_two hindex]
        simp [hw_not_mem, hx]
      obtain ⟨i, hi⟩ := e.surjective ⟨w * x, hxw⟩
      refine ⟨DihedralGroup.sr i.toAdd, ?_⟩
      change w * rot i.toAdd = x
      have hi' : rot i.toAdd = w * x := congrArg Subtype.val hi
      rw [hi', ← mul_assoc, hw_sq, one_mul]
  exact ⟨(MulEquiv.ofBijective hom
    ⟨hhom_injective, hhom_surjective⟩).symm⟩

private theorem outside_reflection_of_mem_sup
    {G : Type u} [Group G] [Finite G]
    (T : Subgroup G) (hT : IsCyclic T) (w g : G)
    (hw_not_mem : w ∉ T) (hw_sq : w * w = 1)
    (hw_inv : ∀ t : G, t ∈ T → w * t * w⁻¹ = t⁻¹)
    (hg : g ∈ T ⊔ Subgroup.zpowers w) (hg_not_mem : g ∉ T) :
    g * g = 1 ∧ ∀ t : G, t ∈ T → g * t * g⁻¹ = t⁻¹ := by
  letI : IsCyclic T := hT
  have hw_inv_eq : w⁻¹ = w :=
    (eq_inv_of_mul_eq_one_left hw_sq).symm
  have hw_ne_one : w ≠ 1 := by
    intro hw
    apply hw_not_mem
    rw [hw]
    exact T.one_mem
  have horder : orderOf w = 2 := by
    have hpow : w ^ 2 = 1 := by simpa [pow_two] using hw_sq
    have hdvd : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one hpow
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact (hw_ne_one (orderOf_eq_one_iff.mp h)).elim
    · exact h
  have hw_normalizer : w ∈ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hw_inv y hy]
      exact T.inv_mem hy
    · intro hy
      have hdouble : w * (w * y * w⁻¹) * w⁻¹ ∈ T := by
        rw [hw_inv (w * y * w⁻¹) hy]
        exact T.inv_mem hy
      have heq : w * (w * y * w⁻¹) * w⁻¹ = y := by
        calc
          w * (w * y * w⁻¹) * w⁻¹ = (w * w) * y * (w * w) := by
            rw [hw_inv_eq]
            group
          _ = y := by simp [hw_sq]
      rwa [heq] at hdouble
  have hz_normalizer :
      Subgroup.zpowers w ≤ Subgroup.normalizer (T : Set G) :=
    Subgroup.zpowers_le.2 hw_normalizer
  have hproduct :
      ((Subgroup.zpowers w : Subgroup G) : Set G) * (T : Set G) =
        (T ⊔ Subgroup.zpowers w : Subgroup G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right
      (Subgroup.zpowers w) T hz_normalizer, sup_comm]
  have hg_product :
      g ∈ ((Subgroup.zpowers w : Subgroup G) : Set G) * (T : Set G) := by
    rw [hproduct]
    exact hg
  rcases hg_product with ⟨z, hz, t, ht, hzt⟩
  change z * t = g at hzt
  have hz_eq_one_or_w : z = 1 ∨ z = w := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← hk]
    have hmod := Int.emod_two_eq_zero_or_one k
    have hreduce : w ^ (k % (orderOf w : ℤ)) = w ^ k :=
      zpow_mod_orderOf w k
    rw [horder] at hreduce
    rcases hmod with hmod | hmod
    · left
      calc
        w ^ k = w ^ (k % (2 : ℤ)) := hreduce.symm
        _ = 1 := by rw [hmod, zpow_zero]
    · right
      calc
        w ^ k = w ^ (k % (2 : ℤ)) := hreduce.symm
        _ = w := by rw [hmod, zpow_one]
  have hz_eq_w : z = w := by
    rcases hz_eq_one_or_w with hz_one | hz_w
    · exfalso
      apply hg_not_mem
      rw [hz_one, one_mul] at hzt
      rwa [← hzt]
    · exact hz_w
  subst z
  have hg_eq : g = w * t := hzt.symm
  have hwt : w * t = t⁻¹ * w := by
    calc
      w * t = (w * t * w⁻¹) * w := by
        rw [hw_inv_eq, mul_assoc, hw_sq, mul_one]
      _ = t⁻¹ * w := by rw [hw_inv t ht]
  constructor
  · rw [hg_eq]
    calc
      (w * t) * (w * t) = (w * t) * (t⁻¹ * w) :=
        congrArg (fun x => (w * t) * x) hwt
      _ = w * (t * t⁻¹) * w := by group
      _ = w * w := by rw [mul_inv_cancel, mul_one]
      _ = 1 := hw_sq
  · intro y hy
    have hcomm : t * y = y * t := by
      exact congrArg Subtype.val
        (mul_comm (⟨t, ht⟩ : T) (⟨y, hy⟩ : T))
    rw [hg_eq, mul_inv_rev]
    calc
      w * t * y * (t⁻¹ * w⁻¹) =
          w * (t * y * t⁻¹) * w⁻¹ := by simp only [mul_assoc]
      _ = w * y * w⁻¹ := by rw [hcomm]; simp [mul_assoc]
      _ = y⁻¹ := hw_inv y hy

/-- The torus-normalizer part of Huppert II.8.22. -/
public theorem huppert_II_8_22_torus_normalizer_data
    {F : Type u} [Field F] [Finite F] {p f r : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (Z : Fin r → Subgroup H)
    (hcyclic : ∀ i, IsCyclic (Z i))
    (hnontrivial : ∀ i, 1 < Nat.card (Z i))
    (hcoprime : ∀ i, Nat.Coprime p (Nat.card (Z i)))
    (hmaximal : ∀ i (W : Subgroup H),
      IsCyclic W → Z i ≤ W → W = Z i) :
    ∃ s : Fin r → ℕ,
      (∀ i, 0 < s i ∧ s i ≤ 2) ∧
      (∀ i, Nat.card (Subgroup.normalizer (Z i : Set H)) =
        Nat.card (Z i) * s i) ∧
      (∀ i, s i = 2 →
        Nonempty (Subgroup.normalizer (Z i : Set H) ≃*
          DihedralGroup (Nat.card (Z i)))) ∧
      (∀ i,
        (Nat.card (Z i) ∣
            (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (Nat.card (Z i) ∣
            (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) := by
  classical
  let P0 : Sylow p (PSL2MatrixGroup F) := default
  obtain ⟨U, S, hUcyclic, hUcard, hScyclic, hScard, hpartition⟩ :=
    huppert_II_8_5_a_psl2_partition hFcard P0
  let Family : Subgroup (PSL2MatrixGroup F) → Prop := fun T =>
    (∃ g, T = (P0 : Subgroup (PSL2MatrixGroup F)).map
      (MulAut.conj g).toMonoidHom) ∨
    (∃ g, T = U.map (MulAut.conj g).toMonoidHom) ∨
    (∃ g, T = S.map (MulAut.conj g).toMonoidHom)
  have hpartition' : ∀ x : PSL2MatrixGroup F, x ≠ 1 →
      ∃! T : Subgroup (PSL2MatrixGroup F), x ∈ T ∧ Family T := by
    simpa [Family] using hpartition
  obtain ⟨U0, wU0, hU0cyclic, hU0card, hwU0N, hwU0T,
      hwU0sq, hwU0inv, hU0candidate, hU0normalizer⟩ :=
    huppert_II_8_3_split_torus_reflection_data hFcard
  obtain ⟨S0, wS0, hS0cyclic, hS0card, hwS0N, hwS0T,
      hwS0sq, hwS0inv, hS0candidate, hS0normalizer⟩ :=
    huppert_II_8_4_nonsplit_torus_reflection_data hFcard
  have hP0card :
      Nat.card (P0 : Subgroup (PSL2MatrixGroup F)) = Nat.card F := by
    obtain ⟨eP⟩ := huppert_II_8_2_a_sylow_equiv_additive hFcard P0
    exact (Nat.card_congr eP.toEquiv).symm
  have hU0cardU : Nat.card U0 = Nat.card U := hU0card.trans hUcard.symm
  have hS0cardS : Nat.card S0 = Nat.card S := hS0card.trans hScard.symm
  have hUalign : ∃ g : PSL2MatrixGroup F,
      U0 = U.map (MulAut.conj g).toMonoidHom := by
    by_cases hUbot : U = ⊥
    · have hbotU0 : (⊥ : Subgroup (PSL2MatrixGroup F)) = U0 := by
        apply Subgroup.eq_of_le_of_card_ge bot_le
        rw [hU0cardU, hUbot]
      refine ⟨1, ?_⟩
      rw [← hbotU0, hUbot]
      simp
    · have hU0ne : U0 ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hU0cardU]
        exact (Subgroup.one_lt_card_iff_ne_bot U).2 hUbot
      obtain ⟨u, hu_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU0ne
      have huG : (u : PSL2MatrixGroup F) ≠ 1 := by
        intro hu
        apply hu_ne
        apply Subtype.ext
        exact hu
      obtain ⟨T, huT, hTfamily⟩ :=
        (hpartition' (u : PSL2MatrixGroup F) huG).exists
      have hU0leT : U0 ≤ T :=
        cyclic_le_unique_partition_family Family hpartition'
          huG huT hTfamily u.property hU0cyclic
      rcases hTfamily with ⟨g, hTg⟩ | ⟨g, hTg⟩ | ⟨g, hTg⟩
      · exfalso
        have hcop : Nat.Coprime (Nat.card U0) (Nat.card T) := by
          rw [hTg, Subgroup.card_map_of_injective
            (MulAut.conj g).injective, hP0card, hU0card]
          exact (hq_coprime_split_order
            (Nat.card F) Nat.card_pos).symm
        exact huG (hmem_eq_one_of_coprime_card U0 T hcop
          u.property (hU0leT u.property))
      · refine ⟨g, ?_⟩
        calc
          U0 = T := Subgroup.eq_of_le_of_card_ge hU0leT (by
            rw [hTg, Subgroup.card_map_of_injective
              (MulAut.conj g).injective, hU0cardU])
          _ = U.map (MulAut.conj g).toMonoidHom := hTg
      · exfalso
        have hcop : Nat.Coprime (Nat.card U0) (Nat.card T) := by
          rw [hTg, Subgroup.card_map_of_injective
            (MulAut.conj g).injective, hScard, hU0card]
          exact hsplit_nonsplit_order_coprime
            (Nat.card F) (Finite.one_lt_card (α := F))
        exact huG (hmem_eq_one_of_coprime_card U0 T hcop
          u.property (hU0leT u.property))
  have hSalign : ∃ g : PSL2MatrixGroup F,
      S0 = S.map (MulAut.conj g).toMonoidHom := by
    by_cases hSbot : S = ⊥
    · have hbotS0 : (⊥ : Subgroup (PSL2MatrixGroup F)) = S0 := by
        apply Subgroup.eq_of_le_of_card_ge bot_le
        rw [hS0cardS, hSbot]
      refine ⟨1, ?_⟩
      rw [← hbotS0, hSbot]
      simp
    · have hS0ne : S0 ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hS0cardS]
        exact (Subgroup.one_lt_card_iff_ne_bot S).2 hSbot
      obtain ⟨s0, hs0_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hS0ne
      have hs0G : (s0 : PSL2MatrixGroup F) ≠ 1 := by
        intro hs0
        apply hs0_ne
        apply Subtype.ext
        exact hs0
      obtain ⟨T, hs0T, hTfamily⟩ :=
        (hpartition' (s0 : PSL2MatrixGroup F) hs0G).exists
      have hS0leT : S0 ≤ T :=
        cyclic_le_unique_partition_family Family hpartition'
          hs0G hs0T hTfamily s0.property hS0cyclic
      rcases hTfamily with ⟨g, hTg⟩ | ⟨g, hTg⟩ | ⟨g, hTg⟩
      · exfalso
        have hcop : Nat.Coprime (Nat.card S0) (Nat.card T) := by
          rw [hTg, Subgroup.card_map_of_injective
            (MulAut.conj g).injective, hP0card, hS0card]
          exact (hq_coprime_nonsplit_order
            (Nat.card F) Nat.card_pos).symm
        exact hs0G (hmem_eq_one_of_coprime_card S0 T hcop
          s0.property (hS0leT s0.property))
      · exfalso
        have hcop : Nat.Coprime (Nat.card S0) (Nat.card T) := by
          rw [hTg, Subgroup.card_map_of_injective
            (MulAut.conj g).injective, hUcard, hS0card]
          exact (hsplit_nonsplit_order_coprime
            (Nat.card F) (Finite.one_lt_card (α := F))).symm
        exact hs0G (hmem_eq_one_of_coprime_card S0 T hcop
          s0.property (hS0leT s0.property))
      · refine ⟨g, ?_⟩
        calc
          S0 = T := Subgroup.eq_of_le_of_card_ge hS0leT (by
            rw [hTg, Subgroup.card_map_of_injective
              (MulAut.conj g).injective, hS0cardS])
          _ = S.map (MulAut.conj g).toMonoidHom := hTg
  obtain ⟨gU, hUalign⟩ := hUalign
  obtain ⟨gS, hSalign⟩ := hSalign
  let eU : PSL2MatrixGroup F ≃* PSL2MatrixGroup F := (MulAut.conj gU).symm
  let eS : PSL2MatrixGroup F ≃* PSL2MatrixGroup F := (MulAut.conj gS).symm
  let wU : PSL2MatrixGroup F := eU wU0
  let wS : PSL2MatrixGroup F := eS wS0
  have hUback : U0.map eU.toMonoidHom = U := by
    apply (Subgroup.map_symm_eq_iff_map_eq (K := U)
      (e := MulAut.conj gU)).mpr
    exact hUalign.symm
  have hSback : S0.map eS.toMonoidHom = S := by
    apply (Subgroup.map_symm_eq_iff_map_eq (K := S)
      (e := MulAut.conj gS)).mpr
    exact hSalign.symm
  have hUdata :
      IsCyclic U ∧
      wU ∈ Subgroup.normalizer (U : Set (PSL2MatrixGroup F)) ∧
      wU ∉ U ∧
      wU * wU = 1 ∧
      (∀ t : PSL2MatrixGroup F, t ∈ U → wU * t * wU⁻¹ = t⁻¹) ∧
      Nat.card (U ⊔ Subgroup.zpowers wU : Subgroup (PSL2MatrixGroup F)) =
        2 * Nat.card U ∧
      ∀ R : Subgroup (PSL2MatrixGroup F), R ≤ U → R ≠ ⊥ →
        Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) =
          U ⊔ Subgroup.zpowers wU := by
    have h := equiv_torus_reflection_data U0 wU0 hU0cyclic hwU0N hwU0T
      hwU0sq hwU0inv hU0candidate hU0normalizer eU
    change IsCyclic (U0.map eU.toMonoidHom) ∧
      wU ∈ Subgroup.normalizer
        (U0.map eU.toMonoidHom : Set (PSL2MatrixGroup F)) ∧
      wU ∉ U0.map eU.toMonoidHom ∧
      wU * wU = 1 ∧
      (∀ t : PSL2MatrixGroup F, t ∈ U0.map eU.toMonoidHom →
        wU * t * wU⁻¹ = t⁻¹) ∧
      Nat.card (U0.map eU.toMonoidHom ⊔ Subgroup.zpowers wU :
        Subgroup (PSL2MatrixGroup F)) =
        2 * Nat.card (U0.map eU.toMonoidHom) ∧
      ∀ R : Subgroup (PSL2MatrixGroup F),
        R ≤ U0.map eU.toMonoidHom → R ≠ ⊥ →
          Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) =
            U0.map eU.toMonoidHom ⊔ Subgroup.zpowers wU at h
    rwa [hUback] at h
  have hSdata :
      IsCyclic S ∧
      wS ∈ Subgroup.normalizer (S : Set (PSL2MatrixGroup F)) ∧
      wS ∉ S ∧
      wS * wS = 1 ∧
      (∀ t : PSL2MatrixGroup F, t ∈ S → wS * t * wS⁻¹ = t⁻¹) ∧
      Nat.card (S ⊔ Subgroup.zpowers wS : Subgroup (PSL2MatrixGroup F)) =
        2 * Nat.card S ∧
      ∀ R : Subgroup (PSL2MatrixGroup F), R ≤ S → R ≠ ⊥ →
        Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) =
          S ⊔ Subgroup.zpowers wS := by
    have h := equiv_torus_reflection_data S0 wS0 hS0cyclic hwS0N hwS0T
      hwS0sq hwS0inv hS0candidate hS0normalizer eS
    change IsCyclic (S0.map eS.toMonoidHom) ∧
      wS ∈ Subgroup.normalizer
        (S0.map eS.toMonoidHom : Set (PSL2MatrixGroup F)) ∧
      wS ∉ S0.map eS.toMonoidHom ∧
      wS * wS = 1 ∧
      (∀ t : PSL2MatrixGroup F, t ∈ S0.map eS.toMonoidHom →
        wS * t * wS⁻¹ = t⁻¹) ∧
      Nat.card (S0.map eS.toMonoidHom ⊔ Subgroup.zpowers wS :
        Subgroup (PSL2MatrixGroup F)) =
        2 * Nat.card (S0.map eS.toMonoidHom) ∧
      ∀ R : Subgroup (PSL2MatrixGroup F),
        R ≤ S0.map eS.toMonoidHom → R ≠ ⊥ →
          Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) =
            S0.map eS.toMonoidHom ⊔ Subgroup.zpowers wS at h
    rwa [hSback] at h
  rcases hUdata with
    ⟨hUcyclic', hwUN, hwUT, hwUsq, hwUinv, hUcandidate, hUnormalizer⟩
  rcases hSdata with
    ⟨hScyclic', hwSN, hwST, hwSsq, hwSinv, hScandidate, hSnormalizer⟩
  have hmap_subtype_cyclic (A : Subgroup H) (hA : IsCyclic A) :
      IsCyclic (A.map H.subtype) := by
    exact (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective A H.subtype H.subtype_injective)).mp hA
  have hcomap_cyclic (A : Subgroup (PSL2MatrixGroup F))
      (hA : IsCyclic A) : IsCyclic (A.comap H.subtype) := by
    letI : IsCyclic A := hA
    have hmap_cyclic' : IsCyclic ((A.comap H.subtype).map H.subtype) :=
      Subgroup.isCyclic_of_le (Subgroup.map_comap_le H.subtype A)
    exact (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective
        (A.comap H.subtype) H.subtype H.subtype_injective)).mpr hmap_cyclic'
  have hambient (i : Fin r) :
      ∃ T : Subgroup (PSL2MatrixGroup F),
        ∃ w : PSL2MatrixGroup F,
        (IsCyclic T ∧
          w ∈ Subgroup.normalizer (T : Set (PSL2MatrixGroup F)) ∧
          w ∉ T ∧
          w * w = 1 ∧
          (∀ t : PSL2MatrixGroup F, t ∈ T → w * t * w⁻¹ = t⁻¹) ∧
          Nat.card (T ⊔ Subgroup.zpowers w : Subgroup (PSL2MatrixGroup F)) =
            2 * Nat.card T ∧
          ∀ R : Subgroup (PSL2MatrixGroup F), R ≤ T → R ≠ ⊥ →
            Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) =
              T ⊔ Subgroup.zpowers w) ∧
        (Z i).map H.subtype ≤ T ∧
        T.comap H.subtype = Z i ∧
        ((Nat.card (Z i) ∣
            (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (Nat.card (Z i) ∣
            (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) := by
    let A : Subgroup (PSL2MatrixGroup F) := (Z i).map H.subtype
    have hZi_ne : Z i ≠ ⊥ :=
      (Subgroup.one_lt_card_iff_ne_bot (Z i)).mp (hnontrivial i)
    have hA_ne : A ≠ ⊥ := by
      intro hA
      apply hZi_ne
      apply (Subgroup.map_eq_bot_iff_of_injective (Z i)
        (f := H.subtype) H.subtype_injective).mp
      exact hA
    have hAcyclic : IsCyclic A := hmap_subtype_cyclic (Z i) (hcyclic i)
    obtain ⟨a, ha_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA_ne
    have haG : (a : PSL2MatrixGroup F) ≠ 1 := by
      intro ha
      apply ha_ne
      apply Subtype.ext
      exact ha
    obtain ⟨T, haT, hTfamily⟩ :=
      (hpartition' (a : PSL2MatrixGroup F) haG).exists
    have hA_le_T : A ≤ T :=
      cyclic_le_unique_partition_family Family hpartition'
        haG haT hTfamily a.property hAcyclic
    have hTcomap (hTcyclic : IsCyclic T) : T.comap H.subtype = Z i := by
      have hWcyclic : IsCyclic (T.comap H.subtype) :=
        hcomap_cyclic T hTcyclic
      have hZ_le : Z i ≤ T.comap H.subtype :=
        Subgroup.map_le_iff_le_comap.mp hA_le_T
      exact hmaximal i (T.comap H.subtype) hWcyclic hZ_le
    rcases hTfamily with ⟨g, hTg⟩ | ⟨g, hTg⟩ | ⟨g, hTg⟩
    · exfalso
      have hcop : Nat.Coprime (Nat.card A) (Nat.card T) := by
        rw [show Nat.card A = Nat.card (Z i) by
              exact Subgroup.card_map_of_injective H.subtype_injective,
          hTg, Subgroup.card_map_of_injective (MulAut.conj g).injective,
          hP0card, hFcard]
        exact ((hcoprime i).pow_left f).symm
      exact haG (hmem_eq_one_of_coprime_card A T hcop
        a.property (hA_le_T a.property))
    · let w : PSL2MatrixGroup F := MulAut.conj g wU
      have hTdata := equiv_torus_reflection_data U wU hUcyclic' hwUN hwUT
        hwUsq hwUinv hUcandidate hUnormalizer (MulAut.conj g)
      rw [← hTg] at hTdata
      refine ⟨T, w, hTdata, hA_le_T, hTcomap hTdata.1, Or.inl ?_⟩
      · have hdvd := Subgroup.card_dvd_of_le hA_le_T
        rw [show Nat.card A = Nat.card (Z i) by
              exact Subgroup.card_map_of_injective H.subtype_injective,
          hTg, Subgroup.card_map_of_injective (MulAut.conj g).injective,
          hUcard] at hdvd
        exact hdvd
    · let w : PSL2MatrixGroup F := MulAut.conj g wS
      have hTdata := equiv_torus_reflection_data S wS hScyclic' hwSN hwST
        hwSsq hwSinv hScandidate hSnormalizer (MulAut.conj g)
      rw [← hTg] at hTdata
      refine ⟨T, w, hTdata, hA_le_T, hTcomap hTdata.1, Or.inr ?_⟩
      · have hdvd := Subgroup.card_dvd_of_le hA_le_T
        rw [show Nat.card A = Nat.card (Z i) by
              exact Subgroup.card_map_of_injective H.subtype_injective,
          hTg, Subgroup.card_map_of_injective (MulAut.conj g).injective,
          hScard] at hdvd
        exact hdvd
  let s : Fin r → ℕ := fun i =>
    (Z i).relIndex (Subgroup.normalizer (Z i : Set H))
  have hlocal (i : Fin r) :
      (0 < s i ∧ s i ≤ 2) ∧
      Nat.card (Subgroup.normalizer (Z i : Set H)) =
        Nat.card (Z i) * s i ∧
      (s i = 2 →
        Nonempty (Subgroup.normalizer (Z i : Set H) ≃*
          DihedralGroup (Nat.card (Z i)))) ∧
      ((Nat.card (Z i) ∣
          (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
        (Nat.card (Z i) ∣
          (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) := by
    obtain ⟨T, w, hdata, hA_le_T, hTcomap, hdvd⟩ := hambient i
    rcases hdata with
      ⟨hTcyclic, _hwN, hwT, hwsq, hwinv, hcandidate_card, hnormalizer⟩
    let A : Subgroup (PSL2MatrixGroup F) := (Z i).map H.subtype
    let B : Subgroup (PSL2MatrixGroup F) :=
      (Subgroup.normalizer (Z i : Set H)).map H.subtype
    let N : Subgroup (PSL2MatrixGroup F) := T ⊔ Subgroup.zpowers w
    have hA_ne : A ≠ ⊥ := by
      intro hA
      have hZi_bot : Z i = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective (Z i)
          (f := H.subtype) H.subtype_injective).mp hA
      exact (hnontrivial i).ne (by rw [hZi_bot]; simp)
    have hB_le : B ≤ N := by
      have hmap : B ≤ Subgroup.normalizer (A : Set (PSL2MatrixGroup F)) :=
        Subgroup.le_normalizer_map H.subtype
      rw [hnormalizer A hA_le_T hA_ne] at hmap
      exact hmap
    have hinter : T ⊓ B = A := by
      apply le_antisymm
      · intro x hx
        rcases hx.2 with ⟨y, hyN, rfl⟩
        have hyT : y ∈ T.comap H.subtype := hx.1
        rw [hTcomap] at hyT
        exact ⟨y, hyT, rfl⟩
      · exact le_inf hA_le_T
          (Subgroup.map_mono Subgroup.le_normalizer)
    have hTindex : T.relIndex N = 2 :=
      relIndex_eq_two_of_card_eq_two_mul T N le_sup_left hcandidate_card
    have hambient_index : A.relIndex B ≤ 2 :=
      relIndex_le_two_of_inter_eq T B N A hB_le hinter hTindex
    have hs_eq : s i = A.relIndex B := by
      exact (Subgroup.relIndex_map_map_of_injective
        (Z i) (Subgroup.normalizer (Z i : Set H))
        H.subtype_injective).symm
    have hs_pos : 0 < s i := by
      rw [hs_eq, Subgroup.relIndex]
      exact Nat.card_pos
    have hs_le : s i ≤ 2 := by
      rw [hs_eq]
      exact hambient_index
    let NH : Subgroup H := Subgroup.normalizer (Z i : Set H)
    let C : Subgroup NH := (Z i).subgroupOf NH
    let eC : C ≃* Z i :=
      Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer
    have hCcard : Nat.card C = Nat.card (Z i) :=
      Nat.card_congr eC.toEquiv
    have hnormalizer_card :
        Nat.card (Subgroup.normalizer (Z i : Set H)) =
          Nat.card (Z i) * s i := by
      calc
        Nat.card (Subgroup.normalizer (Z i : Set H)) = Nat.card NH := rfl
        _ = Nat.card C * C.index := C.card_mul_index.symm
        _ = Nat.card (Z i) * s i := by
          rw [hCcard]
          rfl
    have hdihedral (hs_two : s i = 2) :
        Nonempty (Subgroup.normalizer (Z i : Set H) ≃*
          DihedralGroup (Nat.card (Z i))) := by
      have hCindex : C.index = 2 := by
        change ((Z i).subgroupOf
          (Subgroup.normalizer (Z i : Set H))).index = 2
        exact hs_two
      obtain ⟨a, ha_not, _ha_cosets⟩ :=
        Subgroup.index_eq_two_iff_exists_notMem_and.mp hCindex
      have haB : (((a : NH) : H) : PSL2MatrixGroup F) ∈ B :=
        ⟨((a : NH) : H), a.property, rfl⟩
      have haN : (((a : NH) : H) : PSL2MatrixGroup F) ∈ N := hB_le haB
      have ha_not_T : (((a : NH) : H) : PSL2MatrixGroup F) ∉ T := by
        intro haT
        have ha_comap : ((a : NH) : H) ∈ T.comap H.subtype := haT
        rw [hTcomap] at ha_comap
        apply ha_not
        exact ha_comap
      obtain ⟨ha_sq_ambient, ha_inv_ambient⟩ :=
        outside_reflection_of_mem_sup T hTcyclic w
          (((a : NH) : H) : PSL2MatrixGroup F)
          hwT hwsq hwinv haN ha_not_T
      have ha_sq : a * a = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        exact ha_sq_ambient
      have ha_inv : ∀ c : NH, c ∈ C → a * c * a⁻¹ = c⁻¹ := by
        intro c hc
        apply Subtype.ext
        apply Subtype.ext
        apply ha_inv_ambient
        apply hA_le_T
        exact ⟨((c : NH) : H), hc, rfl⟩
      have hCcyclic : IsCyclic C :=
        (MulEquiv.isCyclic eC).mpr (hcyclic i)
      have hdih := mulEquiv_dihedral_of_cyclic_reflection
        C hCcyclic a ha_not ha_sq ha_inv hCindex
      rw [hCcard] at hdih
      exact hdih
    exact ⟨⟨hs_pos, hs_le⟩, hnormalizer_card, hdihedral, hdvd⟩
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · exact fun i => (hlocal i).1
  · exact fun i => (hlocal i).2.1
  · exact fun i => (hlocal i).2.2.1
  · exact fun i => (hlocal i).2.2.2

/-- The Schur-Zassenhaus part of Huppert II.8.21, separated from the
projective-line argument which makes the complement maximal cyclic in `H`. -/
private theorem h821_schur_zassenhaus_core
    {F : Type u} [Field F] [Finite F] {p f m : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (P : Sylow p H) (hPcard : Nat.card P = p ^ m)
    (N : Subgroup H) (hN : N = Subgroup.normalizer (P : Set H))
    (hP_le_N : (P : Subgroup H) ≤ N)
    (PN : Subgroup N) [PN.Normal]
    (hPN : PN = (P : Subgroup H).subgroupOf N)
    (hquotient_cyclic : IsCyclic (N ⧸ PN))
    (hquotient_card_dvd : Nat.card (N ⧸ PN) ∣ Nat.card F - 1)
    (hcomplement_maximal :
      ∀ C : Subgroup N, PN.IsComplement' C → IsCyclic C →
        let W : Subgroup H := C.map N.subtype
        W = ⊥ ∨
          (1 < Nat.card W ∧
            ∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W)) :
    ∃ W : Subgroup H,
      IsCyclic W ∧
      Nat.Coprime p (Nat.card W) ∧
      (W = ⊥ ∨
        (1 < Nat.card W ∧
          ∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W)) ∧
      Nat.card (Subgroup.normalizer (P : Set H)) =
        Nat.card P * Nat.card W := by
  classical
  have hf_ne_zero : f ≠ 0 := by
    intro hf
    subst f
    have hcard : Nat.card F = 1 := by simpa using hFcard
    exact (Nat.ne_of_gt (Finite.one_lt_card (α := F))) hcard
  have hp_dvd_cardF : p ∣ Nat.card F := by
    rw [hFcard]
    exact dvd_pow_self p hf_ne_zero
  have hp_not_dvd_cardF_sub_one : ¬ p ∣ Nat.card F - 1 := by
    intro hp_sub
    have hp_one : p ∣ 1 := by
      have h := Nat.dvd_sub hp_dvd_cardF hp_sub
      have hcard_pos : 0 < Nat.card F := Nat.card_pos
      have hsub : Nat.card F - (Nat.card F - 1) = 1 := by omega
      rwa [hsub] at h
    exact (Fact.out : p.Prime).not_dvd_one hp_one
  have hcop_p_cardF_sub_one : Nat.Coprime p (Nat.card F - 1) :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp_not_dvd_cardF_sub_one
  have hcop_p_quotient : Nat.Coprime p (Nat.card (N ⧸ PN)) :=
    Nat.Coprime.of_dvd_right hquotient_card_dvd hcop_p_cardF_sub_one
  have hPNcard : Nat.card PN = p ^ m := by
    calc
      Nat.card PN = Nat.card ((P : Subgroup H).subgroupOf N) := by rw [hPN]
      _ = Nat.card P :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le_N).toEquiv
      _ = p ^ m := hPcard
  have hPNindex : PN.index = Nat.card (N ⧸ PN) := rfl
  have hPN_coprime_index : Nat.Coprime (Nat.card PN) PN.index := by
    rw [hPNcard, hPNindex]
    exact hcop_p_quotient.pow_left m
  obtain ⟨C, hPN_C_complement⟩ :=
    Subgroup.exists_right_complement'_of_coprime hPN_coprime_index
  have hC_cyclic : IsCyclic C := by
    let eC : N ⧸ PN ≃* C := hPN_C_complement.symm.QuotientMulEquiv
    letI : IsCyclic (N ⧸ PN) := hquotient_cyclic
    exact isCyclic_of_surjective eC eC.surjective
  have hCcard : Nat.card C = Nat.card (N ⧸ PN) := by
    calc
      Nat.card C = PN.index := hPN_C_complement.symm.index_eq_card.symm
      _ = Nat.card (N ⧸ PN) := hPNindex
  let W : Subgroup H := C.map N.subtype
  have hW_cyclic : IsCyclic W := by
    let eW : C ≃* W :=
      Subgroup.equivMapOfInjective C N.subtype N.subtype_injective
    letI : IsCyclic C := hC_cyclic
    exact isCyclic_of_surjective eW eW.surjective
  have hWcard : Nat.card W = Nat.card C := by
    dsimp [W]
    exact Subgroup.card_map_of_injective N.subtype_injective
  have hW_coprime : Nat.Coprime p (Nat.card W) := by
    rw [hWcard, hCcard]
    exact hcop_p_quotient
  have hW_boundary :
      W = ⊥ ∨
        (1 < Nat.card W ∧
          ∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) := by
    simpa [W] using
      hcomplement_maximal C hPN_C_complement hC_cyclic
  refine ⟨W, hW_cyclic, hW_coprime, hW_boundary, ?_⟩
  rw [← hN]
  calc
    Nat.card N = Nat.card PN * Nat.card C := hPN_C_complement.card_mul.symm
    _ = Nat.card P * Nat.card W := by
      rw [hWcard, hPN, Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe hP_le_N).toEquiv]

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The standard upper-triangular Borel data used in Huppert II.8.21. -/
private theorem h821_standard_borel_data
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) :
    ∃ U T : Subgroup (PSL2MatrixGroup F),
      Nat.card U = Nat.card F ∧
      IsPGroup p U ∧
      IsMulCommutative U ∧
      IsCyclic T ∧
      Nat.card T =
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      Nat.card T ∣ Nat.card F - 1 ∧
      T ≤ Subgroup.normalizer (U : Set (PSL2MatrixGroup F)) ∧
      (∀ t : PSL2MatrixGroup F, t ∈ T →
        ∀ x : PSL2MatrixGroup F, x ∈ U →
          t * x * t⁻¹ = x → t = 1 ∨ x = 1) ∧
      (∀ x : PSL2MatrixGroup F, x ∈ U ⊔ T → x ∉ U →
        ∃ u : PSL2MatrixGroup F, u ∈ U ∧
          x ∈ T.map (MulAut.conj u).toMonoidHom) ∧
      (∀ R : Subgroup (PSL2MatrixGroup F), R ≤ U → R ≠ ⊥ →
        Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) ≤ U ⊔ T) ∧
      ∃ unipotent : AddChar F (PSL2MatrixGroup F),
        ∃ splitTorus : Fˣ →* PSL2MatrixGroup F,
          Function.Injective unipotent ∧
          U = unipotent.toMonoidHom.range ∧
          T = splitTorus.range ∧
          (∀ a : Fˣ, ∀ x : F,
            splitTorus a * unipotent x * (splitTorus a)⁻¹ =
              unipotent ((a : F) ^ 2 * x)) ∧
          (∀ x : F, unipotent x =
            QuotientGroup.mk'
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F))
              (⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩ :
                Matrix.SpecialLinearGroup (Fin 2) F)) ∧
          ∀ a : Fˣ, splitTorus a =
            QuotientGroup.mk'
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F))
              (⟨!![(a : F), 0; 0, (a⁻¹ : F)],
                  by simp [Matrix.det_fin_two]⟩ :
                Matrix.SpecialLinearGroup (Fin 2) F) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F p :=
    charP_of_card_eq_prime_pow (by simpa using hFcard)
  let qSL : Matrix.SpecialLinearGroup (Fin 2) F →* PSL2MatrixGroup F :=
    QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
  let unipotentSL :
      AddChar F (Matrix.SpecialLinearGroup (Fin 2) F) :=
    { toFun := fun a => ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two]⟩
      map_zero_eq_one' := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      map_add_eq_mul' := by
        intro a b
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, add_comm] }
  let unipotent : AddChar F (PSL2MatrixGroup F) :=
    qSL.compAddChar unipotentSL
  have h_unipotent_injective : Function.Injective unipotent := by
    intro a b hab
    have hdiff : unipotent (a - b) = 1 := by
      rw [sub_eq_add_neg, unipotent.map_add_eq_mul,
        unipotent.map_neg_eq_inv, hab, mul_inv_cancel]
    have hcenter :
        unipotentSL (a - b) ∈
          Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
      (QuotientGroup.eq_one_iff (unipotentSL (a - b))).mp hdiff
    have hscalar :=
      Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center
        hcenter (0 : Fin 2)
    have hab0 := congrFun (congrFun hscalar (0 : Fin 2)) (1 : Fin 2)
    apply sub_eq_zero.mp
    simpa using hab0.symm
  let U : Subgroup (PSL2MatrixGroup F) := unipotent.toMonoidHom.range
  have hUcard : Nat.card U = Nat.card F := by
    let e : Multiplicative F ≃ U :=
      Equiv.ofInjective unipotent.toMonoidHom h_unipotent_injective
    exact Nat.card_congr e.symm
  have hU_isPGroup : IsPGroup p U := by
    apply IsPGroup.of_card
    rw [hUcard, hFcard]
  have hU_commutative : IsMulCommutative U := by
    constructor
    constructor
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    rcases hx with ⟨a, rfl⟩
    rcases hy with ⟨b, rfl⟩
    apply Subtype.ext
    change unipotent a.toAdd * unipotent b.toAdd =
      unipotent b.toAdd * unipotent a.toAdd
    rw [← unipotent.map_add_eq_mul, add_comm,
      unipotent.map_add_eq_mul]
  let splitTorusSL : Fˣ →* Matrix.SpecialLinearGroup (Fin 2) F :=
    { toFun := fun a => ⟨!![(a : F), 0; 0, (a⁻¹ : F)], by
          simp [Matrix.det_fin_two]⟩
      map_one' := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, mul_comm] }
  let splitTorus : Fˣ →* PSL2MatrixGroup F :=
    qSL.comp splitTorusSL
  let T : Subgroup (PSL2MatrixGroup F) := splitTorus.range
  have hf_ne_zero : f ≠ 0 :=
    huppert_II_8_27_field_exponent_ne_zero hFcard
  have hcard_roots :
      Nat.card (rootsOfUnity 2 F) =
        Nat.gcd (Nat.card F - 1) 2 := by
    let e :=
      Equiv.Set.image ((↑) : Fˣ → F) (rootsOfUnity 2 F : Set Fˣ)
        Units.val_injective
    have he :
        Nat.card (rootsOfUnity 2 F) =
          Nat.card (((↑) : Fˣ → F) '' (rootsOfUnity 2 F : Set Fˣ)) :=
      Nat.card_congr e
    rw [Units.val_set_image_rootsOfUnity_two] at he
    by_cases hp_two : p = 2
    · have htwo : (2 : F) = 0 := by
        subst p
        exact CharP.cast_eq_zero F 2
      have hneg_one : (-1 : F) = 1 := by
        apply (neg_eq_iff_add_eq_zero).2
        have hone_add_one : (1 : F) + 1 = 0 := by
          rw [show (1 : F) + 1 = 2 by norm_num, htwo]
        exact hone_add_one
      have hleft : Nat.card (rootsOfUnity 2 F) = 1 := by
        simpa [hneg_one] using he
      have hq_even : Even (Nat.card F) := by
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hf_ne_zero
        rw [hFcard, hp_two, hk, pow_succ]
        use 2 ^ k
        ring
      have hq_sub_one_odd : Odd (Nat.card F - 1) := by
        rw [← Nat.not_even_iff_odd]
        intro heven
        have hparity :=
          (Nat.even_sub
            (show 1 ≤ Nat.card F from
              (Finite.one_lt_card (α := F)).le)).mp heven
        exact Nat.not_even_one (hparity.mp hq_even)
      have hgcd : Nat.gcd (Nat.card F - 1) 2 = 1 :=
        Nat.coprime_iff_gcd_eq_one.mp hq_sub_one_odd.coprime_two_right
      rw [hleft, hgcd]
    · have hring_char_ne_two : ringChar F ≠ 2 := by
        rw [ringChar.eq F p]
        exact hp_two
      have hneg_one : (-1 : F) ≠ 1 :=
        Ring.neg_one_ne_one_of_char_ne_two hring_char_ne_two
      have hleft : Nat.card (rootsOfUnity 2 F) = 2 := by
        simpa [hneg_one, Ne.symm hneg_one] using he
      have hq_odd : Odd (Nat.card F) := by
        rw [hFcard]
        exact ((Fact.out : p.Prime).odd_of_ne_two hp_two).pow
      have htwo_dvd : 2 ∣ Nat.card F - 1 := by
        rcases hq_odd with ⟨k, hk⟩
        use k
        omega
      have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 :=
        Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
          (Nat.dvd_gcd htwo_dvd (dvd_refl 2))
      rw [hleft, hgcd]
  have hsplit_mem_ker_iff (a : Fˣ) :
      a ∈ splitTorus.ker ↔ a ∈ rootsOfUnity 2 F := by
    rw [MonoidHom.mem_ker, mem_rootsOfUnity]
    constructor
    · intro ha
      have hcenter :
          splitTorusSL a ∈
            Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
        (QuotientGroup.eq_one_iff (splitTorusSL a)).mp ha
      have hscalar :=
        Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center
          hcenter (0 : Fin 2)
      have ha_inv_val :=
        congrFun (congrFun hscalar (1 : Fin 2)) (1 : Fin 2)
      have ha_inv : a = a⁻¹ := by
        apply Units.ext
        simpa [splitTorusSL] using ha_inv_val
      simpa [pow_two] using (eq_inv_iff_mul_eq_one.mp ha_inv)
    · intro ha
      apply (QuotientGroup.eq_one_iff (splitTorusSL a)).mpr
      rw [Matrix.SpecialLinearGroup.mem_center_iff]
      refine ⟨(a : F), ?_, ?_⟩
      · simpa using congrArg Units.val ha
      · have ha_inv : a = a⁻¹ :=
          eq_inv_iff_mul_eq_one.mpr (by simpa [pow_two] using ha)
        have ha_inv_val : (a : F) = (a⁻¹ : F) := by
          simpa using congrArg Units.val ha_inv
        change Matrix.scalar (Fin 2) (a : F) =
          !![(a : F), 0; 0, (a⁻¹ : F)]
        ext i j
        fin_cases i <;> fin_cases j
        · rfl
        · rfl
        · rfl
        · exact ha_inv_val
  have hsplit_ker_eq : splitTorus.ker = rootsOfUnity 2 F := by
    ext a
    exact hsplit_mem_ker_iff a
  have hsplit_ker_card :
      Nat.card splitTorus.ker = Nat.gcd (Nat.card F - 1) 2 := by
    rw [hsplit_ker_eq, hcard_roots]
  have hsplit_range_mul :
      Nat.card splitTorus.range * Nat.gcd (Nat.card F - 1) 2 =
        Nat.card F - 1 := by
    calc
      Nat.card splitTorus.range * Nat.gcd (Nat.card F - 1) 2 =
          splitTorus.ker.index * Nat.card splitTorus.ker := by
        rw [Subgroup.index_ker, hsplit_ker_card]
      _ = Nat.card Fˣ := splitTorus.ker.index_mul_card
      _ = Nat.card F - 1 := by
        simpa [Nat.card_eq_fintype_card] using
          (Fintype.card_units (α := F))
  have hTcard :
      Nat.card T =
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 := by
    apply Nat.eq_div_of_mul_eq_left
    · rw [← hcard_roots]
      exact Nat.ne_of_gt Nat.card_pos
    · exact hsplit_range_mul
  have hT_cyclic : IsCyclic T := by
    have hUnitsCyclic : IsCyclic Fˣ := by
      letI : IsCyclic (⊤ : Subgroup Fˣ) := isCyclic_subgroup_units ⊤
      exact isCyclic_of_surjective
        ((⊤ : Subgroup Fˣ).subtype) (by
          intro a
          exact ⟨⟨a, Subgroup.mem_top a⟩, rfl⟩)
    letI : IsCyclic Fˣ := hUnitsCyclic
    exact isCyclic_of_surjective splitTorus.rangeRestrict
      splitTorus.rangeRestrict_surjective
  have hTcard_dvd : Nat.card T ∣ Nat.card F - 1 := by
    have hdvd := Subgroup.card_dvd_of_surjective splitTorus.rangeRestrict
      splitTorus.rangeRestrict_surjective
    have hUnitsCard : Nat.card Fˣ = Nat.card F - 1 := by
      simpa [Nat.card_eq_fintype_card] using
        (Fintype.card_units (α := F))
    rw [← hUnitsCard]
    simpa [T] using hdvd
  have hsplitSL_mul (a : Fˣ) (x : F) :
      splitTorusSL a * unipotentSL x =
        unipotentSL ((a : F) ^ 2 * x) * splitTorusSL a := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [splitTorusSL, unipotentSL, Matrix.mul_apply,
        pow_two, mul_assoc, mul_comm]
  have hsplitSL_conj (a : Fˣ) (x : F) :
      splitTorusSL a * unipotentSL x * (splitTorusSL a)⁻¹ =
        unipotentSL ((a : F) ^ 2 * x) := by
    rw [hsplitSL_mul]
    simp
  have hsplit_conj (a : Fˣ) (x : F) :
      splitTorus a * unipotent x * (splitTorus a)⁻¹ =
        unipotent ((a : F) ^ 2 * x) := by
    simpa [splitTorus, unipotent] using congrArg qSL
      (hsplitSL_conj a x)
  have hT_le_normalizer :
      T ≤ Subgroup.normalizer (U : Set (PSL2MatrixGroup F)) := by
    intro t ht
    rcases ht with ⟨a, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rcases hh with ⟨x, hx⟩
      refine ⟨Multiplicative.ofAdd ((a : F) ^ 2 * x.toAdd), ?_⟩
      change unipotent ((a : F) ^ 2 * x.toAdd) =
        splitTorus a * h * (splitTorus a)⁻¹
      rw [← hx]
      exact (hsplit_conj a x.toAdd).symm
    · intro hh
      rcases hh with ⟨y, hy⟩
      refine ⟨Multiplicative.ofAdd (((a⁻¹ : Fˣ) : F) ^ 2 * y.toAdd), ?_⟩
      change unipotent (((a⁻¹ : Fˣ) : F) ^ 2 * y.toAdd) = h
      calc
        unipotent (((a⁻¹ : Fˣ) : F) ^ 2 * y.toAdd) =
            splitTorus a⁻¹ * unipotent y.toAdd * (splitTorus a⁻¹)⁻¹ :=
          (hsplit_conj a⁻¹ y.toAdd).symm
        _ = h := by
          change unipotent y.toAdd = splitTorus a * h * (splitTorus a)⁻¹ at hy
          have hTa_inv : splitTorus a⁻¹ = (splitTorus a)⁻¹ :=
            map_inv splitTorus a
          rw [hy, hTa_inv]
          group
  have hT_fixedPointFree
      (t : PSL2MatrixGroup F) (ht : t ∈ T)
      (x : PSL2MatrixGroup F) (hx : x ∈ U)
      (hfix : t * x * t⁻¹ = x) : t = 1 ∨ x = 1 := by
    rcases ht with ⟨a, ha⟩
    rcases hx with ⟨b, hb⟩
    change unipotent b.toAdd = x at hb
    have hcoord : (a : F) ^ 2 * b.toAdd = b.toAdd := by
      apply h_unipotent_injective
      calc
        unipotent ((a : F) ^ 2 * b.toAdd) =
            splitTorus a * unipotent b.toAdd * (splitTorus a)⁻¹ :=
          (hsplit_conj a b.toAdd).symm
        _ = splitTorus a * x * (splitTorus a)⁻¹ := by rw [hb]
        _ = t * x * t⁻¹ := by rw [ha]
        _ = x := hfix
        _ = unipotent b.toAdd := hb.symm
    by_cases hbzero : b.toAdd = 0
    · right
      rw [← hb, hbzero]
      simp
    · left
      rw [← ha]
      apply MonoidHom.mem_ker.mp
      apply (hsplit_mem_ker_iff a).2
      rw [mem_rootsOfUnity]
      apply Units.ext
      apply mul_right_cancel₀ hbzero
      simpa using hcoord
  have hB_conjugate_torus
      (x : PSL2MatrixGroup F) (hxB : x ∈ U ⊔ T) (hxU : x ∉ U) :
      ∃ u : PSL2MatrixGroup F, u ∈ U ∧
        x ∈ T.map (MulAut.conj u).toMonoidHom := by
    have hB_product :
        (U : Set (PSL2MatrixGroup F)) * (T : Set (PSL2MatrixGroup F)) =
          (U ⊔ T : Subgroup (PSL2MatrixGroup F)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left
        U T hT_le_normalizer]
    change x ∈ ((U ⊔ T : Subgroup (PSL2MatrixGroup F)) :
      Set (PSL2MatrixGroup F)) at hxB
    rw [← hB_product] at hxB
    rcases hxB with ⟨y, hyU, z, hzT, hyz⟩
    rcases hyU with ⟨b, hb⟩
    rcases hzT with ⟨a, ha⟩
    have hfactor : unipotent b.toAdd * splitTorus a = x := by
      rw [← hb, ← ha] at hyz
      exact hyz
    have hsplit_ne_one : splitTorus a ≠ 1 := by
      intro ha_one
      apply hxU
      rw [← hfactor, ha_one, mul_one]
      exact ⟨b, rfl⟩
    have ha_sq_ne : (a : F) ^ 2 ≠ 1 := by
      intro ha_sq
      apply hsplit_ne_one
      have ha_sq_units : a ^ 2 = 1 := by
        apply Units.ext
        simpa using ha_sq
      exact MonoidHom.mem_ker.mp
        ((hsplit_mem_ker_iff a).2
          (by simpa [mem_rootsOfUnity] using ha_sq_units))
    have hden : 1 - (a : F) ^ 2 ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm ha_sq_ne)
    let s : F := b.toAdd / (1 - (a : F) ^ 2)
    let u : PSL2MatrixGroup F := unipotent s
    have hs : s + (a : F) ^ 2 * (-s) = b.toAdd := by
      dsimp [s]
      field_simp [hden]
      ring
    have hx_conj :
        u * splitTorus a * u⁻¹ = x := by
      rw [← hfactor]
      change unipotent s * splitTorus a * (unipotent s)⁻¹ =
        unipotent b.toAdd * splitTorus a
      calc
        unipotent s * splitTorus a * (unipotent s)⁻¹ =
            unipotent s *
              (splitTorus a * unipotent (-s) * (splitTorus a)⁻¹) *
                splitTorus a := by
          rw [unipotent.map_neg_eq_inv]
          group
        _ = unipotent s * unipotent ((a : F) ^ 2 * (-s)) *
              splitTorus a := by
          rw [hsplit_conj]
        _ = unipotent (s + (a : F) ^ 2 * (-s)) * splitTorus a := by
          rw [unipotent.map_add_eq_mul]
        _ = unipotent b.toAdd * splitTorus a := by rw [hs]
    refine ⟨u, ⟨Multiplicative.ofAdd s, rfl⟩, ?_⟩
    rw [← hx_conj]
    exact Subgroup.mem_map_of_mem (MulAut.conj u).toMonoidHom
      (⟨a, rfl⟩ : splitTorus a ∈ T)
  have hnormalizer_le
      (R : Subgroup (PSL2MatrixGroup F)) (hR_le_U : R ≤ U)
      (hR_ne_bot : R ≠ ⊥) :
      Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) ≤ U ⊔ T := by
    obtain ⟨r, hr_ne_one⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR_ne_bot
    have hrU : (r : PSL2MatrixGroup F) ∈ U := hR_le_U r.property
    rcases hrU with ⟨t, ht⟩
    have ht_ne_zero : t.toAdd ≠ 0 := by
      intro ht_zero
      apply hr_ne_one
      apply Subtype.ext
      change (r : PSL2MatrixGroup F) = 1
      rw [← ht]
      change unipotent t.toAdd = 1
      rw [ht_zero]
      simp
    have hr_eq : (r : PSL2MatrixGroup F) = unipotent t.toAdd := by
      simpa using ht.symm
    intro g
    refine QuotientGroup.induction_on g ?_
    intro A hA_normalizes
    have hr_conj_R :
        qSL A * (r : PSL2MatrixGroup F) * (qSL A)⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hA_normalizes
        (r : PSL2MatrixGroup F)).mp r.property
    have hconj_mem :
        qSL A * unipotent t.toAdd * (qSL A)⁻¹ ∈ U := by
      rw [← hr_eq]
      exact hR_le_U hr_conj_R
    rcases hconj_mem with ⟨x, hx⟩
    have hxq :
        qSL (unipotentSL x.toAdd) =
          qSL (A * unipotentSL t.toAdd * A⁻¹) := by
      simpa [unipotent] using hx
    rcases (QuotientGroup.mk'_eq_mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).mp hxq with
      ⟨z, hz_center, hz_eq⟩
    have hz_eq_mul_A :
        unipotentSL x.toAdd * z * A = A * unipotentSL t.toAdd := by
      calc
        unipotentSL x.toAdd * z * A =
            (A * unipotentSL t.toAdd * A⁻¹) * A := by rw [hz_eq]
        _ = A * unipotentSL t.toAdd := by group
    have hscalar :=
      Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center
        hz_center (0 : Fin 2)
    have hz_eq_matrix := congrArg Subtype.val hz_eq_mul_A
    change
      (unipotentSL x.toAdd : Matrix (Fin 2) (Fin 2) F) *
          (z : Matrix (Fin 2) (Fin 2) F) *
            (A : Matrix (Fin 2) (Fin 2) F) =
        (A : Matrix (Fin 2) (Fin 2) F) *
          (unipotentSL t.toAdd : Matrix (Fin 2) (Fin 2) F) at hz_eq_matrix
    rw [← hscalar] at hz_eq_matrix
    have h10 := congrFun (congrFun hz_eq_matrix (1 : Fin 2)) (0 : Fin 2)
    have h11 := congrFun (congrFun hz_eq_matrix (1 : Fin 2)) (1 : Fin 2)
    simp [unipotentSL, Matrix.mul_apply] at h10 h11
    have hc_zero : A (1 : Fin 2) (0 : Fin 2) = 0 := by
      by_cases hr_one : (z : Matrix (Fin 2) (Fin 2) F) 0 0 = 1
      · rw [hr_one, one_mul] at h11
        have hcancel := congrArg (fun y : F => y - A 1 1) h11
        have hct : A 1 0 * t.toAdd = 0 := by
          simpa using hcancel.symm
        exact (mul_eq_zero.mp hct).resolve_right ht_ne_zero
      · have hprod :
            (((z : Matrix (Fin 2) (Fin 2) F) 0 0) - 1) *
                A (1 : Fin 2) (0 : Fin 2) = 0 := by
          calc
            (((z : Matrix (Fin 2) (Fin 2) F) 0 0) - 1) * A 1 0 =
                ((z : Matrix (Fin 2) (Fin 2) F) 0 0) * A 1 0 - A 1 0 := by ring
            _ = 0 := by rw [h10]; ring
        exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hr_one)
    have hdet := A.property
    rw [Matrix.det_fin_two] at hdet
    have had : A (0 : Fin 2) (0 : Fin 2) * A (1 : Fin 2) (1 : Fin 2) = 1 := by
      simpa [hc_zero] using hdet
    have ha_zero : A (0 : Fin 2) (0 : Fin 2) ≠ 0 :=
      left_ne_zero_of_mul_eq_one had
    let aU : Fˣ := Units.mk0 (A (0 : Fin 2) (0 : Fin 2)) ha_zero
    have hd_inv : A (1 : Fin 2) (1 : Fin 2) = (aU⁻¹ : F) := by
      simpa [aU] using eq_inv_of_mul_eq_one_right had
    have hfactor :
        A = unipotentSL (A 0 1 * A 0 0) * splitTorusSL aU := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j
      · simp [unipotentSL, splitTorusSL, Matrix.mul_apply, aU]
      · simp [unipotentSL, splitTorusSL, Matrix.mul_apply, aU, ha_zero]
      · simpa [unipotentSL, splitTorusSL, Matrix.mul_apply, aU] using hc_zero
      · simpa [unipotentSL, splitTorusSL, Matrix.mul_apply, aU] using hd_inv
    have hfactor_q := congrArg qSL hfactor
    change qSL A ∈ U ⊔ T
    have hfactor_q' :
        qSL A = unipotent (A 0 1 * A 0 0) * splitTorus aU := by
      simpa [unipotent, splitTorus] using hfactor_q
    rw [hfactor_q']
    exact (U ⊔ T).mul_mem
      ((show U ≤ U ⊔ T from le_sup_left)
        ⟨Multiplicative.ofAdd (A 0 1 * A 0 0), rfl⟩)
      ((show T ≤ U ⊔ T from le_sup_right) ⟨aU, rfl⟩)
  exact ⟨U, T, hUcard, hU_isPGroup, hU_commutative, hT_cyclic,
    hTcard, hTcard_dvd, hT_le_normalizer, hT_fixedPointFree,
    hB_conjugate_torus, hnormalizer_le, unipotent, splitTorus,
    h_unipotent_injective, rfl, rfl, hsplit_conj,
    fun _ => rfl, fun _ => rfl⟩

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The normalizer quotient in Huppert II.8.21 embeds in the cyclic
split-torus quotient of a standard Borel subgroup. -/
private theorem h821_borel_quotient_data
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (P : Sylow p H) (hP_ne_bot : (P : Subgroup H) ≠ ⊥)
    (N : Subgroup H) (hN : N = Subgroup.normalizer (P : Set H))
    (PN : Subgroup N) [PN.Normal]
    (hPN : PN = (P : Subgroup H).subgroupOf N) :
    IsCyclic (N ⧸ PN) ∧
      Nat.card (N ⧸ PN) ∣
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      (∀ n : N, n ∉ PN → ∀ x : (P : Subgroup H), x ≠ 1 →
        (n : H) * (x : H) * (n : H)⁻¹ ≠ (x : H)) ∧
      ∃ U T : Subgroup (PSL2MatrixGroup F),
        ∃ conjH : H →* PSL2MatrixGroup F,
          Function.Injective conjH ∧
          IsMulCommutative U ∧
          IsCyclic T ∧
          Nat.card T =
            (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∧
          (∀ t : PSL2MatrixGroup F, t ∈ T →
            ∀ x : PSL2MatrixGroup F, x ∈ U →
              t * x * t⁻¹ = x → t = 1 ∨ x = 1) ∧
          (P : Subgroup H).map conjH ≤ U ∧
          U ⊔ T ≤ Subgroup.normalizer
            (U : Set (PSL2MatrixGroup F)) ∧
          (∀ x : PSL2MatrixGroup F, x ∈ U ⊔ T → x ∉ U →
            ∃ u : PSL2MatrixGroup F, u ∈ U ∧
              x ∈ T.map (MulAut.conj u).toMonoidHom) ∧
          (∀ n : N, conjH (n : H) ∈ U ⊔ T) ∧
          (∀ n : N, conjH (n : H) ∈ U ↔ n ∈ PN) ∧
          ∃ unipotent : AddChar F (PSL2MatrixGroup F),
            ∃ splitTorus : Fˣ →* PSL2MatrixGroup F,
              Function.Injective unipotent ∧
              U = unipotent.toMonoidHom.range ∧
              T = splitTorus.range ∧
              (∀ a : Fˣ, ∀ x : F,
                splitTorus a * unipotent x * (splitTorus a)⁻¹ =
                  unipotent ((a : F) ^ 2 * x)) ∧
              (∀ x : F, unipotent x =
                QuotientGroup.mk'
                  (Subgroup.center
                    (Matrix.SpecialLinearGroup (Fin 2) F))
                  (⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩ :
                    Matrix.SpecialLinearGroup (Fin 2) F)) ∧
              ∀ a : Fˣ, splitTorus a =
                QuotientGroup.mk'
                  (Subgroup.center
                    (Matrix.SpecialLinearGroup (Fin 2) F))
                  (⟨!![(a : F), 0; 0, (a⁻¹ : F)],
                      by simp [Matrix.det_fin_two]⟩ :
                    Matrix.SpecialLinearGroup (Fin 2) F) := by
  classical
  obtain ⟨U, T, hUcard, hU_isPGroup, hU_commutative,
      hT_cyclic, hTcard, hTcard_dvd, hT_le_normalizer,
      hT_fixedPointFree, hB_conjugate_torus, hnormalizer_le,
      unipotent, splitTorus, h_unipotent_injective,
      hU_range, hT_range, hsplit_conj, hunipotent_matrix,
      hsplitTorus_matrix⟩ :=
    h821_standard_borel_data hFcard
  obtain ⟨Q0, hU_le_Q0⟩ := hU_isPGroup.exists_le_sylow
  have hQ0card : Nat.card (Q0 : Subgroup (PSL2MatrixGroup F)) = Nat.card F := by
    rcases huppert_II_8_2_a_sylow_equiv_additive hFcard Q0 with ⟨eQ⟩
    exact (Nat.card_congr eQ.toEquiv).symm
  have hU_eq_Q0 : U = (Q0 : Subgroup (PSL2MatrixGroup F)) :=
    Subgroup.eq_of_le_of_card_ge hU_le_Q0 (by rw [hQ0card, hUcard])
  obtain ⟨Q, hQcomap⟩ := P.exists_comap_subtype_eq
  have hPmap_le_Q : (P : Subgroup H).map H.subtype ≤
      (Q : Subgroup (PSL2MatrixGroup F)) := by
    rw [Subgroup.map_le_iff_le_comap, hQcomap]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
    (PSL2MatrixGroup F) Q Q0
  let Pambient : Subgroup (PSL2MatrixGroup F) :=
    (P : Subgroup H).map H.subtype
  let Pconj : Subgroup (PSL2MatrixGroup F) :=
    Pambient.map (MulAut.conj g).toMonoidHom
  have hQconj_eq :
      (Q : Subgroup (PSL2MatrixGroup F)).map
          (MulAut.conj g).toMonoidHom = U := by
    have hg' := congrArg
      (fun S : Sylow p (PSL2MatrixGroup F) =>
        (S : Subgroup (PSL2MatrixGroup F))) hg
    rw [hU_eq_Q0]
    simpa using hg'
  have hPconj_le_U : Pconj ≤ U := by
    rw [← hQconj_eq]
    exact Subgroup.map_mono hPmap_le_Q
  have hPambient_ne_bot : Pambient ≠ ⊥ := by
    intro hbot
    apply hP_ne_bot
    exact (Subgroup.map_eq_bot_iff_of_injective
      (P : Subgroup H) H.subtype_injective).mp hbot
  have hPconj_ne_bot : Pconj ≠ ⊥ := by
    intro hbot
    apply hPambient_ne_bot
    exact (Subgroup.map_eq_bot_iff_of_injective Pambient
      (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective).mp hbot
  let B : Subgroup (PSL2MatrixGroup F) := U ⊔ T
  have hPconj_normalizer_le_B :
      Subgroup.normalizer (Pconj : Set (PSL2MatrixGroup F)) ≤ B := by
    simpa [B] using hnormalizer_le Pconj hPconj_le_U hPconj_ne_bot
  have h_normalizer_conj_to_B (n : N) :
      (MulAut.conj g) (H.subtype n) ∈ B := by
    have hn_normalizer : (n : H) ∈
        Subgroup.normalizer (P : Set H) := by
      rw [← hN]
      exact n.property
    have hn_ambient :
        H.subtype n ∈ Subgroup.normalizer
          (Pambient : Set (PSL2MatrixGroup F)) := by
      apply Subgroup.le_normalizer_map H.subtype
      exact ⟨n, hn_normalizer, rfl⟩
    have hn_conj :
        (MulAut.conj g) (H.subtype n) ∈
          Subgroup.normalizer (Pconj : Set (PSL2MatrixGroup F)) := by
      change (MulAut.conj g) (H.subtype n) ∈
        Subgroup.normalizer
          ((Pambient.map (MulAut.conj g).toMonoidHom :
            Subgroup (PSL2MatrixGroup F)) : Set (PSL2MatrixGroup F))
      apply Subgroup.le_normalizer_map (MulAut.conj g).toMonoidHom
      exact ⟨H.subtype n, hn_ambient, rfl⟩
    exact hPconj_normalizer_le_B hn_conj
  let conjH : H →* PSL2MatrixGroup F :=
    (MulAut.conj g).toMonoidHom.comp H.subtype
  have hconjH_injective : Function.Injective conjH :=
    (MulAut.conj g).injective.comp H.subtype_injective
  let KH : Subgroup H := U.comap conjH
  have hP_le_KH : (P : Subgroup H) ≤ KH := by
    intro x hx
    change conjH x ∈ U
    apply hPconj_le_U
    change conjH x ∈
      Pambient.map (MulAut.conj g).toMonoidHom
    refine ⟨H.subtype x, ?_, rfl⟩
    exact ⟨x, hx, rfl⟩
  have hKH_isPGroup : IsPGroup p KH :=
    hU_isPGroup.comap_of_injective conjH hconjH_injective
  have hKH_eq_P : KH = (P : Subgroup H) :=
    P.is_maximal' hKH_isPGroup hP_le_KH
  have hU_le_B : U ≤ B := by
    exact le_sup_left
  have hT_le_B : T ≤ B := by
    exact le_sup_right
  let UB : Subgroup B := U.subgroupOf B
  let TB : Subgroup B := T.subgroupOf B
  letI hUB_normal : UB.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (sup_le Subgroup.le_normalizer hT_le_normalizer)
  have hUB_sup_TB : UB ⊔ TB = ⊤ := by
    have hsup := Subgroup.subgroupOf_sup hU_le_B hT_le_B
    simpa [B, UB, TB] using hsup.symm
  have hTB_cyclic : IsCyclic TB := by
    let eTB : TB ≃* T := Subgroup.subgroupOfEquivOfLe hT_le_B
    letI : IsCyclic T := hT_cyclic
    exact isCyclic_of_surjective eTB.symm eTB.symm.surjective
  let borelQuotient : B →* B ⧸ UB := QuotientGroup.mk' UB
  have hmap_UB_bot : Subgroup.map borelQuotient UB = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    exact le_of_eq (QuotientGroup.ker_mk' UB).symm
  have hmap_TB_top : Subgroup.map borelQuotient TB = ⊤ := by
    calc
      Subgroup.map borelQuotient TB =
          ⊥ ⊔ Subgroup.map borelQuotient TB := by simp
      _ = Subgroup.map borelQuotient (UB ⊔ TB) := by
        rw [Subgroup.map_sup, hmap_UB_bot]
      _ = Subgroup.map borelQuotient ⊤ := by rw [hUB_sup_TB]
      _ = ⊤ := Subgroup.map_top_of_surjective borelQuotient
        (QuotientGroup.mk'_surjective UB)
  let torusToBorelQuotient : TB →* B ⧸ UB :=
    borelQuotient.comp TB.subtype
  have htorusToBorelQuotient_surjective :
      Function.Surjective torusToBorelQuotient := by
    intro y
    have hy : y ∈ Subgroup.map borelQuotient TB := by
      rw [hmap_TB_top]
      trivial
    rcases hy with ⟨b, hb, hby⟩
    exact ⟨⟨b, hb⟩, hby⟩
  have hB_quotient_cyclic : IsCyclic (B ⧸ UB) := by
    letI : IsCyclic TB := hTB_cyclic
    exact isCyclic_of_surjective torusToBorelQuotient
      htorusToBorelQuotient_surjective
  have hB_quotient_card_dvd : Nat.card (B ⧸ UB) ∣ Nat.card T := by
    have hdvd := Subgroup.card_dvd_of_surjective
      torusToBorelQuotient htorusToBorelQuotient_surjective
    have hTBcard : Nat.card TB = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT_le_B).toEquiv
    rwa [hTBcard] at hdvd
  let normToB : N →* B :=
    (conjH.comp N.subtype).codRestrict B h_normalizer_conj_to_B
  have hnormToB_injective : Function.Injective normToB := by
    intro x y hxy
    apply Subtype.ext
    apply hconjH_injective
    exact congrArg Subtype.val hxy
  let normToBQuotient : N →* B ⧸ UB :=
    borelQuotient.comp normToB
  have hborelQuotient_ker : borelQuotient.ker = UB :=
    QuotientGroup.ker_mk' UB
  have hnormToBQuotient_ker : normToBQuotient.ker = PN := by
    ext n
    constructor
    · intro hn
      have hn' : normToB n ∈ borelQuotient.ker := hn
      rw [hborelQuotient_ker] at hn'
      have hnU : conjH (n : H) ∈ U := hn'
      have hnKH : (n : H) ∈ KH := hnU
      rw [hKH_eq_P] at hnKH
      rw [hPN]
      exact hnKH
    · intro hn
      have hnP : (n : H) ∈ (P : Subgroup H) := by
        rw [hPN] at hn
        exact hn
      have hnU : conjH (n : H) ∈ U := by
        change (n : H) ∈ KH
        rw [hKH_eq_P]
        exact hnP
      have hn' : normToB n ∈ borelQuotient.ker := by
        rw [hborelQuotient_ker]
        exact hnU
      exact hn'
  let eNormalizerQuotient : N ⧸ PN ≃* normToBQuotient.range :=
    (QuotientGroup.quotientMulEquivOfEq hnormToBQuotient_ker.symm).trans
      (QuotientGroup.quotientKerEquivRange normToBQuotient)
  have hNormalizer_quotient_cyclic : IsCyclic (N ⧸ PN) := by
    have hRangeCyclic : IsCyclic normToBQuotient.range := by
      letI : IsCyclic (B ⧸ UB) := hB_quotient_cyclic
      exact Subgroup.isCyclic normToBQuotient.range
    letI : IsCyclic normToBQuotient.range := hRangeCyclic
    exact isCyclic_of_surjective eNormalizerQuotient.symm
      eNormalizerQuotient.symm.surjective
  have hNormalizer_quotient_card_dvd :
      Nat.card (N ⧸ PN) ∣
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 := by
    have hRange_dvd :
        Nat.card normToBQuotient.range ∣ Nat.card (B ⧸ UB) :=
      normToBQuotient.range.card_subgroup_dvd_card
    have hdvd := dvd_trans hRange_dvd hB_quotient_card_dvd
    have hquotient_eq_range :
        Nat.card (N ⧸ PN) = Nat.card normToBQuotient.range :=
      Nat.card_congr eNormalizerQuotient.toEquiv
    rw [hquotient_eq_range]
    rw [← hTcard]
    exact hdvd
  have hP_map_conjH_le_U : (P : Subgroup H).map conjH ≤ U := by
    rw [Subgroup.map_le_iff_le_comap]
    exact hP_le_KH
  have hB_le_normalizer :
      U ⊔ T ≤ Subgroup.normalizer
        (U : Set (PSL2MatrixGroup F)) :=
    sup_le Subgroup.le_normalizer hT_le_normalizer
  have hconjH_mem_U_iff (n : N) :
      conjH (n : H) ∈ U ↔ n ∈ PN := by
    constructor
    · intro hnU
      have hnKH : (n : H) ∈ KH := hnU
      rw [hKH_eq_P] at hnKH
      rw [hPN]
      exact hnKH
    · intro hn
      have hnP : (n : H) ∈ (P : Subgroup H) := by
        rw [hPN] at hn
        exact hn
      change (n : H) ∈ KH
      rw [hKH_eq_P]
      exact hnP
  have hNormalizer_fixedPointFree :
      ∀ n : N, n ∉ PN → ∀ x : (P : Subgroup H), x ≠ 1 →
        (n : H) * (x : H) * (n : H)⁻¹ ≠ (x : H) := by
    intro n hnPN x hx hfix
    have hn_not_U : conjH (n : H) ∉ U := by
      intro hnU
      exact hnPN ((hconjH_mem_U_iff n).mp hnU)
    obtain ⟨u, huU, hntorus⟩ :=
      hB_conjugate_torus (conjH (n : H))
        (h_normalizer_conj_to_B n) hn_not_U
    rcases hntorus with ⟨t, htT, ht⟩
    change u * t * u⁻¹ = conjH (n : H) at ht
    have hxU : conjH (x : H) ∈ U :=
      hP_map_conjH_le_U (Subgroup.mem_map_of_mem conjH x.property)
    let x' : PSL2MatrixGroup F := u⁻¹ * conjH (x : H) * u
    have hx'U : x' ∈ U := by
      exact U.mul_mem (U.mul_mem (U.inv_mem huU) hxU) huU
    have hx'ne : x' ≠ 1 := by
      intro hx'one
      apply hx
      apply Subtype.ext
      apply hconjH_injective
      have hconjx : conjH (x : H) = 1 := by
        calc
          conjH (x : H) = u * x' * u⁻¹ := by
            dsimp [x']
            group
          _ = 1 := by rw [hx'one]; simp
      simpa using hconjx
    have hfixMap :
        conjH (n : H) * conjH (x : H) * (conjH (n : H))⁻¹ =
          conjH (x : H) := by
      simpa using congrArg conjH hfix
    have hfix' : t * x' * t⁻¹ = x' := by
      dsimp [x']
      calc
        t * (u⁻¹ * conjH (x : H) * u) * t⁻¹ =
            u⁻¹ * ((u * t * u⁻¹) * conjH (x : H) *
              (u * t * u⁻¹)⁻¹) * u := by group
        _ = u⁻¹ * (conjH (n : H) * conjH (x : H) *
              (conjH (n : H))⁻¹) * u := by rw [ht]
        _ = u⁻¹ * conjH (x : H) * u := by rw [hfixMap]
    have htne : t ≠ 1 := by
      intro htone
      apply hn_not_U
      rw [← ht, htone]
      simpa using huU
    rcases hT_fixedPointFree t htT x' hx'U hfix' with htone | hx'one
    · exact htne htone
    · exact hx'ne hx'one
  exact ⟨hNormalizer_quotient_cyclic, hNormalizer_quotient_card_dvd,
    hNormalizer_fixedPointFree, U, T, conjH, hconjH_injective,
    hU_commutative, hT_cyclic,
    hTcard, hT_fixedPointFree, hP_map_conjH_le_U, hB_le_normalizer,
    hB_conjugate_torus, h_normalizer_conj_to_B,
    hconjH_mem_U_iff, unipotent, splitTorus,
    h_unipotent_injective, hU_range, hT_range, hsplit_conj,
    hunipotent_matrix, hsplitTorus_matrix⟩


private theorem h821_complement_maximal_of_overgroups_coprime
    {H : Type u} [Group H] [Finite H]
    (N : Subgroup H) (PN C : Subgroup N) [PN.Normal]
    (hcomp : PN.IsComplement' C)
    (hovergroups :
      let W : Subgroup H := C.map N.subtype
      ∀ V : Subgroup H, IsCyclic V → W ≤ V → W ≠ ⊥ →
        V ≤ N ∧ Nat.Coprime (Nat.card PN) (Nat.card V)) :
    let W : Subgroup H := C.map N.subtype
    W = ⊥ ∨
      (1 < Nat.card W ∧
        ∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) := by
  classical
  let W : Subgroup H := C.map N.subtype
  by_cases hWbot : W = ⊥
  · exact Or.inl hWbot
  · right
    refine ⟨(Subgroup.one_lt_card_iff_ne_bot W).2 hWbot, ?_⟩
    intro V hVcyclic hWV
    obtain ⟨hV_le_N, hcoprime⟩ :=
      hovergroups V hVcyclic hWV hWbot
    let VN : Subgroup N := V.subgroupOf N
    have hC_le_VN : C ≤ VN := by
      intro c hc
      change (c : H) ∈ V
      apply hWV
      exact Subgroup.mem_map_of_mem N.subtype hc
    have hVNcard : Nat.card VN = Nat.card V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV_le_N).toEquiv
    have hdisjoint : Disjoint PN VN := by
      rw [disjoint_iff, eq_bot_iff]
      intro x hx
      have hx_order_PN : orderOf x ∣ Nat.card PN := by
        simpa [Subgroup.orderOf_coe] using
          (orderOf_dvd_natCard (⟨x, hx.1⟩ : PN))
      have hx_order_VN : orderOf x ∣ Nat.card VN := by
        simpa [Subgroup.orderOf_coe] using
          (orderOf_dvd_natCard (⟨x, hx.2⟩ : VN))
      have hcoprime' : Nat.Coprime (Nat.card PN) (Nat.card VN) := by
        rw [hVNcard]
        exact hcoprime
      apply orderOf_eq_one_iff.mp
      apply Nat.eq_one_of_dvd_coprimes hcoprime'
      · exact hx_order_PN
      · exact hx_order_VN
    have hsup : PN ⊔ VN = ⊤ := by
      apply top_unique
      rw [← hcomp.sup_eq_top]
      exact sup_le_sup_left hC_le_VN PN
    have hmul : (PN : Set N) * (VN : Set N) = Set.univ := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left PN VN
        Subgroup.le_normalizer_of_normal, hsup]
      rfl
    have hcompV : PN.IsComplement' VN :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisjoint hmul
    have hcardCV : Nat.card C = Nat.card VN := by
      calc
        Nat.card C = PN.index := hcomp.symm.index_eq_card.symm
        _ = Nat.card VN := hcompV.symm.index_eq_card
    have hCV : C = VN :=
      Subgroup.eq_of_le_of_card_ge hC_le_VN (by rw [hcardCV])
    calc
      V = VN.map N.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hV_le_N).symm
      _ = C.map N.subtype := by rw [← hCV]
      _ = W := rfl

private theorem h821_cyclic_overgroup_partition_component
    {G H : Type u} [Group G] [Group H] [Finite H]
    (Family : Subgroup G → Prop)
    (hpartition : ∀ x : G, x ≠ 1 →
      ∃! T : Subgroup G, x ∈ T ∧ Family T)
    (embed : H →* G) (hembed : Function.Injective embed)
    (W : Subgroup H) (A : Subgroup G) (qminus : ℕ)
    (hseed : ∃ x : H, x ∈ W ∧ x ≠ 1 ∧ embed x ∈ A)
    (hAfamily : Family A) (hAcard : Nat.card A ∣ qminus) :
    ∀ V : Subgroup H, IsCyclic V → W ≤ V →
      V.map embed ≤ A ∧ Nat.card V ∣ qminus := by
  intro V hVcyclic hWV
  obtain ⟨x, hxW, hx, hxA⟩ := hseed
  have hxembed : embed x ≠ 1 := by
    intro h
    apply hx
    exact hembed (h.trans (map_one embed).symm)
  have hVmap_cyclic : IsCyclic (V.map embed) := by
    exact (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective V embed hembed)).mp hVcyclic
  have hVmap_le : V.map embed ≤ A :=
    cyclic_le_unique_partition_family Family hpartition hxembed
      hxA hAfamily
      (Subgroup.mem_map_of_mem embed (hWV hxW)) hVmap_cyclic
  refine ⟨hVmap_le, ?_⟩
  have hmapcard : Nat.card (V.map embed) = Nat.card V :=
    Subgroup.card_map_of_injective hembed
  rw [← hmapcard]
  exact dvd_trans (Subgroup.card_dvd_of_le hVmap_le) hAcard


/-- An injective embedding into a commutative ambient `p`-subgroup reflects
normalization of that ambient subgroup back to a Sylow subgroup. -/
private theorem sylow_mem_normalizer_of_embed_mem_normalizer
    {H : Type u} {G : Type v} [Group H] [Finite H] [Group G]
    {p : ℕ} [Fact p.Prime]
    (embed : H →* G) (hembed : Function.Injective embed)
    (P : Sylow p H) (U B : Subgroup G)
    (hU_comm : IsMulCommutative U)
    (hP_le_U : (P : Subgroup H).map embed ≤ U)
    (hB_le : B ≤ Subgroup.normalizer (U : Set G))
    (y : H) (hyB : embed y ∈ B) :
    y ∈ Subgroup.normalizer ((P : Subgroup H) : Set H) := by
  letI : IsMulCommutative U := hU_comm
  let K : Subgroup H :=
    (P : Subgroup H).map (MulAut.conj y).toMonoidHom
  have hyN : embed y ∈ Subgroup.normalizer (U : Set G) := hB_le hyB
  have hK_map_le_U : K.map embed ≤ U := by
    intro z hz
    rcases hz with ⟨k, hkK, rfl⟩
    rcases hkK with ⟨x, hxP, rfl⟩
    have hxU : embed x ∈ U :=
      hP_le_U (Subgroup.mem_map_of_mem embed hxP)
    have hconjU : embed y * embed x * (embed y)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp hyN (embed x)).mp hxU
    simpa [MulAut.conj_apply] using hconjU
  have hK_p : IsPGroup p K :=
    P.isPGroup'.map (MulAut.conj y).toMonoidHom
  have hK_le_normalizer :
      K ≤ Subgroup.normalizer ((P : Subgroup H) : Set H) := by
    intro k hkK
    rw [← Subgroup.conjAct_pointwise_smul_iff]
    change (P : Subgroup H).map (MulAut.conj k).toMonoidHom =
      (P : Subgroup H)
    apply Subgroup.eq_of_le_of_card_ge
    · intro z hz
      rcases hz with ⟨x, hxP, rfl⟩
      have hkU : embed k ∈ U :=
        hK_map_le_U (Subgroup.mem_map_of_mem embed hkK)
      have hxU : embed x ∈ U :=
        hP_le_U (Subgroup.mem_map_of_mem embed hxP)
      have hcomm_embed : embed k * embed x = embed x * embed k := by
        exact congrArg Subtype.val
          (mul_comm (⟨embed k, hkU⟩ : U) (⟨embed x, hxU⟩ : U))
      have hcomm : k * x = x * k := hembed (by simpa using hcomm_embed)
      simpa [MulAut.conj_apply, hcomm] using hxP
    · rw [Subgroup.card_map_of_injective (MulAut.conj k).injective]
  have hsup_p : IsPGroup p ((P : Subgroup H) ⊔ K : Subgroup H) :=
    P.isPGroup'.to_sup_of_normal_left' hK_p hK_le_normalizer
  have hsup_eq : (P : Subgroup H) ⊔ K = (P : Subgroup H) :=
    P.is_maximal' hsup_p le_sup_left
  have hK_le_P : K ≤ (P : Subgroup H) := by
    rw [← hsup_eq]
    exact le_sup_right
  have hK_card : Nat.card K = Nat.card (P : Subgroup H) := by
    exact Subgroup.card_map_of_injective (MulAut.conj y).injective
  have hK_eq : K = (P : Subgroup H) :=
    Subgroup.eq_of_le_of_card_ge hK_le_P (by rw [hK_card])
  rw [← Subgroup.conjAct_pointwise_smul_iff]
  change K = (P : Subgroup H)
  exact hK_eq


/-- A nonidentity element of a cyclic split torus can only lie in the split
component of the II.8.5 partition. Exact split order then identifies that
component with the original torus. -/
private theorem h821_split_partition_seed
    {G : Type u} [Group G] [Finite G]
    (P U S T₀ B : Subgroup G)
    (hpartition : ∀ x : G, x ≠ 1 →
      ∃! A : Subgroup G, x ∈ A ∧
        ((∃ g, A = P.map (MulAut.conj g).toMonoidHom) ∨
          (∃ g, A = U.map (MulAut.conj g).toMonoidHom) ∨
          (∃ g, A = S.map (MulAut.conj g).toMonoidHom)))
    (hT₀cyclic : IsCyclic T₀) (hT₀B : T₀ ≤ B)
    (hP_T₀_coprime : Nat.Coprime (Nat.card P) (Nat.card T₀))
    (hT₀_U_card : Nat.card T₀ = Nat.card U)
    (hT₀_S_coprime : Nat.Coprime (Nat.card T₀) (Nat.card S))
    {x : G} (hx : x ≠ 1) (hxT₀ : x ∈ T₀) :
    ∃ A : Subgroup G, x ∈ A ∧
      ((∃ g, A = P.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, A = U.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, A = S.map (MulAut.conj g).toMonoidHom)) ∧
      A ≤ B ∧ Nat.card A = Nat.card T₀ := by
  let Family : Subgroup G → Prop := fun A =>
    (∃ g, A = P.map (MulAut.conj g).toMonoidHom) ∨
      (∃ g, A = U.map (MulAut.conj g).toMonoidHom) ∨
      (∃ g, A = S.map (MulAut.conj g).toMonoidHom)
  have hpartition' : ∀ y : G, y ≠ 1 →
      ∃! A : Subgroup G, y ∈ A ∧ Family A := by
    simpa [Family] using hpartition
  obtain ⟨A, hxA, hAfamily⟩ := (hpartition' x hx).exists
  have hT₀_le_A : T₀ ≤ A :=
    cyclic_le_unique_partition_family Family hpartition'
      hx hxA hAfamily hxT₀ hT₀cyclic
  rcases hAfamily with ⟨g, hAg⟩ | ⟨g, hAg⟩ | ⟨g, hAg⟩
  · exfalso
    have hcop : Nat.Coprime (Nat.card T₀) (Nat.card A) := by
      rw [hAg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hP_T₀_coprime.symm
    exact hx (hmem_eq_one_of_coprime_card T₀ A hcop
      hxT₀ (hT₀_le_A hxT₀))
  · have hcard : Nat.card T₀ = Nat.card A := by
      rw [hAg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hT₀_U_card
    have hT₀_eq_A : T₀ = A :=
      Subgroup.eq_of_le_of_card_ge hT₀_le_A (by rw [hcard])
    refine ⟨A, hxA, Or.inr (Or.inl ⟨g, hAg⟩), ?_, hcard.symm⟩
    rw [← hT₀_eq_A]
    exact hT₀B
  · exfalso
    have hcop : Nat.Coprime (Nat.card T₀) (Nat.card A) := by
      rw [hAg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hT₀_S_coprime
    exact hx (hmem_eq_one_of_coprime_card T₀ A hcop
      hxT₀ (hT₀_le_A hxT₀))


set_option maxHeartbeats 4000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The Sylow-normalizer part of Huppert II.8.22, with the nontrivial
boundary from II.8.21 made explicit. -/
public theorem huppert_II_8_22_sylow_normalizer_shape
    {F : Type u} [Field F] [Finite F] {p f m r : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (P : Sylow p H) (hPcard : Nat.card P = p ^ m)
    (Z : Fin r → Subgroup H)
    (hcyclic : ∀ i, IsCyclic (Z i))
    (hcoprime : ∀ i, Nat.Coprime p (Nat.card (Z i)))
    (hmaximal : ∀ i (W : Subgroup H),
      IsCyclic W → Z i ≤ W → W = Z i)
    (hrepresentative : ∀ W : Subgroup H,
      IsCyclic W → 1 < Nat.card W →
      Nat.Coprime p (Nat.card W) →
      (∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) →
      ∃ i g, W = (Z i).map (MulAut.conj g).toMonoidHom) :
    1 < p ^ m →
      (Nat.card (Subgroup.normalizer (P : Set H)) = p ^ m ∨
        ∃ i, Nat.card (Subgroup.normalizer (P : Set H)) =
          p ^ m * Nat.card (Z i)) := by
  classical
  intro hPcard_gt
  have hP_ne_bot : (P : Subgroup H) ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, hPcard]
    exact hPcard_gt
  let N : Subgroup H := Subgroup.normalizer (P : Set H)
  have hN : N = Subgroup.normalizer (P : Set H) := rfl
  have hP_le_N : (P : Subgroup H) ≤ N := Subgroup.le_normalizer
  let PN : Subgroup N := (P : Subgroup H).subgroupOf N
  letI : PN.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (by
      simpa [N] : N ≤ Subgroup.normalizer (P : Set H))
  obtain ⟨hquotient_cyclic, hquotient_card_dvd,
      _hNormalizer_fixedPointFree, U, T, embed, hembed, hU_comm, hT_cyclic, hTcard,
      _hT_fixedPointFree, hP_map_le_U, hB_le_normalizer, hB_conjugate_torus,
      hN_maps_B, hU_preimage, _hcoordinates⟩ :=
    h821_borel_quotient_data hFcard H P hP_ne_bot N hN PN rfl
  have hquotient_card_dvd_sub_one :
      Nat.card (N ⧸ PN) ∣ Nat.card F - 1 :=
    dvd_trans hquotient_card_dvd
      (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left (Nat.card F - 1) 2))
  let P₀ : Sylow p (PSL2MatrixGroup F) := default
  obtain ⟨U₈₅, S₈₅, hU₈₅_cyclic, hU₈₅_card,
      hS₈₅_cyclic, hS₈₅_card, hpartition⟩ :=
    huppert_II_8_5_a_psl2_partition hFcard P₀
  let Family : Subgroup (PSL2MatrixGroup F) → Prop := fun A =>
    (∃ g, A = (P₀ : Subgroup (PSL2MatrixGroup F)).map
      (MulAut.conj g).toMonoidHom) ∨
    (∃ g, A = U₈₅.map (MulAut.conj g).toMonoidHom) ∨
    (∃ g, A = S₈₅.map (MulAut.conj g).toMonoidHom)
  have hpartition' : ∀ x : PSL2MatrixGroup F, x ≠ 1 →
      ∃! A : Subgroup (PSL2MatrixGroup F), x ∈ A ∧ Family A := by
    simpa [Family] using hpartition
  have hP₀card :
      Nat.card (P₀ : Subgroup (PSL2MatrixGroup F)) = Nat.card F := by
    obtain ⟨eP₀⟩ := huppert_II_8_2_a_sylow_equiv_additive hFcard P₀
    exact (Nat.card_congr eP₀.toEquiv).symm
  have hP₀_T_coprime :
      Nat.Coprime
        (Nat.card (P₀ : Subgroup (PSL2MatrixGroup F)))
        (Nat.card T) := by
    rw [hP₀card, hTcard]
    exact hq_coprime_split_order (Nat.card F) Nat.card_pos
  have hT_U₈₅_card : Nat.card T = Nat.card U₈₅ := by
    rw [hTcard, hU₈₅_card]
  have hT_S₈₅_coprime : Nat.Coprime (Nat.card T) (Nat.card S₈₅) := by
    rw [hTcard, hS₈₅_card]
    exact hsplit_nonsplit_order_coprime
      (Nat.card F) (Finite.one_lt_card (α := F))
  have hTcard_dvd : Nat.card T ∣ Nat.card F - 1 := by
    rw [hTcard]
    exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left (Nat.card F - 1) 2)
  have hf_ne_zero : f ≠ 0 :=
    huppert_II_8_27_field_exponent_ne_zero hFcard
  have hp_dvd_cardF : p ∣ Nat.card F := by
    rw [hFcard]
    exact dvd_pow_self p hf_ne_zero
  have hp_not_dvd_cardF_sub_one : ¬ p ∣ Nat.card F - 1 := by
    intro hp_sub
    have hp_one : p ∣ 1 := by
      have h := Nat.dvd_sub hp_dvd_cardF hp_sub
      have hcard_pos : 0 < Nat.card F := Nat.card_pos
      have hsub : Nat.card F - (Nat.card F - 1) = 1 := by omega
      rwa [hsub] at h
    exact (Fact.out : p.Prime).not_dvd_one hp_one
  have hcop_p_cardF_sub_one : Nat.Coprime p (Nat.card F - 1) :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      hp_not_dvd_cardF_sub_one
  have hPNcard : Nat.card PN = p ^ m := by
    calc
      Nat.card PN = Nat.card P :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe hP_le_N).toEquiv
      _ = p ^ m := hPcard
  have hcomplement_maximal :
      ∀ C : Subgroup N, PN.IsComplement' C → IsCyclic C →
        let W : Subgroup H := C.map N.subtype
        W = ⊥ ∨
          (1 < Nat.card W ∧
            ∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) := by
    intro C hcomp hC_cyclic
    let W : Subgroup H := C.map N.subtype
    have hovergroups :
        ∀ V : Subgroup H, IsCyclic V → W ≤ V → W ≠ ⊥ →
          V ≤ N ∧ Nat.Coprime (Nat.card PN) (Nat.card V) := by
      intro V hV_cyclic hWV hW_ne_bot
      obtain ⟨w, hw_ne⟩ :=
        Subgroup.ne_bot_iff_exists_ne_one.mp hW_ne_bot
      rcases w.property with ⟨c, hcC, hcw⟩
      have hc_ne : (c : H) ≠ 1 := by
        intro hc_one
        apply hw_ne
        apply Subtype.ext
        exact hcw.symm.trans hc_one
      have hc_not_U : embed (c : H) ∉ U := by
        intro hcU
        have hcPN : c ∈ PN := (hU_preimage c).mp hcU
        have hc_one : c = 1 :=
          Subgroup.disjoint_def.mp hcomp.disjoint hcPN hcC
        apply hc_ne
        simpa using congrArg Subtype.val hc_one
      obtain ⟨u, huU, hcuT⟩ :=
        hB_conjugate_torus (embed (c : H)) (hN_maps_B c) hc_not_U
      let T₀ : Subgroup (PSL2MatrixGroup F) :=
        T.map (MulAut.conj u).toMonoidHom
      have hT₀_cyclic : IsCyclic T₀ := by
        exact (MulEquiv.isCyclic
          (Subgroup.equivMapOfInjective T
            (MulAut.conj u).toMonoidHom
            (MulAut.conj u).injective)).mp hT_cyclic
      have hT₀card : Nat.card T₀ = Nat.card T :=
        Subgroup.card_map_of_injective (MulAut.conj u).injective
      have hT₀_le_B : T₀ ≤ U ⊔ T := by
        rw [Subgroup.map_le_iff_le_comap]
        intro t htT
        change u * t * u⁻¹ ∈ U ⊔ T
        exact (U ⊔ T).mul_mem
          ((U ⊔ T).mul_mem
            ((show U ≤ U ⊔ T from le_sup_left) huU)
            ((show T ≤ U ⊔ T from le_sup_right) htT))
          ((U ⊔ T).inv_mem ((show U ≤ U ⊔ T from le_sup_left) huU))
      have hP₀_T₀_coprime :
          Nat.Coprime
            (Nat.card (P₀ : Subgroup (PSL2MatrixGroup F)))
            (Nat.card T₀) := by
        rw [hT₀card]
        exact hP₀_T_coprime
      have hT₀_U₈₅_card : Nat.card T₀ = Nat.card U₈₅ := by
        rw [hT₀card]
        exact hT_U₈₅_card
      have hT₀_S₈₅_coprime :
          Nat.Coprime (Nat.card T₀) (Nat.card S₈₅) := by
        rw [hT₀card]
        exact hT_S₈₅_coprime
      have hc_embed_ne : embed (c : H) ≠ 1 := by
        intro hc_one
        apply hc_ne
        exact hembed (hc_one.trans (map_one embed).symm)
      obtain ⟨A, hcA, hAfamily, hA_le_B, hAcard⟩ :=
        h821_split_partition_seed
          (P₀ : Subgroup (PSL2MatrixGroup F)) U₈₅ S₈₅ T₀
          (U ⊔ T) hpartition hT₀_cyclic hT₀_le_B
          hP₀_T₀_coprime hT₀_U₈₅_card hT₀_S₈₅_coprime
          hc_embed_ne hcuT
      have hAfamily' : Family A := by
        simpa [Family] using hAfamily
      have hAcard_dvd : Nat.card A ∣ Nat.card F - 1 := by
        rw [hAcard, hT₀card]
        exact hTcard_dvd
      have hseed :
          ∃ x : H, x ∈ W ∧ x ≠ 1 ∧ embed x ∈ A := by
        refine ⟨(c : H), ?_, hc_ne, hcA⟩
        exact Subgroup.mem_map_of_mem N.subtype hcC
      obtain ⟨hVmap_le_A, hVcard_dvd⟩ :=
        h821_cyclic_overgroup_partition_component
          Family hpartition' embed hembed W A (Nat.card F - 1)
          hseed hAfamily' hAcard_dvd V hV_cyclic hWV
      have hV_le_N : V ≤ N := by
        intro y hyV
        rw [hN]
        apply sylow_mem_normalizer_of_embed_mem_normalizer
          embed hembed P U (U ⊔ T) hU_comm hP_map_le_U
          hB_le_normalizer y
        exact hA_le_B
          (hVmap_le_A (Subgroup.mem_map_of_mem embed hyV))
      have hcoprime_V :
          Nat.Coprime (Nat.card PN) (Nat.card V) := by
        rw [hPNcard]
        exact Nat.Coprime.of_dvd_right hVcard_dvd
          (hcop_p_cardF_sub_one.pow_left m)
      exact ⟨hV_le_N, hcoprime_V⟩
    exact h821_complement_maximal_of_overgroups_coprime N PN C hcomp
      hovergroups
  obtain ⟨W, hW_cyclic, hW_coprime, hW_boundary, hnormalizer_card⟩ :=
    h821_schur_zassenhaus_core hFcard H P hPcard N hN hP_le_N
      PN rfl hquotient_cyclic hquotient_card_dvd_sub_one hcomplement_maximal
  rcases hW_boundary with hW_bot | ⟨hW_card, hW_maximal⟩
  · left
    rw [hnormalizer_card, hPcard, hW_bot, Subgroup.card_bot, mul_one]
  · obtain ⟨i, g, hWrep⟩ :=
      hrepresentative W hW_cyclic hW_card hW_coprime hW_maximal
    right
    refine ⟨i, ?_⟩
    rw [hnormalizer_card, hPcard, hWrep,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]

private theorem huppert_II_8_22_punctured_subgroup_card
    {H : Type*} [Group H] [Finite H] (A : Subgroup H) :
    Nat.card {x : A // (x : H) ≠ 1} = Nat.card A - 1 := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype {x : A // (x : H) ≠ 1} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simp

private theorem huppert_II_8_22_conjugacy_orbit_card
    {H : Type*} [Group H] [Finite H] (A : Subgroup H) :
    Nat.card {W : Subgroup H // ∃ g : H,
      W = A.map (MulAut.conj g).toMonoidHom} =
      (Subgroup.normalizer (A : Set H)).index := by
  classical
  letI : MulAction H (Subgroup H) := MulAction.compHom _ MulAut.conj
  have horbit :
      MulAction.orbit H A =
        {W : Subgroup H | ∃ g : H,
          W = A.map (MulAut.conj g).toMonoidHom} := by
    ext W
    constructor
    · intro hW
      rcases hW with ⟨g, rfl⟩
      exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, rfl⟩
  have hstab : MulAction.stabilizer H A =
      Subgroup.normalizer (A : Set H) := by
    ext g
    change g • A = A ↔ g ∈ Subgroup.normalizer (A : Set H)
    rw [eq_comm, SetLike.ext_iff,
      ← inv_mem_iff (G := H) (H := Subgroup.normalizer A),
      Subgroup.mem_normalizer_iff, inv_inv]
    exact
      forall_congr' fun h =>
        iff_congr Iff.rfl
          ⟨fun ⟨a, b, c⟩ => c ▸ by simpa [mul_assoc] using b,
            fun hh => ⟨(MulAut.conj g)⁻¹ h, hh,
              MulAut.apply_inv_self H (MulAut.conj g) h⟩⟩
  change Nat.card ↥{W : Subgroup H | ∃ g : H,
    W = A.map (MulAut.conj g).toMonoidHom} = _
  rw [← horbit, Nat.card_coe_set_eq,
    ← MulAction.index_stabilizer H A, hstab]

private theorem huppert_II_8_22_partition_count_of_unique_family
    {H : Type*} [Group H] [Finite H] {p m r : ℕ} [Fact p.Prime]
    (P : Sylow p H) (hPcard : Nat.card P = p ^ m)
    (Z : Fin r → Subgroup H)
    (hunique : ∀ x : H, x ≠ 1 →
      ∃! A : (Sylow p H) ⊕
          (Σ i : Fin r, {W : Subgroup H // ∃ g : H,
            W = (Z i).map (MulAut.conj g).toMonoidHom}),
        x ∈ match A with
          | Sum.inl Q => (Q : Subgroup H)
          | Sum.inr z => (z.2.1 : Subgroup H)) :
    Nat.card H =
      1 + (p ^ m - 1) *
          (Subgroup.normalizer (P : Set H)).index +
        ∑ i, (Nat.card (Z i) - 1) *
          (Subgroup.normalizer (Z i : Set H)).index := by
  classical
  let Family := (Sylow p H) ⊕
    (Σ i : Fin r, {W : Subgroup H // ∃ g : H,
      W = (Z i).map (MulAut.conj g).toMonoidHom})
  let carrier : Family → Subgroup H := fun A =>
    match A with
    | Sum.inl Q => (Q : Subgroup H)
    | Sum.inr z => (z.2.1 : Subgroup H)
  have hunique' : ∀ x : H, x ≠ 1 → ∃! A : Family, x ∈ carrier A := by
    intro x hx
    simpa [Family, carrier] using hunique x hx
  let Piece := Σ A : Family, {x : carrier A // (x : H) ≠ 1}
  let decode : Unit ⊕ Piece → H := fun z =>
    match z with
    | Sum.inl _ => 1
    | Sum.inr y => (y.2.1 : H)
  have hdecode_bij : Function.Bijective decode := by
    constructor
    · intro a b hab
      rcases a with _ | a
      · rcases b with _ | b
        · rfl
        · exfalso
          exact b.2.2 (by simpa [decode] using hab.symm)
      · rcases b with _ | b
        · exfalso
          exact a.2.2 (by simpa [decode] using hab)
        · rcases a with ⟨A, x⟩
          rcases b with ⟨B, y⟩
          have hxy : (x.1 : H) = (y.1 : H) := by
            simpa [decode] using hab
          have hAB : A = B := by
            apply (hunique' (x.1 : H) x.2).unique
            · exact x.1.2
            · rw [hxy]
              exact y.1.2
          subst B
          have hxy' : x = y := by
            apply Subtype.ext
            apply Subtype.ext
            exact hxy
          subst y
          rfl
    · intro x
      by_cases hx : x = 1
      · exact ⟨Sum.inl (), by simpa [decode, hx]⟩
      · obtain ⟨A, hxA⟩ := (hunique' x hx).exists
        refine ⟨Sum.inr ⟨A, ⟨⟨x, hxA⟩, hx⟩⟩, ?_⟩
        rfl
  let e : Unit ⊕ Piece ≃ H := Equiv.ofBijective decode hdecode_bij
  have hcard_decomp : Nat.card H = 1 + Nat.card Piece := by
    calc
      Nat.card H = Nat.card (Unit ⊕ Piece) := (Nat.card_congr e).symm
      _ = Nat.card Unit + Nat.card Piece := Nat.card_sum
      _ = 1 + Nat.card Piece := by rw [Nat.card_unique]
  have hSylow_card (Q : Sylow p H) : Nat.card Q = p ^ m := by
    calc
      Nat.card Q = Nat.card P := Nat.card_congr (Sylow.equiv Q P).toEquiv
      _ = p ^ m := hPcard
  have hConj_card (i : Fin r) :
      Nat.card {W : Subgroup H // ∃ g : H,
        W = (Z i).map (MulAut.conj g).toMonoidHom} =
        (Subgroup.normalizer (Z i : Set H)).index :=
    huppert_II_8_22_conjugacy_orbit_card (Z i)
  have hConj_subgroup_card (i : Fin r)
      (W : {W : Subgroup H // ∃ g : H,
        W = (Z i).map (MulAut.conj g).toMonoidHom}) :
      Nat.card W.1 = Nat.card (Z i) := by
    rcases W.2 with ⟨g, hg⟩
    rw [hg]
    exact Nat.card_congr ((MulAut.conj g).subgroupMap (Z i)).toEquiv.symm
  let PPiece := Σ Q : Sylow p H,
    {x : (Q : Subgroup H) // (x : H) ≠ 1}
  let ZIndex := Σ i : Fin r, {W : Subgroup H // ∃ g : H,
    W = (Z i).map (MulAut.conj g).toMonoidHom}
  let ZPiece := Σ z : ZIndex,
    {x : (z.2.1 : Subgroup H) // (x : H) ≠ 1}
  have hPpiece_card :
      Nat.card PPiece = Nat.card (Sylow p H) * (p ^ m - 1) := by
    letI : Fintype (Sylow p H) := Fintype.ofFinite (Sylow p H)
    letI (Q : Sylow p H) :
        Fintype {x : (Q : Subgroup H) // (x : H) ≠ 1} :=
      Fintype.ofFinite _
    change Nat.card (Σ Q : Sylow p H,
      {x : (Q : Subgroup H) // (x : H) ≠ 1}) = _
    rw [Nat.card_sigma]
    simp_rw [huppert_II_8_22_punctured_subgroup_card, hSylow_card]
    simp
  have hZpiece_card :
      Nat.card ZPiece =
        ∑ i, Nat.card {W : Subgroup H // ∃ g : H,
            W = (Z i).map (MulAut.conj g).toMonoidHom} *
          (Nat.card (Z i) - 1) := by
    letI (i : Fin r) :
        Fintype {W : Subgroup H // ∃ g : H,
          W = (Z i).map (MulAut.conj g).toMonoidHom} :=
      Fintype.ofFinite _
    letI : Fintype ZIndex := inferInstance
    letI (z : ZIndex) :
        Fintype {x : (z.2.1 : Subgroup H) // (x : H) ≠ 1} :=
      Fintype.ofFinite _
    change Nat.card (Σ z :
      (Σ i : Fin r, {W : Subgroup H // ∃ g : H,
        W = (Z i).map (MulAut.conj g).toMonoidHom}),
      {x : (z.2.1 : Subgroup H) // (x : H) ≠ 1}) = _
    rw [Nat.card_sigma]
    change (∑ z :
      (Σ i : Fin r, {W : Subgroup H // ∃ g : H,
        W = (Z i).map (MulAut.conj g).toMonoidHom}),
      Nat.card {x : (z.2.1 : Subgroup H) // (x : H) ≠ 1}) = _
    rw [Fintype.sum_sigma]
    simp_rw [huppert_II_8_22_punctured_subgroup_card,
      hConj_subgroup_card]
    simp
    apply Finset.sum_congr rfl
    intro i hi
    letI : Fintype {W : Subgroup H // ∃ g : H,
        W = (Z i).map (MulAut.conj g)} :=
      Fintype.ofFinite _
    apply congrArg (fun n => n * (Nat.card (Z i) - 1))
    exact Nat.card_eq_fintype_card.symm
  have hPiece_card :
      Nat.card Piece =
        Nat.card (Sylow p H) * (p ^ m - 1) +
          ∑ i, Nat.card {W : Subgroup H // ∃ g : H,
              W = (Z i).map (MulAut.conj g).toMonoidHom} *
            (Nat.card (Z i) - 1) := by
    have hsplit : Nat.card Piece = Nat.card PPiece + Nat.card ZPiece := by
      let esplit := Equiv.sumSigmaDistrib
        (fun A : Family => {x : carrier A // (x : H) ≠ 1})
      calc
        Nat.card Piece = Nat.card (PPiece ⊕ ZPiece) := by
          simpa [Piece, PPiece, ZPiece, ZIndex, Family, carrier] using
            Nat.card_congr esplit
        _ = Nat.card PPiece + Nat.card ZPiece := Nat.card_sum
    rw [hsplit, hPpiece_card, hZpiece_card]
  calc
    Nat.card H = 1 + Nat.card Piece := hcard_decomp
    _ = 1 +
        (Nat.card (Sylow p H) * (p ^ m - 1) +
          ∑ i, Nat.card {W : Subgroup H // ∃ g : H,
              W = (Z i).map (MulAut.conj g).toMonoidHom} *
            (Nat.card (Z i) - 1)) := by rw [hPiece_card]
    _ = 1 + (p ^ m - 1) *
          (Subgroup.normalizer (P : Set H)).index +
        ∑ i, (Nat.card (Z i) - 1) *
          (Subgroup.normalizer (Z i : Set H)).index := by
      rw [P.card_eq_index_normalizer]
      simp_rw [hConj_card]
      ac_rfl

/-- The subgroup form of the unique partition used in Huppert II.8.22. -/
public theorem huppert_II_8_22_unique_family
    {F : Type u} [Field F] [Finite F] {p f r : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (Z : Fin r → Subgroup H)
    (hcyclic : ∀ i, IsCyclic (Z i))
    (hnontrivial : ∀ i, 1 < Nat.card (Z i))
    (hcoprime : ∀ i, Nat.Coprime p (Nat.card (Z i)))
    (hmaximal : ∀ i (W : Subgroup H),
      IsCyclic W → Z i ≤ W → W = Z i)
    (hrepresentative : ∀ W : Subgroup H,
      IsCyclic W → 1 < Nat.card W →
      Nat.Coprime p (Nat.card W) →
      (∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) →
      ∃ i g, W = (Z i).map (MulAut.conj g).toMonoidHom)
    (hdistinct : ∀ i j g,
      (Z i).map (MulAut.conj g).toMonoidHom = Z j → i = j) :
    ∀ x : H, x ≠ 1 →
      ∃! A : (Sylow p H) ⊕
          (Σ i : Fin r, {W : Subgroup H // ∃ g : H,
            W = (Z i).map (MulAut.conj g).toMonoidHom}),
        x ∈ match A with
          | Sum.inl Q => (Q : Subgroup H)
          | Sum.inr z => (z.2.1 : Subgroup H) := by
  classical
  letI : MulAction H (Subgroup H) := MulAction.compHom _ MulAut.conj
  let P0 : Sylow p (PSL2MatrixGroup F) := default
  obtain ⟨U, S, hUcyclic, hUcard, hScyclic, hScard, hpartition⟩ :=
    huppert_II_8_5_a_psl2_partition hFcard P0
  have hmap_cyclic (A : Subgroup (PSL2MatrixGroup F))
      (hA : IsCyclic A) (g : PSL2MatrixGroup F) :
      IsCyclic (A.map (MulAut.conj g).toMonoidHom) := by
    letI : IsCyclic A := hA
    let e := (MulAut.conj g).subgroupMap A
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  have hcyclic_le_family
      {x : PSL2MatrixGroup F} (hx : x ≠ 1)
      {T V : Subgroup (PSL2MatrixGroup F)}
      (hxT : x ∈ T)
      (hTfamily :
        (∃ g, T = (P0 : Subgroup (PSL2MatrixGroup F)).map
          (MulAut.conj g).toMonoidHom) ∨
        (∃ g, T = U.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, T = S.map (MulAut.conj g).toMonoidHom))
      (hxV : x ∈ V) (hVcyclic : IsCyclic V) : V ≤ T := by
    letI : IsCyclic V := hVcyclic
    rcases IsCyclic.exists_zpow_surjective (G := V) with ⟨v, hv⟩
    have hv_ne : (v : PSL2MatrixGroup F) ≠ 1 := by
      intro hv_one
      obtain ⟨n, hn⟩ := hv ⟨x, hxV⟩
      have hnval : (v ^ n : V) = ⟨x, hxV⟩ := hn
      have hnval' := congrArg Subtype.val hnval
      change ((v : PSL2MatrixGroup F) ^ n) = x at hnval'
      simp [hv_one] at hnval'
      exact hx hnval'.symm
    obtain ⟨Tv, hvTv, _hTv_unique⟩ :=
      hpartition (v : PSL2MatrixGroup F) hv_ne
    have hxTv : x ∈ Tv := by
      obtain ⟨n, hn⟩ := hv ⟨x, hxV⟩
      have hnval : (v : PSL2MatrixGroup F) ^ n = x :=
        congrArg Subtype.val hn
      have hvpow : (v : PSL2MatrixGroup F) ^ n ∈ Tv :=
        Tv.zpow_mem hvTv.1 n
      rwa [hnval] at hvpow
    have hTvT : Tv = T :=
      (hpartition x hx).unique ⟨hxTv, hvTv.2⟩ ⟨hxT, hTfamily⟩
    intro y hyV
    obtain ⟨n, hn⟩ := hv ⟨y, hyV⟩
    have hnval : (v : PSL2MatrixGroup F) ^ n = y :=
      congrArg Subtype.val hn
    have hypow : (v : PSL2MatrixGroup F) ^ n ∈ Tv :=
      Tv.zpow_mem hvTv.1 n
    rw [hTvT, hnval] at hypow
    exact hypow
  have hmap_cyclic_H (A : Subgroup H) (hA : IsCyclic A) (g : H) :
      IsCyclic (g • A : Subgroup H) := by
    change IsCyclic (A.map (MulAut.conj g).toMonoidHom)
    letI : IsCyclic A := hA
    let e := (MulAut.conj g).subgroupMap A
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  have hconj_maximal (i : Fin r) (g : H) :
      ∀ V : Subgroup H, IsCyclic V →
        (g • Z i : Subgroup H) ≤ V → V = (g • Z i : Subgroup H) := by
    intro V hV hle
    have hback_cyclic : IsCyclic (g⁻¹ • V : Subgroup H) :=
      hmap_cyclic_H V hV g⁻¹
    have hback_le : Z i ≤ (g⁻¹ • V : Subgroup H) := by
      have hmap := Subgroup.map_mono
        (f := (MulAut.conj g⁻¹).toMonoidHom) hle
      change (g⁻¹ • (g • Z i) : Subgroup H) ≤
        (g⁻¹ • V : Subgroup H) at hmap
      simpa using hmap
    have heq : (g⁻¹ • V : Subgroup H) = Z i :=
      hmaximal i (g⁻¹ • V : Subgroup H) hback_cyclic hback_le
    have hfront := congrArg (fun W : Subgroup H => g • W) heq
    simpa using hfront
  have hindices_eq (i j : Fin r) (g h : H)
      (heq :
        (Z i).map (MulAut.conj g).toMonoidHom =
          (Z j).map (MulAut.conj h).toMonoidHom) : i = j := by
    have hcancel :
        ((Z i).map (MulAut.conj g).toMonoidHom).map
            (MulAut.conj h).symm.toMonoidHom = Z j :=
      (Subgroup.map_symm_eq_iff_map_eq
        (Z j) (e := MulAut.conj h)).mpr heq.symm
    have hsingle :
        (Z i).map (MulAut.conj (h⁻¹ * g)).toMonoidHom = Z j := by
      calc
        (Z i).map (MulAut.conj (h⁻¹ * g)).toMonoidHom =
            ((Z i).map (MulAut.conj g).toMonoidHom).map
              (MulAut.conj h).symm.toMonoidHom := by
                rw [Subgroup.map_map]
                congr 1
                ext y
                simp [MulAut.conj_apply, mul_assoc]
        _ = Z j := hcancel
    exact hdistinct i j (h⁻¹ * g) hsingle
  have hsylow_coprime_conj (Q : Sylow p H) (i : Fin r) (g : H) :
      Nat.Coprime (Nat.card Q) (Nat.card (g • Z i : Subgroup H)) := by
    rcases Q.isPGroup'.exists_card_eq with ⟨n, hQcard⟩
    rw [hQcard]
    change Nat.Coprime (p ^ n)
      (Nat.card ((Z i).map (MulAut.conj g).toMonoidHom))
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact (hcoprime i).pow_left n
  have hmap_subtype_cyclic (A : Subgroup H) (hA : IsCyclic A) :
      IsCyclic (A.map H.subtype) := by
    exact (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective
        A H.subtype H.subtype_injective)).mp hA
  have hcomap_cyclic (A : Subgroup (PSL2MatrixGroup F))
      (hA : IsCyclic A) : IsCyclic (A.comap H.subtype) := by
    letI : IsCyclic A := hA
    have hmap_cyclic : IsCyclic ((A.comap H.subtype).map H.subtype) :=
      Subgroup.isCyclic_of_le (Subgroup.map_comap_le H.subtype A)
    exact (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective
        (A.comap H.subtype) H.subtype H.subtype_injective)).mpr hmap_cyclic
  have hcomap_card_dvd (A : Subgroup (PSL2MatrixGroup F)) :
      Nat.card (A.comap H.subtype) ∣ Nat.card A :=
    Subgroup.card_comap_dvd_of_injective
      A H.subtype H.subtype_injective
  intro x hx
  have hxG : (x : PSL2MatrixGroup F) ≠ 1 := by
    intro h
    apply hx
    apply Subtype.ext
    exact h
  obtain ⟨T, hxT, hTfamily⟩ :=
    (hpartition (x : PSL2MatrixGroup F) hxG).exists
  have hambient_sylow_family (R : Sylow p (PSL2MatrixGroup F)) :
      ∃ g, (R : Subgroup (PSL2MatrixGroup F)) =
        (P0 : Subgroup (PSL2MatrixGroup F)).map
          (MulAut.conj g).toMonoidHom := by
    obtain ⟨g, hg⟩ :=
      MulAction.exists_smul_eq (PSL2MatrixGroup F) P0 R
    refine ⟨g, ?_⟩
    have hg' := congrArg
      (fun Q : Sylow p (PSL2MatrixGroup F) =>
        (Q : Subgroup (PSL2MatrixGroup F))) hg
    simpa using hg'.symm
  have hambient_eq_T (R : Sylow p (PSL2MatrixGroup F))
      (hxR : (x : PSL2MatrixGroup F) ∈
        (R : Subgroup (PSL2MatrixGroup F))) :
      (R : Subgroup (PSL2MatrixGroup F)) = T := by
    exact (hpartition (x : PSL2MatrixGroup F) hxG).unique
      ⟨hxR, Or.inl (hambient_sylow_family R)⟩
      ⟨hxT, hTfamily⟩
  have hsylow_eq_of_mem (Q₁ Q₂ : Sylow p H)
      (hx₁ : x ∈ (Q₁ : Subgroup H))
      (hx₂ : x ∈ (Q₂ : Subgroup H)) : Q₁ = Q₂ := by
    obtain ⟨R₁, hR₁⟩ := Q₁.exists_comap_subtype_eq
    obtain ⟨R₂, hR₂⟩ := Q₂.exists_comap_subtype_eq
    have hxR₁ : (x : PSL2MatrixGroup F) ∈
        (R₁ : Subgroup (PSL2MatrixGroup F)) := by
      change x ∈ (R₁ : Subgroup _).comap H.subtype
      rw [hR₁]
      exact hx₁
    have hxR₂ : (x : PSL2MatrixGroup F) ∈
        (R₂ : Subgroup (PSL2MatrixGroup F)) := by
      change x ∈ (R₂ : Subgroup _).comap H.subtype
      rw [hR₂]
      exact hx₂
    apply Sylow.ext
    calc
      (Q₁ : Subgroup H) = (R₁ : Subgroup _).comap H.subtype := hR₁.symm
      _ = T.comap H.subtype := congrArg
        (fun W : Subgroup (PSL2MatrixGroup F) => W.comap H.subtype)
        (hambient_eq_T R₁ hxR₁)
      _ = (R₂ : Subgroup _).comap H.subtype := congrArg
        (fun W : Subgroup (PSL2MatrixGroup F) => W.comap H.subtype)
        (hambient_eq_T R₂ hxR₂).symm
      _ = (Q₂ : Subgroup H) := hR₂
  rcases hTfamily with ⟨g, hTg⟩ | hTtorus
  · have hTp : IsPGroup p T := by
      rw [hTg]
      exact P0.isPGroup'.map (MulAut.conj g).toMonoidHom
    let I : Subgroup H := T.comap H.subtype
    have hIp : IsPGroup p I := hTp.comap_subtype
    obtain ⟨Q, hIQ⟩ := hIp.exists_le_sylow
    have hxI : x ∈ I := by
      change (x : PSL2MatrixGroup F) ∈ T
      exact hxT
    refine ⟨Sum.inl Q, hIQ hxI, ?_⟩
    intro A hA
    rcases A with Q' | z
    · exact congrArg Sum.inl (hsylow_eq_of_mem Q' Q hA (hIQ hxI))
    · rcases z with ⟨i, W, g', hW⟩
      exfalso
      have hcop : Nat.Coprime (Nat.card Q) (Nat.card W) := by
        rw [hW]
        exact hsylow_coprime_conj Q i g'
      exact hx (hmem_eq_one_of_coprime_card
        (Q : Subgroup H) W hcop (hIQ hxI) hA)
  · have hTfamily' :
        ((∃ g, T = (P0 : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g).toMonoidHom) ∨
          (∃ g, T = U.map (MulAut.conj g).toMonoidHom) ∨
          (∃ g, T = S.map (MulAut.conj g).toMonoidHom)) :=
      Or.inr hTtorus
    have hTcyclic : IsCyclic T := by
      rcases hTtorus with ⟨g, hg⟩ | ⟨g, hg⟩
      · rw [hg]
        exact hmap_cyclic U hUcyclic g
      · rw [hg]
        exact hmap_cyclic S hScyclic g
    have hpF : p ∣ Nat.card F := by
      rw [hFcard]
      exact dvd_pow_self p
        (huppert_II_8_27_field_exponent_ne_zero hFcard)
    have hFTcoprime : Nat.Coprime (Nat.card F) (Nat.card T) := by
      rcases hTtorus with ⟨g, hg⟩ | ⟨g, hg⟩
      · rw [hg, Subgroup.card_map_of_injective
            (K := U) (f := (MulAut.conj g).toMonoidHom)
            (MulAut.conj g).injective, hUcard]
        exact hq_coprime_split_order (Nat.card F) Nat.card_pos
      · rw [hg, Subgroup.card_map_of_injective
            (K := S) (f := (MulAut.conj g).toMonoidHom)
            (MulAut.conj g).injective, hScard]
        exact hq_coprime_nonsplit_order (Nat.card F) Nat.card_pos
    have hTcoprime : Nat.Coprime p (Nat.card T) :=
      Nat.Coprime.of_dvd_left hpF hFTcoprime
    let W : Subgroup H := T.comap H.subtype
    have hxW : x ∈ W := by
      change (x : PSL2MatrixGroup F) ∈ T
      exact hxT
    have hWcyclic : IsCyclic W := hcomap_cyclic T hTcyclic
    have hWcard : 1 < Nat.card W := by
      apply (Subgroup.one_lt_card_iff_ne_bot W).2
      intro hW
      exact hx (Subgroup.mem_bot.mp (hW ▸ hxW))
    have hWcoprime : Nat.Coprime p (Nat.card W) :=
      Nat.Coprime.of_dvd_right (hcomap_card_dvd T) hTcoprime
    have hWmax :
        ∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W := by
      intro V hV hWV
      have hVmap_cyclic : IsCyclic (V.map H.subtype) :=
        hmap_subtype_cyclic V hV
      have hxVmap :
          (x : PSL2MatrixGroup F) ∈ V.map H.subtype :=
        Subgroup.mem_map_of_mem H.subtype (hWV hxW)
      have hVmap_le_T : V.map H.subtype ≤ T :=
        hcyclic_le_family hxG hxT hTfamily' hxVmap hVmap_cyclic
      have hVleW : V ≤ W :=
        Subgroup.map_le_iff_le_comap.mp hVmap_le_T
      exact le_antisymm hVleW hWV
    obtain ⟨i, g, hWrep⟩ :=
      hrepresentative W hWcyclic hWcard hWcoprime hWmax
    refine ⟨Sum.inr ⟨i, ⟨W, g, hWrep⟩⟩, hxW, ?_⟩
    intro A hA
    rcases A with Q | z
    · exfalso
      have hcop : Nat.Coprime (Nat.card Q) (Nat.card W) := by
        rw [hWrep]
        exact hsylow_coprime_conj Q i g
      exact hx (hmem_eq_one_of_coprime_card
        (Q : Subgroup H) W hcop hA hxW)
    · rcases z with ⟨j, W', h, hW'rep⟩
      have hW'cyclic : IsCyclic W' := by
        rw [hW'rep]
        exact hmap_cyclic_H (Z j) (hcyclic j) h
      have hxW'map :
          (x : PSL2MatrixGroup F) ∈ W'.map H.subtype :=
        Subgroup.mem_map_of_mem H.subtype hA
      have hW'map_le_T : W'.map H.subtype ≤ T :=
        hcyclic_le_family hxG hxT hTfamily' hxW'map
          (hmap_subtype_cyclic W' hW'cyclic)
      have hW'leW : W' ≤ W :=
        Subgroup.map_le_iff_le_comap.mp hW'map_le_T
      have hW'max :
          ∀ V : Subgroup H, IsCyclic V → W' ≤ V → V = W' := by
        rw [hW'rep]
        exact hconj_maximal j h
      have hWW' : W = W' := hW'max W hWcyclic hW'leW
      have hmaps :
          (Z i).map (MulAut.conj g).toMonoidHom =
            (Z j).map (MulAut.conj h).toMonoidHom := by
        rw [← hWrep, ← hW'rep, hWW']
      have hij : i = j := hindices_eq i j g h hmaps
      subst j
      subst W'
      rfl

/-- The disjoint-union count in Huppert II.8.22. -/
public theorem huppert_II_8_22_counting_equation
    {F : Type u} [Field F] [Finite F] {p f m r : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (P : Sylow p H) (hPcard : Nat.card P = p ^ m)
    (Z : Fin r → Subgroup H) (s : Fin r → ℕ)
    (hcyclic : ∀ i, IsCyclic (Z i))
    (hnontrivial : ∀ i, 1 < Nat.card (Z i))
    (hcoprime : ∀ i, Nat.Coprime p (Nat.card (Z i)))
    (hmaximal : ∀ i (W : Subgroup H),
      IsCyclic W → Z i ≤ W → W = Z i)
    (hrepresentative : ∀ W : Subgroup H,
      IsCyclic W → 1 < Nat.card W →
      Nat.Coprime p (Nat.card W) →
      (∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) →
      ∃ i g, W = (Z i).map (MulAut.conj g).toMonoidHom)
    (hdistinct : ∀ i j g,
      (Z i).map (MulAut.conj g).toMonoidHom = Z j → i = j)
    (hnormalizer : ∀ i,
      Nat.card (Subgroup.normalizer (Z i : Set H)) =
        Nat.card (Z i) * s i) :
    Nat.card H =
      1 + ((p ^ m - 1) * Nat.card H) /
          Nat.card (Subgroup.normalizer (P : Set H)) +
        ∑ i, ((Nat.card (Z i) - 1) * Nat.card H) /
          (Nat.card (Z i) * s i) := by
  classical
  have hpartition_count :
      Nat.card H =
        1 + (p ^ m - 1) *
            (Subgroup.normalizer (P : Set H)).index +
          ∑ i, (Nat.card (Z i) - 1) *
            (Subgroup.normalizer (Z i : Set H)).index := by
    apply huppert_II_8_22_partition_count_of_unique_family P hPcard Z
    intro x hx
    convert huppert_II_8_22_unique_family hFcard H Z hcyclic hnontrivial
      hcoprime hmaximal hrepresentative hdistinct x hx using 1
    funext A
    rcases A with Q | z <;> rfl
  have hPindex :
      (Subgroup.normalizer (P : Set H)).index =
        Nat.card H /
          Nat.card (Subgroup.normalizer (P : Set H)) :=
    Nat.eq_div_of_mul_eq_left (Nat.ne_of_gt Nat.card_pos)
      (Subgroup.normalizer (P : Set H)).index_mul_card
  have hZindex :
      ∀ i, (Subgroup.normalizer (Z i : Set H)).index =
        Nat.card H /
          Nat.card (Subgroup.normalizer (Z i : Set H)) := by
    intro i
    exact Nat.eq_div_of_mul_eq_left (Nat.ne_of_gt Nat.card_pos)
      (Subgroup.normalizer (Z i : Set H)).index_mul_card
  nth_rewrite 1 [hpartition_count]
  congr 1
  · rw [Nat.mul_div_assoc _ (Subgroup.card_subgroup_dvd_card
      (Subgroup.normalizer (P : Set H))), ← hPindex]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [← hnormalizer i,
      Nat.mul_div_assoc _ (Subgroup.card_subgroup_dvd_card
        (Subgroup.normalizer (Z i : Set H))), ← hZindex i]

/-- Huppert II.8.22: the counting equation for maximal cyclic `p`-prime subgroups. -/
public theorem huppert_II_8_22_dickson_counting
    {F : Type u} [Field F] [Finite F] {p f m : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (P : Sylow p H) (hPcard : Nat.card P = p ^ m) :
    ∃ (r : ℕ) (Z : Fin r → Subgroup H) (s : Fin r → ℕ),
      (∀ i, IsCyclic (Z i)) ∧
      (∀ i, 1 < Nat.card (Z i)) ∧
      (∀ i, Nat.Coprime p (Nat.card (Z i))) ∧
      (∀ i (W : Subgroup H), IsCyclic W → Z i ≤ W → W = Z i) ∧
      (∀ W : Subgroup H, IsCyclic W → 1 < Nat.card W →
        Nat.Coprime p (Nat.card W) →
        (∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) →
        ∃ i g, W = (Z i).map (MulAut.conj g).toMonoidHom) ∧
      (∀ i j g,
        (Z i).map (MulAut.conj g).toMonoidHom = Z j → i = j) ∧
      (∀ i, 0 < s i ∧ s i ≤ 2) ∧
      (∀ i,
        Nat.card (Subgroup.normalizer (Z i : Set H)) = Nat.card (Z i) * s i) ∧
      (∀ i, s i = 2 →
        Nonempty (Subgroup.normalizer (Z i : Set H) ≃*
          DihedralGroup (Nat.card (Z i)))) ∧
      (1 < p ^ m →
        (Nat.card (Subgroup.normalizer (P : Set H)) = p ^ m ∨
          ∃ i, Nat.card (Subgroup.normalizer (P : Set H)) =
            p ^ m * Nat.card (Z i))) ∧
      (∀ i,
        (Nat.card (Z i) ∣
            (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (Nat.card (Z i) ∣
            (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
      Nat.card H =
        1 + ((p ^ m - 1) * Nat.card H) /
            Nat.card (Subgroup.normalizer (P : Set H)) +
          ∑ i, ((Nat.card (Z i) - 1) * Nat.card H) /
            (Nat.card (Z i) * s i) := by
  rcases huppert_II_8_22_maximal_cyclic_representatives (H := H) p with
    ⟨r, Z, hcyclic, hnontrivial, hcoprime, hmaximal,
      hrepresentative, hdistinct⟩
  rcases huppert_II_8_22_torus_normalizer_data
      hFcard H Z hcyclic hnontrivial hcoprime hmaximal with
    ⟨s, hs, hnormalizer, hdihedral, hdivides⟩
  refine ⟨r, Z, s, hcyclic, hnontrivial, hcoprime, hmaximal,
    hrepresentative, hdistinct, hs, hnormalizer, hdihedral, ?_, hdivides, ?_⟩
  · exact huppert_II_8_22_sylow_normalizer_shape
      hFcard H P hPcard Z hcyclic hcoprime hmaximal hrepresentative
  · exact huppert_II_8_22_counting_equation
      hFcard H P hPcard Z s hcyclic hnontrivial hcoprime hmaximal
        hrepresentative hdistinct hnormalizer
/-- Huppert II.8.23: the Dickson case with a nontrivial self-normalizing Sylow p-subgroup. -/
public theorem huppert_II_8_23_dickson_case_p_part_normalizer_self
    {F : Type u} [Field F] [Finite F] {p f m : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (P : Sylow p H) (hPcard : Nat.card P = p ^ m) (hpm : 1 < p ^ m)
    (hnormalizer : Subgroup.normalizer (P : Set H) = (P : Subgroup H)) :
    (Nat.card H = p ^ m ∧ IsElementaryAbelian p H) ∨
    (p ^ m = 2 ∧ ∃ z : ℕ, ¬ 2 ∣ z ∧
      ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
        (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
      Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
    (p ^ m = 3 ∧ Nonempty (H ≃* alternatingGroup (Fin 4))) := by
  classical
  rcases huppert_II_8_22_dickson_counting hFcard H P hPcard with
    ⟨r, Z, s, hcyclic, hnontrivial, hcoprime, hmaximal,
      hrepresentative, hdistinct, hs, hnormalizerZ, hdihedral,
      _hnormalizerP, hdivides, _hcounting⟩
  let NP := Subgroup.normalizer (P : Set H)
  let NZ : Fin r → Subgroup H := fun i => Subgroup.normalizer (Z i : Set H)
  have h823_partition_count :
      Nat.card H =
        1 + (p ^ m - 1) * NP.index +
          ∑ i, (Nat.card (Z i) - 1) * (NZ i).index := by
    dsimp only [NP, NZ]
    apply huppert_II_8_22_partition_count_of_unique_family P hPcard Z
    intro x hx
    convert huppert_II_8_22_unique_family hFcard H Z hcyclic hnontrivial
      hcoprime hmaximal hrepresentative hdistinct x hx using 1
    funext A
    rcases A with Q | z <;> rfl
  have h823_p_index_factor : p ^ m * NP.index = Nat.card H := by
    have hNPcard : Nat.card NP = p ^ m := by
      dsimp only [NP]
      rw [hnormalizer, hPcard]
    calc
      p ^ m * NP.index = Nat.card NP * NP.index := by rw [hNPcard]
      _ = Nat.card H := NP.card_mul_index
  have h823_z_index_factor :
      ∀ i, (Nat.card (Z i) * s i) * (NZ i).index = Nat.card H := by
    intro i
    have hNZcard : Nat.card (NZ i) = Nat.card (Z i) * s i := by
      dsimp only [NZ]
      exact hnormalizerZ i
    calc
      (Nat.card (Z i) * s i) * (NZ i).index =
          Nat.card (NZ i) * (NZ i).index := by rw [hNZcard]
      _ = Nat.card H := (NZ i).card_mul_index
  have h823_index_count :
      NP.index =
        1 + ∑ i, (Nat.card (Z i) - 1) * (NZ i).index := by
    let T := ∑ i, (Nat.card (Z i) - 1) * (NZ i).index
    have hsplit :
        (p ^ m - 1) * NP.index + NP.index = p ^ m * NP.index := by
      calc
        (p ^ m - 1) * NP.index + NP.index =
            (p ^ m - 1 + 1) * NP.index := by ring
        _ = p ^ m * NP.index := by rw [Nat.sub_add_cancel hpm.le]
    have hcancel :
        (p ^ m - 1) * NP.index + NP.index =
          (p ^ m - 1) * NP.index + (1 + T) := by
      calc
        (p ^ m - 1) * NP.index + NP.index =
            p ^ m * NP.index := hsplit
        _ = Nat.card H := h823_p_index_factor
        _ = 1 + (p ^ m - 1) * NP.index + T := by
          simpa only [T] using h823_partition_count
        _ = (p ^ m - 1) * NP.index + (1 + T) := by omega
    change NP.index = 1 + T
    exact Nat.add_left_cancel hcancel
  have h823_range_bound : r * p ^ m < 4 := by
    let T := ∑ i, (Nat.card (Z i) - 1) * (NZ i).index
    have hterm (i : Fin r) :
        Nat.card H ≤ 4 * ((Nat.card (Z i) - 1) * (NZ i).index) := by
      have hzbound :
          Nat.card (Z i) * s i ≤ 4 * (Nat.card (Z i) - 1) := by
        calc
          Nat.card (Z i) * s i ≤ Nat.card (Z i) * 2 :=
            Nat.mul_le_mul_left (Nat.card (Z i)) (hs i).2
          _ ≤ (2 * (Nat.card (Z i) - 1)) * 2 :=
            Nat.mul_le_mul_right 2 (by
              have hzi := hnontrivial i
              omega)
          _ = 4 * (Nat.card (Z i) - 1) := by ring
      calc
        Nat.card H = (Nat.card (Z i) * s i) * (NZ i).index :=
          (h823_z_index_factor i).symm
        _ ≤ (4 * (Nat.card (Z i) - 1)) * (NZ i).index :=
          Nat.mul_le_mul_right (NZ i).index hzbound
        _ = 4 * ((Nat.card (Z i) - 1) * (NZ i).index) := by ring
    have hrs : r * Nat.card H ≤ 4 * T := by
      calc
        r * Nat.card H = Finset.univ.sum fun _ : Fin r => Nat.card H := by simp
        _ ≤ Finset.univ.sum fun i : Fin r =>
            4 * ((Nat.card (Z i) - 1) * (NZ i).index) :=
          Finset.sum_le_sum fun i _hi => hterm i
        _ = 4 * T := by simp [T, Finset.mul_sum]
    have hcountT : NP.index = 1 + T := by
      simpa only [T] using h823_index_count
    have hT_lt_index : T < NP.index := by omega
    have hscaled_lt : p ^ m * T < Nat.card H := by
      calc
        p ^ m * T < p ^ m * NP.index :=
          (Nat.mul_lt_mul_left (by omega : 0 < p ^ m)).2 hT_lt_index
        _ = Nat.card H := h823_p_index_factor
    have hcancel : (r * p ^ m) * Nat.card H < 4 * Nat.card H := by
      calc
        (r * p ^ m) * Nat.card H = p ^ m * (r * Nat.card H) := by ring
        _ ≤ p ^ m * (4 * T) := Nat.mul_le_mul_left (p ^ m) hrs
        _ = 4 * (p ^ m * T) := by ring
        _ < 4 * Nat.card H :=
          (Nat.mul_lt_mul_left (by norm_num : 0 < 4)).2 hscaled_lt
    exact (Nat.mul_lt_mul_right (Nat.card_pos (α := H))).mp hcancel
  have h823_small_cases :
      r = 0 ∨ (r = 1 ∧ (p ^ m = 2 ∨ p ^ m = 3)) := by
    have hr_le : r ≤ r * p ^ m := by
      simpa using Nat.mul_le_mul_left r hpm.le
    have hr_lt : r < 4 := lt_of_le_of_lt hr_le h823_range_bound
    interval_cases r <;> omega
  have h823_case_zero (hr : r = 0) :
      Nat.card H = p ^ m ∧ IsElementaryAbelian p H := by
    subst r
    have hNPindex : NP.index = 1 := by
      simpa using h823_index_count
    have hPindex : (P : Subgroup H).index = 1 := by
      dsimp only [NP] at hNPindex
      rwa [hnormalizer] at hNPindex
    have hPtop : (P : Subgroup H) = ⊤ := Subgroup.index_eq_one.mp hPindex
    have hHcard : Nat.card H = p ^ m := by
      have h := hPcard
      rw [hPtop] at h
      simpa using h
    letI : Fintype F := Fintype.ofFinite F
    letI : CharP F p :=
      charP_of_card_eq_prime_pow (by simpa using hFcard)
    obtain ⟨Q, hQcomap⟩ := P.exists_comap_subtype_eq
    have hHleQ : H ≤ (Q : Subgroup (PSL2MatrixGroup F)) := by
      intro x hx
      change (⟨x, hx⟩ : H) ∈ (Q : Subgroup _).comap H.subtype
      rw [hQcomap, hPtop]
      simp
    have hFieldElementary : IsElementaryAbelian p (Multiplicative F) := by
      refine
        { toIsMulCommutative :=
            { is_comm := ⟨fun x y => mul_comm x y⟩ }
          exponent_dvd_p := ?_ }
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      change Multiplicative.ofAdd x.toAdd ^ p = 1
      rw [← ofAdd_nsmul]
      simp
    obtain ⟨eQ⟩ := huppert_II_8_2_a_sylow_equiv_additive hFcard Q
    have hQElementary : IsElementaryAbelian p Q := by
      refine
        { toIsMulCommutative :=
            { is_comm := ⟨fun x y => ?_⟩ }
          exponent_dvd_p := ?_ }
      · apply eQ.symm.injective
        simpa using
          hFieldElementary.toIsMulCommutative.is_comm.comm
            (eQ.symm x) (eQ.symm y)
      · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
        intro x
        apply eQ.symm.injective
        have hx : (eQ.symm x) ^ p = 1 :=
          Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            hFieldElementary.exponent_dvd_p (eQ.symm x)
        simpa using hx
    have hHElementary : IsElementaryAbelian p H := by
      letI : IsElementaryAbelian p Q := hQElementary
      refine
        { toIsMulCommutative :=
            { is_comm := ⟨fun x y =>
                Subtype.ext <|
                  Subgroup.mul_comm_of_mem_isMulCommutative
                    (H := (Q : Subgroup (PSL2MatrixGroup F)))
                    (hHleQ x.2) (hHleQ y.2)⟩ }
          exponent_dvd_p := ?_ }
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      apply Subtype.ext
      let xQ : Q := ⟨(x : PSL2MatrixGroup F), hHleQ x.2⟩
      have hxpow : xQ ^ p = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p Q) xQ
      simpa [xQ] using congrArg Subtype.val hxpow
    exact ⟨hHcard, hHElementary⟩
  have h823_case_two (hr : r = 1) (hpm2 : p ^ m = 2) :
      ∃ z : ℕ, ¬ 2 ∣ z ∧
        ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
        Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z) := by
    subst r
    have hcount0 :
        NP.index =
          1 + (Nat.card (Z 0) - 1) * (NZ 0).index := by
      simpa using h823_index_count
    have hPfactor2 : 2 * NP.index = Nat.card H := by
      calc
        2 * NP.index = p ^ m * NP.index :=
          congrArg (fun a => a * NP.index) hpm2.symm
        _ = Nat.card H := h823_p_index_factor
    have hZfactor0 :
        (Nat.card (Z 0) * s 0) * (NZ 0).index = Nat.card H :=
      h823_z_index_factor 0
    have hs0_two : s 0 = 2 := by
      have hs0 := hs 0
      rcases (show s 0 = 1 ∨ s 0 = 2 by omega) with hs0_one | hs0_two
      · have hzbound :
            Nat.card (Z 0) ≤ 2 * (Nat.card (Z 0) - 1) := by
          have hz := hnontrivial 0
          omega
        have hlt :
            Nat.card (Z 0) * (NZ 0).index < 2 * NP.index := by
          calc
            Nat.card (Z 0) * (NZ 0).index ≤
                (2 * (Nat.card (Z 0) - 1)) * (NZ 0).index :=
              Nat.mul_le_mul_right (NZ 0).index hzbound
            _ = 2 * ((Nat.card (Z 0) - 1) * (NZ 0).index) := by ring
            _ < 2 * (1 + (Nat.card (Z 0) - 1) * (NZ 0).index) := by
              omega
            _ = 2 * NP.index := by rw [← hcount0]
        have hbad : Nat.card H < Nat.card H := by
          calc
            Nat.card H = Nat.card (Z 0) * (NZ 0).index := by
              simpa [hs0_one] using hZfactor0.symm
            _ < 2 * NP.index := hlt
            _ = Nat.card H := hPfactor2
        exact (Nat.lt_irrefl _ hbad).elim
      · exact hs0_two
    have hk0_one : (NZ 0).index = 1 := by
      have hZfactor2 :
          2 * (Nat.card (Z 0) * (NZ 0).index) = Nat.card H := by
        calc
          2 * (Nat.card (Z 0) * (NZ 0).index) =
              (Nat.card (Z 0) * 2) * (NZ 0).index := by ring
          _ = (Nat.card (Z 0) * s 0) * (NZ 0).index := by
            rw [hs0_two]
          _ = Nat.card H := hZfactor0
      have hindex_eq : NP.index = Nat.card (Z 0) * (NZ 0).index := by
        apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
        exact hPfactor2.trans hZfactor2.symm
      have hzsplit :
          Nat.card (Z 0) * (NZ 0).index =
            (Nat.card (Z 0) - 1) * (NZ 0).index + (NZ 0).index := by
        calc
          Nat.card (Z 0) * (NZ 0).index =
              (Nat.card (Z 0) - 1 + 1) * (NZ 0).index := by
            rw [Nat.sub_add_cancel (hnontrivial 0).le]
          _ = (Nat.card (Z 0) - 1) * (NZ 0).index + (NZ 0).index := by
            ring
      have hcancel :
          (Nat.card (Z 0) - 1) * (NZ 0).index + (NZ 0).index =
            (Nat.card (Z 0) - 1) * (NZ 0).index + 1 := by
        calc
          (Nat.card (Z 0) - 1) * (NZ 0).index + (NZ 0).index =
              Nat.card (Z 0) * (NZ 0).index := hzsplit.symm
          _ = NP.index := hindex_eq.symm
          _ = 1 + (Nat.card (Z 0) - 1) * (NZ 0).index := hcount0
          _ = (Nat.card (Z 0) - 1) * (NZ 0).index + 1 := by omega
      exact Nat.add_left_cancel hcancel
    have hHcard2 : Nat.card H = 2 * Nat.card (Z 0) := by
      calc
        Nat.card H = (Nat.card (Z 0) * s 0) * (NZ 0).index :=
          hZfactor0.symm
        _ = 2 * Nat.card (Z 0) := by rw [hs0_two, hk0_one]; ring
    have hp_eq_two : p = 2 := by
      have hm_ne_zero : m ≠ 0 := by
        intro hm
        subst m
        norm_num at hpm2
      have hp_dvd : p ∣ 2 := by
        have hp_pow : p ∣ p ^ m := dvd_pow_self p hm_ne_zero
        exact hpm2 ▸ hp_pow
      exact
        (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hp_dvd
    have hzodd : ¬ 2 ∣ Nat.card (Z 0) := by
      apply Nat.prime_two.coprime_iff_not_dvd.mp
      simpa [hp_eq_two] using hcoprime 0
    have hNZtop : NZ 0 = ⊤ := by
      exact Subgroup.index_eq_one.mp hk0_one
    have hHequiv : Nonempty (H ≃* DihedralGroup (Nat.card (Z 0))) := by
      obtain ⟨eD⟩ := hdihedral 0 hs0_two
      let eH : NZ 0 ≃* H :=
        (MulEquiv.subgroupCongr hNZtop).trans
          (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H)
      exact ⟨eH.symm.trans eD⟩
    exact ⟨Nat.card (Z 0), hzodd, hdivides 0, hHcard2, hHequiv⟩
  have h823_case_three (hr : r = 1) (hpm3 : p ^ m = 3) :
      Nonempty (H ≃* alternatingGroup (Fin 4)) := by
    subst r
    have hcount0 :
        NP.index =
          1 + (Nat.card (Z 0) - 1) * (NZ 0).index := by
      simpa using h823_index_count
    have hPfactor3 : 3 * NP.index = Nat.card H := by
      calc
        3 * NP.index = p ^ m * NP.index :=
          congrArg (fun a => a * NP.index) hpm3.symm
        _ = Nat.card H := h823_p_index_factor
    have hZfactor0 :
        (Nat.card (Z 0) * s 0) * (NZ 0).index = Nat.card H :=
      h823_z_index_factor 0
    have hs0_two : s 0 = 2 := by
      have hs0 := hs 0
      rcases (show s 0 = 1 ∨ s 0 = 2 by omega) with hs0_one | hs0_two
      · have hzbound :
            Nat.card (Z 0) ≤ 3 * (Nat.card (Z 0) - 1) := by
          have hz := hnontrivial 0
          omega
        have hlt :
            Nat.card (Z 0) * (NZ 0).index < 3 * NP.index := by
          calc
            Nat.card (Z 0) * (NZ 0).index ≤
                (3 * (Nat.card (Z 0) - 1)) * (NZ 0).index :=
              Nat.mul_le_mul_right (NZ 0).index hzbound
            _ = 3 * ((Nat.card (Z 0) - 1) * (NZ 0).index) := by ring
            _ < 3 * (1 + (Nat.card (Z 0) - 1) * (NZ 0).index) := by
              omega
            _ = 3 * NP.index := by rw [← hcount0]
        have hbad : Nat.card H < Nat.card H := by
          calc
            Nat.card H = Nat.card (Z 0) * (NZ 0).index := by
              simpa [hs0_one] using hZfactor0.symm
            _ < 3 * NP.index := hlt
            _ = Nat.card H := hPfactor3
        exact (Nat.lt_irrefl _ hbad).elim
      · exact hs0_two
    have hz0_two : Nat.card (Z 0) = 2 := by
      have hZfactor2 :
          2 * (Nat.card (Z 0) * (NZ 0).index) = Nat.card H := by
        calc
          2 * (Nat.card (Z 0) * (NZ 0).index) =
              (Nat.card (Z 0) * 2) * (NZ 0).index := by ring
          _ = (Nat.card (Z 0) * s 0) * (NZ 0).index := by
            rw [hs0_two]
          _ = Nat.card H := hZfactor0
      have hfactor_eq :
          3 * NP.index = 2 * (Nat.card (Z 0) * (NZ 0).index) :=
        hPfactor3.trans hZfactor2.symm
      by_contra hz_ne_two
      have hz_ge_three : 3 ≤ Nat.card (Z 0) := by
        have hz := hnontrivial 0
        omega
      have hzbound :
          2 * Nat.card (Z 0) ≤ 3 * (Nat.card (Z 0) - 1) := by
        omega
      have hlt :
          2 * (Nat.card (Z 0) * (NZ 0).index) < 3 * NP.index := by
        calc
          2 * (Nat.card (Z 0) * (NZ 0).index) =
              (2 * Nat.card (Z 0)) * (NZ 0).index := by ring
          _ ≤ (3 * (Nat.card (Z 0) - 1)) * (NZ 0).index :=
            Nat.mul_le_mul_right (NZ 0).index hzbound
          _ = 3 * ((Nat.card (Z 0) - 1) * (NZ 0).index) := by ring
          _ < 3 * (1 + (Nat.card (Z 0) - 1) * (NZ 0).index) := by
            omega
          _ = 3 * NP.index := by rw [← hcount0]
      exact (Nat.lt_irrefl _ (hlt.trans_eq hfactor_eq)).elim
    have hk0_three : (NZ 0).index = 3 := by
      have hcount' : NP.index = 1 + (NZ 0).index := by
        simpa [hz0_two] using hcount0
      have hZfactor4 : 4 * (NZ 0).index = Nat.card H := by
        calc
          4 * (NZ 0).index =
              (Nat.card (Z 0) * s 0) * (NZ 0).index := by
            rw [hz0_two, hs0_two]
          _ = Nat.card H := hZfactor0
      have hfactor' : 3 * NP.index = 4 * (NZ 0).index :=
        hPfactor3.trans hZfactor4.symm
      omega
    have hHcard12 : Nat.card H = 12 := by
      calc
        Nat.card H = (Nat.card (Z 0) * s 0) * (NZ 0).index :=
          hZfactor0.symm
        _ = 12 := by rw [hz0_two, hs0_two, hk0_three]
    have hp_eq_three : p = 3 := by
      have hm_ne_zero : m ≠ 0 := by
        intro hm
        subst m
        norm_num at hpm3
      have hp_dvd : p ∣ 3 := by
        have hp_pow : p ∣ p ^ m := dvd_pow_self p hm_ne_zero
        exact hpm3 ▸ hp_pow
      exact
        (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp hp_dvd
    subst p
    have hSylow4 : Nat.card (Sylow 3 H) = 4 := by
      have hPindex4 : NP.index = 4 := by
        simpa [hz0_two, hk0_three] using hcount0
      calc
        Nat.card (Sylow 3 H) =
            (Subgroup.normalizer (P : Set H)).index :=
          P.card_eq_index_normalizer
        _ = NP.index := by rfl
        _ = 4 := hPindex4
    exact huppert_II_8_17_b_order_twelve_four_sylow_three hHcard12 hSylow4
  rcases h823_small_cases with hr | ⟨hr, hpm2 | hpm3⟩
  · exact Or.inl (h823_case_zero hr)
  · exact Or.inr (Or.inl ⟨hpm2, h823_case_two hr hpm2⟩)
  · exact Or.inr (Or.inr ⟨hpm3, h823_case_three hr hpm3⟩)
set_option maxHeartbeats 1600000 in
/-- Huppert II.8.24: the Dickson case in which p does not divide the subgroup order. -/
public theorem huppert_II_8_24_dickson_case_no_p_part
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (hp_not_dvd_card_H : ¬ p ∣ Nat.card H) :
    (∃ z : ℕ,
      ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
        (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
      Nat.card H = z ∧ IsCyclic H) ∨
    (∃ z : ℕ,
      ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
        (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
      Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
    ((p ≠ 2 ∨ Even f) ∧ Nonempty (H ≃* alternatingGroup (Fin 4))) ∨
    ((16 ∣ p ^ (2 * f) - 1) ∧ Nonempty (H ≃* Equiv.Perm (Fin 4))) ∨
    ((p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) ∧
      Nonempty (H ≃* alternatingGroup (Fin 5))) := by
  classical
  let P : Sylow p H := default
  have hPcard : Nat.card P = p ^ 0 := by
    rw [P.card_eq_multiplicity,
      Nat.factorization_eq_zero_of_not_dvd hp_not_dvd_card_H, pow_zero]
  rcases huppert_II_8_22_dickson_counting
      (m := 0) hFcard H P hPcard with
    ⟨r, Z, s, hcyclic, hnontrivial, hcoprime, hmaximal,
      hrepresentative, hdistinct, hs, hnormalizerZ, hdihedral,
      _hnormalizerP, hdivides, _hcounting⟩
  let NZ : Fin r → Subgroup H := fun i => Subgroup.normalizer (Z i : Set H)
  have h824_partition_count :
      Nat.card H =
        1 + ∑ i, (Nat.card (Z i) - 1) * (NZ i).index := by
    have hraw :
        Nat.card H =
          1 + (p ^ 0 - 1) *
              (Subgroup.normalizer (P : Set H)).index +
            ∑ i, (Nat.card (Z i) - 1) *
              (Subgroup.normalizer (Z i : Set H)).index := by
      apply huppert_II_8_22_partition_count_of_unique_family P hPcard Z
      intro x hx
      convert huppert_II_8_22_unique_family hFcard H Z hcyclic hnontrivial
        hcoprime hmaximal hrepresentative hdistinct x hx using 1
      funext A
      rcases A with Q | z <;> rfl
    simpa only [pow_zero, Nat.reduceSubDiff, zero_mul, zero_add, NZ] using hraw
  have h824_z_index_factor :
      ∀ i, (Nat.card (Z i) * s i) * (NZ i).index = Nat.card H := by
    intro i
    have hNZcard : Nat.card (NZ i) = Nat.card (Z i) * s i := by
      dsimp only [NZ]
      exact hnormalizerZ i
    calc
      (Nat.card (Z i) * s i) * (NZ i).index =
          Nat.card (NZ i) * (NZ i).index := by rw [hNZcard]
      _ = Nat.card H := (NZ i).card_mul_index
  have h824_family_bound : r ≤ 3 := by
    let T := ∑ i, (Nat.card (Z i) - 1) * (NZ i).index
    have hterm (i : Fin r) :
        Nat.card H ≤ 4 * ((Nat.card (Z i) - 1) * (NZ i).index) := by
      have hzbound :
          Nat.card (Z i) * s i ≤ 4 * (Nat.card (Z i) - 1) := by
        calc
          Nat.card (Z i) * s i ≤ Nat.card (Z i) * 2 :=
            Nat.mul_le_mul_left (Nat.card (Z i)) (hs i).2
          _ ≤ (2 * (Nat.card (Z i) - 1)) * 2 :=
            Nat.mul_le_mul_right 2 (by
              have hzi := hnontrivial i
              omega)
          _ = 4 * (Nat.card (Z i) - 1) := by ring
      calc
        Nat.card H = (Nat.card (Z i) * s i) * (NZ i).index :=
          (h824_z_index_factor i).symm
        _ ≤ (4 * (Nat.card (Z i) - 1)) * (NZ i).index :=
          Nat.mul_le_mul_right (NZ i).index hzbound
        _ = 4 * ((Nat.card (Z i) - 1) * (NZ i).index) := by ring
    have hrs : r * Nat.card H ≤ 4 * T := by
      calc
        r * Nat.card H = Finset.univ.sum fun _ : Fin r => Nat.card H := by simp
        _ ≤ Finset.univ.sum fun i : Fin r =>
            4 * ((Nat.card (Z i) - 1) * (NZ i).index) :=
          Finset.sum_le_sum fun i _hi => hterm i
        _ = 4 * T := by simp [T, Finset.mul_sum]
    have hcountT : Nat.card H = 1 + T := by
      simpa only [T] using h824_partition_count
    have hTlt : T < Nat.card H := by omega
    have hcancel : r * Nat.card H < 4 * Nat.card H :=
      hrs.trans_lt
        ((Nat.mul_lt_mul_left (by norm_num : 0 < 4)).2 hTlt)
    have hrlt : r < 4 :=
      (Nat.mul_lt_mul_right (Nat.card_pos (α := H))).mp hcancel
    omega
  have h824_shape :
      (∃ z : ℕ,
        ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
        Nat.card H = z ∧ IsCyclic H) ∨
      (∃ z : ℕ,
        ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
        Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
      Nonempty (H ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (H ≃* alternatingGroup (Fin 5)) := by
    by_cases hr_zero : r = 0
    · subst r
      have hHcard : Nat.card H = 1 := by
        simpa using h824_partition_count
      have hHcyclic : IsCyclic H := by
        letI : Subsingleton H := (Nat.card_eq_one_iff_unique.mp hHcard).1
        exact isCyclic_of_subsingleton
      exact Or.inl ⟨1, Or.inl (one_dvd _), hHcard, hHcyclic⟩
    · have h824_positive_shape :
          (∃ z : ℕ,
            ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
              (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
            Nat.card H = z ∧ IsCyclic H) ∨
          (∃ z : ℕ,
            ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
              (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
            Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
          Nonempty (H ≃* alternatingGroup (Fin 4)) ∨
          Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
          Nonempty (H ≃* alternatingGroup (Fin 5)) := by
        by_cases hr_one : r = 1
        · subst r
          have hs0_one : s 0 = 1 := by
            have hs0 := hs 0
            rcases (show s 0 = 1 ∨ s 0 = 2 by omega) with hs0_one | hs0_two
            · exact hs0_one
            · have hkpos : 0 < (NZ 0).index :=
                Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
              have hzpos : 0 < Nat.card (Z 0) := Nat.card_pos
              have hle :
                  1 + (Nat.card (Z 0) - 1) * (NZ 0).index ≤
                    Nat.card (Z 0) * (NZ 0).index := by
                calc
                  1 + (Nat.card (Z 0) - 1) * (NZ 0).index ≤
                      (NZ 0).index +
                        (Nat.card (Z 0) - 1) * (NZ 0).index := by omega
                  _ = (Nat.card (Z 0) - 1) * (NZ 0).index +
                      (NZ 0).index := Nat.add_comm _ _
                  _ = (Nat.card (Z 0) - 1 + 1) * (NZ 0).index := by ring
                  _ = Nat.card (Z 0) * (NZ 0).index := by
                    rw [Nat.sub_add_cancel (hnontrivial 0).le]
              have hlt :
                  Nat.card (Z 0) * (NZ 0).index <
                    (Nat.card (Z 0) * 2) * (NZ 0).index := by
                have hprodpos :
                    0 < Nat.card (Z 0) * (NZ 0).index :=
                  Nat.mul_pos hzpos hkpos
                calc
                  Nat.card (Z 0) * (NZ 0).index <
                      2 * (Nat.card (Z 0) * (NZ 0).index) := by omega
                  _ = (Nat.card (Z 0) * 2) * (NZ 0).index := by ring
              have hbad : Nat.card H < Nat.card H := by
                calc
                  Nat.card H =
                      1 + (Nat.card (Z 0) - 1) * (NZ 0).index := by
                    simpa using h824_partition_count
                  _ ≤ Nat.card (Z 0) * (NZ 0).index := hle
                  _ < (Nat.card (Z 0) * 2) * (NZ 0).index := hlt
                  _ = Nat.card H := by
                    calc
                      (Nat.card (Z 0) * 2) * (NZ 0).index =
                          (Nat.card (Z 0) * s 0) * (NZ 0).index :=
                        congrArg (fun a =>
                          (Nat.card (Z 0) * a) * (NZ 0).index) hs0_two.symm
                      _ = Nat.card H := h824_z_index_factor 0
              exact (Nat.lt_irrefl _ hbad).elim
          have hcount0 :
              Nat.card H =
                1 + (Nat.card (Z 0) - 1) * (NZ 0).index := by
            simpa using h824_partition_count
          have hfactor0 :
              Nat.card (Z 0) * (NZ 0).index = Nat.card H := by
            simpa [hs0_one] using h824_z_index_factor 0
          have hk_one : (NZ 0).index = 1 := by
            have hzsplit :
                Nat.card (Z 0) * (NZ 0).index =
                  (Nat.card (Z 0) - 1) * (NZ 0).index + (NZ 0).index := by
              calc
                Nat.card (Z 0) * (NZ 0).index =
                    (Nat.card (Z 0) - 1 + 1) * (NZ 0).index := by
                  rw [Nat.sub_add_cancel (hnontrivial 0).le]
                _ = (Nat.card (Z 0) - 1) * (NZ 0).index + (NZ 0).index := by
                  ring
            have hcancel :
                (Nat.card (Z 0) - 1) * (NZ 0).index + (NZ 0).index =
                  (Nat.card (Z 0) - 1) * (NZ 0).index + 1 := by
              calc
                (Nat.card (Z 0) - 1) * (NZ 0).index + (NZ 0).index =
                    Nat.card (Z 0) * (NZ 0).index := hzsplit.symm
                _ = Nat.card H := hfactor0
                _ = 1 + (Nat.card (Z 0) - 1) * (NZ 0).index := hcount0
                _ = (Nat.card (Z 0) - 1) * (NZ 0).index + 1 := by omega
            exact Nat.add_left_cancel hcancel
          have hHcard : Nat.card H = Nat.card (Z 0) := by
            calc
              Nat.card H = Nat.card (Z 0) * (NZ 0).index := hfactor0.symm
              _ = Nat.card (Z 0) := by rw [hk_one, mul_one]
          have hZtop : Z 0 = ⊤ :=
            Subgroup.eq_top_of_card_eq (H := Z 0) hHcard.symm
          have hHcyclic : IsCyclic H := by
            have htopcyclic : IsCyclic (⊤ : Subgroup H) :=
              (MulEquiv.subgroupCongr hZtop).isCyclic.mp (hcyclic 0)
            exact (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H).isCyclic.mp htopcyclic
          exact Or.inl ⟨Nat.card (Z 0), hdivides 0, hHcard, hHcyclic⟩
        · have h824_two_or_three_shape :
              (∃ z : ℕ,
                ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                  (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                Nat.card H = z ∧ IsCyclic H) ∨
              (∃ z : ℕ,
                ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                  (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
              Nonempty (H ≃* alternatingGroup (Fin 4)) ∨
              Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
              Nonempty (H ≃* alternatingGroup (Fin 5)) := by
            by_cases hr_two : r = 2
            · have h824_two_shape :
                  (∃ z : ℕ,
                    ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                      (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                    Nat.card H = z ∧ IsCyclic H) ∨
                  (∃ z : ℕ,
                    ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                      (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                    Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
                  Nonempty (H ≃* alternatingGroup (Fin 4)) ∨
                  Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
                  Nonempty (H ≃* alternatingGroup (Fin 5)) := by
                subst r
                have hnot_one_one (hs0 : s 0 = 1) (hs1 : s 1 = 1) : False := by
                  have hcount :
                      Nat.card H =
                        1 + (Nat.card (Z 0) - 1) * (NZ 0).index +
                          (Nat.card (Z 1) - 1) * (NZ 1).index := by
                    simpa [add_assoc] using h824_partition_count
                  have hfactor0 :
                      Nat.card (Z 0) * (NZ 0).index = Nat.card H := by
                    simpa [hs0] using h824_z_index_factor 0
                  have hfactor1 :
                      Nat.card (Z 1) * (NZ 1).index = Nat.card H := by
                    simpa [hs1] using h824_z_index_factor 1
                  have hrel0 :
                      (Nat.card (Z 0) - 1) * (NZ 0).index + (NZ 0).index =
                        Nat.card H := by
                    calc
                      (Nat.card (Z 0) - 1) * (NZ 0).index + (NZ 0).index =
                          (Nat.card (Z 0) - 1 + 1) * (NZ 0).index := by ring
                      _ = Nat.card (Z 0) * (NZ 0).index := by
                        rw [Nat.sub_add_cancel (hnontrivial 0).le]
                      _ = Nat.card H := hfactor0
                  have hrel1 :
                      (Nat.card (Z 1) - 1) * (NZ 1).index + (NZ 1).index =
                        Nat.card H := by
                    calc
                      (Nat.card (Z 1) - 1) * (NZ 1).index + (NZ 1).index =
                          (Nat.card (Z 1) - 1 + 1) * (NZ 1).index := by ring
                      _ = Nat.card (Z 1) * (NZ 1).index := by
                        rw [Nat.sub_add_cancel (hnontrivial 1).le]
                      _ = Nat.card H := hfactor1
                  have hbound0 : 2 * (NZ 0).index ≤ Nat.card H := by
                    calc
                      2 * (NZ 0).index ≤ Nat.card (Z 0) * (NZ 0).index :=
                        Nat.mul_le_mul_right (NZ 0).index (by
                          have hz := hnontrivial 0
                          omega)
                      _ = Nat.card H := hfactor0
                  have hbound1 : 2 * (NZ 1).index ≤ Nat.card H := by
                    calc
                      2 * (NZ 1).index ≤ Nat.card (Z 1) * (NZ 1).index :=
                        Nat.mul_le_mul_right (NZ 1).index (by
                          have hz := hnontrivial 1
                          omega)
                      _ = Nat.card H := hfactor1
                  omega
                have hnot_two_two (hs0 : s 0 = 2) (hs1 : s 1 = 2) : False := by
                  have hcount :
                      Nat.card H =
                        1 + (Nat.card (Z 0) - 1) * (NZ 0).index +
                          (Nat.card (Z 1) - 1) * (NZ 1).index := by
                    simpa [add_assoc] using h824_partition_count
                  have hfactor0 :
                      2 * (Nat.card (Z 0) * (NZ 0).index) = Nat.card H := by
                    calc
                      2 * (Nat.card (Z 0) * (NZ 0).index) =
                          (Nat.card (Z 0) * 2) * (NZ 0).index := by ring
                      _ = (Nat.card (Z 0) * s 0) * (NZ 0).index :=
                        congrArg (fun a =>
                          (Nat.card (Z 0) * a) * (NZ 0).index) hs0.symm
                      _ = Nat.card H := h824_z_index_factor 0
                  have hfactor1 :
                      2 * (Nat.card (Z 1) * (NZ 1).index) = Nat.card H := by
                    calc
                      2 * (Nat.card (Z 1) * (NZ 1).index) =
                          (Nat.card (Z 1) * 2) * (NZ 1).index := by ring
                      _ = (Nat.card (Z 1) * s 1) * (NZ 1).index :=
                        congrArg (fun a =>
                          (Nat.card (Z 1) * a) * (NZ 1).index) hs1.symm
                      _ = Nat.card H := h824_z_index_factor 1
                  have hrel0 :
                      2 * ((Nat.card (Z 0) - 1) * (NZ 0).index) +
                          2 * (NZ 0).index = Nat.card H := by
                    calc
                      2 * ((Nat.card (Z 0) - 1) * (NZ 0).index) +
                          2 * (NZ 0).index =
                          2 * ((Nat.card (Z 0) - 1 + 1) * (NZ 0).index) := by
                            ring
                      _ = 2 * (Nat.card (Z 0) * (NZ 0).index) := by
                        rw [Nat.sub_add_cancel (hnontrivial 0).le]
                      _ = Nat.card H := hfactor0
                  have hrel1 :
                      2 * ((Nat.card (Z 1) - 1) * (NZ 1).index) +
                          2 * (NZ 1).index = Nat.card H := by
                    calc
                      2 * ((Nat.card (Z 1) - 1) * (NZ 1).index) +
                          2 * (NZ 1).index =
                          2 * ((Nat.card (Z 1) - 1 + 1) * (NZ 1).index) := by
                            ring
                      _ = 2 * (Nat.card (Z 1) * (NZ 1).index) := by
                        rw [Nat.sub_add_cancel (hnontrivial 1).le]
                      _ = Nat.card H := hfactor1
                  have hk0pos : 0 < (NZ 0).index :=
                    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
                  have hk1pos : 0 < (NZ 1).index :=
                    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
                  omega
                have hmixed (i j : Fin 2) (hij : i ≠ j)
                    (hsi : s i = 1) (hsj : s j = 2) :
                    (∃ z : ℕ,
                      ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                        (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                      Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
                    Nonempty (H ≃* alternatingGroup (Fin 4)) := by
                  have hsum :
                      (∑ k, (Nat.card (Z k) - 1) * (NZ k).index) =
                        (Nat.card (Z i) - 1) * (NZ i).index +
                          (Nat.card (Z j) - 1) * (NZ j).index := by
                    fin_cases i <;> fin_cases j
                    · exact (hij rfl).elim
                    · simp
                    · simp [add_comm]
                    · exact (hij rfl).elim
                  have hcount :
                      Nat.card H =
                        1 + (Nat.card (Z i) - 1) * (NZ i).index +
                          (Nat.card (Z j) - 1) * (NZ j).index := by
                    calc
                      Nat.card H =
                          1 + ∑ k, (Nat.card (Z k) - 1) * (NZ k).index :=
                        h824_partition_count
                      _ = 1 + (Nat.card (Z i) - 1) * (NZ i).index +
                          (Nat.card (Z j) - 1) * (NZ j).index := by
                        rw [hsum]
                        simp [add_assoc]
                  have hfactor_i :
                      Nat.card (Z i) * (NZ i).index = Nat.card H := by
                    simpa [hsi] using h824_z_index_factor i
                  have hfactor_j :
                      2 * (Nat.card (Z j) * (NZ j).index) = Nat.card H := by
                    calc
                      2 * (Nat.card (Z j) * (NZ j).index) =
                          (Nat.card (Z j) * 2) * (NZ j).index := by ring
                      _ = (Nat.card (Z j) * s j) * (NZ j).index :=
                        congrArg (fun a =>
                          (Nat.card (Z j) * a) * (NZ j).index) hsj.symm
                      _ = Nat.card H := h824_z_index_factor j
                  have hrel_i :
                      (Nat.card (Z i) - 1) * (NZ i).index + (NZ i).index =
                        Nat.card H := by
                    calc
                      (Nat.card (Z i) - 1) * (NZ i).index + (NZ i).index =
                          (Nat.card (Z i) - 1 + 1) * (NZ i).index := by ring
                      _ = Nat.card (Z i) * (NZ i).index := by
                        rw [Nat.sub_add_cancel (hnontrivial i).le]
                      _ = Nat.card H := hfactor_i
                  have hindex_eq :
                      (NZ i).index =
                        1 + (Nat.card (Z j) - 1) * (NZ j).index := by
                    omega
                  by_cases hzi_two : Nat.card (Z i) = 2
                  · have hdihedral_case :
                        ∃ z : ℕ,
                          ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                            (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                          Nat.card H = 2 * z ∧
                            Nonempty (H ≃* DihedralGroup z) := by
                      have hfactor_i_two : 2 * (NZ i).index = Nat.card H := by
                        calc
                          2 * (NZ i).index = Nat.card (Z i) * (NZ i).index :=
                            congrArg (fun a => a * (NZ i).index) hzi_two.symm
                          _ = Nat.card H := hfactor_i
                      have hindex_i_eq :
                          (NZ i).index = Nat.card (Z j) * (NZ j).index := by
                        apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
                        exact hfactor_i_two.trans hfactor_j.symm
                      have hzsplit :
                          Nat.card (Z j) * (NZ j).index =
                            (Nat.card (Z j) - 1) * (NZ j).index +
                              (NZ j).index := by
                        calc
                          Nat.card (Z j) * (NZ j).index =
                              (Nat.card (Z j) - 1 + 1) * (NZ j).index := by
                            rw [Nat.sub_add_cancel (hnontrivial j).le]
                          _ = (Nat.card (Z j) - 1) * (NZ j).index +
                              (NZ j).index := by ring
                      have hk_j_one : (NZ j).index = 1 := by
                        have hcancel :
                            (Nat.card (Z j) - 1) * (NZ j).index +
                                (NZ j).index =
                              (Nat.card (Z j) - 1) * (NZ j).index + 1 := by
                          calc
                            (Nat.card (Z j) - 1) * (NZ j).index +
                                (NZ j).index =
                                Nat.card (Z j) * (NZ j).index := hzsplit.symm
                            _ = (NZ i).index := hindex_i_eq.symm
                            _ = 1 + (Nat.card (Z j) - 1) * (NZ j).index :=
                              hindex_eq
                            _ = (Nat.card (Z j) - 1) * (NZ j).index + 1 := by
                              omega
                        exact Nat.add_left_cancel hcancel
                      have hHcard : Nat.card H = 2 * Nat.card (Z j) := by
                        calc
                          Nat.card H =
                              2 * (Nat.card (Z j) * (NZ j).index) :=
                            hfactor_j.symm
                          _ = 2 * Nat.card (Z j) := by rw [hk_j_one, mul_one]
                      have hNZtop : NZ j = ⊤ :=
                        Subgroup.index_eq_one.mp hk_j_one
                      obtain ⟨eD⟩ := hdihedral j hsj
                      let eH : NZ j ≃* H :=
                        (MulEquiv.subgroupCongr hNZtop).trans
                          (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H)
                      exact
                        ⟨Nat.card (Z j), hdivides j, hHcard,
                          ⟨eH.symm.trans eD⟩⟩
                    exact Or.inl hdihedral_case
                  · have hA4_case :
                        Nonempty (H ≃* alternatingGroup (Fin 4)) := by
                      have hzi_ge_three : 3 ≤ Nat.card (Z i) := by
                        have hzi := hnontrivial i
                        omega
                      have hterm_lt :
                          (Nat.card (Z j) - 1) * (NZ j).index < (NZ i).index := by
                        omega
                      have hfactor_eq :
                          Nat.card (Z i) * (NZ i).index =
                            2 * (Nat.card (Z j) * (NZ j).index) :=
                        hfactor_i.trans hfactor_j.symm
                      have hzi_lt_four : Nat.card (Z i) < 4 := by
                        by_contra hnot
                        have hzi_ge_four : 4 ≤ Nat.card (Z i) := by omega
                        have hcoeff :
                            2 * Nat.card (Z j) ≤
                              Nat.card (Z i) * (Nat.card (Z j) - 1) := by
                          calc
                            2 * Nat.card (Z j) ≤
                                4 * (Nat.card (Z j) - 1) := by
                              have hzj := hnontrivial j
                              omega
                            _ ≤ Nat.card (Z i) * (Nat.card (Z j) - 1) :=
                              Nat.mul_le_mul_right (Nat.card (Z j) - 1) hzi_ge_four
                        have hbad :
                            2 * (Nat.card (Z j) * (NZ j).index) <
                              2 * (Nat.card (Z j) * (NZ j).index) := by
                          calc
                            2 * (Nat.card (Z j) * (NZ j).index) =
                                (2 * Nat.card (Z j)) * (NZ j).index := by ring
                            _ ≤ (Nat.card (Z i) * (Nat.card (Z j) - 1)) *
                                (NZ j).index :=
                              Nat.mul_le_mul_right (NZ j).index hcoeff
                            _ = Nat.card (Z i) *
                                ((Nat.card (Z j) - 1) * (NZ j).index) := by ring
                            _ < Nat.card (Z i) * (NZ i).index :=
                              (Nat.mul_lt_mul_left (by omega : 0 < Nat.card (Z i))).2
                                hterm_lt
                            _ = 2 * (Nat.card (Z j) * (NZ j).index) := hfactor_eq
                        exact (Nat.lt_irrefl _ hbad).elim
                      have hzi_three : Nat.card (Z i) = 3 := by omega
                      have hfactor_eq_three :
                          3 * (NZ i).index =
                            2 * (Nat.card (Z j) * (NZ j).index) := by
                        calc
                          3 * (NZ i).index = Nat.card (Z i) * (NZ i).index :=
                            congrArg (fun a => a * (NZ i).index) hzi_three.symm
                          _ = 2 * (Nat.card (Z j) * (NZ j).index) := hfactor_eq
                      have hzj_two : Nat.card (Z j) = 2 := by
                        by_contra hzj_ne_two
                        have hzj_ge_three : 3 ≤ Nat.card (Z j) := by
                          have hzj := hnontrivial j
                          omega
                        have hcoeff :
                            2 * Nat.card (Z j) ≤
                              3 * (Nat.card (Z j) - 1) := by omega
                        have hbad :
                            2 * (Nat.card (Z j) * (NZ j).index) <
                              2 * (Nat.card (Z j) * (NZ j).index) := by
                          calc
                            2 * (Nat.card (Z j) * (NZ j).index) =
                                (2 * Nat.card (Z j)) * (NZ j).index := by ring
                            _ ≤ (3 * (Nat.card (Z j) - 1)) * (NZ j).index :=
                              Nat.mul_le_mul_right (NZ j).index hcoeff
                            _ = 3 * ((Nat.card (Z j) - 1) * (NZ j).index) := by ring
                            _ < 3 * (NZ i).index :=
                              (Nat.mul_lt_mul_left (by norm_num : 0 < 3)).2 hterm_lt
                            _ = 2 * (Nat.card (Z j) * (NZ j).index) :=
                              hfactor_eq_three
                        exact (Nat.lt_irrefl _ hbad).elim
                      have hindex' : (NZ i).index = 1 + (NZ j).index := by
                        simpa [hzj_two] using hindex_eq
                      have hfactor' : 3 * (NZ i).index = 4 * (NZ j).index := by
                        calc
                          3 * (NZ i).index =
                              2 * (Nat.card (Z j) * (NZ j).index) :=
                            hfactor_eq_three
                          _ = 4 * (NZ j).index := by rw [hzj_two]; ring
                      have hkj_three : (NZ j).index = 3 := by omega
                      have hki_four : (NZ i).index = 4 := by omega
                      have hHcard12 : Nat.card H = 12 := by
                        calc
                          Nat.card H = Nat.card (Z i) * (NZ i).index :=
                            hfactor_i.symm
                          _ = 12 := by rw [hzi_three, hki_four]
                      have hZiIndex4 : (Z i).index = 4 := by
                        have hmul := (Z i).card_mul_index
                        rw [hzi_three, hHcard12] at hmul
                        omega
                      let hZiP : IsPGroup 3 (Z i) :=
                        IsPGroup.of_card (n := 1) (by simpa using hzi_three)
                      let Q : Sylow 3 H := hZiP.toSylow (by
                        rw [hZiIndex4]
                        norm_num)
                      have hSylow4 : Nat.card (Sylow 3 H) = 4 := by
                        calc
                          Nat.card (Sylow 3 H) =
                              (Subgroup.normalizer (Q : Set H)).index :=
                            Q.card_eq_index_normalizer
                          _ = (NZ i).index := by rfl
                          _ = 4 := hki_four
                      exact
                        huppert_II_8_17_b_order_twelve_four_sylow_three
                          hHcard12 hSylow4
                    exact Or.inr hA4_case
                have hs0_cases : s 0 = 1 ∨ s 0 = 2 := by
                  have h := hs 0
                  omega
                have hs1_cases : s 1 = 1 ∨ s 1 = 2 := by
                  have h := hs 1
                  omega
                rcases hs0_cases with hs0 | hs0 <;>
                  rcases hs1_cases with hs1 | hs1
                · exact (hnot_one_one hs0 hs1).elim
                · rcases hmixed 0 1 (by decide) hs0 hs1 with hdih | hA4
                  · exact Or.inr (Or.inl hdih)
                  · exact Or.inr (Or.inr (Or.inl hA4))
                · rcases hmixed 1 0 (by decide) hs1 hs0 with hdih | hA4
                  · exact Or.inr (Or.inl hdih)
                  · exact Or.inr (Or.inr (Or.inl hA4))
                · exact (hnot_two_two hs0 hs1).elim
              exact h824_two_shape
            · have hr_three : r = 3 := by omega
              have h824_three_shape :
                  (∃ z : ℕ,
                    ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                      (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                    Nat.card H = z ∧ IsCyclic H) ∨
                  (∃ z : ℕ,
                    ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                      (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                    Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
                  Nonempty (H ≃* alternatingGroup (Fin 4)) ∨
                  Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
                  Nonempty (H ≃* alternatingGroup (Fin 5)) := by
                subst r
                have hs_all_two : ∀ i, s i = 2 := by
                  have hcount :
                      Nat.card H =
                        1 + (Nat.card (Z 0) - 1) * (NZ 0).index +
                          (Nat.card (Z 1) - 1) * (NZ 1).index +
                            (Nat.card (Z 2) - 1) * (NZ 2).index := by
                    simpa [add_assoc] using h824_partition_count
                  have hquarter (a : Fin 3) :
                      Nat.card H ≤
                        4 * ((Nat.card (Z a) - 1) * (NZ a).index) := by
                    have hzbound :
                        Nat.card (Z a) * s a ≤ 4 * (Nat.card (Z a) - 1) := by
                      calc
                        Nat.card (Z a) * s a ≤ Nat.card (Z a) * 2 :=
                          Nat.mul_le_mul_left (Nat.card (Z a)) (hs a).2
                        _ ≤ (2 * (Nat.card (Z a) - 1)) * 2 :=
                          Nat.mul_le_mul_right 2 (by
                            have hza := hnontrivial a
                            omega)
                        _ = 4 * (Nat.card (Z a) - 1) := by ring
                    calc
                      Nat.card H =
                          (Nat.card (Z a) * s a) * (NZ a).index :=
                        (h824_z_index_factor a).symm
                      _ ≤ (4 * (Nat.card (Z a) - 1)) * (NZ a).index :=
                        Nat.mul_le_mul_right (NZ a).index hzbound
                      _ = 4 * ((Nat.card (Z a) - 1) * (NZ a).index) := by ring
                  have hhalf (a : Fin 3) (hsa : s a = 1) :
                      2 * Nat.card H ≤
                        4 * ((Nat.card (Z a) - 1) * (NZ a).index) := by
                    have hfactor :
                        Nat.card (Z a) * (NZ a).index = Nat.card H := by
                      simpa [hsa] using h824_z_index_factor a
                    have hzbound :
                        Nat.card (Z a) ≤ 2 * (Nat.card (Z a) - 1) := by
                      have hza := hnontrivial a
                      omega
                    have hle :
                        Nat.card H ≤
                          2 * ((Nat.card (Z a) - 1) * (NZ a).index) := by
                      calc
                        Nat.card H = Nat.card (Z a) * (NZ a).index :=
                          hfactor.symm
                        _ ≤ (2 * (Nat.card (Z a) - 1)) * (NZ a).index :=
                          Nat.mul_le_mul_right (NZ a).index hzbound
                        _ = 2 * ((Nat.card (Z a) - 1) * (NZ a).index) := by ring
                    calc
                      2 * Nat.card H ≤
                          2 * (2 * ((Nat.card (Z a) - 1) * (NZ a).index)) :=
                        Nat.mul_le_mul_left 2 hle
                      _ = 4 * ((Nat.card (Z a) - 1) * (NZ a).index) := by ring
                  intro i
                  have hsi := hs i
                  rcases (show s i = 1 ∨ s i = 2 by omega) with hsi_one | hsi_two
                  · exfalso
                    fin_cases i
                    · have hh := hhalf 0 hsi_one
                      have hq1 := hquarter 1
                      have hq2 := hquarter 2
                      omega
                    · have hq0 := hquarter 0
                      have hh := hhalf 1 hsi_one
                      have hq2 := hquarter 2
                      omega
                    · have hq0 := hquarter 0
                      have hq1 := hquarter 1
                      have hh := hhalf 2 hsi_one
                      omega
                  · exact hsi_two
                have hordered (i j k : Fin 3)
                    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
                    (hji : Nat.card (Z j) ≤ Nat.card (Z i))
                    (hkj : Nat.card (Z k) ≤ Nat.card (Z j)) :
                    (∃ z : ℕ,
                      ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                        (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                      Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
                    Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
                    Nonempty (H ≃* alternatingGroup (Fin 5)) := by
                  have hsum :
                      (∑ a, (Nat.card (Z a) - 1) * (NZ a).index) =
                        (Nat.card (Z i) - 1) * (NZ i).index +
                          (Nat.card (Z j) - 1) * (NZ j).index +
                            (Nat.card (Z k) - 1) * (NZ k).index := by
                    have huniv :
                        ({i, j, k} : Finset (Fin 3)) = Finset.univ := by
                      apply (Finset.card_eq_iff_eq_univ ({i, j, k} : Finset (Fin 3))).mp
                      simp [hij, hik, hjk, Ne.symm]
                    calc
                      (∑ a, (Nat.card (Z a) - 1) * (NZ a).index) =
                          ∑ a ∈ ({i, j, k} : Finset (Fin 3)),
                            (Nat.card (Z a) - 1) * (NZ a).index := by
                              rw [huniv]
                      _ = (Nat.card (Z i) - 1) * (NZ i).index +
                          (Nat.card (Z j) - 1) * (NZ j).index +
                            (Nat.card (Z k) - 1) * (NZ k).index := by
                              simp [hij, hik, hjk, Ne.symm, add_assoc]
                  have hcount :
                      Nat.card H =
                        1 + (Nat.card (Z i) - 1) * (NZ i).index +
                          (Nat.card (Z j) - 1) * (NZ j).index +
                            (Nat.card (Z k) - 1) * (NZ k).index := by
                    calc
                      Nat.card H =
                          1 + ∑ a, (Nat.card (Z a) - 1) * (NZ a).index :=
                        h824_partition_count
                      _ = 1 + (Nat.card (Z i) - 1) * (NZ i).index +
                          (Nat.card (Z j) - 1) * (NZ j).index +
                            (Nat.card (Z k) - 1) * (NZ k).index := by
                        rw [hsum]
                        simp [add_assoc]
                  have hfactor (a : Fin 3) :
                      2 * (Nat.card (Z a) * (NZ a).index) = Nat.card H := by
                    calc
                      2 * (Nat.card (Z a) * (NZ a).index) =
                          (Nat.card (Z a) * 2) * (NZ a).index := by ring
                      _ = (Nat.card (Z a) * s a) * (NZ a).index :=
                        congrArg (fun b =>
                          (Nat.card (Z a) * b) * (NZ a).index)
                          (hs_all_two a).symm
                      _ = Nat.card H := h824_z_index_factor a
                  have hqj :
                      Nat.card (Z i) * (NZ i).index =
                        Nat.card (Z j) * (NZ j).index := by
                    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
                    exact (hfactor i).trans (hfactor j).symm
                  have hqk :
                      Nat.card (Z i) * (NZ i).index =
                        Nat.card (Z k) * (NZ k).index := by
                    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
                    exact (hfactor i).trans (hfactor k).symm
                  have hrel (a : Fin 3) :
                      (Nat.card (Z a) - 1) * (NZ a).index + (NZ a).index =
                        Nat.card (Z a) * (NZ a).index := by
                    calc
                      (Nat.card (Z a) - 1) * (NZ a).index + (NZ a).index =
                          (Nat.card (Z a) - 1 + 1) * (NZ a).index := by ring
                      _ = Nat.card (Z a) * (NZ a).index := by
                        rw [Nat.sub_add_cancel (hnontrivial a).le]
                  have hindex_sum :
                      (NZ i).index + (NZ j).index + (NZ k).index =
                        Nat.card (Z i) * (NZ i).index + 1 := by
                    have hri := hrel i
                    have hrj :
                        (Nat.card (Z j) - 1) * (NZ j).index + (NZ j).index =
                          Nat.card (Z i) * (NZ i).index :=
                      (hrel j).trans hqj.symm
                    have hrk :
                        (Nat.card (Z k) - 1) * (NZ k).index + (NZ k).index =
                          Nat.card (Z i) * (NZ i).index :=
                      (hrel k).trans hqk.symm
                    have htwice :
                        2 * (Nat.card (Z i) * (NZ i).index) =
                          1 + (Nat.card (Z i) - 1) * (NZ i).index +
                            (Nat.card (Z j) - 1) * (NZ j).index +
                              (Nat.card (Z k) - 1) * (NZ k).index :=
                      (hfactor i).trans hcount
                    omega
                  have hclassification :
                      (∃ z : ℕ,
                        ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                          (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                        Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
                      Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
                      Nonempty (H ≃* alternatingGroup (Fin 5)) := by
                    have hki_le_kj : (NZ i).index ≤ (NZ j).index := by
                      by_contra hnot
                      have hlt : (NZ j).index < (NZ i).index := by omega
                      have hprod_lt :
                          Nat.card (Z j) * (NZ j).index <
                            Nat.card (Z i) * (NZ i).index := by
                        calc
                          Nat.card (Z j) * (NZ j).index ≤
                              Nat.card (Z i) * (NZ j).index :=
                            Nat.mul_le_mul_right (NZ j).index hji
                          _ < Nat.card (Z i) * (NZ i).index :=
                            (Nat.mul_lt_mul_left
                              (Nat.card_pos (α := Z i))).2 hlt
                      exact (Nat.lt_irrefl _ (hprod_lt.trans_eq hqj)).elim
                    have hqjk :
                        Nat.card (Z j) * (NZ j).index =
                          Nat.card (Z k) * (NZ k).index :=
                      hqj.symm.trans hqk
                    have hkj_le_kk : (NZ j).index ≤ (NZ k).index := by
                      by_contra hnot
                      have hlt : (NZ k).index < (NZ j).index := by omega
                      have hprod_lt :
                          Nat.card (Z k) * (NZ k).index <
                            Nat.card (Z j) * (NZ j).index := by
                        calc
                          Nat.card (Z k) * (NZ k).index ≤
                              Nat.card (Z j) * (NZ k).index :=
                            Nat.mul_le_mul_right (NZ k).index hkj
                          _ < Nat.card (Z j) * (NZ j).index :=
                            (Nat.mul_lt_mul_left
                              (Nat.card_pos (α := Z j))).2 hlt
                      exact (Nat.lt_irrefl _ (hprod_lt.trans_eq hqjk)).elim
                    have hzk_two : Nat.card (Z k) = 2 := by
                      by_contra hne
                      have hzk_ge_three : 3 ≤ Nat.card (Z k) := by
                        have hzk := hnontrivial k
                        omega
                      have hsum_le :
                          (NZ i).index + (NZ j).index + (NZ k).index ≤
                            3 * (NZ k).index := by omega
                      have hthree_le :
                          3 * (NZ k).index ≤
                            Nat.card (Z i) * (NZ i).index := by
                        calc
                          3 * (NZ k).index ≤
                              Nat.card (Z k) * (NZ k).index :=
                            Nat.mul_le_mul_right (NZ k).index hzk_ge_three
                          _ = Nat.card (Z i) * (NZ i).index := hqk.symm
                      omega
                    have hzj_lt_four : Nat.card (Z j) < 4 := by
                      by_contra hnot
                      have hzj_ge_four : 4 ≤ Nat.card (Z j) := by omega
                      have hfour_le :
                          4 * (NZ j).index ≤
                            Nat.card (Z i) * (NZ i).index := by
                        calc
                          4 * (NZ j).index ≤
                              Nat.card (Z j) * (NZ j).index :=
                            Nat.mul_le_mul_right (NZ j).index hzj_ge_four
                          _ = Nat.card (Z i) * (NZ i).index := hqj.symm
                      have htwo_kj_le_kk :
                          2 * (NZ j).index ≤ (NZ k).index := by
                        have hqk_two :
                            Nat.card (Z i) * (NZ i).index =
                              2 * (NZ k).index := by
                          calc
                            Nat.card (Z i) * (NZ i).index =
                                Nat.card (Z k) * (NZ k).index := hqk
                            _ = 2 * (NZ k).index := by rw [hzk_two]
                        omega
                      have hsum_le :
                          (NZ i).index + (NZ j).index + (NZ k).index ≤
                            2 * (NZ k).index := by omega
                      have hqk_two :
                          Nat.card (Z i) * (NZ i).index =
                            2 * (NZ k).index := by
                        calc
                          Nat.card (Z i) * (NZ i).index =
                              Nat.card (Z k) * (NZ k).index := hqk
                          _ = 2 * (NZ k).index := by rw [hzk_two]
                      omega
                    have hzj_cases :
                        Nat.card (Z j) = 2 ∨ Nat.card (Z j) = 3 := by
                      have hzj_ge_two : 2 ≤ Nat.card (Z j) := by
                        have hzj := hnontrivial j
                        omega
                      omega
                    rcases hzj_cases with hzj_two | hzj_three
                    · have hdihedral_ordered :
                          ∃ z : ℕ,
                            ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                              (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                            Nat.card H = 2 * z ∧
                              Nonempty (H ≃* DihedralGroup z) := by
                        have hkj_eq_kk : (NZ j).index = (NZ k).index := by
                          have htwo_kj_eq_two_kk :
                              2 * (NZ j).index = 2 * (NZ k).index := by
                            calc
                              2 * (NZ j).index =
                                  Nat.card (Z j) * (NZ j).index := by
                                rw [hzj_two]
                              _ = Nat.card (Z k) * (NZ k).index := hqjk
                              _ = 2 * (NZ k).index := by rw [hzk_two]
                          omega
                        have hki_one : (NZ i).index = 1 := by
                          have htwo_kj :
                              2 * (NZ j).index =
                                Nat.card (Z i) * (NZ i).index := by
                            calc
                              2 * (NZ j).index =
                                  Nat.card (Z j) * (NZ j).index := by
                                rw [hzj_two]
                              _ = Nat.card (Z i) * (NZ i).index := hqj.symm
                          omega
                        have hHcard :
                            Nat.card H = 2 * Nat.card (Z i) := by
                          calc
                            Nat.card H =
                                2 * (Nat.card (Z i) * (NZ i).index) :=
                              (hfactor i).symm
                            _ = 2 * Nat.card (Z i) := by rw [hki_one, mul_one]
                        have hNZtop : NZ i = ⊤ :=
                          Subgroup.index_eq_one.mp hki_one
                        obtain ⟨eD⟩ := hdihedral i (hs_all_two i)
                        let eH : NZ i ≃* H :=
                          (MulEquiv.subgroupCongr hNZtop).trans
                            (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H)
                        exact
                          ⟨Nat.card (Z i), hdivides i, hHcard,
                            ⟨eH.symm.trans eD⟩⟩
                      exact Or.inl hdihedral_ordered
                    · have hexceptional :
                          Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
                            Nonempty (H ≃* alternatingGroup (Fin 5)) := by
                        have hzi_lt_six : Nat.card (Z i) < 6 := by
                          by_contra hnot
                          have hzi_ge_six : 6 ≤ Nat.card (Z i) := by omega
                          have hsix_le_q :
                              6 * (NZ i).index ≤
                                Nat.card (Z i) * (NZ i).index :=
                            Nat.mul_le_mul_right (NZ i).index hzi_ge_six
                          have hthree_j :
                              3 * (NZ j).index =
                                Nat.card (Z i) * (NZ i).index := by
                            calc
                              3 * (NZ j).index =
                                  Nat.card (Z j) * (NZ j).index := by
                                rw [hzj_three]
                              _ = Nat.card (Z i) * (NZ i).index := hqj.symm
                          have htwo_k :
                              2 * (NZ k).index =
                                Nat.card (Z i) * (NZ i).index := by
                            calc
                              2 * (NZ k).index =
                                  Nat.card (Z k) * (NZ k).index := by
                                rw [hzk_two]
                              _ = Nat.card (Z i) * (NZ i).index := hqk.symm
                          omega
                        have hzi_cases :
                            Nat.card (Z i) = 3 ∨ Nat.card (Z i) = 4 ∨
                              Nat.card (Z i) = 5 := by
                          have hzi_ge_three : 3 ≤ Nat.card (Z i) := by
                            rw [← hzj_three]
                            exact hji
                          omega
                        rcases hzi_cases with hzi_three | hzi_four | hzi_five
                        · have hindices_three :
                              (NZ i).index = 2 ∧ (NZ j).index = 2 ∧
                                (NZ k).index = 3 := by
                            have hijq := hqj
                            have hikq := hqk
                            have hsumq := hindex_sum
                            rw [hzi_three, hzj_three] at hijq
                            rw [hzi_three, hzk_two] at hikq
                            rw [hzi_three] at hsumq
                            omega
                          have hHcard12 : Nat.card H = 12 := by
                            calc
                              Nat.card H =
                                  2 * (Nat.card (Z i) * (NZ i).index) :=
                                (hfactor i).symm
                              _ = 12 := by rw [hzi_three, hindices_three.1]
                          have hZiIndex4 : (Z i).index = 4 := by
                            have hmul := (Z i).card_mul_index
                            rw [hzi_three, hHcard12] at hmul
                            omega
                          have hZjIndex4 : (Z j).index = 4 := by
                            have hmul := (Z j).card_mul_index
                            rw [hzj_three, hHcard12] at hmul
                            omega
                          let hZiP : IsPGroup 3 (Z i) :=
                            IsPGroup.of_card (n := 1) (by simpa using hzi_three)
                          let hZjP : IsPGroup 3 (Z j) :=
                            IsPGroup.of_card (n := 1) (by simpa using hzj_three)
                          let Qi : Sylow 3 H := hZiP.toSylow (by
                            rw [hZiIndex4]
                            norm_num)
                          let Qj : Sylow 3 H := hZjP.toSylow (by
                            rw [hZjIndex4]
                            norm_num)
                          obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Qi Qj
                          have hconj :
                              (Z i).map (MulAut.conj g).toMonoidHom = Z j := by
                            have hg' := congrArg
                              (fun Q : Sylow 3 H => (Q : Subgroup H)) hg
                            exact hg'
                          exact (hij (hdistinct i j g hconj)).elim
                        · left
                          have hindices_four :
                              (NZ i).index = 3 ∧ (NZ j).index = 4 ∧
                                (NZ k).index = 6 := by
                            have hijq := hqj
                            have hikq := hqk
                            have hsumq := hindex_sum
                            rw [hzi_four, hzj_three] at hijq
                            rw [hzi_four, hzk_two] at hikq
                            rw [hzi_four] at hsumq
                            omega
                          have hHcard24 : Nat.card H = 24 := by
                            calc
                              Nat.card H =
                                  2 * (Nat.card (Z i) * (NZ i).index) :=
                                (hfactor i).symm
                              _ = 24 := by rw [hzi_four, hindices_four.1]
                          have hZjIndex8 : (Z j).index = 8 := by
                            have hmul := (Z j).card_mul_index
                            rw [hzj_three, hHcard24] at hmul
                            omega
                          let hZjP : IsPGroup 3 (Z j) :=
                            IsPGroup.of_card (n := 1) (by simpa using hzj_three)
                          let Q : Sylow 3 H := hZjP.toSylow (by
                            rw [hZjIndex8]
                            norm_num)
                          have hSylow4 : Nat.card (Sylow 3 H) = 4 := by
                            calc
                              Nat.card (Sylow 3 H) =
                                  (Subgroup.normalizer (Q : Set H)).index :=
                                Q.card_eq_index_normalizer
                              _ = (NZ j).index := by rfl
                              _ = 4 := hindices_four.2.1
                          let Ω := Sylow 3 H
                          letI := Fintype.ofFinite Ω
                          have hΩcard : Fintype.card Ω = 4 := by
                            simpa [Ω, Nat.card_eq_fintype_card] using hSylow4
                          let act := MulAction.toPermHom H Ω
                          have hact_inj : Function.Injective act := by
                            rw [← MonoidHom.ker_eq_bot_iff]
                            have hker_le_normalizer (R : Sylow 3 H) :
                                act.ker ≤ Subgroup.normalizer (R : Set H) := by
                              intro x hx
                              have hxperm : act x = 1 := hx
                              have hxfix : x • R = R := by
                                have h := DFunLike.congr_fun hxperm R
                                simpa [act] using h
                              exact Sylow.smul_eq_iff_mem_normalizer.mp hxfix
                            have hnormalizer_card_six :
                                Nat.card (Subgroup.normalizer (Q : Set H)) = 6 := by
                              have hQindex :
                                  (Subgroup.normalizer (Q : Set H)).index = 4 := by
                                calc
                                  (Subgroup.normalizer (Q : Set H)).index =
                                      Nat.card (Sylow 3 H) :=
                                    Q.card_eq_index_normalizer.symm
                                  _ = 4 := hSylow4
                              have hmul :=
                                (Subgroup.normalizer (Q : Set H)).card_mul_index
                              rw [hQindex, hHcard24] at hmul
                              omega
                            have hker_card_dvd_six : Nat.card act.ker ∣ 6 := by
                              simpa [hnormalizer_card_six] using
                                Subgroup.card_dvd_of_le (hker_le_normalizer Q)
                            have hno_sylow_le_ker (R : Sylow 3 H) :
                                ¬ (R : Subgroup H) ≤ act.ker := by
                              intro hRker
                              obtain ⟨S, hSR⟩ :=
                                Fintype.exists_ne_of_one_lt_card
                                  (by omega : 1 < Fintype.card Ω) R
                              have hRnormalizesS :
                                  (R : Subgroup H) ≤
                                    Subgroup.normalizer (S : Set H) := by
                                intro x hx
                                exact hker_le_normalizer S (hRker hx)
                              have hsupP :
                                  IsPGroup 3
                                    ((R : Subgroup H) ⊔ (S : Subgroup H) :
                                      Subgroup H) :=
                                R.isPGroup'.to_sup_of_normal_right'
                                  S.isPGroup' hRnormalizesS
                              have hsup_eq :
                                  (R : Subgroup H) ⊔ (S : Subgroup H) = S :=
                                S.is_maximal' hsupP le_sup_right
                              have hRleS : (R : Subgroup H) ≤ S := by
                                calc
                                  (R : Subgroup H) ≤
                                      (R : Subgroup H) ⊔ (S : Subgroup H) :=
                                    le_sup_left
                                  _ = S := hsup_eq
                              have hS_eq_R : (S : Subgroup H) = R :=
                                R.is_maximal' S.isPGroup' hRleS
                              exact hSR (Sylow.ext hS_eq_R)
                            have hthree_not_dvd_ker : ¬ 3 ∣ Nat.card act.ker := by
                              intro hthree
                              obtain ⟨x, hxorder⟩ :=
                                exists_prime_orderOf_dvd_card' 3 hthree
                              have hxHorder : orderOf (x : H) = 3 :=
                                (Subgroup.orderOf_coe x).trans hxorder
                              have hXisP :
                                  IsPGroup 3 (Subgroup.zpowers (x : H)) :=
                                IsPGroup.of_card
                                  (((Nat.card_zpowers (x : H)).trans hxHorder).trans
                                    (pow_one 3).symm)
                              obtain ⟨R, hXR⟩ := hXisP.exists_le_sylow
                              have hXcard :
                                  Nat.card (Subgroup.zpowers (x : H)) = 3 :=
                                (Nat.card_zpowers (x : H)).trans hxHorder
                              have hRcard : Nat.card R = 3 := by
                                calc
                                  Nat.card R = Nat.card Q :=
                                    Nat.card_congr (Sylow.equiv R Q).toEquiv
                                  _ = 3 := by
                                    change Nat.card (Z j) = 3
                                    exact hzj_three
                              have hXR_eq :
                                  Subgroup.zpowers (x : H) = (R : Subgroup H) :=
                                Subgroup.eq_of_le_of_card_ge hXR (by
                                  rw [hXcard, hRcard])
                              apply hno_sylow_le_ker R
                              rw [← hXR_eq]
                              intro y hy
                              rcases hy with ⟨n, rfl⟩
                              exact act.ker.zpow_mem x.2 n
                            have hker_card_cases :
                                Nat.card act.ker = 1 ∨ Nat.card act.ker = 2 := by
                              have hpos : 0 < Nat.card act.ker := Nat.card_pos
                              have hle : Nat.card act.ker ≤ 6 :=
                                Nat.le_of_dvd (by norm_num) hker_card_dvd_six
                              interval_cases Nat.card act.ker <;> norm_num at *
                            rcases hker_card_cases with hker_one | hker_two
                            · exact Subgroup.card_eq_one.mp hker_one
                            · have horder_six : ∃ x : H, orderOf x = 6 := by
                                obtain ⟨y, hyorder⟩ :=
                                  exists_prime_orderOf_dvd_card' 3 (by
                                    rw [hzj_three])
                                have hyHorder : orderOf (y : H) = 3 :=
                                  (Subgroup.orderOf_coe y).trans hyorder
                                obtain ⟨c, hcorder⟩ :=
                                  exists_prime_orderOf_dvd_card' 2 (by
                                    rw [hker_two])
                                have hcne : c ≠ 1 := by
                                  intro hc
                                  rw [hc, orderOf_one] at hcorder
                                  norm_num at hcorder
                                obtain ⟨c', hc'ne, hc'unique⟩ :=
                                  (Nat.card_eq_two_iff' (1 : act.ker)).mp hker_two
                                have hc_eq : c = c' := hc'unique c hcne
                                have hc_central :
                                    (c : H) ∈ Subgroup.center H := by
                                  rw [Subgroup.mem_center_iff]
                                  intro g
                                  let d : act.ker :=
                                    ⟨g * (c : H) * g⁻¹,
                                      (inferInstance : act.ker.Normal).conj_mem
                                        (c : H) c.2 g⟩
                                  have hdne : d ≠ 1 := by
                                    intro hd
                                    have hdval := congrArg Subtype.val hd
                                    change g * (c : H) * g⁻¹ = 1 at hdval
                                    apply hcne
                                    apply Subtype.ext
                                    calc
                                      (c : H) =
                                          g⁻¹ * (g * (c : H) * g⁻¹) * g := by
                                        group
                                      _ = 1 := by rw [hdval]; simp
                                  have hd_eq : d = c := by
                                    rw [hc_eq]
                                    exact hc'unique d hdne
                                  have hdval := congrArg Subtype.val hd_eq
                                  change g * (c : H) * g⁻¹ = (c : H) at hdval
                                  calc
                                    g * (c : H) =
                                        (g * (c : H) * g⁻¹) * g := by group
                                    _ = (c : H) * g := by rw [hdval]
                                have hcHorder : orderOf (c : H) = 2 :=
                                  (Subgroup.orderOf_coe c).trans hcorder
                                have hcomm : Commute (c : H) (y : H) :=
                                  (Subgroup.mem_center_iff.mp hc_central (y : H)).symm
                                have hcop :
                                    Nat.Coprime (orderOf (c : H))
                                      (orderOf (y : H)) := by
                                  rw [hcHorder, hyHorder]
                                  norm_num
                                refine ⟨(c : H) * (y : H), ?_⟩
                                rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop,
                                  hcHorder, hyHorder]
                              have hno_order_six : ∀ x : H, orderOf x ≠ 6 := by
                                intro x hxorder
                                have hxne : x ≠ 1 := by
                                  intro hx
                                  rw [hx, orderOf_one] at hxorder
                                  norm_num at hxorder
                                obtain ⟨A, hxA, _hAunique⟩ :=
                                  huppert_II_8_22_unique_family hFcard H Z
                                    hcyclic hnontrivial hcoprime hmaximal
                                    hrepresentative hdistinct x hxne
                                rcases A with Qp | z
                                · have hxdvd : orderOf x ∣ Nat.card Qp :=
                                    (Qp : Subgroup H).orderOf_dvd_natCard hxA
                                  have hQpcard : Nat.card Qp = 1 := by
                                    calc
                                      Nat.card Qp = Nat.card P :=
                                        Nat.card_congr (Sylow.equiv Qp P).toEquiv
                                      _ = 1 := by simpa using hPcard
                                  rw [hxorder, hQpcard] at hxdvd
                                  norm_num at hxdvd
                                · have hxdvd : orderOf x ∣ Nat.card z.2.1 :=
                                    z.2.1.orderOf_dvd_natCard hxA
                                  obtain ⟨g, hg⟩ := z.2.2
                                  have hzcard :
                                      Nat.card z.2.1 = Nat.card (Z z.1) := by
                                    rw [hg, Subgroup.card_map_of_injective
                                      (MulAut.conj g).injective]
                                  have huniv :
                                      ({i, j, k} : Finset (Fin 3)) = Finset.univ := by
                                    apply
                                      (Finset.card_eq_iff_eq_univ
                                        ({i, j, k} : Finset (Fin 3))).mp
                                    simp [hij, hik, hjk, Ne.symm]
                                  have hz_cases : z.1 = i ∨ z.1 = j ∨ z.1 = k := by
                                    have hzmem :
                                        z.1 ∈ ({i, j, k} : Finset (Fin 3)) := by
                                      rw [huniv]
                                      simp
                                    simpa [Finset.mem_insert, Finset.mem_singleton]
                                      using hzmem
                                  rw [hxorder, hzcard] at hxdvd
                                  rcases hz_cases with hzi | hzj | hzk
                                  · rw [hzi, hzi_four] at hxdvd
                                    norm_num at hxdvd
                                  · rw [hzj, hzj_three] at hxdvd
                                    norm_num at hxdvd
                                  · rw [hzk, hzk_two] at hxdvd
                                    norm_num at hxdvd
                              obtain ⟨x, hx⟩ := horder_six
                              exact (hno_order_six x hx).elim
                          let eΩ : Ω ≃ Fin 4 := Fintype.equivFinOfCardEq hΩcard
                          let actFin : H →* Equiv.Perm (Fin 4) :=
                            (Equiv.permCongrHom eΩ).toMonoidHom.comp act
                          have hactFin_inj : Function.Injective actFin := by
                            intro x y hxy
                            apply hact_inj
                            apply (Equiv.permCongrHom eΩ).injective
                            simpa [actFin] using hxy
                          let K : Subgroup (Equiv.Perm (Fin 4)) := actFin.range
                          have hrange_inj : Function.Injective actFin.rangeRestrict := by
                            intro x y hxy
                            exact hactFin_inj (congrArg Subtype.val hxy)
                          let eRange : H ≃* K :=
                            MulEquiv.ofBijective actFin.rangeRestrict
                              ⟨hrange_inj,
                                MonoidHom.rangeRestrict_surjective actFin⟩
                          have hKcard : Nat.card K = 24 := by
                            calc
                              Nat.card K = Nat.card H :=
                                (Nat.card_congr eRange.toEquiv).symm
                              _ = 24 := hHcard24
                          have hpermcard :
                              Nat.card (Equiv.Perm (Fin 4)) = 24 := by
                            norm_num [Fintype.card_perm, Nat.factorial]
                          have hKtop : K = ⊤ :=
                            Subgroup.eq_top_of_card_eq (H := K)
                              (hKcard.trans hpermcard.symm)
                          exact
                            ⟨eRange.trans (MulEquiv.subgroupCongr hKtop) |>.trans
                              (Subgroup.topEquiv :
                                (⊤ : Subgroup (Equiv.Perm (Fin 4))) ≃*
                                  Equiv.Perm (Fin 4))⟩
                        · right
                          have hindices_five :
                              (NZ i).index = 6 ∧ (NZ j).index = 10 ∧
                                (NZ k).index = 15 := by
                            have hijq := hqj
                            have hikq := hqk
                            have hsumq := hindex_sum
                            rw [hzi_five, hzj_three] at hijq
                            rw [hzi_five, hzk_two] at hikq
                            rw [hzi_five] at hsumq
                            omega
                          have hHcard60 : Nat.card H = 60 := by
                            calc
                              Nat.card H =
                                  2 * (Nat.card (Z i) * (NZ i).index) :=
                                (hfactor i).symm
                              _ = 60 := by rw [hzi_five, hindices_five.1]
                          have hZiIndex12 : (Z i).index = 12 := by
                            have hmul := (Z i).card_mul_index
                            rw [hzi_five, hHcard60] at hmul
                            omega
                          letI : Fact (Nat.Prime 5) := ⟨by decide⟩
                          let hZiP : IsPGroup 5 (Z i) :=
                            IsPGroup.of_card (n := 1) (by simpa using hzi_five)
                          let Q : Sylow 5 H := hZiP.toSylow (by
                            rw [hZiIndex12]
                            norm_num)
                          have hSylow6 : Nat.card (Sylow 5 H) = 6 := by
                            calc
                              Nat.card (Sylow 5 H) =
                                  (Subgroup.normalizer (Q : Set H)).index :=
                                Q.card_eq_index_normalizer
                              _ = (NZ i).index := by rfl
                              _ = 6 := hindices_five.1
                          let Ω := Sylow 5 H
                          letI := Fintype.ofFinite Ω
                          have hΩcard : Fintype.card Ω = 6 := by
                            simpa [Ω, Nat.card_eq_fintype_card] using hSylow6
                          let act := MulAction.toPermHom H Ω
                          have hact_inj : Function.Injective act := by
                            rw [← MonoidHom.ker_eq_bot_iff]
                            have hker_le_normalizer (R : Sylow 5 H) :
                                act.ker ≤ Subgroup.normalizer (R : Set H) := by
                              intro x hx
                              have hxperm : act x = 1 := hx
                              have hxfix : x • R = R := by
                                have h := DFunLike.congr_fun hxperm R
                                simpa [act] using h
                              exact Sylow.smul_eq_iff_mem_normalizer.mp hxfix
                            have hnormalizer_card_ten :
                                Nat.card (Subgroup.normalizer (Q : Set H)) = 10 := by
                              have hQindex :
                                  (Subgroup.normalizer (Q : Set H)).index = 6 := by
                                calc
                                  (Subgroup.normalizer (Q : Set H)).index =
                                      Nat.card (Sylow 5 H) :=
                                    Q.card_eq_index_normalizer.symm
                                  _ = 6 := hSylow6
                              have hmul :=
                                (Subgroup.normalizer (Q : Set H)).card_mul_index
                              rw [hQindex, hHcard60] at hmul
                              omega
                            have hker_card_dvd_ten : Nat.card act.ker ∣ 10 := by
                              simpa [hnormalizer_card_ten] using
                                Subgroup.card_dvd_of_le (hker_le_normalizer Q)
                            have hno_sylow_le_ker (R : Sylow 5 H) :
                                ¬ (R : Subgroup H) ≤ act.ker := by
                              intro hRker
                              obtain ⟨S, hSR⟩ :=
                                Fintype.exists_ne_of_one_lt_card
                                  (by omega : 1 < Fintype.card Ω) R
                              have hRnormalizesS :
                                  (R : Subgroup H) ≤
                                    Subgroup.normalizer (S : Set H) := by
                                intro x hx
                                exact hker_le_normalizer S (hRker hx)
                              have hsupP :
                                  IsPGroup 5
                                    ((R : Subgroup H) ⊔ (S : Subgroup H) :
                                      Subgroup H) :=
                                R.isPGroup'.to_sup_of_normal_right'
                                  S.isPGroup' hRnormalizesS
                              have hsup_eq :
                                  (R : Subgroup H) ⊔ (S : Subgroup H) = S :=
                                S.is_maximal' hsupP le_sup_right
                              have hRleS : (R : Subgroup H) ≤ S := by
                                calc
                                  (R : Subgroup H) ≤
                                      (R : Subgroup H) ⊔ (S : Subgroup H) :=
                                    le_sup_left
                                  _ = S := hsup_eq
                              have hS_eq_R : (S : Subgroup H) = R :=
                                R.is_maximal' S.isPGroup' hRleS
                              exact hSR (Sylow.ext hS_eq_R)
                            have hfive_not_dvd_ker : ¬ 5 ∣ Nat.card act.ker := by
                              intro hfive
                              obtain ⟨x, hxorder⟩ :=
                                exists_prime_orderOf_dvd_card' 5 hfive
                              have hxHorder : orderOf (x : H) = 5 :=
                                (Subgroup.orderOf_coe x).trans hxorder
                              have hXisP :
                                  IsPGroup 5 (Subgroup.zpowers (x : H)) :=
                                IsPGroup.of_card
                                  (((Nat.card_zpowers (x : H)).trans hxHorder).trans
                                    (pow_one 5).symm)
                              obtain ⟨R, hXR⟩ := hXisP.exists_le_sylow
                              have hXcard :
                                  Nat.card (Subgroup.zpowers (x : H)) = 5 :=
                                (Nat.card_zpowers (x : H)).trans hxHorder
                              have hRcard : Nat.card R = 5 := by
                                calc
                                  Nat.card R = Nat.card Q :=
                                    Nat.card_congr (Sylow.equiv R Q).toEquiv
                                  _ = 5 := by
                                    change Nat.card (Z i) = 5
                                    exact hzi_five
                              have hXR_eq :
                                  Subgroup.zpowers (x : H) = (R : Subgroup H) :=
                                Subgroup.eq_of_le_of_card_ge hXR (by
                                  rw [hXcard, hRcard])
                              apply hno_sylow_le_ker R
                              rw [← hXR_eq]
                              intro y hy
                              rcases hy with ⟨n, rfl⟩
                              exact act.ker.zpow_mem x.2 n
                            have hker_card_cases :
                                Nat.card act.ker = 1 ∨ Nat.card act.ker = 2 := by
                              have hpos : 0 < Nat.card act.ker := Nat.card_pos
                              have hle : Nat.card act.ker ≤ 10 :=
                                Nat.le_of_dvd (by norm_num) hker_card_dvd_ten
                              interval_cases Nat.card act.ker <;> norm_num at *
                            rcases hker_card_cases with hker_one | hker_two
                            · exact Subgroup.card_eq_one.mp hker_one
                            · have horder_ten : ∃ x : H, orderOf x = 10 := by
                                obtain ⟨y, hyorder⟩ :=
                                  exists_prime_orderOf_dvd_card' 5 (by
                                    rw [hzi_five])
                                have hyHorder : orderOf (y : H) = 5 :=
                                  (Subgroup.orderOf_coe y).trans hyorder
                                obtain ⟨c, hcorder⟩ :=
                                  exists_prime_orderOf_dvd_card' 2 (by
                                    rw [hker_two])
                                have hcne : c ≠ 1 := by
                                  intro hc
                                  rw [hc, orderOf_one] at hcorder
                                  norm_num at hcorder
                                obtain ⟨c', hc'ne, hc'unique⟩ :=
                                  (Nat.card_eq_two_iff' (1 : act.ker)).mp hker_two
                                have hc_eq : c = c' := hc'unique c hcne
                                have hc_central :
                                    (c : H) ∈ Subgroup.center H := by
                                  rw [Subgroup.mem_center_iff]
                                  intro g
                                  let d : act.ker :=
                                    ⟨g * (c : H) * g⁻¹,
                                      (inferInstance : act.ker.Normal).conj_mem
                                        (c : H) c.2 g⟩
                                  have hdne : d ≠ 1 := by
                                    intro hd
                                    have hdval := congrArg Subtype.val hd
                                    change g * (c : H) * g⁻¹ = 1 at hdval
                                    apply hcne
                                    apply Subtype.ext
                                    calc
                                      (c : H) =
                                          g⁻¹ * (g * (c : H) * g⁻¹) * g := by
                                        group
                                      _ = 1 := by rw [hdval]; simp
                                  have hd_eq : d = c := by
                                    rw [hc_eq]
                                    exact hc'unique d hdne
                                  have hdval := congrArg Subtype.val hd_eq
                                  change g * (c : H) * g⁻¹ = (c : H) at hdval
                                  calc
                                    g * (c : H) =
                                        (g * (c : H) * g⁻¹) * g := by group
                                    _ = (c : H) * g := by rw [hdval]
                                have hcHorder : orderOf (c : H) = 2 :=
                                  (Subgroup.orderOf_coe c).trans hcorder
                                have hcomm : Commute (c : H) (y : H) :=
                                  (Subgroup.mem_center_iff.mp hc_central (y : H)).symm
                                have hcop :
                                    Nat.Coprime (orderOf (c : H))
                                      (orderOf (y : H)) := by
                                  rw [hcHorder, hyHorder]
                                  norm_num
                                refine ⟨(c : H) * (y : H), ?_⟩
                                rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop,
                                  hcHorder, hyHorder]
                              have hno_order_ten : ∀ x : H, orderOf x ≠ 10 := by
                                intro x hxorder
                                have hxne : x ≠ 1 := by
                                  intro hx
                                  rw [hx, orderOf_one] at hxorder
                                  norm_num at hxorder
                                obtain ⟨A, hxA, _hAunique⟩ :=
                                  huppert_II_8_22_unique_family hFcard H Z
                                    hcyclic hnontrivial hcoprime hmaximal
                                    hrepresentative hdistinct x hxne
                                rcases A with Qp | z
                                · have hxdvd : orderOf x ∣ Nat.card Qp :=
                                    (Qp : Subgroup H).orderOf_dvd_natCard hxA
                                  have hQpcard : Nat.card Qp = 1 := by
                                    calc
                                      Nat.card Qp = Nat.card P :=
                                        Nat.card_congr (Sylow.equiv Qp P).toEquiv
                                      _ = 1 := by simpa using hPcard
                                  rw [hxorder, hQpcard] at hxdvd
                                  norm_num at hxdvd
                                · have hxdvd : orderOf x ∣ Nat.card z.2.1 :=
                                    z.2.1.orderOf_dvd_natCard hxA
                                  obtain ⟨g, hg⟩ := z.2.2
                                  have hzcard :
                                      Nat.card z.2.1 = Nat.card (Z z.1) := by
                                    rw [hg, Subgroup.card_map_of_injective
                                      (MulAut.conj g).injective]
                                  have huniv :
                                      ({i, j, k} : Finset (Fin 3)) = Finset.univ := by
                                    apply
                                      (Finset.card_eq_iff_eq_univ
                                        ({i, j, k} : Finset (Fin 3))).mp
                                    simp [hij, hik, hjk, Ne.symm]
                                  have hz_cases : z.1 = i ∨ z.1 = j ∨ z.1 = k := by
                                    have hzmem :
                                        z.1 ∈ ({i, j, k} : Finset (Fin 3)) := by
                                      rw [huniv]
                                      simp
                                    simpa [Finset.mem_insert, Finset.mem_singleton]
                                      using hzmem
                                  rw [hxorder, hzcard] at hxdvd
                                  rcases hz_cases with hzi | hzj | hzk
                                  · rw [hzi, hzi_five] at hxdvd
                                    norm_num at hxdvd
                                  · rw [hzj, hzj_three] at hxdvd
                                    norm_num at hxdvd
                                  · rw [hzk, hzk_two] at hxdvd
                                    norm_num at hxdvd
                              obtain ⟨x, hx⟩ := horder_ten
                              exact (hno_order_ten x hx).elim
                          have hA5_via_sylow_two :
                              Nonempty (H ≃* alternatingGroup (Fin 5)) := by
                            have hNZkcard4 : Nat.card (NZ k) = 4 := by
                              dsimp only [NZ]
                              rw [hnormalizerZ k, hzk_two, hs_all_two k]
                            letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
                            let hNZkP : IsPGroup 2 (NZ k) :=
                              IsPGroup.of_card (n := 2) (by
                                simpa using hNZkcard4)
                            let P2 : Sylow 2 H := hNZkP.toSylow (by
                              rw [hindices_five.2.2]
                              norm_num)
                            have hSylow2_data :
                                Nat.card (Sylow 2 H) = 5 ∧
                                  ∀ x : H, orderOf x = 2 →
                                    ∃! R : Sylow 2 H,
                                      x ∈ (R : Subgroup H) := by
                              have hSylow2card4 (R : Sylow 2 H) :
                                  Nat.card R = 4 := by
                                calc
                                  Nat.card R = Nat.card P2 :=
                                    Nat.card_congr (Sylow.equiv R P2).toEquiv
                                  _ = 4 := by
                                    change Nat.card (NZ k) = 4
                                    exact hNZkcard4
                              have hno_order_four :
                                  ∀ x : H, orderOf x ≠ 4 := by
                                intro x hxorder
                                have hxne : x ≠ 1 := by
                                  intro hx
                                  rw [hx, orderOf_one] at hxorder
                                  norm_num at hxorder
                                obtain ⟨A, hxA, _hAunique⟩ :=
                                  huppert_II_8_22_unique_family hFcard H Z
                                    hcyclic hnontrivial hcoprime hmaximal
                                    hrepresentative hdistinct x hxne
                                rcases A with Qp | z
                                · have hxdvd : orderOf x ∣ Nat.card Qp :=
                                    (Qp : Subgroup H).orderOf_dvd_natCard hxA
                                  have hQpcard : Nat.card Qp = 1 := by
                                    calc
                                      Nat.card Qp = Nat.card P :=
                                        Nat.card_congr (Sylow.equiv Qp P).toEquiv
                                      _ = 1 := by simpa using hPcard
                                  rw [hxorder, hQpcard] at hxdvd
                                  norm_num at hxdvd
                                · have hxdvd : orderOf x ∣ Nat.card z.2.1 :=
                                    z.2.1.orderOf_dvd_natCard hxA
                                  obtain ⟨g, hg⟩ := z.2.2
                                  have hzcard :
                                      Nat.card z.2.1 = Nat.card (Z z.1) := by
                                    rw [hg, Subgroup.card_map_of_injective
                                      (MulAut.conj g).injective]
                                  have huniv :
                                      ({i, j, k} : Finset (Fin 3)) = Finset.univ := by
                                    apply
                                      (Finset.card_eq_iff_eq_univ
                                        ({i, j, k} : Finset (Fin 3))).mp
                                    simp [hij, hik, hjk, Ne.symm]
                                  have hz_cases : z.1 = i ∨ z.1 = j ∨ z.1 = k := by
                                    have hzmem :
                                        z.1 ∈ ({i, j, k} : Finset (Fin 3)) := by
                                      rw [huniv]
                                      simp
                                    simpa [Finset.mem_insert, Finset.mem_singleton]
                                      using hzmem
                                  rw [hxorder, hzcard] at hxdvd
                                  rcases hz_cases with hzi | hzj | hzk
                                  · rw [hzi, hzi_five] at hxdvd
                                    norm_num at hxdvd
                                  · rw [hzj, hzj_three] at hxdvd
                                    norm_num at hxdvd
                                  · rw [hzk, hzk_two] at hxdvd
                                    norm_num at hxdvd
                              have hsylow2_order_two (R : Sylow 2 H)
                                  {x : H} (hxR : x ∈ (R : Subgroup H))
                                  (hxne : x ≠ 1) : orderOf x = 2 := by
                                have hdvd : orderOf x ∣ 4 := by
                                  simpa [hSylow2card4 R] using
                                    (R : Subgroup H).orderOf_dvd_natCard hxR
                                have hpos : 0 < orderOf x := orderOf_pos x
                                have hne_one : orderOf x ≠ 1 :=
                                  fun h => hxne (orderOf_eq_one_iff.mp h)
                                have hne_four : orderOf x ≠ 4 := hno_order_four x
                                have hle : orderOf x ≤ 4 :=
                                  Nat.le_of_dvd (by norm_num) hdvd
                                interval_cases orderOf x <;> norm_num at *
                              have hinvolution_unique_sylow (x : H)
                                  (hxorder : orderOf x = 2) :
                                  ∃! R : Sylow 2 H, x ∈ (R : Subgroup H) := by
                                have hxne : x ≠ 1 := by
                                  intro hx
                                  rw [hx, orderOf_one] at hxorder
                                  norm_num at hxorder
                                let X : Subgroup H := Subgroup.zpowers x
                                have hXcard : Nat.card X = 2 := by
                                  simpa [X] using
                                    (Nat.card_zpowers x).trans hxorder
                                have hXisP : IsPGroup 2 X :=
                                  IsPGroup.of_card (n := 1) (by simpa using hXcard)
                                obtain ⟨R, hXR⟩ := hXisP.exists_le_sylow
                                have hxR : x ∈ (R : Subgroup H) :=
                                  hXR (by exact Subgroup.mem_zpowers x)
                                have hnormalizerXcard4 :
                                    Nat.card (Subgroup.normalizer (X : Set H)) = 4 := by
                                  obtain ⟨A, hxA, _hAunique⟩ :=
                                    huppert_II_8_22_unique_family hFcard H Z
                                      hcyclic hnontrivial hcoprime hmaximal
                                      hrepresentative hdistinct x hxne
                                  rcases A with Qp | z
                                  · have hxdvd : orderOf x ∣ Nat.card Qp :=
                                      (Qp : Subgroup H).orderOf_dvd_natCard hxA
                                    have hQpcard : Nat.card Qp = 1 := by
                                      calc
                                        Nat.card Qp = Nat.card P :=
                                          Nat.card_congr (Sylow.equiv Qp P).toEquiv
                                        _ = 1 := by simpa using hPcard
                                    rw [hxorder, hQpcard] at hxdvd
                                    norm_num at hxdvd
                                  · have hxdvd : orderOf x ∣ Nat.card z.2.1 :=
                                      z.2.1.orderOf_dvd_natCard hxA
                                    obtain ⟨g, hg⟩ := z.2.2
                                    have hzcard :
                                        Nat.card z.2.1 = Nat.card (Z z.1) := by
                                      rw [hg, Subgroup.card_map_of_injective
                                        (MulAut.conj g).injective]
                                    have huniv :
                                        ({i, j, k} : Finset (Fin 3)) =
                                          Finset.univ := by
                                      apply
                                        (Finset.card_eq_iff_eq_univ
                                          ({i, j, k} : Finset (Fin 3))).mp
                                      simp [hij, hik, hjk, Ne.symm]
                                    have hz_cases :
                                        z.1 = i ∨ z.1 = j ∨ z.1 = k := by
                                      have hzmem :
                                          z.1 ∈ ({i, j, k} : Finset (Fin 3)) := by
                                        rw [huniv]
                                        simp
                                      simpa [Finset.mem_insert,
                                        Finset.mem_singleton] using hzmem
                                    rcases hz_cases with hza | hza | hza
                                    · rw [hxorder, hzcard, hza, hzi_five] at hxdvd
                                      norm_num at hxdvd
                                    · rw [hxorder, hzcard, hza, hzj_three] at hxdvd
                                      norm_num at hxdvd
                                    · have hgk :
                                          z.2.1 = (Z k).map
                                            (MulAut.conj g).toMonoidHom := by
                                        simpa [hza] using hg
                                      have hWcard : Nat.card z.2.1 = 2 := by
                                        rw [hzcard, hza, hzk_two]
                                      have hXeqW : X = z.2.1 :=
                                        Subgroup.eq_of_le_of_card_ge (by
                                          exact Subgroup.zpowers_le.2 hxA) (by
                                            rw [hXcard, hWcard])
                                      rw [hXeqW, hgk]
                                      rw [← Subgroup.map_normalizer_eq_of_bijective
                                        (Z k) (MulAut.conj g).bijective,
                                        Subgroup.card_map_of_injective
                                          (MulAut.conj g).injective]
                                      simpa [NZ] using hNZkcard4
                                have hSylow_eq_normalizer (S : Sylow 2 H)
                                    (hxS : x ∈ (S : Subgroup H)) :
                                    (S : Subgroup H) =
                                      Subgroup.normalizer (X : Set H) := by
                                  have hScard : Nat.card S = 2 ^ 2 := by
                                    norm_num [hSylow2card4 S]
                                  letI : CommGroup S :=
                                    IsPGroup.commGroupOfCardEqPrimeSq hScard
                                  have hXleS : X ≤ (S : Subgroup H) := by
                                    exact Subgroup.zpowers_le.2 hxS
                                  have hnormal :
                                      (X.subgroupOf (S : Subgroup H)).Normal :=
                                    inferInstance
                                  have hSle :
                                      (S : Subgroup H) ≤
                                        Subgroup.normalizer (X : Set H) :=
                                    (Subgroup.normal_subgroupOf_iff_le_normalizer
                                      hXleS).mp hnormal
                                  exact Subgroup.eq_of_le_of_card_ge hSle (by
                                    rw [hSylow2card4 S, hnormalizerXcard4])
                                refine ⟨R, hxR, ?_⟩
                                intro S hxS
                                apply Sylow.ext
                                exact (hSylow_eq_normalizer S hxS).trans
                                  (hSylow_eq_normalizer R hxR).symm
                              let Zodd : Fin 2 → Subgroup H := ![Z i, Z j]
                              have hunique2 : ∀ x : H, x ≠ 1 →
                                  ∃! A : (Sylow 2 H) ⊕
                                      (Σ a : Fin 2,
                                        {W : Subgroup H // ∃ g : H,
                                          W = (Zodd a).map
                                            (MulAut.conj g).toMonoidHom}),
                                    x ∈ match A with
                                      | Sum.inl R => (R : Subgroup H)
                                      | Sum.inr z => (z.2.1 : Subgroup H) := by
                                dsimp only
                                intro x hxne
                                obtain ⟨A, hxA, hAunique⟩ :=
                                  huppert_II_8_22_unique_family hFcard H Z
                                    hcyclic hnontrivial hcoprime hmaximal
                                    hrepresentative hdistinct x hxne
                                rcases A with Qp | z
                                · have hxdvd : orderOf x ∣ Nat.card Qp :=
                                    (Qp : Subgroup H).orderOf_dvd_natCard hxA
                                  have hQpcard : Nat.card Qp = 1 := by
                                    calc
                                      Nat.card Qp = Nat.card P :=
                                        Nat.card_congr (Sylow.equiv Qp P).toEquiv
                                      _ = 1 := by simpa using hPcard
                                  have hxorder_one : orderOf x = 1 :=
                                    Nat.eq_one_of_dvd_one (by
                                      simpa [hQpcard] using hxdvd)
                                  exact
                                    (hxne (orderOf_eq_one_iff.mp hxorder_one)).elim
                                · obtain ⟨g, hg⟩ := z.2.2
                                  have hzcard :
                                      Nat.card z.2.1 = Nat.card (Z z.1) := by
                                    rw [hg, Subgroup.card_map_of_injective
                                      (MulAut.conj g).injective]
                                  have huniv :
                                      ({i, j, k} : Finset (Fin 3)) =
                                        Finset.univ := by
                                    apply
                                      (Finset.card_eq_iff_eq_univ
                                        ({i, j, k} : Finset (Fin 3))).mp
                                    simp [hij, hik, hjk, Ne.symm]
                                  have hz_cases :
                                      z.1 = i ∨ z.1 = j ∨ z.1 = k := by
                                    have hzmem :
                                        z.1 ∈ ({i, j, k} : Finset (Fin 3)) := by
                                      rw [huniv]
                                      simp
                                    simpa [Finset.mem_insert,
                                      Finset.mem_singleton] using hzmem
                                  rcases hz_cases with hza | hza | hza
                                  · let W0 :
                                        {W : Subgroup H // ∃ g : H,
                                          W = (![Z i, Z j] 0).map
                                            (MulAut.conj g).toMonoidHom} :=
                                      ⟨z.2.1, by simpa [hza] using z.2.2⟩
                                    refine ⟨Sum.inr ⟨0, W0⟩, hxA, ?_⟩
                                    intro B hxB
                                    rcases B with R | ⟨b, V⟩
                                    · have hxorder : orderOf x = 2 :=
                                        hsylow2_order_two R hxB hxne
                                      have hxdvd :
                                          orderOf x ∣ Nat.card z.2.1 :=
                                        z.2.1.orderOf_dvd_natCard hxA
                                      rw [hxorder, hzcard, hza, hzi_five]
                                        at hxdvd
                                      norm_num at hxdvd
                                    · fin_cases b
                                      · let V0 :
                                            {W : Subgroup H // ∃ g : H,
                                              W = (Z i).map
                                                (MulAut.conj g).toMonoidHom} :=
                                          ⟨V.1, by simpa using V.2⟩
                                        have heq :=
                                          hAunique (Sum.inr ⟨i, V0⟩) hxB
                                        cases heq
                                        rfl
                                      · let V1 :
                                            {W : Subgroup H // ∃ g : H,
                                              W = (Z j).map
                                                (MulAut.conj g).toMonoidHom} :=
                                          ⟨V.1, by simpa using V.2⟩
                                        have heq :=
                                          hAunique (Sum.inr ⟨j, V1⟩) hxB
                                        have hjza : j = z.1 :=
                                          congrArg (fun C => match C with
                                            | Sum.inl _ => i
                                            | Sum.inr w => w.1) heq
                                        have hij' : j = i := hjza.trans hza
                                        exact (hij hij'.symm).elim
                                  · let W1 :
                                        {W : Subgroup H // ∃ g : H,
                                          W = (![Z i, Z j] 1).map
                                            (MulAut.conj g).toMonoidHom} :=
                                      ⟨z.2.1, by simpa [hza] using z.2.2⟩
                                    refine ⟨Sum.inr ⟨1, W1⟩, hxA, ?_⟩
                                    intro B hxB
                                    rcases B with R | ⟨b, V⟩
                                    · have hxorder : orderOf x = 2 :=
                                        hsylow2_order_two R hxB hxne
                                      have hxdvd :
                                          orderOf x ∣ Nat.card z.2.1 :=
                                        z.2.1.orderOf_dvd_natCard hxA
                                      rw [hxorder, hzcard, hza, hzj_three]
                                        at hxdvd
                                      norm_num at hxdvd
                                    · fin_cases b
                                      · let V0 :
                                            {W : Subgroup H // ∃ g : H,
                                              W = (Z i).map
                                                (MulAut.conj g).toMonoidHom} :=
                                          ⟨V.1, by simpa using V.2⟩
                                        have heq :=
                                          hAunique (Sum.inr ⟨i, V0⟩) hxB
                                        have hiza : i = z.1 :=
                                          congrArg (fun C => match C with
                                            | Sum.inl _ => j
                                            | Sum.inr w => w.1) heq
                                        have hji' : i = j := hiza.trans hza
                                        exact (hij hji').elim
                                      · let V1 :
                                            {W : Subgroup H // ∃ g : H,
                                              W = (Z j).map
                                                (MulAut.conj g).toMonoidHom} :=
                                          ⟨V.1, by simpa using V.2⟩
                                        have heq :=
                                          hAunique (Sum.inr ⟨j, V1⟩) hxB
                                        cases heq
                                        rfl
                                  · have hxdvd :
                                        orderOf x ∣ Nat.card z.2.1 :=
                                      z.2.1.orderOf_dvd_natCard hxA
                                    have hxorder : orderOf x = 2 := by
                                      have hpos : 0 < orderOf x := orderOf_pos x
                                      have hne_one : orderOf x ≠ 1 :=
                                        fun h => hxne (orderOf_eq_one_iff.mp h)
                                      have hdvd2 : orderOf x ∣ 2 := by
                                        simpa [hzcard, hza, hzk_two] using hxdvd
                                      have hle : orderOf x ≤ 2 :=
                                        Nat.le_of_dvd (by norm_num) hdvd2
                                      omega
                                    obtain ⟨R, hxR, hRunique⟩ :=
                                      hinvolution_unique_sylow x hxorder
                                    refine ⟨Sum.inl R, hxR, ?_⟩
                                    intro B hxB
                                    rcases B with S | ⟨b, V⟩
                                    · exact congrArg Sum.inl (hRunique S hxB)
                                    · fin_cases b
                                      · have hxdvdV :
                                            orderOf x ∣ Nat.card V.1 :=
                                          V.1.orderOf_dvd_natCard hxB
                                        obtain ⟨a, ha⟩ := V.2
                                        have hVcard :
                                            Nat.card V.1 = Nat.card (Z i) := by
                                          rw [ha, Subgroup.card_map_of_injective
                                            (MulAut.conj a).injective]
                                          simp [Zodd]
                                        rw [hxorder, hVcard, hzi_five] at hxdvdV
                                        norm_num at hxdvdV
                                      · have hxdvdV :
                                            orderOf x ∣ Nat.card V.1 :=
                                          V.1.orderOf_dvd_natCard hxB
                                        obtain ⟨a, ha⟩ := V.2
                                        have hVcard :
                                            Nat.card V.1 = Nat.card (Z j) := by
                                          rw [ha, Subgroup.card_map_of_injective
                                            (MulAut.conj a).injective]
                                          simp [Zodd]
                                        rw [hxorder, hVcard, hzj_three] at hxdvdV
                                        norm_num at hxdvdV
                              have hP2card : Nat.card P2 = 2 ^ 2 := by
                                change Nat.card (NZ k) = 2 ^ 2
                                norm_num [hNZkcard4]
                              have hcount2 :
                                  Nat.card H =
                                    1 + (2 ^ 2 - 1) *
                                        (Subgroup.normalizer (P2 : Set H)).index +
                                      ∑ a, (Nat.card (Zodd a) - 1) *
                                        (Subgroup.normalizer
                                          (Zodd a : Set H)).index := by
                                apply
                                  huppert_II_8_22_partition_count_of_unique_family
                                    P2 hP2card Zodd
                                intro x hx
                                convert hunique2 x hx using 1
                                funext A
                                rcases A with R | z <;> rfl
                              have hP2normalizer_index :
                                  (Subgroup.normalizer (P2 : Set H)).index =
                                    Nat.card (Sylow 2 H) :=
                                P2.card_eq_index_normalizer.symm
                              rw [hP2normalizer_index] at hcount2
                              simp [Zodd, Fin.sum_univ_two, NZ, hHcard60,
                                hzi_five, hzj_three, hindices_five.1,
                                hindices_five.2.1] at hcount2
                              constructor
                              · omega
                              · exact hinvolution_unique_sylow
                            have hSylow2card5 : Nat.card (Sylow 2 H) = 5 :=
                              hSylow2_data.1
                            have hinvolution_unique_sylow :
                                ∀ x : H, orderOf x = 2 →
                                  ∃! R : Sylow 2 H,
                                    x ∈ (R : Subgroup H) :=
                              hSylow2_data.2
                            let Ω2 := Sylow 2 H
                            letI := Fintype.ofFinite Ω2
                            have hΩ2card : Fintype.card Ω2 = 5 := by
                              simpa [Ω2, Nat.card_eq_fintype_card] using hSylow2card5
                            let act2 := MulAction.toPermHom H Ω2
                            have hact2_inj : Function.Injective act2 := by
                              rw [← MonoidHom.ker_eq_bot_iff]
                              have hker_le_normalizer (R : Sylow 2 H) :
                                  act2.ker ≤
                                    Subgroup.normalizer (R : Set H) := by
                                intro x hx
                                have hxperm : act2 x = 1 := hx
                                have hxfix : x • R = R := by
                                  have h := DFunLike.congr_fun hxperm R
                                  simpa [act2] using h
                                exact Sylow.smul_eq_iff_mem_normalizer.mp hxfix
                              have hnormalizer_card_twelve :
                                  Nat.card
                                      (Subgroup.normalizer (P2 : Set H)) = 12 := by
                                have hP2index :
                                    (Subgroup.normalizer (P2 : Set H)).index = 5 := by
                                  calc
                                    (Subgroup.normalizer (P2 : Set H)).index =
                                        Nat.card (Sylow 2 H) :=
                                      P2.card_eq_index_normalizer.symm
                                    _ = 5 := hSylow2card5
                                have hmul :=
                                  (Subgroup.normalizer
                                    (P2 : Set H)).card_mul_index
                                rw [hP2index, hHcard60] at hmul
                                omega
                              have hker_card_dvd_twelve :
                                  Nat.card act2.ker ∣ 12 := by
                                simpa [hnormalizer_card_twelve] using
                                  Subgroup.card_dvd_of_le
                                    (hker_le_normalizer P2)
                              have hker_has_no_involution :
                                  ∀ x : act2.ker, orderOf x ≠ 2 := by
                                intro x hxorder
                                have hxHorder : orderOf (x : H) = 2 :=
                                  (Subgroup.orderOf_coe x).trans hxorder
                                obtain ⟨R, hxR, hRunique⟩ :=
                                  hinvolution_unique_sylow (x : H) hxHorder
                                obtain ⟨S, hSR⟩ :=
                                  Fintype.exists_ne_of_one_lt_card
                                    (by omega : 1 < Fintype.card Ω2) R
                                let X : Subgroup H :=
                                  Subgroup.zpowers (x : H)
                                have hXcard : Nat.card X = 2 := by
                                  simpa [X] using
                                    (Nat.card_zpowers (x : H)).trans hxHorder
                                have hXisP : IsPGroup 2 X :=
                                  IsPGroup.of_card (n := 1) (by
                                    simpa using hXcard)
                                have hXnormalizesS :
                                    X ≤ Subgroup.normalizer (S : Set H) := by
                                  exact Subgroup.zpowers_le.2
                                    (hker_le_normalizer S x.2)
                                have hsupP :
                                    IsPGroup 2
                                      (X ⊔ (S : Subgroup H) : Subgroup H) :=
                                  hXisP.to_sup_of_normal_right'
                                    S.isPGroup' hXnormalizesS
                                have hsup_eq :
                                    X ⊔ (S : Subgroup H) = S :=
                                  S.is_maximal' hsupP le_sup_right
                                have hxS : (x : H) ∈ (S : Subgroup H) := by
                                  have hxjoin :
                                      (x : H) ∈ X ⊔ (S : Subgroup H) :=
                                    (show X ≤ X ⊔ (S : Subgroup H) from
                                      le_sup_left) (by
                                        exact Subgroup.mem_zpowers (x : H))
                                  rw [hsup_eq] at hxjoin
                                  exact hxjoin
                                exact hSR (hRunique S hxS)
                              have htwo_not_dvd_ker :
                                  ¬ 2 ∣ Nat.card act2.ker := by
                                intro htwo
                                obtain ⟨x, hxorder⟩ :=
                                  exists_prime_orderOf_dvd_card' 2 htwo
                                exact hker_has_no_involution x hxorder
                              have hker_card_cases :
                                  Nat.card act2.ker = 1 ∨
                                    Nat.card act2.ker = 3 := by
                                have hpos : 0 < Nat.card act2.ker := Nat.card_pos
                                have hle : Nat.card act2.ker ≤ 12 :=
                                  Nat.le_of_dvd (by norm_num)
                                    hker_card_dvd_twelve
                                interval_cases h : Nat.card act2.ker
                                · omega
                                · exfalso
                                  apply htwo_not_dvd_ker
                                  norm_num [h]
                                · omega
                                · exfalso
                                  apply htwo_not_dvd_ker
                                  norm_num [h]
                                · norm_num [h] at hker_card_dvd_twelve
                                · exfalso
                                  apply htwo_not_dvd_ker
                                  norm_num [h]
                                · norm_num [h] at hker_card_dvd_twelve
                                · exfalso
                                  apply htwo_not_dvd_ker
                                  norm_num [h]
                                · norm_num [h] at hker_card_dvd_twelve
                                · exfalso
                                  apply htwo_not_dvd_ker
                                  norm_num [h]
                                · norm_num [h] at hker_card_dvd_twelve
                                · exfalso
                                  apply htwo_not_dvd_ker
                                  norm_num [h]
                              rcases hker_card_cases with hker_one | hker_three
                              · exact Subgroup.card_eq_one.mp hker_one
                              · have hSylow3card10 :
                                    Nat.card (Sylow 3 H) = 10 := by
                                  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
                                  have hZjIndex20 : (Z j).index = 20 := by
                                    have hmul := (Z j).card_mul_index
                                    rw [hzj_three, hHcard60] at hmul
                                    omega
                                  let hZjP : IsPGroup 3 (Z j) :=
                                    IsPGroup.of_card (n := 1) (by
                                      simpa using hzj_three)
                                  let Q3 : Sylow 3 H := hZjP.toSylow (by
                                    rw [hZjIndex20]
                                    norm_num)
                                  calc
                                    Nat.card (Sylow 3 H) =
                                        (Subgroup.normalizer
                                          (Q3 : Set H)).index :=
                                      Q3.card_eq_index_normalizer
                                    _ = (NZ j).index := by rfl
                                    _ = 10 := hindices_five.2.1
                                have hker_is_sylow_three :
                                    ∃ R : Sylow 3 H,
                                      (R : Subgroup H) = act2.ker := by
                                  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
                                  have hkerP : IsPGroup 3 act2.ker :=
                                    IsPGroup.of_card (n := 1) (by
                                      simpa using hker_three)
                                  have hkerIndex20 : act2.ker.index = 20 := by
                                    have hmul := act2.ker.card_mul_index
                                    rw [hker_three, hHcard60] at hmul
                                    omega
                                  let R3 : Sylow 3 H := hkerP.toSylow (by
                                    rw [hkerIndex20]
                                    norm_num)
                                  exact ⟨R3, rfl⟩
                                obtain ⟨R3, hR3⟩ := hker_is_sylow_three
                                have hR3normal : (R3 : Subgroup H).Normal := by
                                  rw [hR3]
                                  exact inferInstance
                                letI : Unique (Sylow 3 H) :=
                                  Sylow.unique_of_normal R3 hR3normal
                                have hSylow3card1 :
                                    Nat.card (Sylow 3 H) = 1 := Nat.card_unique
                                omega
                            let eΩ2 : Ω2 ≃ Fin 5 :=
                              Fintype.equivFinOfCardEq hΩ2card
                            let actFin2 : H →* Equiv.Perm (Fin 5) :=
                              (Equiv.permCongrHom eΩ2).toMonoidHom.comp act2
                            have hactFin2_inj : Function.Injective actFin2 := by
                              intro x y hxy
                              apply hact2_inj
                              apply (Equiv.permCongrHom eΩ2).injective
                              simpa [actFin2] using hxy
                            let K2 : Subgroup (Equiv.Perm (Fin 5)) := actFin2.range
                            have hrange2_inj :
                                Function.Injective actFin2.rangeRestrict := by
                              intro x y hxy
                              exact hactFin2_inj (congrArg Subtype.val hxy)
                            let eRange2 : H ≃* K2 :=
                              MulEquiv.ofBijective actFin2.rangeRestrict
                                ⟨hrange2_inj,
                                  MonoidHom.rangeRestrict_surjective actFin2⟩
                            have hK2card : Nat.card K2 = 60 := by
                              calc
                                Nat.card K2 = Nat.card H :=
                                  (Nat.card_congr eRange2.toEquiv).symm
                                _ = 60 := hHcard60
                            have hperm5card :
                                Nat.card (Equiv.Perm (Fin 5)) = 120 := by
                              norm_num [Fintype.card_perm, Nat.factorial]
                            have hK2index : K2.index = 2 := by
                              have hmul := K2.index_mul_card
                              rw [hK2card, hperm5card] at hmul
                              omega
                            have hK2alt : K2 = alternatingGroup (Fin 5) :=
                              Equiv.Perm.eq_alternatingGroup_of_index_eq_two hK2index
                            exact ⟨eRange2.trans (MulEquiv.subgroupCongr hK2alt)⟩
                          exact hA5_via_sylow_two
                      exact Or.inr hexceptional
                  exact hclassification
                by_cases h01 : Nat.card (Z 0) ≤ Nat.card (Z 1)
                · by_cases h12 : Nat.card (Z 1) ≤ Nat.card (Z 2)
                  · rcases hordered 2 1 0 (by decide) (by decide) (by decide)
                        h12 h01 with hdih | hS4 | hA5
                    · exact Or.inr (Or.inl hdih)
                    · exact Or.inr (Or.inr (Or.inr (Or.inl hS4)))
                    · exact Or.inr (Or.inr (Or.inr (Or.inr hA5)))
                  · by_cases h02 : Nat.card (Z 0) ≤ Nat.card (Z 2)
                    · rcases hordered 1 2 0 (by decide) (by decide) (by decide)
                          (by omega) h02 with hdih | hS4 | hA5
                      · exact Or.inr (Or.inl hdih)
                      · exact Or.inr (Or.inr (Or.inr (Or.inl hS4)))
                      · exact Or.inr (Or.inr (Or.inr (Or.inr hA5)))
                    · rcases hordered 1 0 2 (by decide) (by decide) (by decide)
                          h01 (by omega) with hdih | hS4 | hA5
                      · exact Or.inr (Or.inl hdih)
                      · exact Or.inr (Or.inr (Or.inr (Or.inl hS4)))
                      · exact Or.inr (Or.inr (Or.inr (Or.inr hA5)))
                · by_cases h02 : Nat.card (Z 0) ≤ Nat.card (Z 2)
                  · rcases hordered 2 0 1 (by decide) (by decide) (by decide)
                        h02 (by omega) with hdih | hS4 | hA5
                    · exact Or.inr (Or.inl hdih)
                    · exact Or.inr (Or.inr (Or.inr (Or.inl hS4)))
                    · exact Or.inr (Or.inr (Or.inr (Or.inr hA5)))
                  · by_cases h12 : Nat.card (Z 1) ≤ Nat.card (Z 2)
                    · rcases hordered 0 2 1 (by decide) (by decide) (by decide)
                          (by omega) h12 with hdih | hS4 | hA5
                      · exact Or.inr (Or.inl hdih)
                      · exact Or.inr (Or.inr (Or.inr (Or.inl hS4)))
                      · exact Or.inr (Or.inr (Or.inr (Or.inr hA5)))
                    · rcases hordered 0 1 2 (by decide) (by decide) (by decide)
                          (by omega) (by omega) with hdih | hS4 | hA5
                      · exact Or.inr (Or.inl hdih)
                      · exact Or.inr (Or.inr (Or.inr (Or.inl hS4)))
                      · exact Or.inr (Or.inr (Or.inr (Or.inr hA5)))
              exact h824_three_shape
          exact h824_two_or_three_shape
      exact h824_positive_shape
  have h824_A4_restriction
      (hA4 : Nonempty (H ≃* alternatingGroup (Fin 4))) :
      p ≠ 2 ∨ Even f := by
    left
    intro hp2
    subst p
    apply hp_not_dvd_card_H
    have hc := Nat.card_congr hA4.some.toEquiv
    have hA4card : Nat.card (alternatingGroup (Fin 4)) = 12 := by
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [hc, hA4card]
    norm_num
  have h824_S4_restriction
      (hS4 : Nonempty (H ≃* Equiv.Perm (Fin 4))) :
      16 ∣ p ^ (2 * f) - 1 := by
    have hS4_p_ne_two : p ≠ 2 := by
      intro hp2
      subst p
      apply hp_not_dvd_card_H
      have hHcard : Nat.card H = 24 := by
        calc
          Nat.card H = Nat.card (Equiv.Perm (Fin 4)) :=
            Nat.card_congr hS4.some.toEquiv
          _ = 24 := by norm_num [Fintype.card_perm, Nat.factorial]
      rw [hHcard]
      norm_num
    have hS4_cycle_four : ∃ x : H, orderOf x = 4 := by
      refine ⟨hS4.some.symm (Fin.cycleRange (3 : Fin 4)), ?_⟩
      rw [hS4.some.symm.orderOf_eq]
      rw [← Equiv.Perm.lcm_cycleType,
        Fin.cycleType_cycleRange (by decide : (3 : Fin 4) ≠ 0)]
      norm_num
    have hS4_cycle_four_family :
        ∃ a : Fin r, 4 ∣ Nat.card (Z a) := by
      obtain ⟨x, hxorder⟩ := hS4_cycle_four
      have hxne : x ≠ 1 := by
        intro hx
        rw [hx, orderOf_one] at hxorder
        norm_num at hxorder
      obtain ⟨A, hxA, _hAunique⟩ :=
        huppert_II_8_22_unique_family hFcard H Z
          hcyclic hnontrivial hcoprime hmaximal
          hrepresentative hdistinct x hxne
      rcases A with Qp | z
      · have hxdvd : orderOf x ∣ Nat.card Qp :=
          (Qp : Subgroup H).orderOf_dvd_natCard hxA
        have hQpcard : Nat.card Qp = 1 := by
          calc
            Nat.card Qp = Nat.card P :=
              Nat.card_congr (Sylow.equiv Qp P).toEquiv
            _ = 1 := by simpa using hPcard
        rw [hxorder, hQpcard] at hxdvd
        norm_num at hxdvd
      · have hxdvd : orderOf x ∣ Nat.card z.2.1 :=
          z.2.1.orderOf_dvd_natCard hxA
        obtain ⟨g, hg⟩ := z.2.2
        have hzcard : Nat.card z.2.1 = Nat.card (Z z.1) := by
          rw [hg, Subgroup.card_map_of_injective
            (MulAut.conj g).injective]
        refine ⟨z.1, ?_⟩
        simpa [hxorder, hzcard] using hxdvd
    have hS4_four_torus :
        4 ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∨
          4 ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 := by
      obtain ⟨a, ha⟩ := hS4_cycle_four_family
      rcases hdivides a with hsplit | hnonsplit
      · exact Or.inl (dvd_trans ha hsplit)
      · exact Or.inr (dvd_trans ha hnonsplit)
    have hS4_q_odd : Odd (Nat.card F) := by
      rw [hFcard]
      exact ((Fact.out : p.Prime).odd_of_ne_two hS4_p_ne_two).pow
    have hS4_two_dvd_sub : 2 ∣ Nat.card F - 1 := by
      rcases hS4_q_odd with ⟨k, hk⟩
      use k
      omega
    have hS4_two_dvd_add : 2 ∣ Nat.card F + 1 := by
      exact hS4_q_odd.add_one.two_dvd
    have hS4_gcd_two : Nat.gcd (Nat.card F - 1) 2 = 2 := by
      exact Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
        (Nat.dvd_gcd hS4_two_dvd_sub (dvd_refl 2))
    have hS4_eight_torus :
        8 ∣ Nat.card F - 1 ∨ 8 ∣ Nat.card F + 1 := by
      rw [hS4_gcd_two] at hS4_four_torus
      rcases hS4_four_torus with hminus | hplus
      · left
        obtain ⟨a, ha⟩ := hminus
        use a
        calc
          Nat.card F - 1 = (Nat.card F - 1) / 2 * 2 :=
            (Nat.div_mul_cancel hS4_two_dvd_sub).symm
          _ = (4 * a) * 2 := by rw [ha]
          _ = 8 * a := by ring
      · right
        obtain ⟨a, ha⟩ := hplus
        use a
        calc
          Nat.card F + 1 = (Nat.card F + 1) / 2 * 2 :=
            (Nat.div_mul_cancel hS4_two_dvd_add).symm
          _ = (4 * a) * 2 := by rw [ha]
          _ = 8 * a := by ring
    have hS4_sixteen_q_sq_sub_one :
        16 ∣ Nat.card F ^ 2 - 1 := by
      have hfactor :
          Nat.card F ^ 2 - 1 =
            (Nat.card F - 1) * (Nat.card F + 1) := by
        simpa [mul_comm] using Nat.sq_sub_sq (Nat.card F) 1
      rw [hfactor]
      rcases hS4_eight_torus with hminus | hplus
      · have hmul := Nat.mul_dvd_mul hminus hS4_two_dvd_add
        norm_num at hmul
        exact hmul
      · have hmul := Nat.mul_dvd_mul hS4_two_dvd_sub hplus
        norm_num at hmul
        exact hmul
    rw [hFcard, ← pow_mul] at hS4_sixteen_q_sq_sub_one
    simpa [mul_comm] using hS4_sixteen_q_sq_sub_one
  have h824_A5_restriction
      (hA5 : Nonempty (H ≃* alternatingGroup (Fin 5))) :
      p = 5 ∨ 5 ∣ p ^ (2 * f) - 1 := by
    have hA5_cycle_five : ∃ x : H, orderOf x = 5 := by
      let y : alternatingGroup (Fin 5) :=
        ⟨Fin.cycleRange (4 : Fin 5), by
          rw [Equiv.Perm.mem_alternatingGroup, Fin.sign_cycleRange]
          decide⟩
      refine ⟨hA5.some.symm y, ?_⟩
      rw [hA5.some.symm.orderOf_eq, ← Subgroup.orderOf_coe y]
      change orderOf (Fin.cycleRange (4 : Fin 5)) = 5
      rw [← Equiv.Perm.lcm_cycleType,
        Fin.cycleType_cycleRange (by decide : (4 : Fin 5) ≠ 0)]
      norm_num
    have hA5_cycle_five_family :
        ∃ a : Fin r, 5 ∣ Nat.card (Z a) := by
      obtain ⟨x, hxorder⟩ := hA5_cycle_five
      have hxne : x ≠ 1 := by
        intro hx
        rw [hx, orderOf_one] at hxorder
        norm_num at hxorder
      obtain ⟨A, hxA, _hAunique⟩ :=
        huppert_II_8_22_unique_family hFcard H Z
          hcyclic hnontrivial hcoprime hmaximal
          hrepresentative hdistinct x hxne
      rcases A with Qp | z
      · have hxdvd : orderOf x ∣ Nat.card Qp :=
          (Qp : Subgroup H).orderOf_dvd_natCard hxA
        have hQpcard : Nat.card Qp = 1 := by
          calc
            Nat.card Qp = Nat.card P :=
              Nat.card_congr (Sylow.equiv Qp P).toEquiv
            _ = 1 := by simpa using hPcard
        rw [hxorder, hQpcard] at hxdvd
        norm_num at hxdvd
      · have hxdvd : orderOf x ∣ Nat.card z.2.1 :=
          z.2.1.orderOf_dvd_natCard hxA
        obtain ⟨g, hg⟩ := z.2.2
        have hzcard : Nat.card z.2.1 = Nat.card (Z z.1) := by
          rw [hg, Subgroup.card_map_of_injective
            (MulAut.conj g).injective]
        refine ⟨z.1, ?_⟩
        simpa [hxorder, hzcard] using hxdvd
    have hA5_five_torus_quotient :
        5 ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∨
          5 ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 := by
      obtain ⟨a, ha⟩ := hA5_cycle_five_family
      rcases hdivides a with hsplit | hnonsplit
      · exact Or.inl (dvd_trans ha hsplit)
      · exact Or.inr (dvd_trans ha hnonsplit)
    have hA5_five_torus_factor :
        5 ∣ Nat.card F - 1 ∨ 5 ∣ Nat.card F + 1 := by
      have hq : 1 ≤ Nat.card F :=
        (Finite.one_lt_card (α := F)).le
      have hdvd_sub : Nat.gcd (Nat.card F - 1) 2 ∣ Nat.card F - 1 :=
        Nat.gcd_dvd_left _ _
      have hdvd_two : Nat.gcd (Nat.card F - 1) 2 ∣ 2 :=
        Nat.gcd_dvd_right _ _
      have hdvd_add : Nat.gcd (Nat.card F - 1) 2 ∣ Nat.card F + 1 := by
        have h := Nat.dvd_add hdvd_sub hdvd_two
        convert h using 1 <;> omega
      rcases hA5_five_torus_quotient with hminus | hplus
      · exact Or.inl
          (dvd_trans hminus (Nat.div_dvd_of_dvd hdvd_sub))
      · exact Or.inr
          (dvd_trans hplus (Nat.div_dvd_of_dvd hdvd_add))
    have hA5_five_q_sq_sub_one :
        5 ∣ Nat.card F ^ 2 - 1 := by
      have hfactor :
          Nat.card F ^ 2 - 1 =
            (Nat.card F - 1) * (Nat.card F + 1) := by
        simpa [mul_comm] using Nat.sq_sub_sq (Nat.card F) 1
      rw [hfactor]
      rcases hA5_five_torus_factor with hminus | hplus
      · exact dvd_mul_of_dvd_left hminus _
      · exact dvd_mul_of_dvd_right hplus _
    right
    rw [hFcard, ← pow_mul] at hA5_five_q_sq_sub_one
    simpa [mul_comm] using hA5_five_q_sq_sub_one
  rcases h824_shape with hcyc | hdih | hA4 | hS4 | hA5
  · exact Or.inl hcyc
  · exact Or.inr (Or.inl hdih)
  · exact Or.inr (Or.inr (Or.inl ⟨h824_A4_restriction hA4, hA4⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h824_S4_restriction hS4, hS4⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h824_A5_restriction hA5, hA5⟩)))

/-- Huppert II.4.7, in the degree-six, order-sixty case used by II.8.25:
a faithful primitive permutation group of degree six and order sixty is `A5`. -/
public theorem huppert_II_4_7_primitive_degree_six_order_sixty
    {G Ω : Type u} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    [FaithfulSMul G Ω]
    (hprimitive : MulAction.IsPreprimitive G Ω)
    (hΩcard : Nat.card Ω = 6) (hGcard : Nat.card G = 60) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype Ω := Fintype.ofFinite Ω
  haveI : MulAction.IsPreprimitive G Ω := hprimitive
  have hΩfcard : Fintype.card Ω = 6 := by
    simpa [Nat.card_eq_fintype_card] using hΩcard
  letI : Nonempty Ω := Fintype.card_pos_iff.mp (by rw [hΩfcard]; norm_num)
  have hnormal_transitive
      (N : Subgroup G) [N.Normal] (hN_ne_bot : N ≠ ⊥) :
      MulAction.IsPretransitive N Ω := by
    apply MulAction.IsQuasiPreprimitive.isPretransitive_of_normal
    intro hfixed
    apply hN_ne_bot
    apply le_antisymm
    · intro g hg
      have hg_one : g = 1 :=
        (faithfulSMul_iff.mp (inferInstance : FaithfulSMul G Ω)) g fun x =>
          (show x ∈ MulAction.fixedPoints N Ω by simp [hfixed]) ⟨g, hg⟩
      simp [hg_one]
    · exact bot_le
  have hnormal_card_dvd_six
      (N : Subgroup G) [N.Normal] (hN_ne_bot : N ≠ ⊥) :
      6 ∣ Nat.card N := by
    letI : MulAction.IsPretransitive N Ω := hnormal_transitive N hN_ne_bot
    let a : Ω := Classical.arbitrary Ω
    have hdiv := (MulAction.stabilizer N a).index_dvd_card
    rw [MulAction.index_stabilizer_of_transitive, hΩcard] at hdiv
    exact hdiv
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 G := default
  have hfac60_two : (Nat.factorization 60) 2 = 2 := by
    have hle : 2 ≤ (Nat.factorization 60) 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization (by norm_num)).mp
        (by norm_num)
    have hnle : ¬ 3 ≤ (Nat.factorization 60) 2 := by
      intro h
      have hdvd :=
        (Nat.prime_two.pow_dvd_iff_le_factorization (by norm_num)).mpr h
      norm_num at hdvd
    omega
  have hPcard : Nat.card P = 4 := by
    rw [P.card_eq_multiplicity, hGcard]
    rw [hfac60_two]
    norm_num
  have hPindex : P.index = 15 := by
    have hmul := P.card_mul_index
    rw [hPcard, hGcard] at hmul
    omega
  have hSylow2_dvd : Nat.card (Sylow 2 G) ∣ 15 := by
    simpa [hPindex] using P.card_dvd_index
  have hSylow2_not_even : ¬ 2 ∣ Nat.card (Sylow 2 G) :=
    not_dvd_card_sylow 2 G
  have hSylow2_cases :
      Nat.card (Sylow 2 G) = 1 ∨
        Nat.card (Sylow 2 G) = 3 ∨
        Nat.card (Sylow 2 G) = 5 ∨
        Nat.card (Sylow 2 G) = 15 := by
    have hpos : 0 < Nat.card (Sylow 2 G) := Nat.card_pos
    have hle : Nat.card (Sylow 2 G) ≤ 15 :=
      Nat.le_of_dvd (by norm_num) hSylow2_dvd
    interval_cases h : Nat.card (Sylow 2 G) <;> norm_num [h] at *
  have hSylow2card5 : Nat.card (Sylow 2 G) = 5 := by
    rcases hSylow2_cases with hcard1 | hcard3 | hcard5 | hcard15
    · haveI : Subsingleton (Sylow 2 G) :=
        (Nat.card_eq_one_iff_unique.mp hcard1).1
      letI : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
      have hP_ne_bot : (P : Subgroup G) ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hPcard]
        norm_num
      have hdiv := hnormal_card_dvd_six (P : Subgroup G) hP_ne_bot
      rw [hPcard] at hdiv
      norm_num at hdiv
    · let act3 := MulAction.toPermHom G (Sylow 2 G)
      have hker_le_normalizer (Q : Sylow 2 G) :
          act3.ker ≤
            Subgroup.normalizer ((Q : Subgroup G) : Set G) := by
        intro x hx
        have hxperm : act3 x = 1 := hx
        have hxfix : x • Q = Q := by
          have h := DFunLike.congr_fun hxperm Q
          simpa [act3] using h
        exact Sylow.smul_eq_iff_mem_normalizer.mp hxfix
      have hnormalizer_card_twenty :
          Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) = 20 := by
        have hindex :
            (Subgroup.normalizer ((P : Subgroup G) : Set G)).index = 3 := by
          calc
            (Subgroup.normalizer ((P : Subgroup G) : Set G)).index =
                Nat.card (Sylow 2 G) := P.card_eq_index_normalizer.symm
            _ = 3 := hcard3
        have hmul :=
          (Subgroup.normalizer ((P : Subgroup G) : Set G)).card_mul_index
        rw [hindex, hGcard] at hmul
        omega
      have hker_card_dvd_twenty : Nat.card act3.ker ∣ 20 := by
        have hcard := Subgroup.card_dvd_of_le (hker_le_normalizer P)
        rw [hnormalizer_card_twenty] at hcard
        exact hcard
      have hker_bot : act3.ker = ⊥ := by
        by_contra hker
        have hdiv6 := hnormal_card_dvd_six act3.ker hker
        have : 6 ∣ 20 := dvd_trans hdiv6 hker_card_dvd_twenty
        norm_num at this
      have hact3_inj : Function.Injective act3 := by
        rw [← MonoidHom.ker_eq_bot_iff]
        exact hker_bot
      letI : Fintype (Sylow 2 G) := Fintype.ofFinite (Sylow 2 G)
      have hSylow2fcard : Fintype.card (Sylow 2 G) = 3 := by
        simpa [Nat.card_eq_fintype_card] using hcard3
      have hcard_le := Nat.card_le_card_of_injective act3 hact3_inj
      have hperm_card : Nat.card (Equiv.Perm (Sylow 2 G)) = 6 := by
        rw [Nat.card_eq_fintype_card]
        simp [Fintype.card_perm, hSylow2fcard, Nat.factorial]
      rw [hGcard, hperm_card] at hcard_le
      omega
    · exact hcard5
    · have hnormalizer_card_four :
          Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) = 4 := by
        have hindex :
            (Subgroup.normalizer ((P : Subgroup G) : Set G)).index = 15 := by
          calc
            (Subgroup.normalizer ((P : Subgroup G) : Set G)).index =
                Nat.card (Sylow 2 G) := P.card_eq_index_normalizer.symm
            _ = 15 := hcard15
        have hmul :=
          (Subgroup.normalizer ((P : Subgroup G) : Set G)).card_mul_index
        rw [hindex, hGcard] at hmul
        omega
      have hnormalizer_eq :
          Subgroup.normalizer ((P : Subgroup G) : Set G) =
            (P : Subgroup G) := by
        symm
        apply Subgroup.eq_of_le_of_card_ge Subgroup.le_normalizer
        rw [hnormalizer_card_four, hPcard]
      have hnormalizer_le_centralizer :
          Subgroup.normalizer ((P : Subgroup G) : Set G) ≤
            Subgroup.centralizer ((P : Subgroup G) : Set G) := by
        rw [hnormalizer_eq]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        let xP : P := ⟨x, hx⟩
        let yP : P := ⟨y, hy⟩
        exact congrArg Subtype.val
          (IsPGroup.commutative_of_card_eq_prime_sq (p := 2)
            (by simpa [Nat.card_eq_fintype_card] using hPcard) yP xP)
      let K : Subgroup G :=
        (MonoidHom.transferSylow P hnormalizer_le_centralizer).ker
      letI : K.Normal := inferInstance
      have hcomp : K.IsComplement' P := by
        exact MonoidHom.ker_transferSylow_isComplement'
          P hnormalizer_le_centralizer
      have hKcard : Nat.card K = 15 := by
        have hmul := hcomp.card_mul
        rw [hPcard, hGcard] at hmul
        omega
      have hK_ne_bot : K ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hKcard]
        norm_num
      have hdiv := hnormal_card_dvd_six K hK_ne_bot
      rw [hKcard] at hdiv
      norm_num at hdiv
  let act2 := MulAction.toPermHom G (Sylow 2 G)
  have hker_le_normalizer (Q : Sylow 2 G) :
      act2.ker ≤ Subgroup.normalizer ((Q : Subgroup G) : Set G) := by
    intro x hx
    have hxperm : act2 x = 1 := hx
    have hxfix : x • Q = Q := by
      have h := DFunLike.congr_fun hxperm Q
      simpa [act2] using h
    exact Sylow.smul_eq_iff_mem_normalizer.mp hxfix
  have hnormalizer_card_twelve :
      Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) = 12 := by
    have hindex :
        (Subgroup.normalizer ((P : Subgroup G) : Set G)).index = 5 := by
      calc
        (Subgroup.normalizer ((P : Subgroup G) : Set G)).index =
            Nat.card (Sylow 2 G) := P.card_eq_index_normalizer.symm
        _ = 5 := hSylow2card5
    have hmul :=
      (Subgroup.normalizer ((P : Subgroup G) : Set G)).card_mul_index
    rw [hindex, hGcard] at hmul
    omega
  have hker_card_dvd_twelve : Nat.card act2.ker ∣ 12 := by
    have hcard := Subgroup.card_dvd_of_le (hker_le_normalizer P)
    rw [hnormalizer_card_twelve] at hcard
    exact hcard
  have hker_bot : act2.ker = ⊥ := by
    by_contra hker_ne_bot
    have hdiv6 := hnormal_card_dvd_six act2.ker hker_ne_bot
    have hker_cases : Nat.card act2.ker = 6 ∨ Nat.card act2.ker = 12 := by
      have hpos : 0 < Nat.card act2.ker := Nat.card_pos
      have hle : Nat.card act2.ker ≤ 12 :=
        Nat.le_of_dvd (by norm_num) hker_card_dvd_twelve
      interval_cases h : Nat.card act2.ker <;> norm_num [h] at *
    rcases hker_cases with hker6 | hker12
    · let K : Subgroup G := act2.ker
      letI : K.Normal := inferInstance
      letI : Fact (Nat.Prime 3) := ⟨by decide⟩
      let Q : Sylow 3 K := default
      have hfac6_three : (Nat.factorization 6) 3 = 1 := by
        rw [show 6 = 3 * 2 by norm_num,
          Nat.factorization_mul_apply_of_coprime (by norm_num : Nat.Coprime 3 2),
          Nat.prime_three.factorization_self,
          Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2)]
      have hQcard : Nat.card Q = 3 := by
        rw [Q.card_eq_multiplicity, show Nat.card K = 6 from hker6]
        rw [hfac6_three]
        norm_num
      have hQindex : Q.index = 2 := by
        have hmul := Q.card_mul_index
        rw [hQcard, show Nat.card K = 6 from hker6] at hmul
        omega
      have hSylow3_dvd : Nat.card (Sylow 3 K) ∣ 2 := by
        simpa [hQindex] using Q.card_dvd_index
      have hSylow3_mod := card_sylow_modEq_one 3 K
      have hSylow3card1 : Nat.card (Sylow 3 K) = 1 := by
        have hpos : 0 < Nat.card (Sylow 3 K) := Nat.card_pos
        have hle : Nat.card (Sylow 3 K) ≤ 2 :=
          Nat.le_of_dvd (by norm_num) hSylow3_dvd
        interval_cases h : Nat.card (Sylow 3 K)
        · rfl
        · have hfalse : ¬(2 : ℕ) ≡ 1 [MOD 3] := by decide
          exact (hfalse (h ▸ hSylow3_mod)).elim
      haveI : Subsingleton (Sylow 3 K) :=
        (Nat.card_eq_one_iff_unique.mp hSylow3card1).1
      letI : (Q : Subgroup K).Characteristic :=
        Sylow.characteristic_of_subsingleton Q
      let QG : Subgroup G := (Q : Subgroup K).map K.subtype
      letI : QG.Normal := inferInstance
      have hQGcard : Nat.card QG = 3 := by
        rw [Subgroup.card_map_of_injective K.subtype_injective, hQcard]
      have hQG_ne_bot : QG ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hQGcard]
        norm_num
      have hdiv := hnormal_card_dvd_six QG hQG_ne_bot
      rw [hQGcard] at hdiv
      norm_num at hdiv
    · let K : Subgroup G := act2.ker
      letI : K.Normal := inferInstance
      let Q : Sylow 2 K := default
      have hfac12_two : (Nat.factorization 12) 2 = 2 := by
        have hle : 2 ≤ (Nat.factorization 12) 2 :=
          (Nat.prime_two.pow_dvd_iff_le_factorization (by norm_num)).mp
            (by norm_num)
        have hnle : ¬ 3 ≤ (Nat.factorization 12) 2 := by
          intro h
          have hdvd :=
            (Nat.prime_two.pow_dvd_iff_le_factorization (by norm_num)).mpr h
          norm_num at hdvd
        omega
      have hQcard : Nat.card Q = 4 := by
        rw [Q.card_eq_multiplicity, show Nat.card K = 12 from hker12]
        rw [hfac12_two]
        norm_num
      obtain ⟨R, hQR⟩ := Q.exists_comap_subtype_eq
      have hK_le_normalizer : K ≤ Subgroup.normalizer (R : Set G) :=
        hker_le_normalizer R
      have hQnormal : (Q : Subgroup K).Normal := by
        rw [← hQR]
        change (R.subgroupOf K).Normal
        exact Subgroup.normal_subgroupOf_of_le_normalizer hK_le_normalizer
      letI : (Q : Subgroup K).Characteristic :=
        Sylow.characteristic_of_normal Q hQnormal
      let QG : Subgroup G := (Q : Subgroup K).map K.subtype
      letI : QG.Normal := inferInstance
      have hQGcard : Nat.card QG = 4 := by
        rw [Subgroup.card_map_of_injective K.subtype_injective, hQcard]
      have hQG_ne_bot : QG ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hQGcard]
        norm_num
      have hdiv := hnormal_card_dvd_six QG hQG_ne_bot
      rw [hQGcard] at hdiv
      norm_num at hdiv
  have hact2_inj : Function.Injective act2 := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact hker_bot
  letI : Fintype (Sylow 2 G) := Fintype.ofFinite (Sylow 2 G)
  have hSylow2fcard : Fintype.card (Sylow 2 G) = 5 := by
    simpa [Nat.card_eq_fintype_card] using hSylow2card5
  let eΩ2 : Sylow 2 G ≃ Fin 5 := Fintype.equivFinOfCardEq hSylow2fcard
  let actFin2 : G →* Equiv.Perm (Fin 5) :=
    (Equiv.permCongrHom eΩ2).toMonoidHom.comp act2
  have hactFin2_inj : Function.Injective actFin2 := by
    intro x y hxy
    apply hact2_inj
    apply (Equiv.permCongrHom eΩ2).injective
    simpa [actFin2] using hxy
  let A : Subgroup (Equiv.Perm (Fin 5)) := actFin2.range
  let eRange : G ≃* A :=
    MulEquiv.ofBijective actFin2.rangeRestrict
      ⟨fun x y hxy => hactFin2_inj (congrArg Subtype.val hxy),
        MonoidHom.rangeRestrict_surjective actFin2⟩
  have hAcard : Nat.card A = 60 := by
    rw [← Nat.card_congr eRange.toEquiv, hGcard]
  have hperm5card : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    norm_num [Fintype.card_perm, Nat.factorial]
  have hAindex : A.index = 2 := by
    have hmul := A.index_mul_card
    rw [hAcard, hperm5card] at hmul
    omega
  have hAalt : A = alternatingGroup (Fin 5) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hAindex
  exact ⟨eRange.trans (MulEquiv.subgroupCongr hAalt)⟩

/-- Huppert II.8.25: a faithful transitive permutation group of degree six
and order sixty is `A5`. -/
public theorem huppert_II_8_25_transitive_degree_six_order_sixty
    {G Ω : Type u} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    [FaithfulSMul G Ω]
    (htransitive : MulAction.IsPretransitive G Ω)
    (hΩcard : Nat.card Ω = 6) (hGcard : Nat.card G = 60) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  have htwo_transitive : MulAction.IsMultiplyPretransitive G Ω 2 := by
    classical
    letI := Fintype.ofFinite Ω
    letI : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hΩfcard : Fintype.card Ω = 6 := by
      simpa [Nat.card_eq_fintype_card] using hΩcard
    have hfive : 5 ∣ Nat.card G := by
      rw [hGcard]
      norm_num
    obtain ⟨g, hgorder⟩ := exists_prime_orderOf_dvd_card' 5 hfive
    let σ : Equiv.Perm Ω := MulAction.toPerm g
    have hσorder : orderOf σ = 5 := by
      calc
        orderOf σ = orderOf g :=
          orderOf_injective (MulAction.toPermHom G Ω)
            (MulAction.toPerm_injective : Function.Injective
              (MulAction.toPerm : G → Equiv.Perm Ω)) g
        _ = 5 := hgorder
    have hσcycle : σ.IsCycle :=
      Equiv.Perm.isCycle_of_prime_order'
        (by simpa [hσorder] using (Fact.out : Nat.Prime 5))
        (by rw [hΩfcard, hσorder]; norm_num)
    have hfixed_card : Nat.card (Function.fixedPoints σ) = 1 := by
      rw [Nat.card_eq_fintype_card, σ.card_fixedPoints, hσcycle.cycleType,
        Multiset.sum_singleton, ← hσcycle.orderOf, hσorder, hΩfcard]
    have hfixed_nonempty : Nonempty (Function.fixedPoints σ) :=
      Finite.card_pos_iff.mp (by rw [hfixed_card]; norm_num)
    obtain ⟨x, hx⟩ := hfixed_nonempty
    have hσx : σ x = x := hx
    have hfixed_unique {y : Ω} (hy : σ y = y) : y = x := by
      have hsub : Subsingleton (Function.fixedPoints σ) :=
        (Nat.card_eq_one_iff_unique.mp hfixed_card).1
      exact congrArg Subtype.val
        (hsub.elim (⟨y, hy⟩ : Function.fixedPoints σ) ⟨x, hx⟩)
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    obtain ⟨u, hu⟩ := htransitive.exists_smul_eq a x
    obtain ⟨v, hv⟩ := htransitive.exists_smul_eq x c
    have hub_ne : u • b ≠ x := by
      intro hub
      exact hab (smul_left_cancel u (hu.trans hub.symm))
    have hvd_ne : v⁻¹ • d ≠ x := by
      intro hvd
      apply hcd
      calc
        c = v • x := hv.symm
        _ = v • (v⁻¹ • d) := by rw [hvd]
        _ = d := smul_inv_smul v d
    have hσub : σ (u • b) ≠ u • b := by
      intro hfix
      exact hub_ne (hfixed_unique hfix)
    have hσvd : σ (v⁻¹ • d) ≠ v⁻¹ • d := by
      intro hfix
      exact hvd_ne (hfixed_unique hfix)
    obtain ⟨n, hn⟩ := hσcycle.exists_pow_eq hσub hσvd
    have hperm_pow : MulAction.toPerm (g ^ n) = σ ^ n := by
      change (MulAction.toPermHom G Ω) (g ^ n) = σ ^ n
      rw [map_pow]
      rfl
    have hgpow_b : (g ^ n) • (u • b) = v⁻¹ • d := by
      change (MulAction.toPerm (g ^ n)) (u • b) = v⁻¹ • d
      rw [hperm_pow]
      exact hn
    have hσpow_x (k : ℕ) : (σ ^ k) x = x := by
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ, Equiv.Perm.mul_apply, hσx, ih]
    have hgpow_x : (g ^ n) • x = x := by
      change (MulAction.toPerm (g ^ n)) x = x
      rw [hperm_pow]
      exact hσpow_x n
    refine ⟨v * g ^ n * u, ?_, ?_⟩
    · simp only [mul_smul]
      rw [hu, hgpow_x, hv]
    · simp only [mul_smul]
      rw [hgpow_b, smul_inv_smul]
  have hprimitive : MulAction.IsPreprimitive G Ω :=
    MulAction.isPreprimitive_of_is_two_pretransitive htwo_transitive
  exact huppert_II_4_7_primitive_degree_six_order_sixty
    hprimitive hΩcard hGcard

/-- The II.8.2(a) consequence used in II.8.26: a Sylow subgroup of a
subgroup of `PSL(2,p^f)` is elementary abelian. -/
private theorem h826_sylow_elementary
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (P : Sylow p H) :
    IsElementaryAbelian p P := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : CharP F p :=
    charP_of_card_eq_prime_pow (by simpa using hFcard)
  obtain ⟨Q, hQcomap⟩ := P.exists_comap_subtype_eq
  have hPmemQ (x : P) :
      (((x : P) : H) : PSL2MatrixGroup F) ∈ (Q : Subgroup _) := by
    have hx :
        (x : H) ∈ (Q : Subgroup (PSL2MatrixGroup F)).comap H.subtype := by
      rw [hQcomap]
      exact x.property
    exact hx
  have hFieldElementary : IsElementaryAbelian p (Multiplicative F) := by
    refine
      { toIsMulCommutative :=
          { is_comm := ⟨fun x y => mul_comm x y⟩ }
        exponent_dvd_p := ?_ }
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    change Multiplicative.ofAdd x.toAdd ^ p = 1
    rw [← ofAdd_nsmul]
    simp
  obtain ⟨eQ⟩ := huppert_II_8_2_a_sylow_equiv_additive hFcard Q
  have hQElementary : IsElementaryAbelian p Q := by
    refine
      { toIsMulCommutative :=
          { is_comm := ⟨fun x y => ?_⟩ }
        exponent_dvd_p := ?_ }
    · apply eQ.symm.injective
      simpa using
        hFieldElementary.toIsMulCommutative.is_comm.comm
          (eQ.symm x) (eQ.symm y)
    · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      apply eQ.symm.injective
      have hx : (eQ.symm x) ^ p = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          hFieldElementary.exponent_dvd_p (eQ.symm x)
      simpa using hx
  refine
    { toIsMulCommutative :=
        { is_comm := ⟨fun x y => ?_⟩ }
      exponent_dvd_p := ?_ }
  · apply Subtype.ext
    apply Subtype.ext
    let xQ : Q := ⟨((x : H) : PSL2MatrixGroup F), hPmemQ x⟩
    let yQ : Q := ⟨((y : H) : PSL2MatrixGroup F), hPmemQ y⟩
    have hxy := congrArg Subtype.val
      (hQElementary.toIsMulCommutative.is_comm.comm xQ yQ)
    simpa [xQ, yQ] using hxy
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply Subtype.ext
    apply Subtype.ext
    let xQ : Q := ⟨((x : H) : PSL2MatrixGroup F), hPmemQ x⟩
    have hxpow : xQ ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        hQElementary.exponent_dvd_p xQ
    simpa [xQ] using congrArg Subtype.val hxpow

private theorem h826_card_actor_dvd_two_mul_card_of_stabilizer_card_le_two
    {A X : Type*} [Group A] [MulAction A X] [Finite A] [Finite X]
    (hstab : ∀ x : X, Nat.card (MulAction.stabilizer A x) ≤ 2) :
    Nat.card A ∣ 2 * Nat.card X := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype X := Fintype.ofFinite X
  let Ω := Quotient (MulAction.orbitRel A X)
  letI : Fintype Ω := Fintype.ofFinite Ω
  have hterm (ω : Ω) :
      Nat.card A ∣
        2 * (Nat.card A /
          Nat.card (MulAction.stabilizer A ω.out)) := by
    have hspos : 0 < Nat.card (MulAction.stabilizer A ω.out) :=
      Nat.card_pos
    have hsle := hstab ω.out
    have hscases :
        Nat.card (MulAction.stabilizer A ω.out) = 1 ∨
          Nat.card (MulAction.stabilizer A ω.out) = 2 := by
      omega
    rcases hscases with hs | hs
    · rw [hs]
      simp
    · rw [hs]
      have hdS :
          Nat.card (MulAction.stabilizer A ω.out) ∣ Nat.card A :=
        Subgroup.card_subgroup_dvd_card (MulAction.stabilizer A ω.out)
      have hd : 2 ∣ Nat.card A := by
        rw [hs] at hdS
        exact hdS
      obtain ⟨k, hk⟩ := hd
      rw [hk]
      simp
  have hsum : Nat.card A ∣
      ∑ ω : Ω, 2 * (Nat.card A /
        Nat.card (MulAction.stabilizer A ω.out)) :=
    Finset.dvd_sum fun ω _hω => hterm ω
  have hformula : Nat.card X =
      ∑ ω : Ω, Nat.card A /
        Nat.card (MulAction.stabilizer A ω.out) := by
    simpa [Nat.card_eq_fintype_card] using
      MulAction.card_eq_sum_card_group_div_card_stabilizer A X
  rw [← Finset.mul_sum, ← hformula] at hsum
  exact hsum

private theorem h826_subgroup_card_le_two_of_disjoint_le_normalizer
    {G : Type*} [Group G] [Finite G] (Q S : Subgroup G)
    (hSle : S ≤ Subgroup.normalizer (Q : Set G))
    (hdisjoint : Disjoint S Q)
    (hNcard : Nat.card (Subgroup.normalizer (Q : Set G)) =
      2 * Nat.card Q) :
    Nat.card S ≤ 2 := by
  classical
  let N : Subgroup G := Subgroup.normalizer (Q : Set G)
  let QN : Subgroup N := Q.subgroupOf N
  let SN : Subgroup N := S.subgroupOf N
  letI : QN.Normal := by
    dsimp only [QN]
    exact Subgroup.normal_subgroupOf_of_le_normalizer (by
      simpa [N] : N ≤ Subgroup.normalizer (Q : Set G))
  let φ : SN →* N ⧸ QN :=
    (QuotientGroup.mk' QN).comp SN.subtype
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have hker : φ (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have hQmem : (x : N) * (y : N)⁻¹ ∈ QN :=
      (QuotientGroup.eq_one_iff ((x : N) * (y : N)⁻¹)).mp hker
    have hQmemG : (x : G) * (y : G)⁻¹ ∈ Q := hQmem
    have hSmemG : (x : G) * (y : G)⁻¹ ∈ S :=
      S.mul_mem x.property (S.inv_mem y.property)
    have honeG : (x : G) * (y : G)⁻¹ = 1 :=
      Subgroup.disjoint_def.mp hdisjoint hSmemG hQmemG
    apply Subtype.ext
    apply Subtype.ext
    exact mul_inv_eq_one.mp honeG
  have hcardSN_dvd : Nat.card SN ∣ Nat.card (N ⧸ QN) :=
    Subgroup.card_dvd_of_injective φ hφinj
  have hQNcard : Nat.card QN = Nat.card Q := by
    dsimp only [QN]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv
  have hSNcard : Nat.card SN = Nat.card S := by
    dsimp only [SN]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSle).toEquiv
  have hquotient_card : Nat.card (N ⧸ QN) = 2 := by
    have hfactor := Subgroup.card_eq_card_quotient_mul_card_subgroup QN
    change Nat.card N = Nat.card (N ⧸ QN) * Nat.card QN at hfactor
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := Q))
    calc
      Nat.card (N ⧸ QN) * Nat.card Q = Nat.card N := by
        rw [← hQNcard]
        exact hfactor.symm
      _ = 2 * Nat.card Q := by simpa [N] using hNcard
  rw [hSNcard, hquotient_card] at hcardSN_dvd
  exact Nat.le_of_dvd (by norm_num) hcardSN_dvd

private theorem h826_conjugacy_class_card_divisibility
    {G : Type*} [Group G] [Finite G] (A B : Subgroup G)
    (hA_normalizer : Nat.card (Subgroup.normalizer (A : Set G)) =
      2 * Nat.card A)
    (hdisjoint : ∀ g : G,
      Disjoint B (A.map (MulAut.conj g).toMonoidHom)) :
    Nat.card B ∣ 2 * (Subgroup.normalizer (A : Set G)).index := by
  classical
  letI : MulAction G (Subgroup G) := MulAction.compHom _ MulAut.conj
  have hsmul_normalizer (g : G) (Q : Subgroup G) :
      g • Q = Q ↔ g ∈ Subgroup.normalizer (Q : Set G) := by
    rw [eq_comm, SetLike.ext_iff,
      ← inv_mem_iff (G := G) (H := Subgroup.normalizer Q),
      Subgroup.mem_normalizer_iff, inv_inv]
    exact forall_congr' fun h => iff_congr Iff.rfl
      ⟨fun ⟨a, b, c⟩ => c ▸ by simpa [mul_assoc] using b,
        fun hh => ⟨(MulAut.conj g)⁻¹ h, hh,
          MulAut.apply_inv_self G (MulAut.conj g) h⟩⟩
  have hstabA : MulAction.stabilizer G A =
      Subgroup.normalizer (A : Set G) := by
    ext g
    change g • A = A ↔ g ∈ Subgroup.normalizer (A : Set G)
    exact hsmul_normalizer g A
  let q : MulAction.orbitRel.Quotient G (Subgroup G) := Quotient.mk'' A
  let C := MulAction.orbitRel.Quotient.orbit q
  letI : MulAction B C := MulAction.compHom C B.subtype
  have hCcard : Nat.card C =
      (Subgroup.normalizer (A : Set G)).index := by
    change Nat.card ↥(MulAction.orbitRel.Quotient.orbit q) = _
    rw [show MulAction.orbitRel.Quotient.orbit q = MulAction.orbit G A by
      simp [q], Nat.card_coe_set_eq, ← MulAction.index_stabilizer G A, hstabA]
  have hstabilizer (x : C) :
      Nat.card (MulAction.stabilizer B x) ≤ 2 := by
    let St : Subgroup B := MulAction.stabilizer B x
    let S : Subgroup G := St.map B.subtype
    have hQconj : ∃ g : G,
        (x : Subgroup G) = A.map (MulAut.conj g).toMonoidHom := by
      have hx := x.property
      change (x : Subgroup G) ∈
        MulAction.orbitRel.Quotient.orbit q at hx
      rw [show MulAction.orbitRel.Quotient.orbit q = MulAction.orbit G A by
        simp [q]] at hx
      rcases hx with ⟨g, hg⟩
      exact ⟨g, hg.symm⟩
    have hSleN : S ≤
        Subgroup.normalizer ((x : Subgroup G) : Set G) := by
      rintro y ⟨z, hz, rfl⟩
      have hfix : z • x = x := MulAction.mem_stabilizer_iff.mp hz
      have hfix' : (z : G) • (x : Subgroup G) = (x : Subgroup G) :=
        congrArg Subtype.val hfix
      exact (hsmul_normalizer (z : G) (x : Subgroup G)).mp hfix'
    have hSleB : S ≤ B := by
      rintro y ⟨z, _hz, rfl⟩
      exact z.property
    obtain ⟨g, hg⟩ := hQconj
    have hdisjBQ : Disjoint B (x : Subgroup G) := by
      rw [hg]
      exact hdisjoint g
    have hdisjSQ : Disjoint S (x : Subgroup G) :=
      hdisjBQ.mono hSleB le_rfl
    have hQnormalizer :
        Nat.card (Subgroup.normalizer ((x : Subgroup G) : Set G)) =
          2 * Nat.card (x : Subgroup G) := by
      rw [hg,
        ← Subgroup.map_normalizer_eq_of_bijective A (MulAut.conj g).bijective,
        Subgroup.card_map_of_injective (MulAut.conj g).injective,
        Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hA_normalizer
    calc
      Nat.card St = Nat.card S := by
        symm
        exact Subgroup.card_map_of_injective B.subtype_injective
      _ ≤ 2 := h826_subgroup_card_le_two_of_disjoint_le_normalizer
        (x : Subgroup G) S hSleN hdisjSQ hQnormalizer
  have hdiv :=
    h826_card_actor_dvd_two_mul_card_of_stabilizer_card_le_two hstabilizer
  rwa [hCcard] at hdiv

private theorem h826_punctured_conjugacy_class_card_divisibility
    {G : Type*} [Group G] [Finite G] (A : Subgroup G)
    (hA_normalizer : Nat.card (Subgroup.normalizer (A : Set G)) =
      2 * Nat.card A)
    (hdisjoint : ∀ g : G,
      A.map (MulAut.conj g).toMonoidHom ≠ A →
        Disjoint A (A.map (MulAut.conj g).toMonoidHom)) :
    Nat.card A ∣
      2 * ((Subgroup.normalizer (A : Set G)).index - 1) := by
  classical
  letI : MulAction G (Subgroup G) := MulAction.compHom _ MulAut.conj
  have hsmul_normalizer (g : G) (Q : Subgroup G) :
      g • Q = Q ↔ g ∈ Subgroup.normalizer (Q : Set G) := by
    rw [eq_comm, SetLike.ext_iff,
      ← inv_mem_iff (G := G) (H := Subgroup.normalizer Q),
      Subgroup.mem_normalizer_iff, inv_inv]
    exact forall_congr' fun h => iff_congr Iff.rfl
      ⟨fun ⟨a, b, c⟩ => c ▸ by simpa [mul_assoc] using b,
        fun hh => ⟨(MulAut.conj g)⁻¹ h, hh,
          MulAut.apply_inv_self G (MulAut.conj g) h⟩⟩
  have hstabA : MulAction.stabilizer G A =
      Subgroup.normalizer (A : Set G) := by
    ext g
    change g • A = A ↔ g ∈ Subgroup.normalizer (A : Set G)
    exact hsmul_normalizer g A
  let q : MulAction.orbitRel.Quotient G (Subgroup G) := Quotient.mk'' A
  let C := MulAction.orbitRel.Quotient.orbit q
  let base : C := ⟨A, by simp [C, q]⟩
  let X := {x : C // x ≠ base}
  letI : MulAction A C := MulAction.compHom C A.subtype
  have hbase_fixed (a : A) : a • base = base := by
    apply Subtype.ext
    change (a : G) • A = A
    exact (hsmul_normalizer (a : G) A).mpr
      (Subgroup.le_normalizer a.property)
  letI : MulAction A X :=
    { smul := fun a x => ⟨a • (x : C), by
        intro h
        apply x.2
        have hax : a • (x : C) = base := h
        calc
          (x : C) = a⁻¹ • (a • (x : C)) :=
            (inv_smul_smul a (x : C)).symm
          _ = a⁻¹ • base := congrArg (fun y : C => a⁻¹ • y) hax
          _ = base := hbase_fixed a⁻¹⟩
      one_smul := by
        intro x
        apply Subtype.ext
        exact one_smul A (x : C)
      mul_smul := by
        intro a b x
        apply Subtype.ext
        exact mul_smul a b (x : C) }
  have hCcard : Nat.card C =
      (Subgroup.normalizer (A : Set G)).index := by
    change Nat.card ↥(MulAction.orbitRel.Quotient.orbit q) = _
    rw [show MulAction.orbitRel.Quotient.orbit q = MulAction.orbit G A by
      simp [q], Nat.card_coe_set_eq, ← MulAction.index_stabilizer G A, hstabA]
  have hXcard : Nat.card X = Nat.card C - 1 := by
    letI : Fintype C := Fintype.ofFinite C
    letI : Fintype X := Fintype.ofFinite X
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    change Fintype.card {x : C // x ≠ base} = Fintype.card C - 1
    simp
  have hstabilizer (x : X) :
      Nat.card (MulAction.stabilizer A x) ≤ 2 := by
    let St : Subgroup A := MulAction.stabilizer A x
    let S : Subgroup G := St.map A.subtype
    have hQconj : ∃ g : G,
        (((x : X) : C) : Subgroup G) =
          A.map (MulAut.conj g).toMonoidHom := by
      have hx := ((x : X) : C).property
      change (((x : X) : C) : Subgroup G) ∈
        MulAction.orbitRel.Quotient.orbit q at hx
      rw [show MulAction.orbitRel.Quotient.orbit q = MulAction.orbit G A by
        simp [q]] at hx
      rcases hx with ⟨g, hg⟩
      exact ⟨g, hg.symm⟩
    have hSleN : S ≤ Subgroup.normalizer
        ((((x : X) : C) : Subgroup G) : Set G) := by
      rintro y ⟨z, hz, rfl⟩
      have hfix : z • x = x := MulAction.mem_stabilizer_iff.mp hz
      have hfixC : z • ((x : X) : C) = ((x : X) : C) :=
        congrArg Subtype.val hfix
      have hfix' : (z : G) • (((x : X) : C) : Subgroup G) =
          (((x : X) : C) : Subgroup G) := congrArg Subtype.val hfixC
      exact (hsmul_normalizer (z : G)
        (((x : X) : C) : Subgroup G)).mp hfix'
    have hSleA : S ≤ A := by
      rintro y ⟨z, _hz, rfl⟩
      exact z.property
    obtain ⟨g, hg⟩ := hQconj
    have hQne : (((x : X) : C) : Subgroup G) ≠ A := by
      intro heq
      apply x.2
      apply Subtype.ext
      exact heq
    have hmap_ne : A.map (MulAut.conj g).toMonoidHom ≠ A := by
      rw [← hg]
      exact hQne
    have hdisjAQ : Disjoint A (((x : X) : C) : Subgroup G) := by
      rw [hg]
      exact hdisjoint g hmap_ne
    have hdisjSQ : Disjoint S (((x : X) : C) : Subgroup G) :=
      hdisjAQ.mono hSleA le_rfl
    have hQnormalizer : Nat.card (Subgroup.normalizer
        ((((x : X) : C) : Subgroup G) : Set G)) =
        2 * Nat.card (((x : X) : C) : Subgroup G) := by
      rw [hg,
        ← Subgroup.map_normalizer_eq_of_bijective A (MulAut.conj g).bijective,
        Subgroup.card_map_of_injective (MulAut.conj g).injective,
        Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hA_normalizer
    calc
      Nat.card St = Nat.card S := by
        symm
        exact Subgroup.card_map_of_injective A.subtype_injective
      _ ≤ 2 := h826_subgroup_card_le_two_of_disjoint_le_normalizer
        (((x : X) : C) : Subgroup G) S hSleN hdisjSQ hQnormalizer
  have hdiv :=
    h826_card_actor_dvd_two_mul_card_of_stabilizer_card_le_two hstabilizer
  rwa [hXcard, hCcard] at hdiv

private theorem h826_distinct_torus_conjugates_disjoint
    {F : Type*} [Field F] [Finite F] {p f r : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (Z : Fin r → Subgroup H)
    (hcyclic : ∀ i, IsCyclic (Z i))
    (hnontrivial : ∀ i, 1 < Nat.card (Z i))
    (hcoprime : ∀ i, Nat.Coprime p (Nat.card (Z i)))
    (hmaximal : ∀ i (W : Subgroup H),
      IsCyclic W → Z i ≤ W → W = Z i)
    (hrepresentative : ∀ W : Subgroup H,
      IsCyclic W → 1 < Nat.card W →
      Nat.Coprime p (Nat.card W) →
      (∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) →
      ∃ i g, W = (Z i).map (MulAut.conj g).toMonoidHom)
    (hdistinct : ∀ i j g,
      (Z i).map (MulAut.conj g).toMonoidHom = Z j → i = j)
    {i j : Fin r} {A B : Subgroup H}
    (hA : ∃ g, A = (Z i).map (MulAut.conj g).toMonoidHom)
    (hB : ∃ g, B = (Z j).map (MulAut.conj g).toMonoidHom)
    (hAB : A ≠ B) :
    Disjoint A B := by
  rw [Subgroup.disjoint_def]
  intro x hxA hxB
  by_contra hx
  have hu := huppert_II_8_22_unique_family hFcard H Z hcyclic
    hnontrivial hcoprime hmaximal hrepresentative hdistinct x hx
  let a : (Sylow p H) ⊕
      (Σ k : Fin r, {W : Subgroup H // ∃ g : H,
        W = (Z k).map (MulAut.conj g).toMonoidHom}) :=
    Sum.inr ⟨i, ⟨A, hA⟩⟩
  let b : (Sylow p H) ⊕
      (Σ k : Fin r, {W : Subgroup H // ∃ g : H,
        W = (Z k).map (MulAut.conj g).toMonoidHom}) :=
    Sum.inr ⟨j, ⟨B, hB⟩⟩
  have ha : x ∈ match a with
      | Sum.inl Q => (Q : Subgroup H)
      | Sum.inr z => (z.2.1 : Subgroup H) := hxA
  have hb : x ∈ match b with
      | Sum.inl Q => (Q : Subgroup H)
      | Sum.inr z => (z.2.1 : Subgroup H) := hxB
  have hab : a = b := hu.unique ha hb
  have hab' := Sum.inr.inj hab
  have hsub : A = B := congrArg
    (fun z : Σ k : Fin r, {W : Subgroup H // ∃ g : H,
      W = (Z k).map (MulAut.conj g).toMonoidHom} =>
        (z.2.1 : Subgroup H)) hab'
  exact hAB hsub

private theorem h826_card_actor_dvd_group_card_sub_one
    {A E : Type*} [Group A] [Finite A] [Group E] [Finite E]
    [MulDistribMulAction A E]
    (hfree : ∀ a : A, a ≠ 1 → ∀ e : E, a • e = e → e = 1) :
    Nat.card A ∣ Nat.card E - 1 := by
  classical
  let X := {e : E // e ≠ 1}
  letI : MulAction A X :=
    { smul := fun a e => ⟨a • (e : E), by
        intro h
        apply e.2
        have h' := congrArg (fun x : E => a⁻¹ • x) h
        simpa using h'⟩
      one_smul := by
        intro e
        apply Subtype.ext
        change (1 : A) • (e : E) = (e : E)
        exact one_smul A (e : E)
      mul_smul := by
        intro a b e
        apply Subtype.ext
        change (a * b) • (e : E) = a • (b • (e : E))
        exact mul_smul a b (e : E) }
  have hstab : ∀ e : X, MulAction.stabilizer A e = ⊥ := by
    intro e
    rw [eq_bot_iff]
    intro a ha
    have hae : a • e = e := by
      simpa [MulAction.mem_stabilizer_iff] using ha
    by_contra ha_ne_one
    have hfix : a • (e : E) = (e : E) := congrArg Subtype.val hae
    exact e.2 (hfree a ha_ne_one (e : E) hfix)
  have hcard := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
  have hXcard : Nat.card X = Nat.card E - 1 := by
    letI : Fintype E := Fintype.ofFinite E
    letI : Fintype X := Fintype.ofFinite X
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    change Fintype.card {e : E // e ≠ 1} = Fintype.card E - 1
    simp
  rw [hXcard, Nat.card_prod] at hcard
  exact ⟨Nat.card (Quotient (MulAction.orbitRel A X)), by
    rw [mul_comm]
    exact hcard⟩

private theorem h826_card_actor_dvd_two_mul_card
    {A X : Type*} [Group A] [Finite A] [Finite X] [MulAction A X]
    (hstab : ∀ x : X, Nat.card (MulAction.stabilizer A x) ≤ 2) :
    Nat.card A ∣ 2 * Nat.card X := by
  classical
  let Ω := Quotient (MulAction.orbitRel A X)
  letI : Fintype Ω := Fintype.ofFinite Ω
  have horbit (ω : Ω) :
      Nat.card A ∣ 2 * Nat.card (MulAction.orbit A ω.out) := by
    letI : Fintype A := Fintype.ofFinite A
    letI : Fintype (MulAction.orbit A ω.out) := Fintype.ofFinite _
    letI : Fintype (MulAction.stabilizer A ω.out) := Fintype.ofFinite _
    have hmul :
        Nat.card (MulAction.orbit A ω.out) *
            Nat.card (MulAction.stabilizer A ω.out) = Nat.card A := by
      simpa [Nat.card_eq_fintype_card] using
        MulAction.card_orbit_mul_card_stabilizer_eq_card_group A ω.out
    have hstab_cases :
        Nat.card (MulAction.stabilizer A ω.out) = 1 ∨
          Nat.card (MulAction.stabilizer A ω.out) = 2 := by
      have hpos : 0 < Nat.card (MulAction.stabilizer A ω.out) := Nat.card_pos
      have hle := hstab ω.out
      omega
    rcases hstab_cases with hs | hs
    · rw [hs, mul_one] at hmul
      rw [← hmul]
      exact ⟨2, by ring⟩
    · rw [hs] at hmul
      rw [← hmul]
      exact ⟨1, by ring⟩
  have hcardX :
      Nat.card X = ∑ ω : Ω, Nat.card (MulAction.orbit A ω.out) := by
    calc
      Nat.card X =
          Nat.card (Σ ω : Ω, MulAction.orbit A ω.out) :=
        Nat.card_congr (MulAction.selfEquivSigmaOrbits A X)
      _ = ∑ ω : Ω, Nat.card (MulAction.orbit A ω.out) := Nat.card_sigma
  have hsum :
      Nat.card A ∣
        ∑ ω : Ω, 2 * Nat.card (MulAction.orbit A ω.out) := by
    exact Finset.dvd_sum fun ω _hω => horbit ω
  simpa only [hcardX, Finset.mul_sum] using hsum

private theorem h826_card_pgl2
    {K : Type u} [Field K] [Finite K] :
    Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  let GL2 := GL (Fin 2) K
  let PGL2 := Matrix.ProjGenLinGroup (Fin 2) K
  let centerGL := Subgroup.center GL2
  have hscalar_inj : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ → GL2) := by
    intro x y hxy
    apply Units.ext
    have h := congrArg (fun A : GL2 =>
      ((A : Matrix (Fin 2) (Fin 2) K) 0 0)) hxy
    simpa [Matrix.GeneralLinearGroup.scalar] using h
  have hcenter : Nat.card centerGL = Nat.card K - 1 := by
    dsimp [centerGL, GL2]
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    calc
      Nat.card
          (Matrix.GeneralLinearGroup.scalar (Fin 2)).range =
          Nat.card Kˣ :=
        (Nat.card_congr (Equiv.ofInjective
          (Matrix.GeneralLinearGroup.scalar (Fin 2)) hscalar_inj)).symm
      _ = Nat.card K - 1 := by
        simpa [Nat.card_eq_fintype_card] using Fintype.card_units K
  have hGL : Nat.card GL2 =
      (Nat.card K ^ 2 - 1) *
        (Nat.card K ^ 2 - Nat.card K) := by
    simpa [GL2, Fin.prod_univ_two] using
      (Matrix.card_GL_field (𝔽 := K) 2)
  let mkPGL : GL2 →* PGL2 := Matrix.ProjGenLinGroup.mk
  have hrange : mkPGL.range = ⊤ :=
    MonoidHom.range_eq_top.mpr Matrix.ProjGenLinGroup.mk_surjective
  have hindex : centerGL.index = Nat.card PGL2 := by
    calc
      centerGL.index = mkPGL.ker.index := by
        rw [Matrix.ProjGenLinGroup.ker_mk]
      _ = Nat.card mkPGL.range := Subgroup.index_ker mkPGL
      _ = Nat.card PGL2 := by rw [hrange]; simp
  have hmul := centerGL.index_mul_card
  rw [hindex, hcenter, hGL] at hmul
  have hdiff : Nat.card K ^ 2 - Nat.card K =
      Nat.card K * (Nat.card K - 1) := by
    rw [pow_two]
    calc
      Nat.card K * Nat.card K - Nat.card K =
          Nat.card K * Nat.card K - Nat.card K * 1 := by simp
      _ = Nat.card K * (Nat.card K - 1) :=
        (Nat.mul_sub_left_distrib _ _ _).symm
  rw [hdiff] at hmul
  apply Nat.eq_of_mul_eq_mul_left
    (Nat.sub_pos_iff_lt.mpr (Finite.one_lt_card (α := K)))
  calc
    (Nat.card K - 1) * Nat.card PGL2 =
        Nat.card PGL2 * (Nat.card K - 1) := by ac_rfl
    _ = (Nat.card K ^ 2 - 1) *
        (Nat.card K * (Nat.card K - 1)) := hmul
    _ = (Nat.card K - 1) *
        (Nat.card K * (Nat.card K ^ 2 - 1)) := by ring

private def h826_pglMap
    {K : Type u} {F : Type v} [Field K] [Field F]
    (e : K →+* F) :
    Matrix.ProjGenLinGroup (Fin 2) K →*
      Matrix.ProjGenLinGroup (Fin 2) F := by
  let f : GL (Fin 2) K →*
      Matrix.ProjGenLinGroup (Fin 2) F :=
    Matrix.ProjGenLinGroup.mk.comp
      (Matrix.GeneralLinearGroup.map e)
  apply Matrix.ProjGenLinGroup.lift f
  ext a
  change Matrix.ProjGenLinGroup.mk
      (Matrix.GeneralLinearGroup.map e
        (Matrix.GeneralLinearGroup.scalar (Fin 2) a)) = 1
  rw [← MonoidHom.mem_ker, Matrix.ProjGenLinGroup.ker_mk,
    Matrix.GeneralLinearGroup.center_eq_range_scalar]
  refine ⟨Units.map e a, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.map,
      Matrix.GeneralLinearGroup.scalar]

set_option backward.isDefEq.respectTransparency false in
private theorem h826_pglMap_mk
    {K : Type u} {F : Type v} [Field K] [Field F]
    (e : K →+* F) (A : GL (Fin 2) K) :
    h826_pglMap e (Matrix.ProjGenLinGroup.mk A) =
      Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.map e A) := by
  unfold h826_pglMap
  exact Matrix.ProjGenLinGroup.lift_mk _ A

private theorem h826_pglMap_injective
    {K : Type u} {F : Type v} [Field K] [Field F]
    (e : K →+* F) (he : Function.Injective e) :
    Function.Injective (h826_pglMap e) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext x
  constructor
  · intro hx
    rcases Matrix.ProjGenLinGroup.mk_surjective x with ⟨A, rfl⟩
    rw [MonoidHom.mem_ker, h826_pglMap_mk] at hx
    have hcenterF :
        Matrix.GeneralLinearGroup.map e A ∈
          Subgroup.center (GL (Fin 2) F) := by
      rw [← Matrix.ProjGenLinGroup.ker_mk, MonoidHom.mem_ker]
      exact hx
    rcases
        Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp
          hcenterF with ⟨c, hc⟩
    have hc00 :
        c = e ((A : Matrix (Fin 2) (Fin 2) K) 0 0) := by
      have h := congrFun (congrFun hc (0 : Fin 2)) (0 : Fin 2)
      simpa [Matrix.GeneralLinearGroup.map_apply] using h
    have hcenterK : A ∈ Subgroup.center (GL (Fin 2) K) := by
      rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
      refine ⟨(A : Matrix (Fin 2) (Fin 2) K) 0 0, ?_⟩
      ext i j
      apply he
      have h := congrFun (congrFun hc i) j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.GeneralLinearGroup.map_apply, hc00] at h ⊢ <;>
        exact h
    rw [Subgroup.mem_bot, ← MonoidHom.mem_ker,
      Matrix.ProjGenLinGroup.ker_mk]
    exact hcenterK
  · intro hx
    rw [Subgroup.mem_bot] at hx
    simp [hx]

private def h826_pslToPGL
    {K : Type u} [Field K] :
    PSL2MatrixGroup K →*
      Matrix.ProjGenLinGroup (Fin 2) K := by
  let f : Matrix.SpecialLinearGroup (Fin 2) K →*
      Matrix.ProjGenLinGroup (Fin 2) K :=
    Matrix.ProjGenLinGroup.mk.comp
      Matrix.SpecialLinearGroup.toGL
  apply QuotientGroup.lift
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) f
  intro A hA
  rw [MonoidHom.mem_ker]
  change Matrix.ProjGenLinGroup.mk
      (Matrix.SpecialLinearGroup.toGL A) = 1
  rw [← MonoidHom.mem_ker, Matrix.ProjGenLinGroup.ker_mk]
  apply Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.2
  rcases Matrix.SpecialLinearGroup.mem_center_iff.mp hA with
    ⟨c, _, hc⟩
  exact ⟨c, by simpa using hc⟩

private theorem h826_pslToPGL_mk
    {K : Type u} [Field K]
    (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    h826_pslToPGL
        (QuotientGroup.mk'
          (Subgroup.center
            (Matrix.SpecialLinearGroup (Fin 2) K)) A) =
      Matrix.ProjGenLinGroup.mk
        (Matrix.SpecialLinearGroup.toGL A) := by
  rfl

private theorem h826_pslToPGL_injective
    {K : Type u} [Field K] :
    Function.Injective (h826_pslToPGL (K := K)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext x
  constructor
  · intro hx
    rcases QuotientGroup.mk'_surjective
        (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) K)) x with ⟨A, rfl⟩
    rw [MonoidHom.mem_ker, h826_pslToPGL_mk] at hx
    have hcenterGL :
        Matrix.SpecialLinearGroup.toGL A ∈
          Subgroup.center (GL (Fin 2) K) := by
      rw [← Matrix.ProjGenLinGroup.ker_mk, MonoidHom.mem_ker]
      exact hx
    rcases
        Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp
          hcenterGL with ⟨c, hc⟩
    have hc_sq : c ^ 2 = 1 := by
      have hc' :
          Matrix.scalar (Fin 2) c =
            (A : Matrix (Fin 2) (Fin 2) K) := by
        simpa using hc
      have hdet := A.property
      rw [← hc'] at hdet
      simpa [Matrix.det_diagonal, Fin.prod_univ_two, pow_two] using hdet
    have hcenterSL :
        A ∈ Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) K) := by
      rw [Matrix.SpecialLinearGroup.mem_center_iff]
      exact ⟨c, by simpa using hc_sq, by simpa using hc⟩
    exact (QuotientGroup.eq_one_iff A).mpr hcenterSL
  · intro hx
    rw [Subgroup.mem_bot] at hx
    simp [hx]

private def h826_slEquiv
    {K : Type u} {L : Type v} [Field K] [Field L]
    (e : K ≃+* L) :
    Matrix.SpecialLinearGroup (Fin 2) K ≃*
      Matrix.SpecialLinearGroup (Fin 2) L := by
  let f : Matrix.SpecialLinearGroup (Fin 2) K →*
      Matrix.SpecialLinearGroup (Fin 2) L :=
    Matrix.SpecialLinearGroup.map e.toRingHom
  let g : Matrix.SpecialLinearGroup (Fin 2) L →*
      Matrix.SpecialLinearGroup (Fin 2) K :=
    Matrix.SpecialLinearGroup.map e.symm.toRingHom
  apply MonoidHom.toMulEquiv f g
  · apply MonoidHom.ext
    intro A
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [f, g, Matrix.SpecialLinearGroup.map_apply_coe]
  · apply MonoidHom.ext
    intro A
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [f, g, Matrix.SpecialLinearGroup.map_apply_coe]

private def h826_pslEquiv
    {K : Type u} {L : Type v} [Field K] [Field L]
    (e : K ≃+* L) :
    PSL2MatrixGroup K ≃* PSL2MatrixGroup L := by
  let eSL := h826_slEquiv e
  apply QuotientGroup.congr
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) L)) eSL
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    exact (MulEquivClass.apply_mem_center_iff eSL).2 hB
  · intro hA
    refine ⟨eSL.symm A, ?_, eSL.apply_symm_apply A⟩
    exact (MulEquivClass.apply_mem_center_iff eSL.symm).2 hA

set_option backward.isDefEq.respectTransparency false in
private theorem h826_pslToPGL_range_le_of_index_two
    {K : Type u} [Field K] [Finite K]
    (htwo : (2 : K) ≠ 0)
    (M : Subgroup (Matrix.ProjGenLinGroup (Fin 2) K))
    (hMindex : M.index = 2) :
    (h826_pslToPGL (K := K)).range ≤ M := by
  classical
  intro x hx
  rcases hx with ⟨y, rfl⟩
  induction y using QuotientGroup.induction_on with
  | _ A =>
      change h826_pslToPGL
          (QuotientGroup.mk'
            (Subgroup.center
              (Matrix.SpecialLinearGroup (Fin 2) K)) A) ∈ M
      rw [h826_pslToPGL_mk]
      let PMatrix : Matrix (Fin 2) (Fin 2) K → Prop := fun B =>
        ∃ hB : Matrix.det B = 1,
          Matrix.ProjGenLinGroup.mk
            (Matrix.SpecialLinearGroup.toGL
              (⟨B, hB⟩ : Matrix.SpecialLinearGroup (Fin 2) K)) ∈ M
      have hP : PMatrix (A : Matrix (Fin 2) (Fin 2) K) := by
        apply Matrix.diagonal_transvection_induction PMatrix
        · intro D hdet
          have hDdet : Matrix.det (Matrix.diagonal D) = 1 :=
            hdet.trans A.property
          let AD : Matrix.SpecialLinearGroup (Fin 2) K :=
            ⟨Matrix.diagonal D, hDdet⟩
          have hDprod : D 0 * D 1 = 1 := by
            simpa [Matrix.det_diagonal, Fin.prod_univ_two] using hDdet
          have hD0ne : D 0 ≠ 0 := by
            intro hzero
            rw [hzero, zero_mul] at hDprod
            exact zero_ne_one hDprod
          let B : GL (Fin 2) K :=
            Matrix.GeneralLinearGroup.mkOfDetNeZero
              !![D 0, 0; 0, 1]
              (by simp [Matrix.det_fin_two, hD0ne])
          let d0 : Kˣ := Units.mk0 (D 0) hD0ne
          have hmat :
              B * B =
                Matrix.GeneralLinearGroup.scalar (Fin 2) d0 *
                  Matrix.SpecialLinearGroup.toGL AD := by
            apply Matrix.GeneralLinearGroup.ext
            intro i j
            fin_cases i <;> fin_cases j <;>
              simp [B, d0, AD, Matrix.GeneralLinearGroup.scalar,
                Matrix.mul_apply, hDprod]
          refine ⟨hDdet, ?_⟩
          have hsquare :=
            Subgroup.sq_mem_of_index_two hMindex
              (Matrix.ProjGenLinGroup.mk B)
          rw [pow_two, ← map_mul, hmat, map_mul,
            Matrix.ProjGenLinGroup.mk_scalar, one_mul] at hsquare
          exact hsquare
        · intro t
          let thalf : Matrix.TransvectionStruct (Fin 2) K :=
            ⟨t.i, t.j, t.hij, t.c / 2⟩
          let B : Matrix.SpecialLinearGroup (Fin 2) K :=
            ⟨thalf.toMatrix, thalf.det⟩
          let C : Matrix.SpecialLinearGroup (Fin 2) K :=
            ⟨t.toMatrix, t.det⟩
          have hc : t.c / 2 + t.c / 2 = t.c := by
            field_simp
            ring
          have hBC : B * B = C := by
            apply Subtype.ext
            change Matrix.transvection t.i t.j (t.c / 2) *
                Matrix.transvection t.i t.j (t.c / 2) =
              Matrix.transvection t.i t.j t.c
            rw [Matrix.transvection_mul_transvection_same
              t.i t.j t.hij, hc]
          refine ⟨t.det, ?_⟩
          have hsquare :=
            Subgroup.sq_mem_of_index_two hMindex
              (Matrix.ProjGenLinGroup.mk
                (Matrix.SpecialLinearGroup.toGL B))
          rw [pow_two, ← map_mul, ← map_mul, hBC] at hsquare
          exact hsquare
        · rintro B C ⟨hBdet, hB⟩ ⟨hCdet, hC⟩
          have hBCdet : Matrix.det (B * C) = 1 := by
            simp [hBdet, hCdet]
          let Bs : Matrix.SpecialLinearGroup (Fin 2) K := ⟨B, hBdet⟩
          let Cs : Matrix.SpecialLinearGroup (Fin 2) K := ⟨C, hCdet⟩
          let BCs : Matrix.SpecialLinearGroup (Fin 2) K :=
            ⟨B * C, hBCdet⟩
          have hmul : Bs * Cs = BCs := by rfl
          refine ⟨hBCdet, ?_⟩
          change Matrix.ProjGenLinGroup.mk
              (Matrix.SpecialLinearGroup.toGL BCs) ∈ M
          rw [← hmul, map_mul, map_mul]
          exact M.mul_mem hB hC
      rcases hP with ⟨hdet, hmem⟩
      simpa only [Subsingleton.elim hdet A.property] using hmem

private theorem h826_pslToPGL_range_index_eq_two
    {K : Type u} [Field K] [Finite K]
    (hneg : (-1 : K) ≠ 1) :
    (h826_pslToPGL (K := K)).range.index = 2 := by
  let iota := h826_pslToPGL (K := K)
  have hcenter :
      Nat.card
          (Subgroup.center
            (Matrix.SpecialLinearGroup (Fin 2) K)) = 2 :=
    huppert614_card_center_of_neg_one_ne_one hneg
  have hPSLmul := huppert614_card_psl_mul_center (K := K)
  rw [hcenter] at hPSLmul
  have hPGLcard := h826_card_pgl2 (K := K)
  have hrangeCard :
      Nat.card (PSL2MatrixGroup K) = Nat.card iota.range :=
    Nat.card_congr (MonoidHom.ofInjective h826_pslToPGL_injective).toEquiv
  have hindex := iota.range.index_mul_card
  rw [← hrangeCard, hPGLcard, ← hPSLmul] at hindex
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := PSL2MatrixGroup K))
  calc
    iota.range.index * Nat.card (PSL2MatrixGroup K) =
        Nat.card (PSL2MatrixGroup K) * 2 := hindex
    _ = 2 * Nat.card (PSL2MatrixGroup K) := by ring

private theorem h826_index_two_subgroup_eq_pslRange
    {K : Type u} [Field K] [Finite K]
    (htwo : (2 : K) ≠ 0)
    (M : Subgroup (Matrix.ProjGenLinGroup (Fin 2) K))
    (hMindex : M.index = 2)
    (hPSLindex : (h826_pslToPGL (K := K)).range.index = 2) :
    M = (h826_pslToPGL (K := K)).range := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  let R := (h826_pslToPGL (K := K)).range
  letI : Finite (Matrix.ProjGenLinGroup (Fin 2) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  letI : Finite M := Finite.of_injective M.subtype M.subtype_injective
  letI : Finite R := Finite.of_injective R.subtype R.subtype_injective
  have hRleM : R ≤ M :=
    h826_pslToPGL_range_le_of_index_two htwo M hMindex
  have hMcard := M.card_mul_index
  have hRcard := R.card_mul_index
  rw [hMindex] at hMcard
  rw [hPSLindex] at hRcard
  have hcardEq : Nat.card M = Nat.card R := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2)
    exact hMcard.trans hRcard.symm
  exact (Subgroup.eq_of_le_of_card_ge hRleM (by rw [hcardEq])).symm

private def h826_scalarStabilizer
    {F : Type*} [Field F] [Finite F] (W : AddSubgroup F) :
    Subfield F where
  carrier := {a | ∀ x : F, x ∈ W → a * x ∈ W}
  zero_mem' := by
    intro x hx
    simpa using W.zero_mem
  one_mem' := by
    intro x hx
    simpa using hx
  add_mem' := by
    intro a b ha hb x hx
    rw [add_mul]
    exact W.add_mem (ha x hx) (hb x hx)
  neg_mem' := by
    intro a ha x hx
    rw [neg_mul]
    exact W.neg_mem (ha x hx)
  mul_mem' := by
    intro a b ha hb x hx
    rw [mul_assoc]
    exact ha (b * x) (hb x hx)
  inv_mem' := by
    intro a ha
    by_cases ha0 : a = 0
    · subst a
      intro x hx
      simpa using W.zero_mem
    · let φ : W → W := fun x => ⟨a * (x : F), ha x x.property⟩
      have hφinj : Function.Injective φ := by
        intro x y hxy
        apply Subtype.ext
        have hval := congrArg Subtype.val hxy
        exact mul_left_cancel₀ ha0 hval
      have hφsurj : Function.Surjective φ :=
        Finite.injective_iff_surjective.mp hφinj
      intro x hx
      obtain ⟨y, hy⟩ := hφsurj ⟨x, hx⟩
      have hyval : a * (y : F) = x := congrArg Subtype.val hy
      have heq : a⁻¹ * x = (y : F) := by
        rw [← hyval]
        field_simp
      rw [heq]
      exact y.property

private theorem h826_exponent_dvd_of_pow_sub_one_dvd
    {p m f : ℕ} (hp : 2 ≤ p)
    (h : p ^ m - 1 ∣ p ^ f - 1) :
    m ∣ f := by
  have hgcd :
      Nat.gcd (p ^ m - 1) (p ^ f - 1) = p ^ m - 1 :=
    Nat.gcd_eq_left_iff_dvd.mpr h
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at hgcd
  have hleft : 1 ≤ p ^ Nat.gcd m f := one_le_pow₀ (by omega)
  have hright : 1 ≤ p ^ m := one_le_pow₀ (by omega)
  have hpow : p ^ Nat.gcd m f = p ^ m := by omega
  have heq : Nat.gcd m f = m := Nat.pow_right_injective hp hpow
  rw [← heq]
  exact Nat.gcd_dvd_right m f

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
private theorem h826_group_order_cases
    (q a b n u v w : ℕ)
    (hq : 1 < q) (ha : 1 < a) (hb : 1 < b)
    (hqa : Nat.Coprime q a) (hqb : Nat.Coprime q b)
    (hadiv : a ∣ q - 1) (hgcd : Nat.gcd a b ∣ 2)
    (hnlcm : n = Nat.lcm (q * a) (Nat.lcm (2 * a) (2 * b)))
    (hqu : (q * a) * u = n)
    (hav : (2 * a) * v = n)
    (hbw : (2 * b) * w = n)
    (hcount :
      n = 1 + (q - 1) * u + (a - 1) * v + (b - 1) * w) :
    (q = 3 ∧ a = 2 ∧ b = 5 ∧ n = 60) ∨
      (a = q - 1 ∧ b = q + 1 ∧
        n = (q + 1) * q * (q - 1)) ∨
      (Nat.Coprime q 2 ∧
        a = (q - 1) / 2 ∧ b = (q + 1) / 2 ∧
        n = ((q + 1) * q * (q - 1)) / Nat.gcd (q - 1) 2) := by
  have hqpos : 0 < q := by omega
  have hap : 0 < a := by omega
  have hbp : 0 < b := by omega
  have hab_dvd_inner : a * b ∣ Nat.lcm (2 * a) (2 * b) := by
    calc
      a * b = Nat.gcd a b * Nat.lcm a b := (Nat.gcd_mul_lcm a b).symm
      _ ∣ 2 * Nat.lcm a b :=
        Nat.mul_dvd_mul_right hgcd (Nat.lcm a b)
      _ = Nat.lcm (2 * a) (2 * b) := (Nat.lcm_mul_left 2 a b).symm
  have hab_dvd_c :
      a * b ∣ Nat.lcm (q * a) (Nat.lcm (2 * a) (2 * b)) :=
    dvd_trans hab_dvd_inner (Nat.dvd_lcm_right _ _)
  have hq_dvd_c :
      q ∣ Nat.lcm (q * a) (Nat.lcm (2 * a) (2 * b)) :=
    dvd_trans (dvd_mul_right q a) (Nat.dvd_lcm_left _ _)
  have hqab_dvd_c :
      q * (a * b) ∣ Nat.lcm (q * a) (Nat.lcm (2 * a) (2 * b)) :=
    (hqa.mul_right hqb).mul_dvd_of_dvd_of_dvd hq_dvd_c hab_dvd_c
  have hc_dvd_twoqab :
      Nat.lcm (q * a) (Nat.lcm (2 * a) (2 * b)) ∣
        2 * q * a * b := by
    apply Nat.lcm_dvd
    · exact ⟨2 * b, by ring⟩
    · apply Nat.lcm_dvd
      · exact ⟨q * b, by ring⟩
      · exact ⟨q * a, by ring⟩
  have hnshape : n = q * a * b ∨ n = 2 * q * a * b := by
    let c := Nat.lcm (q * a) (Nat.lcm (2 * a) (2 * b))
    have hqab_dvd : q * a * b ∣ c := by
      simpa [c, mul_assoc] using hqab_dvd_c
    obtain ⟨k, hk⟩ := hqab_dvd
    have hc_dvd : c ∣ 2 * (q * a * b) := by
      simpa [c, mul_assoc] using hc_dvd_twoqab
    have hk_dvd_two : k ∣ 2 := by
      apply Nat.dvd_of_mul_dvd_mul_left
        (by positivity : 0 < q * a * b)
      have : (q * a * b) * k ∣ (q * a * b) * 2 := by
        rw [← hk]
        simpa [mul_assoc, mul_left_comm, mul_comm] using hc_dvd
      exact this
    have hcpos : 0 < c :=
      Nat.lcm_pos (by positivity)
        (Nat.lcm_pos (by positivity) (by positivity))
    have hkpos : 0 < k := by
      by_contra hk0
      have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
      rw [hkzero, mul_zero] at hk
      exact (Nat.ne_of_gt hcpos) hk
    have hkcases : k = 1 ∨ k = 2 := by
      have hkle : k ≤ 2 := Nat.le_of_dvd (by norm_num) hk_dvd_two
      omega
    rcases hkcases with rfl | rfl
    · left
      rw [hnlcm]
      simpa [c, mul_assoc] using hk
    · right
      rw [hnlcm]
      convert hk using 1 <;> ring
  rcases hnshape with hn | hn
  · have hu : u = b := by
      apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < q * a)
      calc
        (q * a) * u = n := hqu
        _ = (q * a) * b := by simpa [mul_assoc] using hn
    have hv : 2 * v = q * b := by
      apply Nat.eq_of_mul_eq_mul_left hap
      calc
        a * (2 * v) = (2 * a) * v := by ring
        _ = n := hav
        _ = a * (q * b) := by rw [hn]; ring
    have hw : 2 * w = q * a := by
      apply Nat.eq_of_mul_eq_mul_left hbp
      calc
        b * (2 * w) = (2 * b) * w := by ring
        _ = n := hbw
        _ = b * (q * a) := by rw [hn]; ring
    have hrel : q * a + 2 * (b - 1) = q * b := by
      have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel hq.le
      have hasub : a - 1 + 1 = a := Nat.sub_add_cancel ha.le
      have hbsub : b - 1 + 1 = b := Nat.sub_add_cancel hb.le
      have htwosub : 2 * b - 1 + 1 = 2 * b :=
        Nat.sub_add_cancel (by omega : 1 ≤ 2 * b)
      zify at hn hu hv hw hcount hqsub hasub hbsub htwosub ⊢
      nlinarith
    have hab : a < b := by
      by_contra hnot
      have hle : b ≤ a := by omega
      have hmul_le := Nat.mul_le_mul_left q hle
      have hbsub : b - 1 + 1 = b := Nat.sub_add_cancel hb.le
      zify at hrel hle hmul_le hbsub ⊢
      nlinarith
    have hrel' : (b - a) * q = 2 * (b - 1) := by
      have hsub : b - a + a = b := Nat.sub_add_cancel hab.le
      have hbsub : b - 1 + 1 = b := Nat.sub_add_cancel hb.le
      zify at hrel hsub hbsub ⊢
      nlinarith
    have hq_dvd_twice : q ∣ 2 * (b - 1) :=
      ⟨b - a, by simpa [mul_comm] using hrel'.symm⟩
    have hq_dvd_bsub : q ∣ b - 1 := by
      rcases Nat.coprime_or_dvd_of_prime Nat.prime_two q with h2q | h2q
      · exact h2q.symm.dvd_of_dvd_mul_left hq_dvd_twice
      · have ha_not_even : ¬ Even a := by
          intro hae
          have htwo_one : 2 ∣ 1 := by
            rw [← hqa.gcd_eq_one]
            exact Nat.dvd_gcd h2q (even_iff_two_dvd.mp hae)
          norm_num at htwo_one
        have hb_not_even : ¬ Even b := by
          intro hbe
          have htwo_one : 2 ∣ 1 := by
            rw [← hqb.gcd_eq_one]
            exact Nat.dvd_gcd h2q (even_iff_two_dvd.mp hbe)
          norm_num at htwo_one
        have hdelta_even : 2 ∣ b - a := by
          rw [← even_iff_two_dvd, Nat.even_sub hab.le]
          constructor
          · exact fun hbe => (hb_not_even hbe).elim
          · exact fun hae => (ha_not_even hae).elim
        obtain ⟨k, hk⟩ := hdelta_even
        refine ⟨k, ?_⟩
        have hcancel : k * q = b - 1 := by
          rw [hk] at hrel'
          have hbsub : b - 1 + 1 = b := Nat.sub_add_cancel hb.le
          zify at hrel' hbsub ⊢
          nlinarith
        simpa [mul_comm] using hcancel.symm
    obtain ⟨k, hk⟩ := hq_dvd_bsub
    have hbk : b = 1 + q * k := by
      have hbsub : b - 1 + 1 = b := Nat.sub_add_cancel hb.le
      zify at hk hbsub ⊢
      nlinarith
    have hdelta : b - a = 2 * k := by
      apply Nat.eq_of_mul_eq_mul_right hqpos
      calc
        (b - a) * q = 2 * (b - 1) := hrel'
        _ = 2 * (q * k) := by rw [hk]
        _ = (2 * k) * q := by ring
    have hale : a ≤ q - 1 := Nat.le_of_dvd (by omega) hadiv
    have hq3 : 3 ≤ q := by omega
    have hqsub_two : q - 2 + 2 = q :=
      Nat.sub_add_cancel (by omega : 2 ≤ q)
    have hak : a = 1 + k * (q - 2) := by
      zify at hbk hdelta hqsub_two ⊢
      nlinarith
    have hkpos : 0 < k := by omega
    have hk_le_one : k ≤ 1 := by
      have hmul_le : k * (q - 2) ≤ 1 * (q - 2) := by
        have hqsub_one : q - 2 + 1 = q - 1 := by omega
        zify at hak hale hqsub_one ⊢
        nlinarith
      exact (Nat.mul_le_mul_right_iff (by omega : 0 < q - 2)).mp hmul_le
    have hkone : k = 1 := by omega
    right
    left
    have haeq : a = q - 1 := by
      simp [hkone] at hak
      omega
    have hbeq : b = q + 1 := by omega
    refine ⟨haeq, hbeq, ?_⟩
    rw [hn, haeq, hbeq]
    ring
  · have hqodd : Nat.Coprime q 2 := by
      rcases Nat.coprime_or_dvd_of_prime Nat.prime_two q with h2q | h2q
      · exact h2q.symm
      · exfalso
        have hc_dvd_qab :
            Nat.lcm (q * a) (Nat.lcm (2 * a) (2 * b)) ∣
              q * a * b := by
          apply Nat.lcm_dvd
          · exact ⟨b, by ring⟩
          · apply Nat.lcm_dvd
            · obtain ⟨q2, hq2⟩ := h2q
              exact ⟨q2 * b, by rw [hq2]; ring⟩
            · obtain ⟨q2, hq2⟩ := h2q
              exact ⟨q2 * a, by rw [hq2]; ring⟩
        have hdiv : 2 * q * a * b ∣ q * a * b := by
          rw [← hn, hnlcm]
          exact hc_dvd_qab
        have hpos : 0 < q * a * b := by positivity
        have hle := Nat.le_of_dvd hpos hdiv
        have hdouble : 2 * (q * a * b) ≤ q * a * b := by
          simpa [mul_assoc] using hle
        omega
    have hu : u = 2 * b := by
      apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < q * a)
      calc
        (q * a) * u = n := hqu
        _ = (q * a) * (2 * b) := by rw [hn]; ring
    have hv : v = q * b := by
      apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 * a)
      calc
        (2 * a) * v = n := hav
        _ = (2 * a) * (q * b) := by rw [hn]; ring
    have hw : w = q * a := by
      apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 * b)
      calc
        (2 * b) * w = n := hbw
        _ = (2 * b) * (q * a) := by rw [hn]; ring
    have hrel : q * a + (2 * b - 1) = q * b := by
      have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel hq.le
      have hasub : a - 1 + 1 = a := Nat.sub_add_cancel ha.le
      have hbsub : b - 1 + 1 = b := Nat.sub_add_cancel hb.le
      have htwosub : 2 * b - 1 + 1 = 2 * b :=
        Nat.sub_add_cancel (by omega : 1 ≤ 2 * b)
      zify at hn hu hv hw hcount hqsub hasub hbsub htwosub ⊢
      nlinarith
    have hab : a < b := by
      by_contra hnot
      have hle : b ≤ a := by omega
      have hmul_le := Nat.mul_le_mul_left q hle
      have htwosub : 2 * b - 1 + 1 = 2 * b :=
        Nat.sub_add_cancel (by omega : 1 ≤ 2 * b)
      zify at hrel hle hmul_le htwosub ⊢
      nlinarith
    have hrel' : (b - a) * q = 2 * b - 1 := by
      have hsub : b - a + a = b := Nat.sub_add_cancel hab.le
      have htwob : 1 ≤ 2 * b := by omega
      have htwosub : 2 * b - 1 + 1 = 2 * b :=
        Nat.sub_add_cancel htwob
      zify at hrel hsub htwosub ⊢
      nlinarith
    have hq_dvd : q ∣ 2 * b - 1 :=
      ⟨b - a, by simpa [mul_comm] using hrel'.symm⟩
    obtain ⟨k, hk⟩ := hq_dvd
    have htwo_b : 2 * b = 1 + q * k := by omega
    have hdelta : b - a = k := by
      apply Nat.eq_of_mul_eq_mul_right hqpos
      calc
        (b - a) * q = 2 * b - 1 := hrel'
        _ = q * k := hk
        _ = k * q := by ring
    have hak : a + k = b := by omega
    have hale : a ≤ q - 1 := Nat.le_of_dvd (by omega) hadiv
    have hkpos : 0 < k := by omega
    have hqodd' : Odd q := hqodd.odd_of_right
    have hkodd : Odd k := by
      rw [← Nat.not_even_iff_odd]
      intro hkeven
      have hqkeven : Even (q * k) := hkeven.mul_left q
      rcases hqkeven with ⟨r, hr⟩
      omega
    have hkle : k ≤ 3 := by
      have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel hq.le
      have htwosub : 2 * b - 1 + 1 = 2 * b :=
        Nat.sub_add_cancel (by omega : 1 ≤ 2 * b)
      zify at htwo_b hak hale hqsub htwosub ⊢
      nlinarith
    have hkcases : k = 1 ∨ k = 3 := by
      rcases hkodd with ⟨j, hj⟩
      omega
    rcases hkcases with hk1 | hk3
    · right
      right
      have hqgcd : Nat.gcd (q - 1) 2 = 2 := by
        apply Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
        apply Nat.dvd_gcd
        · rcases hqodd' with ⟨r, hr⟩
          exact ⟨r, by simpa [hr]⟩
        · exact dvd_refl 2
      have htwoa : 2 * a = q - 1 := by
        have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel hq.le
        zify at hk1 hak htwo_b hqsub ⊢
        nlinarith
      have htwobb : 2 * b = q + 1 := by
        zify at hk1 htwo_b ⊢
        nlinarith
      have hqsub_even : 2 ∣ q - 1 := ⟨a, htwoa.symm⟩
      have hqadd_even : 2 ∣ q + 1 := ⟨b, htwobb.symm⟩
      have haeq : a = (q - 1) / 2 := by
        rw [← htwoa]
        simp
      have hbeq : b = (q + 1) / 2 := by
        rw [← htwobb]
        simp
      refine ⟨hqodd, haeq, hbeq, ?_⟩
      rw [hn, hqgcd, haeq, hbeq]
      obtain ⟨x, hx⟩ := hqsub_even
      obtain ⟨y, hy⟩ := hqadd_even
      rw [hx, hy]
      simp
      rw [show 2 * y * q * (2 * x) = (2 * q * x * y) * 2 by ring]
      simp
    · left
      have hqle : q ≤ 3 := by
        have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel hq.le
        have hqsub_two : q - 2 + 2 = q :=
          Nat.sub_add_cancel (by omega : 2 ≤ q)
        simp [hk3] at hak htwo_b
        zify at hak htwo_b hale hqsub hqsub_two ⊢
        nlinarith
      have hqeq : q = 3 := by omega
      subst q
      have haeq : a = 2 := by omega
      have hbeq : b = 5 := by omega
      exact ⟨rfl, haeq, hbeq, by simp [hn, haeq, hbeq]⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4000000 in
/-- Huppert II.8.26: the Dickson case with a larger Sylow p-normalizer. -/
public theorem huppert_II_8_26_dickson_case_p_part_normalizer_large
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (P : Sylow p H) (hP_nontrivial : Nat.card P ≠ 1)
    (hnormalizer : Subgroup.normalizer (P : Set H) ≠ (P : Subgroup H)) :
    (∃ m t : ℕ,
      t ∣ p ^ m - 1 ∧
      t ∣ (p ^ f - 1) / Nat.gcd (p ^ f - 1) 2 ∧
      ∃ N C : Subgroup H,
        N.Normal ∧ IsElementaryAbelian p N ∧ Nat.card N = p ^ m ∧
        IsCyclic C ∧ Nat.card C = t ∧ Disjoint N C ∧ N ⊔ C = ⊤) ∨
    (∃ m : ℕ, p ^ m = 3 ∧
      (p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) ∧
      Nonempty (H ≃* alternatingGroup (Fin 5))) ∨
    (∃ m : ℕ, m ≠ 0 ∧ 2 * m ∣ f ∧
      Nonempty (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) ∨
    (∃ m : ℕ, m ≠ 0 ∧ m ∣ f ∧
      Nonempty (H ≃* PSL2MatrixGroup (GaloisField p m))) := by
  obtain ⟨m, hPm⟩ := P.isPGroup'.exists_card_eq
  have hm_ne_zero : m ≠ 0 := by
    intro hm
    subst m
    apply hP_nontrivial
    simpa using hPm
  have h826_counting_shapes :
      Nat.card H = Nat.card (Subgroup.normalizer (P : Set H)) ∨
      (p ^ m = 3 ∧ Nat.card H = 60 ∧
        (p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) ∧
        Nat.card (Sylow 5 H) = 6 ∧
        Function.Injective (MulAction.toPermHom H (Sylow 5 H))) ∨
      (2 * m ∣ f ∧ Nonempty
        (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) ∨
      (m ∣ f ∧ Nonempty
        (H ≃* PSL2MatrixGroup (GaloisField p m))) := by
    classical
    letI : Fintype F := Fintype.ofFinite F
    letI : CharP F p :=
      charP_of_card_eq_prime_pow (by simpa using hFcard)
    rcases huppert_II_8_22_dickson_counting hFcard H P hPm with
      ⟨r, Z, s, hcyclic, hnontrivial, hcoprime, hmaximal,
        hrepresentative, hdistinct, hs, hnormalizerZ, _hdihedral,
        hnormalizerP, hdivides, _hcounting⟩
    let NP : Subgroup H := Subgroup.normalizer (P : Set H)
    let NZ : Fin r → Subgroup H := fun i =>
      Subgroup.normalizer (Z i : Set H)
    let term : Fin r → ℕ := fun i =>
      (Nat.card (Z i) - 1) * (NZ i).index
    have hpartition_count :
        Nat.card H =
          1 + (p ^ m - 1) * NP.index + ∑ i, term i := by
      dsimp only [NP, NZ, term]
      apply huppert_II_8_22_partition_count_of_unique_family P hPm Z
      intro x hx
      convert huppert_II_8_22_unique_family hFcard H Z hcyclic hnontrivial
        hcoprime hmaximal hrepresentative hdistinct x hx using 1
      funext A
      rcases A with Q | z <;> rfl
    have hz_index_factor :
        ∀ i, (Nat.card (Z i) * s i) * (NZ i).index = Nat.card H := by
      intro i
      have hNZcard : Nat.card (NZ i) = Nat.card (Z i) * s i := by
        dsimp only [NZ]
        exact hnormalizerZ i
      calc
        (Nat.card (Z i) * s i) * (NZ i).index =
            Nat.card (NZ i) * (NZ i).index := by rw [hNZcard]
        _ = Nat.card H := (NZ i).card_mul_index
    have hterm_factor (i : Fin r) :
        term i + (NZ i).index =
          Nat.card (Z i) * (NZ i).index := by
      dsimp only [term]
      calc
        (Nat.card (Z i) - 1) * (NZ i).index + (NZ i).index =
            (Nat.card (Z i) - 1 + 1) * (NZ i).index := by ring
        _ = Nat.card (Z i) * (NZ i).index := by
          rw [Nat.sub_add_cancel (hnontrivial i).le]
    have hterm_bound (i : Fin r) :
        Nat.card H ≤ 4 * term i := by
      have hzbound :
          Nat.card (Z i) * s i ≤ 4 * (Nat.card (Z i) - 1) := by
        calc
          Nat.card (Z i) * s i ≤ Nat.card (Z i) * 2 :=
            Nat.mul_le_mul_left (Nat.card (Z i)) (hs i).2
          _ ≤ (2 * (Nat.card (Z i) - 1)) * 2 :=
            Nat.mul_le_mul_right 2 (by
              have hzi := hnontrivial i
              omega)
          _ = 4 * (Nat.card (Z i) - 1) := by ring
      calc
        Nat.card H = (Nat.card (Z i) * s i) * (NZ i).index :=
          (hz_index_factor i).symm
        _ ≤ (4 * (Nat.card (Z i) - 1)) * (NZ i).index :=
          Nat.mul_le_mul_right (NZ i).index hzbound
        _ = 4 * term i := by simp only [term]; ring
    have hfamily_bound : r ≤ 3 := by
      let T := ∑ i, term i
      have hrs : r * Nat.card H ≤ 4 * T := by
        calc
          r * Nat.card H = Finset.univ.sum fun _ : Fin r => Nat.card H := by simp
          _ ≤ Finset.univ.sum fun i : Fin r => 4 * term i :=
            Finset.sum_le_sum fun i _hi => hterm_bound i
          _ = 4 * T := by simp [T, Finset.mul_sum]
      have hTlt : T < Nat.card H := by
        have hcount : Nat.card H =
            1 + (p ^ m - 1) * NP.index + T := by
          simpa only [T] using hpartition_count
        omega
      have hcancel : r * Nat.card H < 4 * Nat.card H :=
        hrs.trans_lt ((Nat.mul_lt_mul_left (by norm_num : 0 < 4)).2 hTlt)
      have hrlt : r < 4 :=
        (Nat.mul_lt_mul_right (Nat.card_pos (α := H))).mp hcancel
      omega
    have hpm_gt : 1 < p ^ m := by
      exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr
        ⟨pow_ne_zero m (Fact.out : p.Prime).ne_zero,
          fun h => hP_nontrivial (hPm.trans h)⟩
    obtain ⟨i0, hNPcard⟩ :
        ∃ i, Nat.card NP = p ^ m * Nat.card (Z i) := by
      rcases hnormalizerP hpm_gt with hsmall | hlarge
      · exfalso
        have hPN : (P : Subgroup H) = NP := by
          apply Subgroup.eq_of_le_of_card_ge Subgroup.le_normalizer
          have hsmall' : Nat.card NP = p ^ m := by
            simpa only [NP] using hsmall
          have hcard_ge : Nat.card NP ≤ Nat.card (P : Subgroup H) := by
            rw [hsmall', hPm]
          exact hcard_ge
        exact hnormalizer (by simpa [NP] using hPN.symm)
      · exact hlarge
    have hNP_index_factor :
        (p ^ m * Nat.card (Z i0)) * NP.index = Nat.card H := by
      calc
        (p ^ m * Nat.card (Z i0)) * NP.index =
            Nat.card NP * NP.index := by rw [hNPcard]
        _ = Nat.card H := NP.card_mul_index
    have hpre_shape :
        Nat.card H = Nat.card NP ∨ (r = 2 ∧ ∀ i, s i = 2) := by
      let rest : Fin r → ℕ := fun i =>
        ∑ j ∈ Finset.univ.erase i, term j
      have hsum_rest (i : Fin r) :
          (∑ j, term j) = term i + rest i := by
        simpa only [rest, add_comm] using
          (Finset.sum_erase_add Finset.univ term (Finset.mem_univ i)).symm
      have hNPindex_pos : 0 < NP.index :=
        Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      have hNZindex_pos (i : Fin r) : 0 < (NZ i).index :=
        Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      have hq_ge_two : 2 ≤ p ^ m := hpm_gt
      have hindex_one (hsi : s i0 = 1) :
          (NZ i0).index = p ^ m * NP.index := by
        apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Z i0))
        calc
          Nat.card (Z i0) * (NZ i0).index = Nat.card H := by
            simpa [hsi] using hz_index_factor i0
          _ = (p ^ m * Nat.card (Z i0)) * NP.index :=
            hNP_index_factor.symm
          _ = Nat.card (Z i0) * (p ^ m * NP.index) := by ring
      have hindex_two (hsi : s i0 = 2) :
          p ^ m * NP.index = 2 * (NZ i0).index := by
        apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Z i0))
        calc
          Nat.card (Z i0) * (p ^ m * NP.index) = Nat.card H := by
            rw [← hNP_index_factor]
            ring
          _ = (Nat.card (Z i0) * 2) * (NZ i0).index := by
            simpa [hsi] using (hz_index_factor i0).symm
          _ = Nat.card (Z i0) * (2 * (NZ i0).index) := by ring
      have hq_term :
          (p ^ m - 1) * NP.index + NP.index = p ^ m * NP.index := by
        calc
          (p ^ m - 1) * NP.index + NP.index =
              (p ^ m - 1 + 1) * NP.index := by ring
          _ = p ^ m * NP.index := by
            rw [Nat.sub_add_cancel hpm_gt.le]
      have hrest_eq_of_one (hsi : s i0 = 1) :
          NP.index = 1 + rest i0 := by
        have hcount := hpartition_count
        rw [hsum_rest i0] at hcount
        have hzfactor :
            Nat.card (Z i0) * (NZ i0).index = Nat.card H := by
          simpa [hsi] using hz_index_factor i0
        have hidx := hindex_one hsi
        have hrel := hterm_factor i0
        omega
      have hrest_lt_of_two (hsi : s i0 = 2) :
          rest i0 < Nat.card (Z i0) * (NZ i0).index := by
        have hcount := hpartition_count
        rw [hsum_rest i0] at hcount
        have hzfactor :
            2 * (Nat.card (Z i0) * (NZ i0).index) = Nat.card H := by
          calc
            2 * (Nat.card (Z i0) * (NZ i0).index) =
                (Nat.card (Z i0) * 2) * (NZ i0).index := by ring
            _ = (Nat.card (Z i0) * s i0) * (NZ i0).index := by rw [hsi]
            _ = Nat.card H := hz_index_factor i0
        have hidx := hindex_two hsi
        have hNPindex_le : NP.index ≤ (NZ i0).index := by
          have hmul := Nat.mul_le_mul_right NP.index hq_ge_two
          rw [hidx] at hmul
          omega
        have hrel := hterm_factor i0
        omega
      have hother_lower_one (hsi : s i0 = 1)
          (j : Fin r) (hji : j ≠ i0) : NP.index ≤ term j := by
        have hfour_le :
            4 * NP.index ≤ Nat.card H := by
          have hqz : 4 ≤ p ^ m * Nat.card (Z i0) :=
            Nat.mul_le_mul hq_ge_two (hnontrivial i0)
          calc
            4 * NP.index ≤
                (p ^ m * Nat.card (Z i0)) * NP.index :=
              Nat.mul_le_mul_right NP.index hqz
            _ = Nat.card H := hNP_index_factor
        have hj := hterm_bound j
        omega
      have hother_lower_two (hsi : s i0 = 2)
          (j : Fin r) (hji : j ≠ i0) :
          Nat.card (Z i0) * (NZ i0).index ≤ 2 * term j := by
        have hzfactor :
            2 * (Nat.card (Z i0) * (NZ i0).index) = Nat.card H := by
          calc
            2 * (Nat.card (Z i0) * (NZ i0).index) =
                (Nat.card (Z i0) * 2) * (NZ i0).index := by ring
            _ = (Nat.card (Z i0) * s i0) * (NZ i0).index := by rw [hsi]
            _ = Nat.card H := hz_index_factor i0
        have hj := hterm_bound j
        omega
      have hr_pos : 0 < r := Nat.zero_lt_of_lt i0.isLt
      have hr_cases : r = 1 ∨ r = 2 ∨ r = 3 := by omega
      rcases hr_cases with hr_one | hr_two | hr_three
      · subst r
        have hi0 : i0 = (0 : Fin 1) := Subsingleton.elim _ _
        subst i0
        rcases (show s 0 = 1 ∨ s 0 = 2 by have h := hs 0; omega) with
          hs0 | hs0
        · left
          have hrest : rest 0 = 0 := by simp [rest]
          have hindex : NP.index = 1 := by
            have h : NP.index = 1 + rest 0 := by
              simpa using hrest_eq_of_one hs0
            omega
          calc
            Nat.card H = Nat.card NP * NP.index := NP.card_mul_index.symm
            _ = Nat.card NP := by rw [hindex, mul_one]
        · exfalso
          have hcount := hpartition_count
          rw [hsum_rest 0] at hcount
          have hrest : rest 0 = 0 := by simp [rest]
          have hzfactor :
              2 * (Nat.card (Z 0) * (NZ 0).index) = Nat.card H := by
            calc
              2 * (Nat.card (Z 0) * (NZ 0).index) =
                  (Nat.card (Z 0) * 2) * (NZ 0).index := by ring
              _ = (Nat.card (Z 0) * s 0) * (NZ 0).index := by rw [hs0]
              _ = Nat.card H := hz_index_factor 0
          have hidx : p ^ m * NP.index = 2 * (NZ 0).index := by
            simpa using hindex_two hs0
          have hNPindex_le : NP.index ≤ (NZ 0).index := by
            have hmul := Nat.mul_le_mul_right NP.index hq_ge_two
            rw [hidx] at hmul
            omega
          have hrel := hterm_factor 0
          have hz_lower :
              2 * (NZ 0).index ≤ Nat.card (Z 0) * (NZ 0).index :=
            Nat.mul_le_mul_right (NZ 0).index (hnontrivial 0)
          omega
      · right
        refine ⟨hr_two, ?_⟩
        subst r
        fin_cases i0
        · have hs0_two : s 0 = 2 := by
            rcases (show s 0 = 1 ∨ s 0 = 2 by have h := hs 0; omega) with
              hs0 | hs0
            · have hrest : NP.index = 1 + rest 0 := by
                simpa using hrest_eq_of_one hs0
              have hlower := hother_lower_one hs0 1 (by decide)
              have hrest_term : rest 0 = term 1 := by
                change (∑ j ∈ Finset.univ.erase (0 : Fin 2), term j) = term 1
                rw [show Finset.univ.erase (0 : Fin 2) = {1} by decide]
                simp
              omega
            · exact hs0
          have hs1_two : s 1 = 2 := by
            rcases (show s 1 = 1 ∨ s 1 = 2 by have h := hs 1; omega) with
              hs1 | hs1
            · have hrest_lt :
                  rest 0 < Nat.card (Z 0) * (NZ 0).index := by
                simpa using hrest_lt_of_two hs0_two
              have hrest_term : rest 0 = term 1 := by
                change (∑ j ∈ Finset.univ.erase (0 : Fin 2), term j) = term 1
                rw [show Finset.univ.erase (0 : Fin 2) = {1} by decide]
                simp
              have hzfactor0 :
                  2 * (Nat.card (Z 0) * (NZ 0).index) = Nat.card H := by
                calc
                  2 * (Nat.card (Z 0) * (NZ 0).index) =
                      (Nat.card (Z 0) * 2) * (NZ 0).index := by ring
                  _ = (Nat.card (Z 0) * s 0) * (NZ 0).index := by rw [hs0_two]
                  _ = Nat.card H := hz_index_factor 0
              have hzfactor1 :
                  Nat.card (Z 1) * (NZ 1).index = Nat.card H := by
                simpa [hs1] using hz_index_factor 1
              have hrel1 := hterm_factor 1
              have hk1_bound :
                  2 * (NZ 1).index ≤ Nat.card H := by
                calc
                  2 * (NZ 1).index ≤
                      Nat.card (Z 1) * (NZ 1).index :=
                    Nat.mul_le_mul_right (NZ 1).index (hnontrivial 1)
                  _ = Nat.card H := hzfactor1
              omega
            · exact hs1
          intro i
          fin_cases i
          · exact hs0_two
          · exact hs1_two
        · have hs1_two : s 1 = 2 := by
            rcases (show s 1 = 1 ∨ s 1 = 2 by have h := hs 1; omega) with
              hs1 | hs1
            · have hrest : NP.index = 1 + rest 1 := by
                simpa using hrest_eq_of_one hs1
              have hlower := hother_lower_one hs1 0 (by decide)
              have hrest_term : rest 1 = term 0 := by
                change (∑ j ∈ Finset.univ.erase (1 : Fin 2), term j) = term 0
                rw [show Finset.univ.erase (1 : Fin 2) = {0} by decide]
                simp
              omega
            · exact hs1
          have hs0_two : s 0 = 2 := by
            rcases (show s 0 = 1 ∨ s 0 = 2 by have h := hs 0; omega) with
              hs0 | hs0
            · have hrest_lt :
                  rest 1 < Nat.card (Z 1) * (NZ 1).index := by
                simpa using hrest_lt_of_two hs1_two
              have hrest_term : rest 1 = term 0 := by
                change (∑ j ∈ Finset.univ.erase (1 : Fin 2), term j) = term 0
                rw [show Finset.univ.erase (1 : Fin 2) = {0} by decide]
                simp
              have hzfactor1 :
                  2 * (Nat.card (Z 1) * (NZ 1).index) = Nat.card H := by
                calc
                  2 * (Nat.card (Z 1) * (NZ 1).index) =
                      (Nat.card (Z 1) * 2) * (NZ 1).index := by ring
                  _ = (Nat.card (Z 1) * s 1) * (NZ 1).index := by rw [hs1_two]
                  _ = Nat.card H := hz_index_factor 1
              have hzfactor0 :
                  Nat.card (Z 0) * (NZ 0).index = Nat.card H := by
                simpa [hs0] using hz_index_factor 0
              have hrel0 := hterm_factor 0
              have hk0_bound :
                  2 * (NZ 0).index ≤ Nat.card H := by
                calc
                  2 * (NZ 0).index ≤
                      Nat.card (Z 0) * (NZ 0).index :=
                    Nat.mul_le_mul_right (NZ 0).index (hnontrivial 0)
                  _ = Nat.card H := hzfactor0
              omega
            · exact hs0
          intro i
          fin_cases i
          · exact hs0_two
          · exact hs1_two
      · exfalso
        subst r
        rcases (show s i0 = 1 ∨ s i0 = 2 by have h := hs i0; omega) with
          hsi | hsi
        · have hrest := hrest_eq_of_one hsi
          have hlower : 2 * NP.index ≤ rest i0 := by
            calc
              2 * NP.index =
                  ∑ j ∈ Finset.univ.erase i0, NP.index := by simp
              _ ≤ ∑ j ∈ Finset.univ.erase i0, term j :=
                Finset.sum_le_sum fun j hj =>
                  hother_lower_one hsi j (Finset.ne_of_mem_erase hj)
              _ = rest i0 := rfl
          omega
        · have hrest := hrest_lt_of_two hsi
          have hlower :
              Nat.card (Z i0) * (NZ i0).index ≤ rest i0 := by
            have hsum :
                2 * (Nat.card (Z i0) * (NZ i0).index) ≤
                  2 * rest i0 := by
              calc
                2 * (Nat.card (Z i0) * (NZ i0).index) =
                    ∑ j ∈ Finset.univ.erase i0,
                      Nat.card (Z i0) * (NZ i0).index := by simp
                _ ≤ ∑ j ∈ Finset.univ.erase i0, 2 * term j :=
                  Finset.sum_le_sum fun j hj =>
                    hother_lower_two hsi j (Finset.ne_of_mem_erase hj)
                _ = 2 * rest i0 := by simp [rest, Finset.mul_sum]
            omega
          omega
    rcases hpre_shape with hnormal | ⟨hr, hs_two⟩
    · exact Or.inl (by simpa [NP] using hnormal)
    · subst r
      have hP_ne_bot : (P : Subgroup H) ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hPm]
        exact hpm_gt
      let PN : Subgroup NP := (P : Subgroup H).subgroupOf NP
      letI : PN.Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer (by
          simpa [NP] : NP ≤ Subgroup.normalizer (P : Set H))
      obtain ⟨hquotient_cyclic, hquotient_card_dvd,
          hNormalizer_fixedPointFree, U, T, conjH, hconjH_injective,
          hU_commutative, hT_cyclic, hTcard, hT_fixedPointFree,
          hP_map_conjH_le_U, hB_le_normalizer, hB_conjugate_torus,
          hNP_maps_B, hU_preimage, unipotent, splitTorus,
          h_unipotent_injective, hU_range, hT_range, hsplit_conj,
          hunipotent_matrix, hsplitTorus_matrix⟩ :=
        h821_borel_quotient_data hFcard H P hP_ne_bot NP rfl PN rfl
      have hi0_divisors :
          Nat.card (Z i0) ∣ p ^ m - 1 ∧
          Nat.card (Z i0) ∣
            (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 := by
        have hquotient_card_dvd_sub_one :
            Nat.card (NP ⧸ PN) ∣ Nat.card F - 1 :=
          dvd_trans hquotient_card_dvd
            (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left (Nat.card F - 1) 2))
        have hf_ne_zero : f ≠ 0 :=
          huppert_II_8_27_field_exponent_ne_zero hFcard
        have hp_dvd_cardF : p ∣ Nat.card F := by
          rw [hFcard]
          exact dvd_pow_self p hf_ne_zero
        have hp_not_dvd_cardF_sub_one : ¬ p ∣ Nat.card F - 1 := by
          intro hp_sub
          have hp_one : p ∣ 1 := by
            have hd := Nat.dvd_sub hp_dvd_cardF hp_sub
            have hsub : Nat.card F - (Nat.card F - 1) = 1 := by
              have hcard_pos : 0 < Nat.card F := Nat.card_pos
              omega
            rwa [hsub] at hd
          exact (Fact.out : p.Prime).not_dvd_one hp_one
        have hcop_p_quotient : Nat.Coprime p (Nat.card (NP ⧸ PN)) :=
          Nat.Coprime.of_dvd_right hquotient_card_dvd_sub_one
            ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
              hp_not_dvd_cardF_sub_one)
        have hPNcard : Nat.card PN = p ^ m := by
          calc
            Nat.card PN = Nat.card P :=
              Nat.card_congr
                (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv
            _ = p ^ m := hPm
        have hPNindex : PN.index = Nat.card (NP ⧸ PN) := rfl
        have hPN_coprime_index : Nat.Coprime (Nat.card PN) PN.index := by
          rw [hPNcard, hPNindex]
          exact hcop_p_quotient.pow_left m
        obtain ⟨C, hcomp⟩ :=
          Subgroup.exists_right_complement'_of_coprime hPN_coprime_index
        have hCcard : Nat.card C = Nat.card (Z i0) := by
          have hmul := hcomp.card_mul
          rw [hPNcard, hNPcard] at hmul
          exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_lt hpm_gt) hmul
        letI : MulDistribMulAction C PN :=
          MulDistribMulAction.compHom PN
            ((MulAut.conjNormal (H := PN)).comp C.subtype)
        have hfree :
            ∀ c : C, c ≠ 1 → ∀ x : PN, c • x = x → x = 1 := by
          intro c hc x hfix
          by_contra hx
          have hc_not_PN : (c : NP) ∉ PN := by
            intro hcPN
            have hc_one : (c : NP) = 1 :=
              Subgroup.disjoint_def.mp hcomp.disjoint hcPN c.property
            apply hc
            apply Subtype.ext
            exact hc_one
          have hx_mem_P : ((x : NP) : H) ∈ (P : Subgroup H) := by
            have hx_mem := x.property
            change ((x : NP) : H) ∈ (P : Subgroup H) at hx_mem
            exact hx_mem
          let xP : P := ⟨((x : NP) : H), hx_mem_P⟩
          have hxP_ne : xP ≠ 1 := by
            intro hxP
            apply hx
            apply Subtype.ext
            apply Subtype.ext
            exact congrArg (fun y : P => (y : H)) hxP
          have hfixNP := congrArg Subtype.val hfix
          change (c : NP) * (x : NP) * (c : NP)⁻¹ = (x : NP) at hfixNP
          have hfixH := congrArg Subtype.val hfixNP
          exact (hNormalizer_fixedPointFree (c : NP) hc_not_PN xP hxP_ne hfixH).elim
        have hCdiv : Nat.card C ∣ p ^ m - 1 := by
          have hdiv := h826_card_actor_dvd_group_card_sub_one hfree
          rwa [hPNcard] at hdiv
        have hCquotient : Nat.card C = Nat.card (NP ⧸ PN) := by
          calc
            Nat.card C = PN.index := hcomp.symm.index_eq_card.symm
            _ = Nat.card (NP ⧸ PN) := rfl
        constructor
        · rwa [← hCcard]
        · rw [← hCcard, hCquotient]
          exact hquotient_card_dvd
      have hi0_dvd_sub_one := hi0_divisors.1
      have hi0_dvd_ambient := hi0_divisors.2
      let i1 : Fin 2 := if i0 = 0 then 1 else 0
      have hi1_ne_i0 : i1 ≠ i0 := by
        fin_cases i0 <;> simp [i1]
      have hi0_ne_i1 : i0 ≠ i1 := Ne.symm hi1_ne_i0
      have huniv_pair : ({i0, i1} : Finset (Fin 2)) = Finset.univ := by
        ext j
        fin_cases i0 <;> fin_cases j <;> simp [i1]
      have htorus_inf_eq_bot (i j : Fin 2) (g : H)
          (hne : Z i ≠ (Z j).map (MulAut.conj g).toMonoidHom) :
          Z i ⊓ (Z j).map (MulAut.conj g).toMonoidHom = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        by_cases hx_one : x = 1
        · simp [hx_one]
        · exfalso
          obtain ⟨A, hxA, hAunique⟩ :=
            huppert_II_8_22_unique_family hFcard H Z hcyclic hnontrivial
              hcoprime hmaximal hrepresentative hdistinct x hx_one
          let Ai : (Sylow p H) ⊕
              (Σ k : Fin 2, {W : Subgroup H // ∃ a : H,
                W = (Z k).map (MulAut.conj a).toMonoidHom}) :=
            Sum.inr ⟨i, ⟨Z i, ⟨1, by ext y; simp [MulAut.conj_apply]⟩⟩⟩
          let Aj : (Sylow p H) ⊕
              (Σ k : Fin 2, {W : Subgroup H // ∃ a : H,
                W = (Z k).map (MulAut.conj a).toMonoidHom}) :=
            Sum.inr ⟨j, ⟨(Z j).map (MulAut.conj g).toMonoidHom, ⟨g, rfl⟩⟩⟩
          have hxAi : x ∈ match Ai with
              | Sum.inl Q => (Q : Subgroup H)
              | Sum.inr z => (z.2.1 : Subgroup H) := by
            simpa [Ai] using hx.1
          have hxAj : x ∈ match Aj with
              | Sum.inl Q => (Q : Subgroup H)
              | Sum.inr z => (z.2.1 : Subgroup H) := by
            simpa [Aj] using hx.2
          have hAiAj : Ai = Aj :=
            (hAunique Ai hxAi).trans (hAunique Aj hxAj).symm
          have hcarrier := congrArg
            (fun B => match B with
              | Sum.inl Q => (Q : Subgroup H)
              | Sum.inr z => (z.2.1 : Subgroup H)) hAiAj
          exact hne (by simpa [Ai, Aj] using hcarrier)
      letI : MulAction H (Subgroup H) := MulAction.compHom _ MulAut.conj
      let X := MulAction.orbit H (Z i0)
      let base : X := ⟨Z i0, MulAction.mem_orbit_self (Z i0)⟩
      letI : Nonempty X := ⟨base⟩
      have hbase_fixed (a : Z i0) : a • base = base := by
        apply Subtype.ext
        change (a : H) • Z i0 = Z i0
        simpa using Subgroup.conj_smul_eq_self_of_mem a.property
      let X0 : SubMulAction (Z i0) X :=
        { carrier := {W | W ≠ base}
          smul_mem' := by
            intro a W hW
            intro haW
            apply hW
            calc
              W = a⁻¹ • (a • W) := (inv_smul_smul a W).symm
              _ = a⁻¹ • base := congrArg (fun Y : X => a⁻¹ • Y) haW
              _ = base := hbase_fixed a⁻¹ }
      have hstab_normalizer (W : Subgroup H) :
          MulAction.stabilizer H W =
            Subgroup.normalizer (W : Set H) := by
        ext g
        change g • W = W ↔ g ∈ Subgroup.normalizer (W : Set H)
        rw [eq_comm, SetLike.ext_iff,
          ← inv_mem_iff (G := H) (H := Subgroup.normalizer W),
          Subgroup.mem_normalizer_iff, inv_inv]
        exact
          forall_congr' fun h =>
            iff_congr Iff.rfl
              ⟨fun ⟨a, b, c⟩ => c ▸ by simpa [mul_assoc] using b,
                fun hh => ⟨(MulAut.conj g)⁻¹ h, hh,
                  MulAut.apply_inv_self H (MulAut.conj g) h⟩⟩
      have horbit_normalizer_card (W : X) :
          Nat.card (Subgroup.normalizer ((W : Subgroup H) : Set H)) =
            2 * Nat.card (W : Subgroup H) := by
        rcases W.property with ⟨g, hg⟩
        have hgmap :
            (W : Subgroup H) =
              (Z i0).map (MulAut.conj g).toMonoidHom := by
          change (W : Subgroup H) = g • Z i0
          exact hg.symm
        calc
          Nat.card (Subgroup.normalizer ((W : Subgroup H) : Set H)) =
              Nat.card (Subgroup.normalizer (Z i0 : Set H)) := by
            rw [hgmap, ← Subgroup.map_equiv_normalizer_eq,
              Subgroup.card_map_of_injective (MulAut.conj g).injective]
          _ = Nat.card (Z i0) * 2 := by rw [hnormalizerZ i0, hs_two i0]
          _ = 2 * Nat.card (W : Subgroup H) := by
            rw [hgmap,
              Subgroup.card_map_of_injective (MulAut.conj g).injective]
            ring
      have hrestricted_stabilizer_card_le_two
          (A : Subgroup H) (W : X)
          (hAW : A ⊓ (W : Subgroup H) = ⊥) :
          Nat.card (MulAction.stabilizer A W) ≤ 2 := by
        let B : Subgroup H :=
          A ⊓ Subgroup.normalizer (((W : Subgroup H)) : Set H)
        have hWB :
            (W : Subgroup H) ⊓ B = ⊥ := by
          calc
            (W : Subgroup H) ⊓ B =
                (A ⊓ (W : Subgroup H)) ⊓
                  Subgroup.normalizer (((W : Subgroup H)) : Set H) := by
              dsimp only [B]
              ac_rfl
            _ = ⊥ := by simp [hAW]
        have hWindex :
            (W : Subgroup H).relIndex
                (Subgroup.normalizer (((W : Subgroup H)) : Set H)) = 2 :=
          relIndex_eq_two_of_card_eq_two_mul
            (W : Subgroup H)
            (Subgroup.normalizer (((W : Subgroup H)) : Set H))
            Subgroup.le_normalizer (horbit_normalizer_card W)
        have hBrel : (⊥ : Subgroup H).relIndex B ≤ 2 :=
          relIndex_le_two_of_inter_eq
            (W : Subgroup H) B
            (Subgroup.normalizer (((W : Subgroup H)) : Set H)) ⊥
            inf_le_right hWB hWindex
        have hBcard : Nat.card B ≤ 2 := by
          simpa only [Subgroup.relIndex_bot_left] using hBrel
        have hstab_eq :
            MulAction.stabilizer A W =
              (Subgroup.normalizer (((W : Subgroup H)) : Set H)).subgroupOf A := by
          ext a
          rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
          constructor
          · intro ha
            have haval := congrArg Subtype.val ha
            change (a : H) • (W : Subgroup H) = (W : Subgroup H) at haval
            have hamem :
                (a : H) ∈ MulAction.stabilizer H (W : Subgroup H) := by
              simpa [MulAction.mem_stabilizer_iff] using haval
            rwa [hstab_normalizer] at hamem
          · intro ha
            apply Subtype.ext
            change (a : H) • (W : Subgroup H) = (W : Subgroup H)
            have hamem :
                (a : H) ∈ MulAction.stabilizer H (W : Subgroup H) := by
              rwa [hstab_normalizer]
            simpa [MulAction.mem_stabilizer_iff] using hamem
        rw [hstab_eq]
        calc
          Nat.card
                ((Subgroup.normalizer (((W : Subgroup H)) : Set H)).subgroupOf A) =
              Nat.card
                (((Subgroup.normalizer (((W : Subgroup H)) : Set H)).subgroupOf A).map
                  A.subtype) :=
            (Subgroup.card_map_of_injective A.subtype_injective).symm
          _ = Nat.card
                ↥((Subgroup.normalizer (((W : Subgroup H)) : Set H) : Subgroup H) ⊓ A) := by
            rw [Subgroup.subgroupOf_map_subtype]
          _ = Nat.card B := by
            apply congrArg (fun K : Subgroup H => Nat.card K)
            dsimp only [B]
            exact inf_comm _ _
          _ ≤ 2 := hBcard
      have hstab_X0 (W : X0) :
          Nat.card (MulAction.stabilizer (Z i0) W) ≤ 2 := by
        have hW_ne : (W : X) ≠ base := W.property
        rcases (W : X).property with ⟨g, hg⟩
        have hgmap :
            ((W : X) : Subgroup H) =
              (Z i0).map (MulAut.conj g).toMonoidHom := by
          change ((W : X) : Subgroup H) = g • Z i0
          exact hg.symm
        have hinter :
            Z i0 ⊓ ((W : X) : Subgroup H) = ⊥ := by
          rw [hgmap]
          apply htorus_inf_eq_bot
          intro heq
          apply hW_ne
          apply Subtype.ext
          exact (heq.trans hgmap.symm).symm
        have hle :=
          hrestricted_stabilizer_card_le_two (Z i0) (W : X) hinter
        have hstab_eq :
            MulAction.stabilizer (Z i0) W =
              MulAction.stabilizer (Z i0) (W : X) := by
          ext a
          simp only [MulAction.mem_stabilizer_iff]
          constructor
          · exact fun h => congrArg Subtype.val h
          · exact fun h => Subtype.ext h
        rwa [hstab_eq]
      have hi0_dvd_orbit_punctured :
          Nat.card (Z i0) ∣ 2 * Nat.card X0 :=
        h826_card_actor_dvd_two_mul_card hstab_X0
      have hX0card : Nat.card X0 = Nat.card X - 1 := by
        change Nat.card {W : X // W ≠ base} = Nat.card X - 1
        letI : Fintype X := Fintype.ofFinite X
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        simp
      have hi0_dvd_orbit :
          Nat.card (Z i0) ∣ 2 * (Nat.card X - 1) := by
        rwa [hX0card] at hi0_dvd_orbit_punctured
      have hstab_i1 (W : X) :
          Nat.card (MulAction.stabilizer (Z i1) W) ≤ 2 := by
        rcases W.property with ⟨g, hg⟩
        have hgmap :
            (W : Subgroup H) =
              (Z i0).map (MulAut.conj g).toMonoidHom := by
          change (W : Subgroup H) = g • Z i0
          exact hg.symm
        have hne : Z i1 ≠
            (Z i0).map (MulAut.conj g).toMonoidHom := by
          intro heq
          apply hi0_ne_i1
          exact hdistinct i0 i1 g heq.symm
        have hinter : Z i1 ⊓ (W : Subgroup H) = ⊥ := by
          rw [hgmap]
          exact htorus_inf_eq_bot i1 i0 g hne
        exact hrestricted_stabilizer_card_le_two (Z i1) W hinter
      have hi1_dvd_orbit :
          Nat.card (Z i1) ∣ 2 * Nat.card X :=
        h826_card_actor_dvd_two_mul_card hstab_i1
      have htorus_gcd :
          Nat.gcd (Nat.card (Z i0)) (Nat.card (Z i1)) ∣ 2 := by
        have hleft :
            Nat.gcd (Nat.card (Z i0)) (Nat.card (Z i1)) ∣
              2 * (Nat.card X - 1) :=
          dvd_trans (Nat.gcd_dvd_left _ _) hi0_dvd_orbit
        have hright :
            Nat.gcd (Nat.card (Z i0)) (Nat.card (Z i1)) ∣
              2 * Nat.card X :=
          dvd_trans (Nat.gcd_dvd_right _ _) hi1_dvd_orbit
        have hsub := Nat.dvd_sub hright hleft
        have hXpos : 0 < Nat.card X := Nat.card_pos
        have hdiff : 2 * Nat.card X - 2 * (Nat.card X - 1) = 2 := by
          omega
        rwa [hdiff] at hsub
      let c := Nat.lcm (p ^ m * Nat.card (Z i0))
        (Nat.lcm (2 * Nat.card (Z i0)) (2 * Nat.card (Z i1)))
      have hi0_factor :
          (2 * Nat.card (Z i0)) * (NZ i0).index = Nat.card H := by
        calc
          (2 * Nat.card (Z i0)) * (NZ i0).index =
              (Nat.card (Z i0) * 2) * (NZ i0).index := by ring
          _ = (Nat.card (Z i0) * s i0) * (NZ i0).index := by
            rw [hs_two i0]
          _ = Nat.card H := hz_index_factor i0
      have hi1_factor :
          (2 * Nat.card (Z i1)) * (NZ i1).index = Nat.card H := by
        calc
          (2 * Nat.card (Z i1)) * (NZ i1).index =
              (Nat.card (Z i1) * 2) * (NZ i1).index := by ring
          _ = (Nat.card (Z i1) * s i1) * (NZ i1).index := by
            rw [hs_two i1]
          _ = Nat.card H := hz_index_factor i1
      have hqa_dvd_c : p ^ m * Nat.card (Z i0) ∣ c := by
        exact Nat.dvd_lcm_left _ _
      have h2a_dvd_c : 2 * Nat.card (Z i0) ∣ c := by
        exact dvd_trans (Nat.dvd_lcm_left _ _) (Nat.dvd_lcm_right _ _)
      have h2b_dvd_c : 2 * Nat.card (Z i1) ∣ c := by
        exact dvd_trans (Nat.dvd_lcm_right _ _) (Nat.dvd_lcm_right _ _)
      have hc_dvd_H : c ∣ Nat.card H := by
        apply Nat.lcm_dvd
        · exact ⟨NP.index, hNP_index_factor.symm⟩
        · apply Nat.lcm_dvd
          · exact ⟨(NZ i0).index, hi0_factor.symm⟩
          · exact ⟨(NZ i1).index, hi1_factor.symm⟩
      have hquotient_dvd_NP : Nat.card H / c ∣ NP.index := by
        have hdiv := Nat.div_dvd_div_left hc_dvd_H hqa_dvd_c
        have hindex : NP.index =
            Nat.card H / (p ^ m * Nat.card (Z i0)) :=
          Nat.eq_div_of_mul_eq_right
            (Nat.ne_of_gt (Nat.mul_pos (Nat.zero_lt_of_lt hpm_gt)
              (Nat.card_pos (α := Z i0)))) hNP_index_factor
        rwa [← hindex] at hdiv
      have hquotient_dvd_NZi0 : Nat.card H / c ∣ (NZ i0).index := by
        have hdiv := Nat.div_dvd_div_left hc_dvd_H h2a_dvd_c
        have hindex : (NZ i0).index =
            Nat.card H / (2 * Nat.card (Z i0)) :=
          Nat.eq_div_of_mul_eq_right
            (Nat.ne_of_gt (Nat.mul_pos (by norm_num)
              (Nat.card_pos (α := Z i0)))) hi0_factor
        rwa [← hindex] at hdiv
      have hquotient_dvd_NZi1 : Nat.card H / c ∣ (NZ i1).index := by
        have hdiv := Nat.div_dvd_div_left hc_dvd_H h2b_dvd_c
        have hindex : (NZ i1).index =
            Nat.card H / (2 * Nat.card (Z i1)) :=
          Nat.eq_div_of_mul_eq_right
            (Nat.ne_of_gt (Nat.mul_pos (by norm_num)
              (Nat.card_pos (α := Z i1)))) hi1_factor
        rwa [← hindex] at hdiv
      have hsum_pair :
          (∑ i, term i) = term i0 + term i1 := by
        rw [← huniv_pair]
        simp [hi0_ne_i1]
      have hcount_pair : Nat.card H =
          1 + (p ^ m - 1) * NP.index +
            (Nat.card (Z i0) - 1) * (NZ i0).index +
            (Nat.card (Z i1) - 1) * (NZ i1).index := by
        rw [hpartition_count, hsum_pair]
        simp only [term]
        ring
      have hquotient_dvd_tail : Nat.card H / c ∣
          (p ^ m - 1) * NP.index +
            (Nat.card (Z i0) - 1) * (NZ i0).index +
            (Nat.card (Z i1) - 1) * (NZ i1).index := by
        exact Nat.dvd_add
          (Nat.dvd_add
            (dvd_mul_of_dvd_right hquotient_dvd_NP _)
            (dvd_mul_of_dvd_right hquotient_dvd_NZi0 _))
          (dvd_mul_of_dvd_right hquotient_dvd_NZi1 _)
      have hquotient_dvd_H : Nat.card H / c ∣ Nat.card H :=
        Nat.div_dvd_of_dvd hc_dvd_H
      have hquotient_dvd_one : Nat.card H / c ∣ 1 := by
        have hsub := Nat.dvd_sub hquotient_dvd_H hquotient_dvd_tail
        have htail_eq : Nat.card H -
            ((p ^ m - 1) * NP.index +
              (Nat.card (Z i0) - 1) * (NZ i0).index +
              (Nat.card (Z i1) - 1) * (NZ i1).index) = 1 := by
          omega
        rwa [htail_eq] at hsub
      have hquotient_one : Nat.card H / c = 1 :=
        Nat.eq_one_of_dvd_one hquotient_dvd_one
      have hH_eq_c : Nat.card H = c := by
        have hmul := Nat.div_mul_cancel hc_dvd_H
        rw [hquotient_one, one_mul] at hmul
        exact hmul.symm
      have hPNcard : Nat.card PN = p ^ m := by
        calc
          Nat.card PN = Nat.card P :=
            Nat.card_congr
              (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv
          _ = p ^ m := hPm
      have hPNindex : PN.index = Nat.card (Z i0) := by
        have hmul := PN.card_mul_index
        rw [hPNcard, hNPcard] at hmul
        exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_lt hpm_gt) hmul
      have hPN_coprime_index : Nat.Coprime (Nat.card PN) PN.index := by
        rw [hPNcard, hPNindex]
        exact (hcoprime i0).pow_left m
      obtain ⟨C, hcomp⟩ :=
        Subgroup.exists_right_complement'_of_coprime hPN_coprime_index
      have hCcyclic : IsCyclic C := by
        let eC : NP ⧸ PN ≃* C := hcomp.symm.QuotientMulEquiv
        letI : IsCyclic (NP ⧸ PN) := hquotient_cyclic
        exact isCyclic_of_surjective eC.toMonoidHom eC.surjective
      have hCcard : Nat.card C = Nat.card (Z i0) := by
        calc
          Nat.card C = PN.index := hcomp.symm.index_eq_card.symm
          _ = Nat.card (Z i0) := hPNindex
      letI : IsCyclic C := hCcyclic
      obtain ⟨cgen, hcgen⟩ := IsCyclic.exists_generator (α := C)
      have hcgen_ne_one : cgen ≠ 1 := by
        intro hc
        have hsub : Subsingleton C := by
          constructor
          intro x y
          rcases hcgen x with ⟨i, hi⟩
          rcases hcgen y with ⟨j, hj⟩
          rw [hc] at hi hj
          simp only [one_zpow] at hi hj
          exact hi.symm.trans hj
        have hcard_one : Nat.card C = 1 := Nat.card_eq_one_iff_unique.mpr
          ⟨hsub, ⟨1⟩⟩
        rw [hCcard] at hcard_one
        exact (hnontrivial i0).ne hcard_one.symm
      let cN : NP := (cgen : C)
      have hcN_not_PN : cN ∉ PN := by
        intro hcPN
        have hcC : cN ∈ C := cgen.property
        have hc_one : cN = 1 :=
          Subgroup.disjoint_def.mp hcomp.disjoint hcPN hcC
        exact hcgen_ne_one (Subtype.ext hc_one)
      have hcN_not_U : conjH (cN : H) ∉ U := by
        intro hcU
        exact hcN_not_PN ((hU_preimage cN).mp hcU)
      obtain ⟨u, huU, hc_torus⟩ :=
        hB_conjugate_torus (conjH (cN : H))
          (hNP_maps_B cN) hcN_not_U
      rcases hc_torus with ⟨t, htT, ht⟩
      change u * t * u⁻¹ = conjH (cN : H) at ht
      let conjH' : H →* PSL2MatrixGroup F :=
        (MulAut.conj u⁻¹).toMonoidHom.comp conjH
      have hconjH'_injective : Function.Injective conjH' :=
        (MulAut.conj u⁻¹).injective.comp hconjH_injective
      have hP_map_conjH'_le_U : (P : Subgroup H).map conjH' ≤ U := by
        rintro y ⟨x, hxP, rfl⟩
        change u⁻¹ * conjH x * (u⁻¹)⁻¹ ∈ U
        exact U.mul_mem
          (U.mul_mem (U.inv_mem huU)
            (hP_map_conjH_le_U (Subgroup.mem_map_of_mem conjH hxP)))
          (by simpa using huU)
      have hcgen_image : conjH' (cN : H) = t := by
        dsimp only [conjH']
        change u⁻¹ * conjH (cN : H) * (u⁻¹)⁻¹ = t
        rw [← ht]
        group
      rw [hT_range] at htT
      rcases htT with ⟨r, hr⟩
      have hcgen_split : conjH' (cN : H) = splitTorus r := by
        rw [hcgen_image, hr]
      let P0 : Subgroup (PSL2MatrixGroup F) :=
        (P : Subgroup H).map conjH'
      let W : AddSubgroup F :=
        { carrier := {x | unipotent x ∈ P0}
          zero_mem' := by
            change unipotent 0 ∈ P0
            simpa using P0.one_mem
          add_mem' := by
            intro x y hx hy
            change unipotent (x + y) ∈ P0
            rw [unipotent.map_add_eq_mul]
            exact P0.mul_mem hx hy
          neg_mem' := by
            intro x hx
            change unipotent (-x) ∈ P0
            rw [unipotent.map_neg_eq_inv]
            exact P0.inv_mem hx }
      have hWcard : Nat.card W = p ^ m := by
        let eW : W ≃ P0 := Equiv.ofBijective
          (fun x : W => (⟨unipotent (x : F), x.property⟩ : P0)) (by
            constructor
            · intro x y hxy
              apply Subtype.ext
              apply h_unipotent_injective
              exact congrArg Subtype.val hxy
            · intro y
              have hyU : (y : PSL2MatrixGroup F) ∈ U := by
                apply hP_map_conjH'_le_U
                exact y.property
              rw [hU_range] at hyU
              rcases hyU with ⟨x, hx⟩
              refine ⟨⟨x, ?_⟩, ?_⟩
              · change unipotent.toMonoidHom x ∈ P0
                rw [hx]
                exact y.property
              · apply Subtype.ext
                exact hx)
        calc
          Nat.card W = Nat.card P0 := Nat.card_congr eW
          _ = Nat.card P :=
            Subgroup.card_map_of_injective hconjH'_injective
          _ = p ^ m := hPm
      have hW_ne_bot : W ≠ ⊥ := by
        rw [← AddSubgroup.one_lt_card_iff_ne_bot, hWcard]
        exact hpm_gt
      obtain ⟨x0, hx0_ne_zero⟩ :=
        AddSubgroup.ne_bot_iff_exists_ne_zero.mp hW_ne_bot
      have hx0_val_ne_zero : (x0 : F) ≠ 0 := by
        intro hx
        exact hx0_ne_zero (Subtype.ext hx)
      have hx0_unipotent_ne_one : unipotent (x0 : F) ≠ 1 := by
        intro hx
        have hxzero := h_unipotent_injective
          (hx.trans unipotent.map_zero_eq_one.symm)
        exact hx0_ne_zero (Subtype.ext hxzero)
      have hlambda_mem_W :
          ∀ x : F, x ∈ W → (r : F) ^ 2 * x ∈ W := by
        intro x hxW
        change unipotent ((r : F) ^ 2 * x) ∈ P0
        rw [← hsplit_conj]
        rcases hxW with ⟨y, hyP, hy⟩
        have hc_normalizes :
            (cN : H) ∈ Subgroup.normalizer (P : Set H) := cN.property
        have hcyP :
            (cN : H) * y * (cN : H)⁻¹ ∈ (P : Subgroup H) :=
          (Subgroup.mem_normalizer_iff.mp hc_normalizes y).mp hyP
        refine ⟨(cN : H) * y * (cN : H)⁻¹, hcyP, ?_⟩
        rw [map_mul, map_mul, map_inv, hcgen_split, hy]
      let K : Subfield F := h826_scalarStabilizer W
      have hlambda_mem_K : (r : F) ^ 2 ∈ K := hlambda_mem_W
      have hK_le_W_card : Nat.card K ≤ Nat.card W := by
        let φ : K → W := fun a =>
          ⟨(a : F) * (x0 : F), a.property (x0 : F) x0.property⟩
        have hφinj : Function.Injective φ := by
          intro a b hab
          apply Subtype.ext
          have hval := congrArg Subtype.val hab
          exact mul_right_cancel₀ hx0_val_ne_zero hval
        exact Nat.card_le_card_of_injective φ hφinj
      have hK_le_q : Nat.card K ≤ p ^ m := by
        rw [← hWcard]
        exact hK_le_W_card
      have hcgen_order : orderOf cgen = Nat.card C :=
        orderOf_eq_card_of_forall_mem_zpowers hcgen
      have hsplit_order :
          orderOf (splitTorus r) = Nat.card (Z i0) := by
        calc
          orderOf (splitTorus r) = orderOf (conjH' (cN : H)) := by
            rw [hcgen_split]
          _ = orderOf (cN : H) :=
            orderOf_injective conjH' hconjH'_injective (cN : H)
          _ = orderOf cN := Subgroup.orderOf_coe cN
          _ = orderOf cgen := Subgroup.orderOf_coe cgen
          _ = Nat.card C := hcgen_order
          _ = Nat.card (Z i0) := hCcard
      let lambdaU : Fˣ := r ^ 2
      have hsplit_pow_fixed (j : ℕ) :
          (splitTorus r) ^ j * unipotent (x0 : F) *
              ((splitTorus r) ^ j)⁻¹ =
            unipotent ((lambdaU ^ j : Fˣ) * (x0 : F)) := by
        calc
          (splitTorus r) ^ j * unipotent (x0 : F) *
                ((splitTorus r) ^ j)⁻¹ =
              splitTorus (r ^ j) * unipotent (x0 : F) *
                (splitTorus (r ^ j))⁻¹ := by rw [map_pow]
          _ = unipotent (((r ^ j : Fˣ) : F) ^ 2 * (x0 : F)) :=
            hsplit_conj (r ^ j) (x0 : F)
          _ = unipotent ((lambdaU ^ j : Fˣ) * (x0 : F)) := by
            congr 2
            simp only [lambdaU, Units.val_pow_eq_pow_val]
            ring
      have hlambda_pow_of_split_pow {j : ℕ}
          (hj : (splitTorus r) ^ j = 1) :
          lambdaU ^ j = 1 := by
        have hfix := hsplit_pow_fixed j
        rw [hj] at hfix
        simp only [one_mul, mul_one, inv_one] at hfix
        have hcoord :
            (x0 : F) = (lambdaU ^ j : Fˣ) * (x0 : F) :=
          h_unipotent_injective hfix
        apply Units.ext
        apply mul_right_cancel₀ hx0_val_ne_zero
        simpa using hcoord.symm
      have hsplit_pow_of_lambda_pow {j : ℕ}
          (hj : lambdaU ^ j = 1) :
          (splitTorus r) ^ j = 1 := by
        have hfix := hsplit_pow_fixed j
        rw [hj] at hfix
        simp only [Units.val_one, one_mul] at hfix
        have hsplit_mem : splitTorus r ∈ T := by
          rw [hT_range]
          exact ⟨r, rfl⟩
        rcases hT_fixedPointFree
            ((splitTorus r) ^ j) (T.pow_mem hsplit_mem j)
            (unipotent (x0 : F))
            (hP_map_conjH'_le_U x0.property) hfix with ht | hx
        · exact ht
        · exact (hx0_unipotent_ne_one hx).elim
      have hlambda_order :
          orderOf lambdaU = Nat.card (Z i0) := by
        apply Nat.dvd_antisymm
        · apply orderOf_dvd_of_pow_eq_one
          apply hlambda_pow_of_split_pow
          rw [← hsplit_order]
          exact pow_orderOf_eq_one (splitTorus r)
        · rw [← hsplit_order]
          apply orderOf_dvd_of_pow_eq_one
          apply hsplit_pow_of_lambda_pow
          exact pow_orderOf_eq_one lambdaU
      let lambdaK0 : K := ⟨(lambdaU : F), hlambda_mem_K⟩
      have hlambdaK0_ne_zero : lambdaK0 ≠ 0 := by
        intro hzero
        have hval := congrArg Subtype.val hzero
        exact Units.ne_zero lambdaU hval
      let lambdaK : Kˣ := Units.mk0 lambdaK0 hlambdaK0_ne_zero
      let inclUnits : Kˣ →* Fˣ :=
        Units.map (K.subtype : K →+* F)
      have hinclUnits_injective : Function.Injective inclUnits :=
        Units.map_injective K.subtype_injective
      have hlambda_map :
          inclUnits lambdaK = lambdaU := by
        apply Units.ext
        rfl
      have hlambdaK_order :
          orderOf lambdaK = Nat.card (Z i0) := by
        calc
          orderOf lambdaK = orderOf (inclUnits lambdaK) :=
            (orderOf_injective inclUnits hinclUnits_injective lambdaK).symm
          _ = orderOf lambdaU := congrArg orderOf hlambda_map
          _ = Nat.card (Z i0) := hlambda_order
      have hKunits_card : Nat.card Kˣ = Nat.card K - 1 := by
        letI : Fintype K := Fintype.ofFinite K
        simpa [Nat.card_eq_fintype_card] using Fintype.card_units K
      have hCcard_dvd_K_sub_one : Nat.card (Z i0) ∣ Nat.card K - 1 := by
        rw [← hKunits_card, ← hlambdaK_order]
        exact orderOf_dvd_natCard lambdaK
      have hK_lower : Nat.card (Z i0) + 1 ≤ Nat.card K := by
        have hKcard_gt : 1 < Nat.card K := Finite.one_lt_card
        have hle := Nat.le_of_dvd (by omega) hCcard_dvd_K_sub_one
        calc
          Nat.card (Z i0) + 1 ≤ (Nat.card K - 1) + 1 :=
            Nat.add_le_add_right hle 1
          _ = Nat.card K := Nat.sub_add_cancel hKcard_gt.le
      let Point := ℙ F (Fin 2 → F)
      let inf : Point :=
        Projectivization.mk F ![(1 : F), 0] (by simp)
      let zero : Point :=
        Projectivization.mk F ![(0 : F), 1] (by simp)
      let affine (x : F) : Point :=
        Projectivization.mk F ![x, 1] (by simp)
      obtain ⟨rho, hrho, hrho_apply, _hrho_two_transitive⟩ :=
        huppert_II_6_11_projective_action (K := F) 2 (by omega)
      letI : MulAction (PSL2MatrixGroup F) Point :=
        MulAction.compHom Point rho
      have hunipotent_fixes_inf (x : F) :
          unipotent x • inf = inf := by
        rw [hunipotent_matrix]
        change rho
            (QuotientGroup.mk'
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F))
              (⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩ :
                Matrix.SpecialLinearGroup (Fin 2) F)) inf = inf
        rw [hrho_apply]
        dsimp only [inf]
        rw [Projectivization.smul_mk]
        apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).2
        refine ⟨1, ?_⟩
        ext i
        fin_cases i <;>
          simp [Matrix.GeneralLinearGroup.toLin_apply,
            Matrix.mulVec, dotProduct]
      have hsplit_fixes_inf (a : Fˣ) :
          splitTorus a • inf = inf := by
        rw [hsplitTorus_matrix]
        change rho
            (QuotientGroup.mk'
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F))
              (⟨!![(a : F), 0; 0, (a⁻¹ : F)],
                  by simp [Matrix.det_fin_two]⟩ :
                Matrix.SpecialLinearGroup (Fin 2) F)) inf = inf
        rw [hrho_apply]
        dsimp only [inf]
        rw [Projectivization.smul_mk]
        apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).2
        refine ⟨(a : F), ?_⟩
        ext i
        fin_cases i <;>
          simp [Matrix.GeneralLinearGroup.toLin_apply,
            Matrix.mulVec, dotProduct]
      have hsplit_fixes_zero (a : Fˣ) :
          splitTorus a • zero = zero := by
        rw [hsplitTorus_matrix]
        change rho
            (QuotientGroup.mk'
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F))
              (⟨!![(a : F), 0; 0, (a⁻¹ : F)],
                  by simp [Matrix.det_fin_two]⟩ :
                Matrix.SpecialLinearGroup (Fin 2) F)) zero = zero
        rw [hrho_apply]
        dsimp only [zero]
        rw [Projectivization.smul_mk]
        apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).2
        refine ⟨(a⁻¹ : F), ?_⟩
        ext i
        fin_cases i <;>
          simp [Matrix.GeneralLinearGroup.toLin_apply,
            Matrix.mulVec, dotProduct]
      have hunipotent_affine (w x : F) :
          unipotent w • affine x = affine (x + w) := by
        rw [hunipotent_matrix]
        change rho
            (QuotientGroup.mk'
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F))
              (⟨!![1, w; 0, 1], by simp [Matrix.det_fin_two]⟩ :
                Matrix.SpecialLinearGroup (Fin 2) F)) (affine x) =
          affine (x + w)
        rw [hrho_apply]
        dsimp only [affine]
        rw [Projectivization.smul_mk]
        apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).2
        refine ⟨1, ?_⟩
        ext i
        fin_cases i <;>
          simp [Matrix.GeneralLinearGroup.toLin_apply,
            Matrix.mulVec, dotProduct, add_comm]
      have hunipotent_fixed_eq_inf
          (w : F) (hw : w ≠ 0) (z : Point)
          (hfix : unipotent w • z = z) :
          z = inf := by
        rw [← Projectivization.mk_rep z] at hfix
        rw [hunipotent_matrix] at hfix
        change rho
            (QuotientGroup.mk'
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F))
              (⟨!![1, w; 0, 1], by simp [Matrix.det_fin_two]⟩ :
                Matrix.SpecialLinearGroup (Fin 2) F))
              (Projectivization.mk F z.rep z.rep_nonzero) =
            Projectivization.mk F z.rep z.rep_nonzero at hfix
        rw [hrho_apply, Projectivization.smul_mk] at hfix
        rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp hfix with
          ⟨a, ha⟩
        have h0 := congrFun ha (0 : Fin 2)
        have h1 := congrFun ha (1 : Fin 2)
        simp [Matrix.GeneralLinearGroup.toLin_apply,
          Matrix.mulVec, dotProduct] at h0 h1
        by_cases hz1 : z.rep 1 = 0
        · rw [← Projectivization.mk_rep z]
          dsimp only [inf]
          apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).2
          refine ⟨z.rep 0, ?_⟩
          ext i
          fin_cases i
          · simp
          · simpa [hz1]
        · have ha_one : a = 1 := by
            apply mul_right_cancel₀ hz1
            simpa using h1
          rw [ha_one, one_mul] at h0
          have hprod : w * z.rep 1 = 0 := by
            linear_combination -h0
          exact (mul_ne_zero hw hz1 hprod).elim
      have hB_fixes_inf :
          U ⊔ T ≤ MulAction.stabilizer (PSL2MatrixGroup F) inf := by
        apply sup_le
        · intro g hg
          rw [MulAction.mem_stabilizer_iff]
          rw [hU_range] at hg
          rcases hg with ⟨x, rfl⟩
          exact hunipotent_fixes_inf x
        · intro g hg
          rw [MulAction.mem_stabilizer_iff]
          rw [hT_range] at hg
          rcases hg with ⟨a, rfl⟩
          exact hsplit_fixes_inf a
      have hfix_inf_mem_B
          (g : PSL2MatrixGroup F) (hfix : g • inf = inf) :
          g ∈ U ⊔ T := by
        refine QuotientGroup.induction_on g ?_ hfix
        intro A hAfix
        have hA10 :
            (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
          change rho
              (QuotientGroup.mk'
                (Subgroup.center
                  (Matrix.SpecialLinearGroup (Fin 2) F)) A) inf = inf at hAfix
          rw [hrho_apply] at hAfix
          dsimp only [inf] at hAfix
          rw [Projectivization.smul_mk] at hAfix
          rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp hAfix with
            ⟨a, ha⟩
          have h1 := congrFun ha (1 : Fin 2)
          simpa [Matrix.GeneralLinearGroup.toLin_apply,
            Matrix.mulVec, dotProduct] using h1.symm
        have hdet :
            (A : Matrix (Fin 2) (Fin 2) F) 0 0 *
                (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
          have h := A.property
          rw [Matrix.det_fin_two, hA10, mul_zero, sub_zero] at h
          exact h
        have ha_zero :
            (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 :=
          left_ne_zero_of_mul_eq_one hdet
        let aU : Fˣ :=
          Units.mk0 ((A : Matrix (Fin 2) (Fin 2) F) 0 0) ha_zero
        have hd_inv :
            (A : Matrix (Fin 2) (Fin 2) F) 1 1 = (aU⁻¹ : F) := by
          simpa [aU] using eq_inv_of_mul_eq_one_right hdet
        let Bsl : Matrix.SpecialLinearGroup (Fin 2) F :=
          ⟨!![1,
              (A : Matrix (Fin 2) (Fin 2) F) 0 1 *
                (A : Matrix (Fin 2) (Fin 2) F) 0 0;
              0, 1], by simp [Matrix.det_fin_two]⟩
        let Dsl : Matrix.SpecialLinearGroup (Fin 2) F :=
          ⟨!![(aU : F), 0; 0, (aU⁻¹ : F)],
            by simp [Matrix.det_fin_two]⟩
        have hfactor : A = Bsl * Dsl := by
          apply Subtype.ext
          ext i j
          fin_cases i <;> fin_cases j
          · simp [Bsl, Dsl, Matrix.mul_apply, aU]
          · simp [Bsl, Dsl, Matrix.mul_apply, aU, ha_zero]
          · simpa [Bsl, Dsl, Matrix.mul_apply, aU] using hA10
          · simpa [Bsl, Dsl, Matrix.mul_apply, aU] using hd_inv
        have hBsl :
            QuotientGroup.mk'
                (Subgroup.center
                  (Matrix.SpecialLinearGroup (Fin 2) F)) Bsl =
              unipotent
                ((A : Matrix (Fin 2) (Fin 2) F) 0 1 *
                  (A : Matrix (Fin 2) (Fin 2) F) 0 0) := by
          rw [hunipotent_matrix]
        have hDsl :
            QuotientGroup.mk'
                (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F)) Dsl =
              splitTorus aU := by
          rw [hsplitTorus_matrix]
        change QuotientGroup.mk'
            (Subgroup.center
              (Matrix.SpecialLinearGroup (Fin 2) F)) A ∈ U ⊔ T
        rw [hfactor, map_mul, hBsl, hDsl]
        exact (U ⊔ T).mul_mem
          ((show U ≤ U ⊔ T from le_sup_left)
            (by rw [hU_range]; exact ⟨_, rfl⟩))
          ((show T ≤ U ⊔ T from le_sup_right)
            (by rw [hT_range]; exact ⟨_, rfl⟩))
      have hmem_NP_of_image_mem_B
          (g : H) (hgB : conjH' g ∈ U ⊔ T) :
          g ∈ NP := by
        let Qg : Subgroup H :=
          (P : Subgroup H).map (MulAut.conj g).toMonoidHom
        have hg_normalizes_U :
            conjH' g ∈ Subgroup.normalizer (U : Set (PSL2MatrixGroup F)) :=
          hB_le_normalizer hgB
        have hQg_map_le_U : Qg.map conjH' ≤ U := by
          rintro y ⟨z, ⟨x, hxP, rfl⟩, rfl⟩
          change conjH' (g * x * g⁻¹) ∈ U
          rw [map_mul, map_mul, map_inv]
          exact
            (Subgroup.mem_normalizer_iff.mp hg_normalizes_U
              (conjH' x)).mp
              (hP_map_conjH'_le_U
                (Subgroup.mem_map_of_mem conjH' hxP))
        have hP_normalizes_Qg :
            (P : Subgroup H) ≤ Subgroup.normalizer (Qg : Set H) := by
          intro x hxP
          rw [Subgroup.mem_normalizer_iff]
          intro y
          have hxU : conjH' x ∈ U :=
            hP_map_conjH'_le_U (Subgroup.mem_map_of_mem conjH' hxP)
          have hzU (z : H) (hz : z ∈ Qg) : conjH' z ∈ U :=
            hQg_map_le_U (Subgroup.mem_map_of_mem conjH' hz)
          have hcomm (z : H) (hz : z ∈ Qg) : Commute x z := by
            apply hconjH'_injective
            simpa only [map_mul] using congrArg Subtype.val
              ((@IsMulCommutative.is_comm U _ hU_commutative).comm
                (⟨conjH' x, hxU⟩ : U) (⟨conjH' z, hzU z hz⟩ : U))
          constructor
          · intro hy
            have hxy : x * y * x⁻¹ = y := by
              calc
                x * y * x⁻¹ = y * x * x⁻¹ := by
                  rw [(hcomm y hy).eq]
                _ = y := by simp
            rwa [hxy]
          · intro hy
            have hzcomm : Commute x (x * y * x⁻¹) :=
              hcomm (x * y * x⁻¹) hy
            have hy_eq : y = x * y * x⁻¹ := by
              calc
                y = x⁻¹ * (x * y * x⁻¹) * x := by group
                _ = x⁻¹ * (x * (x * y * x⁻¹)) := by
                  rw [mul_assoc, hzcomm.eq.symm]
                _ = x * y * x⁻¹ := by simp
            rw [hy_eq]
            exact hy
        have hQg_isPGroup : IsPGroup p Qg :=
          P.isPGroup'.map (MulAut.conj g).toMonoidHom
        have hsup_isPGroup :
            IsPGroup p ((P : Subgroup H) ⊔ Qg : Subgroup H) :=
          P.isPGroup'.to_sup_of_normal_right' hQg_isPGroup hP_normalizes_Qg
        have hsup_eq_P :
            (P : Subgroup H) ⊔ Qg = (P : Subgroup H) :=
          P.is_maximal' hsup_isPGroup le_sup_left
        have hQg_le_P : Qg ≤ (P : Subgroup H) := by
          calc
            Qg ≤ (P : Subgroup H) ⊔ Qg := le_sup_right
            _ = (P : Subgroup H) := hsup_eq_P
        have hQg_card : Nat.card Qg = Nat.card P :=
          Subgroup.card_map_of_injective (MulAut.conj g).injective
        have hQg_eq_P : Qg = (P : Subgroup H) :=
          Subgroup.eq_of_le_of_card_ge hQg_le_P (by rw [hQg_card])
        apply (Subgroup.conjAct_pointwise_smul_iff
          (H := (P : Subgroup H)) (g := g)).mp
        change Qg = (P : Subgroup H)
        exact hQg_eq_P
      let rhoH : H →* Equiv.Perm Point := rho.comp conjH'
      letI : MulAction H Point := MulAction.compHom Point rhoH
      have hstabilizer_inf :
          MulAction.stabilizer H inf = NP := by
        ext g
        rw [MulAction.mem_stabilizer_iff]
        constructor
        · intro hfix
          apply hmem_NP_of_image_mem_B g
          apply hfix_inf_mem_B (conjH' g)
          exact hfix
        · intro hgNP
          have hgB0 : conjH (g : H) ∈ U ⊔ T :=
            hNP_maps_B ⟨g, hgNP⟩
          have hgB : conjH' g ∈ U ⊔ T := by
            change u⁻¹ * conjH g * (u⁻¹)⁻¹ ∈ U ⊔ T
            exact (U ⊔ T).mul_mem
              ((U ⊔ T).mul_mem
                ((show U ≤ U ⊔ T from le_sup_left) (U.inv_mem huU)) hgB0)
              ((show U ≤ U ⊔ T from le_sup_left) (by simpa using huU))
          apply hB_fixes_inf
          exact hgB
      let S := MulAction.orbit H inf
      let baseS : S := ⟨inf, MulAction.mem_orbit_self inf⟩
      have hstabilizer_base :
          MulAction.stabilizer H baseS = NP := by
        ext g
        rw [MulAction.mem_stabilizer_iff]
        constructor
        · intro hfix
          have hfix_val := congrArg Subtype.val hfix
          have : g • inf = inf := by
            simpa only [MulAction.orbit.coe_smul] using hfix_val
          rw [← MulAction.mem_stabilizer_iff, hstabilizer_inf] at this
          exact this
        · intro hg
          apply Subtype.ext
          change g • inf = inf
          rw [← MulAction.mem_stabilizer_iff, hstabilizer_inf]
          exact hg
      have hsplit_fixed_eq_inf_or_zero
          (a : Fˣ) (ha : splitTorus a ≠ 1) (z : Point)
          (hfix : splitTorus a • z = z) :
          z = inf ∨ z = zero := by
        rw [← Projectivization.mk_rep z] at hfix
        rw [hsplitTorus_matrix] at hfix
        change rho
            (QuotientGroup.mk'
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F))
              (⟨!![(a : F), 0; 0, (a⁻¹ : F)],
                  by simp [Matrix.det_fin_two]⟩ :
                Matrix.SpecialLinearGroup (Fin 2) F))
              (Projectivization.mk F z.rep z.rep_nonzero) =
            Projectivization.mk F z.rep z.rep_nonzero at hfix
        rw [hrho_apply, Projectivization.smul_mk] at hfix
        rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp hfix with
          ⟨c0, hc0⟩
        have h0 := congrFun hc0 (0 : Fin 2)
        have h1 := congrFun hc0 (1 : Fin 2)
        simp [Matrix.GeneralLinearGroup.toLin_apply,
          Matrix.mulVec, dotProduct] at h0 h1
        by_cases hz0 : z.rep 0 = 0
        · right
          rw [← Projectivization.mk_rep z]
          dsimp only [zero]
          apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).2
          refine ⟨z.rep 1, ?_⟩
          ext i
          fin_cases i
          · simpa [hz0]
          · simp
        · by_cases hz1 : z.rep 1 = 0
          · left
            rw [← Projectivization.mk_rep z]
            dsimp only [inf]
            apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).2
            refine ⟨z.rep 0, ?_⟩
            ext i
            fin_cases i
            · simp
            · simpa [hz1]
          · exfalso
            have hc_eq_a : c0 = (a : F) := by
              apply mul_right_cancel₀ hz0
              simpa using h0
            have hc_eq_ainv : c0 = (a⁻¹ : F) := by
              apply mul_right_cancel₀ hz1
              simpa using h1
            have ha_sq : (a : F) ^ 2 = 1 := by
              have hai : (a : F) = (a⁻¹ : F) :=
                hc_eq_a.symm.trans hc_eq_ainv
              calc
                (a : F) ^ 2 = (a : F) * (a : F) := pow_two _
                _ = (a : F) * (a⁻¹ : F) :=
                  congrArg (fun z : F => (a : F) * z) hai
                _ = 1 := mul_inv_cancel₀ (Units.ne_zero a)
            have hfix_x0 :
                splitTorus a * unipotent (x0 : F) *
                    (splitTorus a)⁻¹ =
                  unipotent (x0 : F) := by
              rw [hsplit_conj, ha_sq, one_mul]
            have haT : splitTorus a ∈ T := by
              rw [hT_range]
              exact ⟨a, rfl⟩
            rcases hT_fixedPointFree
                (splitTorus a) haT (unipotent (x0 : F))
                (hP_map_conjH'_le_U x0.property) hfix_x0 with ha1 | hx1
            · exact ha ha1
            · exact hx0_unipotent_ne_one hx1
      have hzero_mem_S
          (hS_card : Nat.card S = p ^ m + 1) :
          zero ∈ S := by
        by_contra hzero_not
        let cToH : C →* H := NP.subtype.comp C.subtype
        letI : MulAction C S := MulAction.compHom S cToH
        have hbase_fixed (d : C) : d • baseS = baseS := by
          apply Subtype.ext
          change (cToH d) • inf = inf
          apply MulAction.mem_stabilizer_iff.mp
          rw [hstabilizer_inf]
          exact (d : NP).property
        let S0 : SubMulAction C S :=
          { carrier := {y | y ≠ baseS}
            smul_mem' := by
              intro d y hy hdy
              apply hy
              calc
                y = d⁻¹ • (d • y) := (inv_smul_smul d y).symm
                _ = d⁻¹ • baseS := congrArg (fun z : S => d⁻¹ • z) hdy
                _ = baseS := hbase_fixed d⁻¹ }
        have hstab (y : S0) :
            MulAction.stabilizer C y = ⊥ := by
          rw [eq_bot_iff]
          intro d hd
          by_contra hd_ne_one
          have hdy : d • (y : S) = (y : S) := by
            have hdy0 : d • y = y :=
              MulAction.mem_stabilizer_iff.mp hd
            simpa only [SubMulAction.val_smul] using
              congrArg Subtype.val hdy0
          have hpoint_fixed :
              conjH' (cToH d) • ((y : S) : Point) = ((y : S) : Point) := by
            have hval := congrArg Subtype.val hdy
            exact hval
          rcases hcgen d with ⟨j, hj⟩
          have himage :
              conjH' (cToH d) = splitTorus (r ^ j) := by
            calc
              conjH' (cToH d) = conjH' (cToH (cgen ^ j)) := by rw [← hj]
              _ = (conjH' (cToH cgen)) ^ j := map_zpow conjH' _ _
              _ = (splitTorus r) ^ j := by
                have hcToH : cToH cgen = (cN : H) := rfl
                rw [hcToH, hcgen_split]
              _ = splitTorus (r ^ j) := (map_zpow splitTorus r j).symm
          have himage_ne : splitTorus (r ^ j) ≠ 1 := by
            intro himage_one
            apply hd_ne_one
            apply Subtype.ext
            apply Subtype.ext
            apply hconjH'_injective
            change conjH' (cToH d) = conjH' (cToH 1)
            rw [himage, himage_one]
            exact (map_one conjH').symm
          have hfixed_cases :=
            hsplit_fixed_eq_inf_or_zero (r ^ j) himage_ne
              ((y : S) : Point) (by rwa [← himage])
          rcases hfixed_cases with hyinf | hyzero
          · apply y.property
            apply Subtype.ext
            exact hyinf
          · apply hzero_not
            rw [← hyzero]
            exact (y : S).property
        have hC_dvd_S0 : Nat.card C ∣ Nat.card S0 := by
          have hcard :=
            Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
          rw [Nat.card_prod] at hcard
          exact ⟨Nat.card (Quotient (MulAction.orbitRel C S0)), by
            rw [mul_comm]
            exact hcard⟩
        have hS0card : Nat.card S0 = p ^ m := by
          have hsub : Nat.card S0 = Nat.card S - 1 := by
            change Nat.card {y : S // y ≠ baseS} = Nat.card S - 1
            letI : Fintype S := Fintype.ofFinite S
            rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
            simp
          rw [hsub, hS_card]
          omega
        have hzi0_dvd_q : Nat.card (Z i0) ∣ p ^ m := by
          rw [← hCcard, ← hS0card]
          exact hC_dvd_S0
        have hzi0_dvd_one : Nat.card (Z i0) ∣ 1 := by
          have hsub := Nat.dvd_sub hzi0_dvd_q hi0_dvd_sub_one
          have hdiff : p ^ m - (p ^ m - 1) = 1 := by omega
          rwa [hdiff] at hsub
        have hzi0_one := Nat.eq_one_of_dvd_one hzi0_dvd_one
        exact (hnontrivial i0).ne hzi0_one.symm
      have haffine_injective : Function.Injective affine := by
        intro x y hxy
        dsimp only [affine] at hxy
        rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp hxy with
          ⟨a, ha⟩
        have h0 := congrFun ha (0 : Fin 2)
        have h1 := congrFun ha (1 : Fin 2)
        simp at h1
        simpa [h1] using h0.symm
      have hsubline_swap
          (hS_card : Nat.card S = p ^ m + 1) :
          ∃ h : H,
            h • inf = zero ∧ h • zero = inf ∧
            (∀ z : S, (z : Point) ≠ inf →
              ∃ w : W, (z : Point) = affine (w : F)) ∧
            NP ⊔ Subgroup.zpowers h = ⊤ := by
        have hzeroS : zero ∈ S := hzero_mem_S hS_card
        have hzero_ne_inf : zero ≠ inf := by
          intro hzero_inf
          dsimp only [zero, inf] at hzero_inf
          rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp
              hzero_inf with ⟨a, ha⟩
          have h0 := congrFun ha (0 : Fin 2)
          have h1 := congrFun ha (1 : Fin 2)
          simp at h1
        let zeroS : S := ⟨zero, hzeroS⟩
        let S0 := {z : S // z ≠ baseS}
        have hS0card : Nat.card S0 = p ^ m := by
          have hsub : Nat.card S0 = Nat.card S - 1 := by
            change Nat.card {z : S // z ≠ baseS} = Nat.card S - 1
            letI : Fintype S := Fintype.ofFinite S
            rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
            simp
          rw [hsub, hS_card]
          omega
        have haffine_mem_S (w : W) : affine (w : F) ∈ S := by
          rcases w.property with ⟨g, hgP, hg⟩
          rcases hzeroS with ⟨h0, hh0⟩
          change h0 • inf = zero at hh0
          refine ⟨g * h0, ?_⟩
          change (g * h0) • inf = affine (w : F)
          rw [mul_smul, hh0]
          change rho (conjH' g) zero = affine (w : F)
          rw [hg]
          simpa using hunipotent_affine (w : F) 0
        have haffine_ne_inf (w : W) : affine (w : F) ≠ inf := by
          intro hwi
          dsimp only [affine, inf] at hwi
          rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp hwi with
            ⟨a, ha⟩
          have h1 := congrFun ha (1 : Fin 2)
          simp at h1
        let affineW : W → S0 := fun w =>
          ⟨⟨affine (w : F), haffine_mem_S w⟩, by
            intro heq
            apply haffine_ne_inf w
            exact congrArg Subtype.val heq⟩
        have haffineW_inj : Function.Injective affineW := by
          intro x y hxy
          apply Subtype.ext
          apply haffine_injective
          exact congrArg (fun z : S0 => ((z : S) : Point)) hxy
        have haffineW_card : Nat.card W = Nat.card S0 := by
          rw [hWcard, hS0card]
        have haffineW_surj : Function.Surjective affineW :=
          (Nat.bijective_iff_injective_and_card affineW).mpr
            ⟨haffineW_inj, haffineW_card⟩ |>.2
        have hcover :
            ∀ z : S, (z : Point) ≠ inf →
              ∃ w : W, (z : Point) = affine (w : F) := by
          intro z hz
          have hzbase : z ≠ baseS := by
            intro heq
            exact hz (congrArg Subtype.val heq)
          obtain ⟨w, hw⟩ := haffineW_surj ⟨z, hzbase⟩
          refine ⟨w, ?_⟩
          exact congrArg (fun y : S0 => ((y : S) : Point)) hw.symm
        have hP_trans :
            ∀ y z : S0, ∃ g : P, (g : H) • (y : S) = (z : S) := by
          intro y z
          obtain ⟨wy, hwy⟩ := hcover (y : S) (by
            intro hy
            exact y.property (Subtype.ext hy))
          obtain ⟨wz, hwz⟩ := hcover (z : S) (by
            intro hz
            exact z.property (Subtype.ext hz))
          have hdiff_mem : unipotent ((wz : F) - (wy : F)) ∈ P0 := by
            change (wz : F) - (wy : F) ∈ W
            exact W.sub_mem wz.property wy.property
          rcases hdiff_mem with ⟨g, hgP, hg⟩
          refine ⟨⟨g, hgP⟩, ?_⟩
          apply Subtype.ext
          change rho (conjH' g) ((y : S) : Point) = ((z : S) : Point)
          rw [hwy, hwz, hg]
          change unipotent ((wz : F) - (wy : F)) • affine (wy : F) =
            affine (wz : F)
          rw [hunipotent_affine]
          congr 2
          ring
        have htwo :
            MulAction.IsMultiplyPretransitive H S 2 := by
          rw [MulAction.is_two_pretransitive_iff]
          intro a b c d hab hcd
          letI : MulAction.IsPretransitive H S := inferInstance
          obtain ⟨g, hg⟩ :=
            (inferInstance : MulAction.IsPretransitive H S).exists_smul_eq
              a baseS
          obtain ⟨k, hk⟩ :=
            (inferInstance : MulAction.IsPretransitive H S).exists_smul_eq
              baseS c
          have hgb : g • b ≠ baseS := by
            intro hgb
            exact hab (smul_left_cancel g (hg.trans hgb.symm))
          have hkd : k⁻¹ • d ≠ baseS := by
            intro hkd
            apply hcd
            calc
              c = k • baseS := hk.symm
              _ = k • (k⁻¹ • d) := by rw [hkd]
              _ = d := smul_inv_smul k d
          obtain ⟨p0, hp0⟩ :=
            hP_trans ⟨g • b, hgb⟩ ⟨k⁻¹ • d, hkd⟩
          refine ⟨k * (p0 : H) * g, ?_, ?_⟩
          · simp only [mul_smul]
            have hpbase : (p0 : H) • baseS = baseS := by
              apply Subtype.ext
              change (p0 : H) • inf = inf
              rw [← MulAction.mem_stabilizer_iff, hstabilizer_inf]
              exact Subgroup.le_normalizer p0.property
            rw [hg, hpbase, hk]
          · simp only [mul_smul]
            rw [hp0, smul_inv_smul]
        have hzeroS_ne_base : zeroS ≠ baseS := by
          intro heq
          exact hzero_ne_inf (congrArg Subtype.val heq)
        letI : Nontrivial S :=
          ⟨⟨zeroS, baseS, hzeroS_ne_base⟩⟩
        have htwo' := (MulAction.is_two_pretransitive_iff.mp htwo)
          hzeroS_ne_base.symm hzeroS_ne_base
        rcases htwo' with ⟨h, hinf, hzero⟩
        haveI : MulAction.IsPreprimitive H S :=
          MulAction.isPreprimitive_of_is_two_pretransitive htwo
        have hcoatom :
            IsCoatom (MulAction.stabilizer H baseS) :=
          MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive H baseS
        rw [hstabilizer_base] at hcoatom
        have hgen : NP ⊔ Subgroup.zpowers h = ⊤ := by
          rcases hcoatom.le_iff.mp le_sup_left with htop | heq
          · exact htop
          · exfalso
            have hhNP : h ∈ NP := by
              rw [← heq]
              exact (show Subgroup.zpowers h ≤ NP ⊔ Subgroup.zpowers h from
                le_sup_right) (Subgroup.mem_zpowers h)
            have hhfix : h • inf = inf := by
              rw [← MulAction.mem_stabilizer_iff, hstabilizer_inf]
              exact hhNP
            exact hzero_ne_inf ((congrArg Subtype.val hinf).symm.trans hhfix)
        refine ⟨h, congrArg Subtype.val hinf,
          congrArg Subtype.val hzero, hcover, hgen⟩
      have hPGL_embedding
          (hKcard : Nat.card K = p ^ m)
          (hswap : H) (hswap_inf : hswap • inf = zero)
          (hswap_zero : hswap • zero = inf)
          (hcover : ∀ z : S, (z : Point) ≠ inf →
            ∃ w : W, (z : Point) = affine (w : F))
          (hgen : NP ⊔ Subgroup.zpowers hswap = ⊤) :
          ∃ phi : H →* Matrix.ProjGenLinGroup (Fin 2) K,
            Function.Injective phi := by
        let scalarMap : K → W := fun a =>
          ⟨(a : F) * (x0 : F), a.property (x0 : F) x0.property⟩
        have hscalarMap_inj : Function.Injective scalarMap := by
          intro a b hab
          apply Subtype.ext
          have hval := congrArg Subtype.val hab
          exact mul_right_cancel₀ hx0_val_ne_zero hval
        have hscalarMap_card : Nat.card K = Nat.card W := by
          rw [hKcard, hWcard]
        have hscalarMap_surj : Function.Surjective scalarMap :=
          (Nat.bijective_iff_injective_and_card scalarMap).mpr
            ⟨hscalarMap_inj, hscalarMap_card⟩ |>.2
        have hW_span (w : W) :
            ∃ k : K, (w : F) = (k : F) * (x0 : F) := by
          obtain ⟨k, hk⟩ := hscalarMap_surj w
          exact ⟨k, congrArg Subtype.val hk.symm⟩
        have haffine_ne_inf (w : W) : affine (w : F) ≠ inf := by
          intro hwi
          dsimp only [affine, inf] at hwi
          rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp hwi with
            ⟨a, ha⟩
          have h1 := congrFun ha (1 : Fin 2)
          simp at h1
        let D : GL (Fin 2) F :=
          Matrix.GeneralLinearGroup.mkOfDetNeZero
            !![(x0 : F), 0; 0, 1]
            (by simp [Matrix.det_fin_two, hx0_val_ne_zero])
        let Di : GL (Fin 2) F :=
          Matrix.GeneralLinearGroup.mkOfDetNeZero
            !![(x0 : F)⁻¹, 0; 0, 1]
            (by simp [Matrix.det_fin_two, hx0_val_ne_zero])
        have hDi : Di = D⁻¹ := by
          apply eq_inv_of_mul_eq_one_right
          apply Matrix.GeneralLinearGroup.ext
          intro i j
          fin_cases i <;> fin_cases j <;>
            simp [D, Di, Matrix.mul_apply, hx0_ne_zero]
        let iotaF : PSL2MatrixGroup F →*
            Matrix.ProjGenLinGroup (Fin 2) F :=
          h826_pslToPGL
        let dPGL : Matrix.ProjGenLinGroup (Fin 2) F :=
          Matrix.ProjGenLinGroup.mk D
        let toF : H →* Matrix.ProjGenLinGroup (Fin 2) F :=
          (MulAut.conj dPGL⁻¹).toMonoidHom.comp
            (iotaF.comp conjH')
        let j : Matrix.ProjGenLinGroup (Fin 2) K →*
            Matrix.ProjGenLinGroup (Fin 2) F :=
          h826_pglMap K.subtype
        have hj_injective : Function.Injective j :=
          h826_pglMap_injective K.subtype K.subtype_injective
        let L : Subgroup H := j.range.comap toF
        have hP_le_L : (P : Subgroup H) ≤ L := by
          intro x hxP
          have hxU : conjH' x ∈ U :=
            hP_map_conjH'_le_U
              (Subgroup.mem_map_of_mem conjH' hxP)
          rw [hU_range] at hxU
          rcases hxU with ⟨w, hw⟩
          have hwW : w ∈ W := by
            change unipotent.toMonoidHom w ∈ P0
            rw [hw]
            exact Subgroup.mem_map_of_mem conjH' hxP
          obtain ⟨k, hk⟩ := hW_span ⟨w, hwW⟩
          let Usl : Matrix.SpecialLinearGroup (Fin 2) F :=
            ⟨!![1, w; 0, 1], by simp [Matrix.det_fin_two]⟩
          let Ak : GL (Fin 2) K :=
            Matrix.GeneralLinearGroup.mkOfDetNeZero
              !![1, k; 0, 1] (by simp [Matrix.det_fin_two])
          have hmat :
              Di * Matrix.SpecialLinearGroup.toGL Usl * D =
                Matrix.GeneralLinearGroup.map K.subtype Ak := by
            apply Matrix.GeneralLinearGroup.ext
            intro i j0
            fin_cases i <;> fin_cases j0 <;>
              simp [D, Di, Usl, Ak, Matrix.mul_apply, hx0_ne_zero, hk,
                mul_comm] <;>
              field_simp
            simpa [mul_comm] using hk
          change toF x ∈ j.range
          refine ⟨Matrix.ProjGenLinGroup.mk Ak, ?_⟩
          change j (Matrix.ProjGenLinGroup.mk Ak) = toF x
          rw [h826_pglMap_mk]
          have hiota :
              iotaF (conjH' x) =
                Matrix.ProjGenLinGroup.mk
                  (Matrix.SpecialLinearGroup.toGL Usl) := by
            rw [← hw]
            change iotaF (unipotent (w : F)) =
              Matrix.ProjGenLinGroup.mk
                (Matrix.SpecialLinearGroup.toGL Usl)
            rw [hunipotent_matrix]
            exact h826_pslToPGL_mk Usl
          change
            Matrix.ProjGenLinGroup.mk
                (Matrix.GeneralLinearGroup.map K.subtype Ak) =
              dPGL⁻¹ * iotaF (conjH' x) * (dPGL⁻¹)⁻¹
          rw [hiota]
          have hd_inv :
              dPGL⁻¹ = Matrix.ProjGenLinGroup.mk Di := by
            dsimp only [dPGL]
            rw [← map_inv, ← hDi]
          have hd_inv_inv :
              (Matrix.ProjGenLinGroup.mk Di)⁻¹ =
                Matrix.ProjGenLinGroup.mk D := by
            rw [← map_inv, hDi, inv_inv]
          rw [hd_inv, hd_inv_inv]
          change
            Matrix.ProjGenLinGroup.mk
                (Matrix.GeneralLinearGroup.map K.subtype Ak) =
              Matrix.ProjGenLinGroup.mk Di *
                Matrix.ProjGenLinGroup.mk
                  (Matrix.SpecialLinearGroup.toGL Usl) *
                Matrix.ProjGenLinGroup.mk D
          rw [← map_mul, ← map_mul, hmat]
        have hcgen_mem_L : (cN : H) ∈ L := by
          let Bk : GL (Fin 2) K :=
            Matrix.GeneralLinearGroup.mkOfDetNeZero
              !![lambdaK0, 0; 0, 1]
              (by simp [Matrix.det_fin_two, hlambdaK0_ne_zero])
          let BF : GL (Fin 2) F :=
            Matrix.GeneralLinearGroup.mkOfDetNeZero
              !![(lambdaU : F), 0; 0, 1]
              (by simp [Matrix.det_fin_two])
          let Rgl : GL (Fin 2) F :=
            Matrix.SpecialLinearGroup.toGL
              (⟨!![(r : F), 0; 0, (r⁻¹ : F)],
                  by simp [Matrix.det_fin_two]⟩ :
                Matrix.SpecialLinearGroup (Fin 2) F)
          have hmap_Bk :
              Matrix.GeneralLinearGroup.map K.subtype Bk = BF := by
            apply Matrix.GeneralLinearGroup.ext
            intro i j0
            fin_cases i <;> fin_cases j0 <;>
              simp [Bk, BF, lambdaK0, lambdaU]
          have hBF_scalar :
              BF =
                Matrix.GeneralLinearGroup.scalar (Fin 2) r * Rgl := by
            apply Matrix.GeneralLinearGroup.ext
            intro i j0
            fin_cases i <;> fin_cases j0 <;>
              simp [BF, Rgl, lambdaU,
                Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, pow_two]
          have hBF_comm_D : Di * BF * D = BF := by
            apply Matrix.GeneralLinearGroup.ext
            intro i j0
            fin_cases i <;> fin_cases j0 <;>
              simp [D, Di, BF, Matrix.mul_apply, hx0_ne_zero] <;>
              field_simp
          change toF (cN : H) ∈ j.range
          refine ⟨Matrix.ProjGenLinGroup.mk Bk, ?_⟩
          change j (Matrix.ProjGenLinGroup.mk Bk) = toF (cN : H)
          rw [h826_pglMap_mk, hmap_Bk]
          have hiota :
              iotaF (conjH' (cN : H)) =
                Matrix.ProjGenLinGroup.mk BF := by
            rw [hcgen_split, hsplitTorus_matrix,
              h826_pslToPGL_mk]
            rw [hBF_scalar, map_mul,
              Matrix.ProjGenLinGroup.mk_scalar, one_mul]
          change
            Matrix.ProjGenLinGroup.mk BF =
              dPGL⁻¹ * iotaF (conjH' (cN : H)) * (dPGL⁻¹)⁻¹
          rw [hiota]
          have hd_inv :
              dPGL⁻¹ = Matrix.ProjGenLinGroup.mk Di := by
            dsimp only [dPGL]
            rw [← map_inv, ← hDi]
          have hd_inv_inv :
              (Matrix.ProjGenLinGroup.mk Di)⁻¹ =
                Matrix.ProjGenLinGroup.mk D := by
            rw [← map_inv, hDi, inv_inv]
          rw [hd_inv, hd_inv_inv]
          change Matrix.ProjGenLinGroup.mk BF =
            Matrix.ProjGenLinGroup.mk Di *
              Matrix.ProjGenLinGroup.mk BF *
                Matrix.ProjGenLinGroup.mk D
          rw [← map_mul, ← map_mul, hBF_comm_D]
        have hswap_mem_L : hswap ∈ L := by
          rcases QuotientGroup.mk'_surjective
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F))
              (conjH' hswap) with ⟨A, hA⟩
          have hA00 :
              (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := by
            have hfix := hswap_inf
            change rho (conjH' hswap) inf = zero at hfix
            rw [← hA, hrho_apply] at hfix
            dsimp only [inf, zero] at hfix
            rw [Projectivization.smul_mk] at hfix
            rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp hfix with
              ⟨a, ha⟩
            have h0 := congrFun ha (0 : Fin 2)
            simpa [Matrix.GeneralLinearGroup.toLin_apply,
              Matrix.mulVec, dotProduct] using h0.symm
          have hA11 :
              (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
            have hfix := hswap_zero
            change rho (conjH' hswap) zero = inf at hfix
            rw [← hA, hrho_apply] at hfix
            dsimp only [inf, zero] at hfix
            rw [Projectivization.smul_mk] at hfix
            rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp hfix with
              ⟨a, ha⟩
            have h1 := congrFun ha (1 : Fin 2)
            simpa [Matrix.GeneralLinearGroup.toLin_apply,
              Matrix.mulVec, dotProduct] using h1.symm
          have hA10_ne :
              (A : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
            intro hc
            have hdet := A.property
            rw [Matrix.det_fin_two, hA00, hA11, hc] at hdet
            norm_num at hdet
          have haffine_x0_mem : affine (x0 : F) ∈ S := by
            rcases x0.property with ⟨g, hgP, hg⟩
            refine ⟨g * hswap, ?_⟩
            change (g * hswap) • inf = affine (x0 : F)
            rw [mul_smul, hswap_inf]
            change rho (conjH' g) zero = affine (x0 : F)
            rw [hg]
            simpa using hunipotent_affine (x0 : F) 0
          let zswap : S :=
            ⟨hswap • affine (x0 : F), by
              rcases haffine_x0_mem with ⟨g, hg⟩
              change g • inf = affine (x0 : F) at hg
              refine ⟨hswap * g, ?_⟩
              change (hswap * g) • inf = hswap • affine (x0 : F)
              rw [mul_smul, hg]⟩
          have hzswap_ne_inf : (zswap : Point) ≠ inf := by
            intro hz
            have hzero_eq :
                hswap • zero = hswap • affine (x0 : F) := by
              change hswap • zero = (zswap : Point)
              rw [hswap_zero, hz]
            have hzero_affine : zero = affine (x0 : F) :=
              smul_left_cancel hswap hzero_eq
            have hxzero : (0 : F) = (x0 : F) := by
              apply haffine_injective
              simpa [affine, zero] using hzero_affine
            exact hx0_ne_zero (Subtype.ext hxzero.symm)
          obtain ⟨w, hw⟩ := hcover zswap hzswap_ne_inf
          obtain ⟨k, hk⟩ := hW_span w
          have hk_ne_zero : k ≠ 0 := by
            intro hk0
            have hwzero : (w : F) = 0 := by simp [hk, hk0]
            have hz_zero : (zswap : Point) = zero := by
              rw [hw, hwzero]
            have hinf_affine :
                hswap • inf = hswap • affine (x0 : F) := by
              rw [hswap_inf, ← hz_zero]
            have hia : inf = affine (x0 : F) :=
              smul_left_cancel hswap hinf_affine
            exact (haffine_ne_inf x0) hia.symm
          have hact :
              rho (QuotientGroup.mk'
                (Subgroup.center
                  (Matrix.SpecialLinearGroup (Fin 2) F)) A)
                  (affine (x0 : F)) =
                affine (w : F) := by
            rw [hA]
            exact hw
          dsimp only [affine] at hact
          rw [hrho_apply, Projectivization.smul_mk] at hact
          rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp hact with
            ⟨a0, ha0⟩
          have ha0_0 := congrFun ha0 (0 : Fin 2)
          have ha0_1 := congrFun ha0 (1 : Fin 2)
          simp [Matrix.GeneralLinearGroup.toLin_apply,
            Matrix.mulVec, dotProduct, hA00, hA11] at ha0_0 ha0_1
          let Ak : GL (Fin 2) K :=
            Matrix.GeneralLinearGroup.mkOfDetNeZero
              !![0, k; 1, 0]
              (by simp [Matrix.det_fin_two, hk_ne_zero])
          let scale : Fˣ := Units.mk0
            ((A : Matrix (Fin 2) (Fin 2) F) 1 0 * (x0 : F))
            (mul_ne_zero hA10_ne hx0_val_ne_zero)
          have hmat :
              Di * Matrix.SpecialLinearGroup.toGL A * D =
                Matrix.GeneralLinearGroup.scalar (Fin 2) scale *
                  Matrix.GeneralLinearGroup.map K.subtype Ak := by
            apply Matrix.GeneralLinearGroup.ext
            intro i j0
            fin_cases i <;> fin_cases j0
            · simp [D, Di, Ak, scale, Matrix.mul_apply, Matrix.vecMul,
                dotProduct, hA00]
            · simp [D, Di, Ak, scale, Matrix.mul_apply, Matrix.vecMul,
                dotProduct, hA00, hx0_ne_zero]
              rw [← ha0_0, ha0_1, hk]
              field_simp
            · simp [D, Di, Ak, scale, Matrix.mul_apply, Matrix.vecMul,
                dotProduct, hA11]
            · simp [D, Di, Ak, scale, Matrix.mul_apply, Matrix.vecMul,
                dotProduct, hA11]
          change toF hswap ∈ j.range
          refine ⟨Matrix.ProjGenLinGroup.mk Ak, ?_⟩
          change j (Matrix.ProjGenLinGroup.mk Ak) = toF hswap
          rw [h826_pglMap_mk]
          have hiota :
              iotaF (conjH' hswap) =
                Matrix.ProjGenLinGroup.mk
                  (Matrix.SpecialLinearGroup.toGL A) := by
            rw [← hA]
            exact h826_pslToPGL_mk A
          change
            Matrix.ProjGenLinGroup.mk
                (Matrix.GeneralLinearGroup.map K.subtype Ak) =
              dPGL⁻¹ * iotaF (conjH' hswap) * (dPGL⁻¹)⁻¹
          rw [hiota]
          have hd_inv :
              dPGL⁻¹ = Matrix.ProjGenLinGroup.mk Di := by
            dsimp only [dPGL]
            rw [← map_inv, ← hDi]
          have hd_inv_inv :
              (Matrix.ProjGenLinGroup.mk Di)⁻¹ =
                Matrix.ProjGenLinGroup.mk D := by
            rw [← map_inv, hDi, inv_inv]
          rw [hd_inv, hd_inv_inv]
          change
            Matrix.ProjGenLinGroup.mk
                (Matrix.GeneralLinearGroup.map K.subtype Ak) =
              Matrix.ProjGenLinGroup.mk Di *
                Matrix.ProjGenLinGroup.mk
                  (Matrix.SpecialLinearGroup.toGL A) *
                Matrix.ProjGenLinGroup.mk D
          rw [← map_mul, ← map_mul, hmat, map_mul,
            Matrix.ProjGenLinGroup.mk_scalar, one_mul]
        have hNP_le_L : NP ≤ L := by
          have hPN_le : PN ≤ L.comap NP.subtype := by
            intro n hn
            apply hP_le_L
            exact hn
          have hC_le : C ≤ L.comap NP.subtype := by
            intro d hd
            let dc : C := ⟨d, hd⟩
            rcases hcgen dc with ⟨z, hz⟩
            have hzNP : (cgen : NP) ^ z = d :=
              congrArg Subtype.val hz
            have hzH : ((cgen : NP) : H) ^ z = (d : H) :=
              congrArg Subtype.val hzNP
            change ((d : NP) : H) ∈ L
            rw [← hzH]
            simpa only [cN] using L.zpow_mem hcgen_mem_L z
          have htop_le : (⊤ : Subgroup NP) ≤ L.comap NP.subtype := by
            rw [← hcomp.sup_eq_top]
            exact sup_le hPN_le hC_le
          intro n hn
          change (⟨n, hn⟩ : NP) ∈ L.comap NP.subtype
          exact htop_le (Subgroup.mem_top (⟨n, hn⟩ : NP))
        have hLtop : L = ⊤ := by
          apply top_unique
          rw [← hgen]
          exact sup_le hNP_le_L
            (Subgroup.zpowers_le.mpr hswap_mem_L)
        have htoF_range : ∀ x : H, toF x ∈ j.range := by
          intro x
          change x ∈ L
          rw [hLtop]
          trivial
        let toRange : H →* j.range :=
          toF.codRestrict j.range htoF_range
        let eJ : Matrix.ProjGenLinGroup (Fin 2) K ≃* j.range :=
          MulEquiv.ofBijective j.rangeRestrict
            ⟨fun a b hab => hj_injective (congrArg Subtype.val hab),
              MonoidHom.rangeRestrict_surjective j⟩
        let phi : H →* Matrix.ProjGenLinGroup (Fin 2) K :=
          eJ.symm.toMonoidHom.comp toRange
        have hphi_injective : Function.Injective phi := by
          intro x y hxy
          apply hconjH'_injective
          apply h826_pslToPGL_injective
          apply (MulAut.conj dPGL⁻¹).injective
          change toF x = toF y
          have hrange : toRange x = toRange y := by
            apply eJ.symm.injective
            exact hxy
          exact congrArg Subtype.val hrange
        exact ⟨phi, hphi_injective⟩
      have htwo_torus_core :
          (p ^ m = 3 ∧ Nat.card H = 60 ∧
            (p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) ∧
            Nat.card (Sylow 5 H) = 6 ∧
            Function.Injective (MulAction.toPermHom H (Sylow 5 H))) ∨
          (2 * m ∣ f ∧ Nonempty
            (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) ∨
          (m ∣ f ∧ Nonempty
            (H ≃* PSL2MatrixGroup (GaloisField p m))) := by
        have horder_cases :=
          h826_group_order_cases
            (p ^ m) (Nat.card (Z i0)) (Nat.card (Z i1))
            (Nat.card H) NP.index (NZ i0).index (NZ i1).index
            hpm_gt (hnontrivial i0) (hnontrivial i1)
            ((hcoprime i0).pow_left m) ((hcoprime i1).pow_left m)
            hi0_dvd_sub_one htorus_gcd
            (by simpa only [c] using hH_eq_c)
            hNP_index_factor hi0_factor hi1_factor hcount_pair
        rcases horder_cases with hsmall | hfull | hhalf
        · left
          rcases hsmall with ⟨hpm3, hi0card, hi1card, hcard60⟩
          have hrestriction : p = 5 ∨ 5 ∣ p ^ (2 * f) - 1 := by
            by_cases hp5 : p = 5
            · exact Or.inl hp5
            · right
              have hfive_torus :
                  5 ∣ (Nat.card F - 1) /
                      Nat.gcd (Nat.card F - 1) 2 ∨
                    5 ∣ (Nat.card F + 1) /
                      Nat.gcd (Nat.card F - 1) 2 := by
                have h := hdivides i1
                rw [hi1card] at h
                exact h
              have hgcd_dvd_add :
                  Nat.gcd (Nat.card F - 1) 2 ∣ Nat.card F + 1 := by
                have hadd := Nat.dvd_add
                  (Nat.gcd_dvd_left (Nat.card F - 1) 2)
                  (Nat.gcd_dvd_right (Nat.card F - 1) 2)
                have hFpos : 0 < Nat.card F := Nat.card_pos
                convert hadd using 1 <;> omega
              have hfive_factor :
                  5 ∣ Nat.card F - 1 ∨ 5 ∣ Nat.card F + 1 := by
                rcases hfive_torus with hminus | hplus
                · exact Or.inl (dvd_trans hminus
                    (Nat.div_dvd_of_dvd
                      (Nat.gcd_dvd_left (Nat.card F - 1) 2)))
                · exact Or.inr (dvd_trans hplus
                    (Nat.div_dvd_of_dvd hgcd_dvd_add))
              have hfive_sq : 5 ∣ Nat.card F ^ 2 - 1 := by
                have hfactor :
                    Nat.card F ^ 2 - 1 =
                      (Nat.card F - 1) * (Nat.card F + 1) := by
                  simpa [mul_comm] using Nat.sq_sub_sq (Nat.card F) 1
                rw [hfactor]
                rcases hfive_factor with hminus | hplus
                · exact dvd_mul_of_dvd_left hminus _
                · exact dvd_mul_of_dvd_right hplus _
              rw [hFcard, ← pow_mul] at hfive_sq
              simpa [mul_comm] using hfive_sq
          have hi1index : (Z i1).index = 12 := by
            have hmul := (Z i1).card_mul_index
            rw [hi1card, hcard60] at hmul
            apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 5)
            simpa using hmul
          have hNZi1index : (NZ i1).index = 6 := by
            have hfactor := hi1_factor
            rw [hi1card, hcard60] at hfactor
            apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 10)
            norm_num at hfactor ⊢
            exact hfactor
          letI : Fact (Nat.Prime 5) := ⟨by decide⟩
          let hZi1P : IsPGroup 5 (Z i1) :=
            IsPGroup.of_card (n := 1) (by simpa using hi1card)
          let Q : Sylow 5 H := hZi1P.toSylow (by
            rw [hi1index]
            norm_num)
          have hSylow5 : Nat.card (Sylow 5 H) = 6 := by
            calc
              Nat.card (Sylow 5 H) =
                  (Subgroup.normalizer (Q : Set H)).index :=
                Q.card_eq_index_normalizer
              _ = (NZ i1).index := by rfl
              _ = 6 := hNZi1index
          let act := MulAction.toPermHom H (Sylow 5 H)
          have hker_le_normalizer (R : Sylow 5 H) :
              act.ker ≤ Subgroup.normalizer (R : Set H) := by
            intro x hx
            have hxperm : act x = 1 := hx
            have hxfix : x • R = R := by
              have h := DFunLike.congr_fun hxperm R
              simpa [act] using h
            exact Sylow.smul_eq_iff_mem_normalizer.mp hxfix
          have hnormalizer_card_ten :
              Nat.card (Subgroup.normalizer (Q : Set H)) = 10 := by
            have hQindex :
                (Subgroup.normalizer (Q : Set H)).index = 6 := by
              calc
                (Subgroup.normalizer (Q : Set H)).index =
                    Nat.card (Sylow 5 H) :=
                  Q.card_eq_index_normalizer.symm
                _ = 6 := hSylow5
            have hmul :=
              (Subgroup.normalizer (Q : Set H)).card_mul_index
            rw [hQindex, hcard60] at hmul
            apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 6)
            simpa using hmul
          have hker_card_dvd_ten : Nat.card act.ker ∣ 10 := by
            have hdvd : Nat.card act.ker ∣
                Nat.card (Subgroup.normalizer (Q : Set H)) :=
              Subgroup.card_dvd_of_le (hker_le_normalizer Q)
            rw [hnormalizer_card_ten] at hdvd
            exact hdvd
          have hno_sylow_le_ker (R : Sylow 5 H) :
              ¬ (R : Subgroup H) ≤ act.ker := by
            intro hRker
            letI : Fintype (Sylow 5 H) := Fintype.ofFinite _
            obtain ⟨S, hSR⟩ :=
              Fintype.exists_ne_of_one_lt_card
                (by simpa [Nat.card_eq_fintype_card] using
                  (show 1 < Nat.card (Sylow 5 H) by
                    rw [hSylow5]
                    norm_num)) R
            have hRnormalizesS :
                (R : Subgroup H) ≤ Subgroup.normalizer (S : Set H) := by
              intro x hx
              exact hker_le_normalizer S (hRker hx)
            have hsupP :
                IsPGroup 5
                  ((R : Subgroup H) ⊔ (S : Subgroup H) : Subgroup H) :=
              R.isPGroup'.to_sup_of_normal_right' S.isPGroup' hRnormalizesS
            have hsup_eq :
                (R : Subgroup H) ⊔ (S : Subgroup H) = S :=
              S.is_maximal' hsupP le_sup_right
            have hRleS : (R : Subgroup H) ≤ S := by
              calc
                (R : Subgroup H) ≤ (R : Subgroup H) ⊔ (S : Subgroup H) :=
                  le_sup_left
                _ = S := hsup_eq
            exact hSR (Sylow.ext (R.is_maximal' S.isPGroup' hRleS))
          have hfive_not_dvd_ker : ¬ 5 ∣ Nat.card act.ker := by
            intro hfive
            obtain ⟨x, hxorder⟩ :=
              exists_prime_orderOf_dvd_card' 5 hfive
            have hxHorder : orderOf (x : H) = 5 :=
              (Subgroup.orderOf_coe x).trans hxorder
            have hXisP : IsPGroup 5 (Subgroup.zpowers (x : H)) :=
              IsPGroup.of_card
                (((Nat.card_zpowers (x : H)).trans hxHorder).trans
                  (pow_one 5).symm)
            obtain ⟨R, hXR⟩ := hXisP.exists_le_sylow
            have hXcard : Nat.card (Subgroup.zpowers (x : H)) = 5 :=
              (Nat.card_zpowers (x : H)).trans hxHorder
            have hRcard : Nat.card R = 5 := by
              calc
                Nat.card R = Nat.card Q :=
                  Nat.card_congr (Sylow.equiv R Q).toEquiv
                _ = 5 := by
                  change Nat.card (Z i1) = 5
                  exact hi1card
            have hXR_eq :
                Subgroup.zpowers (x : H) = (R : Subgroup H) :=
              Subgroup.eq_of_le_of_card_ge hXR (by rw [hXcard, hRcard])
            apply hno_sylow_le_ker R
            rw [← hXR_eq]
            intro y hy
            rcases hy with ⟨j, rfl⟩
            exact act.ker.zpow_mem x.2 j
          have hker_card_cases :
              Nat.card act.ker = 1 ∨ Nat.card act.ker = 2 := by
            have hpos : 0 < Nat.card act.ker := Nat.card_pos
            have hle : Nat.card act.ker ≤ 10 :=
              Nat.le_of_dvd (by norm_num) hker_card_dvd_ten
            interval_cases h : Nat.card act.ker <;> norm_num [h] at *
          have hker_bot : act.ker = ⊥ := by
            rcases hker_card_cases with hker_one | hker_two
            · exact Subgroup.card_eq_one.mp hker_one
            · exfalso
              obtain ⟨y, hyorder⟩ :=
                exists_prime_orderOf_dvd_card' 5 (by
                  rw [hcard60]
                  norm_num)
              obtain ⟨c0, hc0order⟩ :=
                exists_prime_orderOf_dvd_card' 2 (by rw [hker_two])
              have hc0ne : c0 ≠ 1 := by
                intro hc
                rw [hc, orderOf_one] at hc0order
                norm_num at hc0order
              obtain ⟨c1, hc1ne, hc1unique⟩ :=
                (Nat.card_eq_two_iff' (1 : act.ker)).mp hker_two
              have hc0eq : c0 = c1 := hc1unique c0 hc0ne
              have hc0central : (c0 : H) ∈ Subgroup.center H := by
                rw [Subgroup.mem_center_iff]
                intro g
                let d : act.ker :=
                  ⟨g * (c0 : H) * g⁻¹,
                    (inferInstance : act.ker.Normal).conj_mem
                      (c0 : H) c0.2 g⟩
                have hdne : d ≠ 1 := by
                  intro hd
                  have hdval := congrArg Subtype.val hd
                  change g * (c0 : H) * g⁻¹ = 1 at hdval
                  apply hc0ne
                  apply Subtype.ext
                  calc
                    (c0 : H) = g⁻¹ * (g * (c0 : H) * g⁻¹) * g := by group
                    _ = 1 := by rw [hdval]; simp
                have hdeq : d = c0 := by
                  rw [hc0eq]
                  exact hc1unique d hdne
                have hdval := congrArg Subtype.val hdeq
                change g * (c0 : H) * g⁻¹ = (c0 : H) at hdval
                calc
                  g * (c0 : H) = (g * (c0 : H) * g⁻¹) * g := by group
                  _ = (c0 : H) * g := by rw [hdval]
              have hc0Horder : orderOf (c0 : H) = 2 :=
                (Subgroup.orderOf_coe c0).trans hc0order
              have hyHorder : orderOf (y : H) = 5 :=
                hyorder
              have hcomm : Commute (c0 : H) (y : H) :=
                (Subgroup.mem_center_iff.mp hc0central (y : H)).symm
              have hcop :
                  Nat.Coprime (orderOf (c0 : H)) (orderOf (y : H)) := by
                rw [hc0Horder, hyHorder]
                norm_num
              let x : H := (c0 : H) * (y : H)
              have hxorder : orderOf x = 10 := by
                dsimp only [x]
                rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop,
                  hc0Horder, hyHorder]
              have hxne : x ≠ 1 := by
                intro hx
                rw [hx, orderOf_one] at hxorder
                norm_num at hxorder
              obtain ⟨A, hxA, _⟩ :=
                huppert_II_8_22_unique_family hFcard H Z
                  hcyclic hnontrivial hcoprime hmaximal
                  hrepresentative hdistinct x hxne
              rcases A with Qp | z
              · have hxdvd : orderOf x ∣ Nat.card Qp :=
                  (Qp : Subgroup H).orderOf_dvd_natCard hxA
                have hQpcard : Nat.card Qp = 3 := by
                  calc
                    Nat.card Qp = Nat.card P :=
                      Nat.card_congr (Sylow.equiv Qp P).toEquiv
                    _ = 3 := hPm.trans hpm3
                rw [hxorder, hQpcard] at hxdvd
                norm_num at hxdvd
              · have hxdvd : orderOf x ∣ Nat.card z.2.1 :=
                  z.2.1.orderOf_dvd_natCard hxA
                obtain ⟨g, hg⟩ := z.2.2
                have hzcard : Nat.card z.2.1 = Nat.card (Z z.1) := by
                  rw [hg, Subgroup.card_map_of_injective
                    (MulAut.conj g).injective]
                have hz_cases : z.1 = i0 ∨ z.1 = i1 := by
                  have hzmem : z.1 ∈ ({i0, i1} : Finset (Fin 2)) := by
                    rw [huniv_pair]
                    simp
                  simpa using hzmem
                rw [hxorder, hzcard] at hxdvd
                rcases hz_cases with hzi0 | hzi1
                · rw [hzi0, hi0card] at hxdvd
                  norm_num at hxdvd
                · rw [hzi1, hi1card] at hxdvd
                  norm_num at hxdvd
          have hfaithful : Function.Injective act := by
            rw [← MonoidHom.ker_eq_bot_iff]
            exact hker_bot
          exact ⟨hpm3, hcard60, hrestriction, hSylow5, hfaithful⟩
        · have hKcard : Nat.card K = p ^ m := by
            apply Nat.le_antisymm hK_le_q
            calc
              p ^ m = (p ^ m - 1) + 1 :=
                (Nat.sub_add_cancel (Nat.zero_lt_of_lt hpm_gt)).symm
              _ = Nat.card (Z i0) + 1 := by rw [hfull.1]
              _ ≤ Nat.card K := hK_lower
          have hS_card : Nat.card S = p ^ m + 1 := by
            have hNPindex : NP.index = p ^ m + 1 := by
              have hqsubpos : 0 < p ^ m - 1 := by omega
              apply Nat.eq_of_mul_eq_mul_left
                (Nat.mul_pos (Nat.zero_lt_of_lt hpm_gt)
                  hqsubpos)
              calc
                (p ^ m * (p ^ m - 1)) * NP.index =
                    Nat.card NP * NP.index := by rw [hNPcard, hfull.1]
                _ = Nat.card H := NP.card_mul_index
                _ = (p ^ m + 1) * p ^ m * (p ^ m - 1) := hfull.2.2
                _ = (p ^ m * (p ^ m - 1)) * (p ^ m + 1) := by ring
            have hindex_card :=
              MulAction.index_stabilizer_of_transitive H baseS
            rw [hstabilizer_base, hNPindex] at hindex_card
            exact hindex_card.symm
          obtain ⟨hswap, hswap_inf, hswap_zero, hcover, hgen⟩ :=
            hsubline_swap hS_card
          have hmdiv : m ∣ f := by
            have hsplit_dvd :
                p ^ m - 1 ∣
                  (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 := by
              rw [← hfull.1]
              exact hi0_dvd_ambient
            have hpowdiv : p ^ m - 1 ∣ p ^ f - 1 := by
              rw [← hFcard]
              exact dvd_trans hsplit_dvd
                (Nat.div_dvd_of_dvd
                  (Nat.gcd_dvd_left (Nat.card F - 1) 2))
            exact h826_exponent_dvd_of_pow_sub_one_dvd
              (Fact.out : p.Prime).two_le hpowdiv
          obtain ⟨phi, hphi⟩ :=
            hPGL_embedding hKcard hswap hswap_inf hswap_zero hcover hgen
          have hPGLcard :
              Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) =
                p ^ m * ((p ^ m) ^ 2 - 1) := by
            rw [h826_card_pgl2, hKcard]
          have hfactor :
              (p ^ m) ^ 2 - 1 =
                (p ^ m - 1) * (p ^ m + 1) := by
            simpa [mul_comm] using Nat.sq_sub_sq (p ^ m) 1
          have hFullCardEq :
              Nat.card H =
                Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) := by
            rw [hfull.2.2, hPGLcard, hfactor]
            ring
          letI : Fintype K := Fintype.ofFinite K
          letI : Finite (Matrix.ProjGenLinGroup (Fin 2) K) :=
            Finite.of_surjective Matrix.ProjGenLinGroup.mk
              Matrix.ProjGenLinGroup.mk_surjective
          let eHPGL :
              H ≃* Matrix.ProjGenLinGroup (Fin 2) K :=
            MulEquiv.ofBijective phi
              ((Nat.bijective_iff_injective_and_card phi).2
                ⟨hphi, hFullCardEq⟩)
          by_cases hp_two : p = 2
          · subst p
            letI : CharP K 2 :=
              charP_of_card_eq_prime_pow (by simpa using hKcard)
            letI : Algebra (ZMod 2) K := ZMod.algebra K 2
            have htwozero : (2 : K) = 0 :=
              CharP.cast_eq_zero K 2
            have hneg_one : (-1 : K) = 1 := by
              apply (neg_eq_iff_add_eq_zero).2
              rw [show (1 : K) + 1 = 2 by norm_num, htwozero]
            have hcenter :
                Nat.card
                    (Subgroup.center
                      (Matrix.SpecialLinearGroup (Fin 2) K)) = 1 :=
              huppert614_card_center_of_neg_one_eq_one hneg_one
            have hPSLcard := huppert614_card_psl_mul_center (K := K)
            rw [hcenter, mul_one] at hPSLcard
            have hPSLPGLcard :
                Nat.card (PSL2MatrixGroup K) =
                  Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) :=
              hPSLcard.trans (h826_card_pgl2 (K := K)).symm
            let ePSLPGL :
                PSL2MatrixGroup K ≃*
                  Matrix.ProjGenLinGroup (Fin 2) K :=
              MulEquiv.ofBijective h826_pslToPGL
                ((Nat.bijective_iff_injective_and_card
                    (h826_pslToPGL (K := K))).2
                  ⟨h826_pslToPGL_injective, hPSLPGLcard⟩)
            let eK :=
              GaloisField.algEquivGaloisField 2 m hKcard
            let eHPSL : H ≃* PSL2MatrixGroup K :=
              eHPGL.trans ePSLPGL.symm
            exact Or.inr (Or.inr
              ⟨hmdiv, ⟨eHPSL.trans (h826_pslEquiv eK.toRingEquiv)⟩⟩)
          · have hp_odd : Odd p :=
              (Fact.out : p.Prime).odd_of_ne_two hp_two
            have hFodd : Odd (Nat.card F) := by
              rw [hFcard]
              exact hp_odd.pow
            have hF_two_dvd : 2 ∣ Nat.card F - 1 :=
              even_iff_two_dvd.mp (Nat.Odd.sub_odd hFodd odd_one)
            have hFgcd : Nat.gcd (Nat.card F - 1) 2 = 2 :=
              Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
                (Nat.dvd_gcd hF_two_dvd (dvd_refl 2))
            have hsplit_dvd :
                p ^ m - 1 ∣ (p ^ f - 1) / 2 := by
              rw [← hFcard, ← hFgcd, ← hfull.1]
              exact hi0_dvd_ambient
            have hpow_two_dvd : 2 ∣ p ^ f - 1 := by
              rwa [← hFcard]
            have htwo_split_dvd :
                2 * (p ^ m - 1) ∣ p ^ f - 1 :=
              Nat.mul_dvd_of_dvd_div hpow_two_dvd hsplit_dvd
            have hqminus_dvd : p ^ m - 1 ∣ p ^ f - 1 :=
              dvd_trans hsplit_dvd
                (Nat.div_dvd_of_dvd hpow_two_dvd)
            have htwo_dvd_quot :
                2 ∣ (p ^ f - 1) / (p ^ m - 1) :=
              (Nat.dvd_div_iff_mul_dvd hqminus_dvd).2
                (by simpa [mul_comm] using htwo_split_dvd)
            obtain ⟨k, hfk⟩ := hmdiv
            have hquotEven :
                Even (((p ^ m) ^ k - 1) / (p ^ m - 1)) := by
              rw [hfk, pow_mul] at htwo_dvd_quot
              exact even_iff_two_dvd.mpr htwo_dvd_quot
            have hsumEven :
                Even (∑ i ∈ Finset.range k, (p ^ m) ^ i) := by
              rw [Nat.geomSum_eq (by omega)]
              exact hquotEven
            have hkEven : Even k := by
              rw [Finset.even_sum_iff_even_card_odd] at hsumEven
              simpa [(hp_odd.pow : Odd (p ^ m)).pow] using hsumEven
            have htwo_m_div : 2 * m ∣ f := by
              rcases hkEven with ⟨r0, hr0⟩
              refine ⟨r0, ?_⟩
              rw [hfk, hr0]
              ring
            letI : Algebra (ZMod p) K := ZMod.algebra K p
            let eK :=
              GaloisField.algEquivGaloisField p m hKcard
            let pglHom :
                Matrix.ProjGenLinGroup (Fin 2) K →*
                  Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m) :=
              h826_pglMap eK.toRingEquiv.toRingHom
            letI : Finite
                (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m)) :=
              Finite.of_surjective Matrix.ProjGenLinGroup.mk
                Matrix.ProjGenLinGroup.mk_surjective
            have hPGLFieldCard :
                Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) =
                  Nat.card
                    (Matrix.ProjGenLinGroup (Fin 2)
                      (GaloisField p m)) := by
              rw [h826_card_pgl2, h826_card_pgl2,
                Nat.card_congr eK.toEquiv]
            let ePGL :
                Matrix.ProjGenLinGroup (Fin 2) K ≃*
                  Matrix.ProjGenLinGroup (Fin 2)
                    (GaloisField p m) :=
              MulEquiv.ofBijective pglHom
                ((Nat.bijective_iff_injective_and_card pglHom).2
                  ⟨h826_pglMap_injective _
                    eK.injective, hPGLFieldCard⟩)
            exact Or.inr (Or.inl
              ⟨htwo_m_div, ⟨eHPGL.trans ePGL⟩⟩)
        · have hqodd : Odd (p ^ m) := hhalf.1.odd_of_right
          have hp_ne_two : p ≠ 2 := by
            intro hp
            subst p
            have hnot : ¬ 2 ∣ 2 ^ m :=
              Nat.prime_two.coprime_iff_not_dvd.mp hhalf.1.symm
            exact hnot (dvd_pow_self 2 hm_ne_zero)
          have hp_three : 3 ≤ p := by
            have hpgt := (Fact.out : p.Prime).one_lt
            omega
          have hq_two_dvd : 2 ∣ p ^ m - 1 :=
            even_iff_two_dvd.mp (Nat.Odd.sub_odd hqodd odd_one)
          have hzi0_twice :
              2 * Nat.card (Z i0) = p ^ m - 1 := by
              rw [hhalf.2.1, mul_comm]
              exact Nat.div_mul_cancel hq_two_dvd
          letI : Algebra (ZMod p) K := ZMod.algebra K p
          have hKcard : Nat.card K = p ^ m := by
            let e := Module.finrank (ZMod p) K
            have hKpow : p ^ e = Nat.card K :=
              FiniteField.pow_finrank_eq_natCard p K
            have he_le_m : e ≤ m := by
              rw [← Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt,
                hKpow]
              exact hK_le_q
            obtain ⟨m0, hm0⟩ :=
              Nat.exists_eq_succ_of_ne_zero hm_ne_zero
            have hqeq : p ^ m = p ^ m0 * p := by
              rw [hm0, pow_succ]
            have hprev_lt_K : p ^ m0 < Nat.card K := by
              have hp_bound :
                  3 * p ^ m0 ≤ p ^ m := by
                rw [hqeq]
                simpa [mul_comm] using
                  Nat.mul_le_mul_left (p ^ m0) hp_three
              omega
            have heq : e = m := by
              by_contra hne
              have he_lt : e < m := lt_of_le_of_ne he_le_m hne
              have he_le_m0 : e ≤ m0 := by omega
              have hpow_le : p ^ e ≤ p ^ m0 :=
                Nat.pow_le_pow_right (Fact.out : p.Prime).pos he_le_m0
              rw [hKpow] at hpow_le
              omega
            rw [← hKpow, heq]
          have hS_card : Nat.card S = p ^ m + 1 := by
            have hcard_rewrite :
                Nat.card H =
                  (p ^ m + 1) * p ^ m * ((p ^ m - 1) / 2) := by
              rw [hhalf.2.2.2, show Nat.gcd (p ^ m - 1) 2 = 2 from
                Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
                  (Nat.dvd_gcd hq_two_dvd (dvd_refl 2))]
              exact Nat.mul_div_assoc ((p ^ m + 1) * p ^ m)
                hq_two_dvd
            have hNPindex : NP.index = p ^ m + 1 := by
              have hhalfpos : 0 < (p ^ m - 1) / 2 :=
                Nat.div_pos (by omega) (by norm_num)
              apply Nat.eq_of_mul_eq_mul_left
                (Nat.mul_pos (Nat.zero_lt_of_lt hpm_gt)
                  hhalfpos)
              calc
                (p ^ m * ((p ^ m - 1) / 2)) * NP.index =
                    Nat.card NP * NP.index := by
                      rw [hNPcard, hhalf.2.1]
                _ = Nat.card H := NP.card_mul_index
                _ = (p ^ m + 1) * p ^ m * ((p ^ m - 1) / 2) :=
                  hcard_rewrite
                _ = (p ^ m * ((p ^ m - 1) / 2)) * (p ^ m + 1) := by ring
            have hindex_card :=
              MulAction.index_stabilizer_of_transitive H baseS
            rw [hstabilizer_base, hNPindex] at hindex_card
            exact hindex_card.symm
          obtain ⟨hswap, hswap_inf, hswap_zero, hcover, hgen⟩ :=
            hsubline_swap hS_card
          have hmdiv : m ∣ f := by
            have hf_ne_zero :=
              huppert_II_8_27_field_exponent_ne_zero hFcard
            have hFodd : Odd (Nat.card F) := by
              rw [hFcard]
              exact ((Fact.out : p.Prime).odd_of_ne_two hp_ne_two).pow
            have hF_two_dvd : 2 ∣ Nat.card F - 1 :=
              even_iff_two_dvd.mp (Nat.Odd.sub_odd hFodd odd_one)
            have hFgcd : Nat.gcd (Nat.card F - 1) 2 = 2 :=
              Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
                (Nat.dvd_gcd hF_two_dvd (dvd_refl 2))
            have hhalf_dvd :
                (p ^ m - 1) / 2 ∣ (Nat.card F - 1) / 2 := by
              calc
                (p ^ m - 1) / 2 = Nat.card (Z i0) := hhalf.2.1.symm
                _ ∣ (Nat.card F - 1) /
                    Nat.gcd (Nat.card F - 1) 2 := hi0_dvd_ambient
                _ = (Nat.card F - 1) / 2 := by rw [hFgcd]
            obtain ⟨k, hk⟩ := hhalf_dvd
            have hpowdiv_card : p ^ m - 1 ∣ Nat.card F - 1 := by
              refine ⟨k, ?_⟩
              calc
                Nat.card F - 1 =
                    ((Nat.card F - 1) / 2) * 2 :=
                  (Nat.div_mul_cancel hF_two_dvd).symm
                _ = (((p ^ m - 1) / 2) * k) * 2 := by rw [hk]
                _ = (p ^ m - 1) * k := by
                  rw [mul_assoc, mul_comm k 2, ← mul_assoc,
                    Nat.div_mul_cancel hq_two_dvd]
            have hpowdiv : p ^ m - 1 ∣ p ^ f - 1 := by
              rwa [hFcard] at hpowdiv_card
            exact h826_exponent_dvd_of_pow_sub_one_dvd
              (Fact.out : p.Prime).two_le hpowdiv
          obtain ⟨phi, hphi⟩ :=
            hPGL_embedding hKcard hswap hswap_inf hswap_zero hcover hgen
          have hcharF_ne_two : ringChar F ≠ 2 := by
            rw [ringChar.eq F p]
            exact hp_ne_two
          have hnegF : (-1 : F) ≠ 1 :=
            Ring.neg_one_ne_one_of_char_ne_two hcharF_ne_two
          have hnegK : (-1 : K) ≠ 1 := by
            intro hneg
            apply hnegF
            simpa using congrArg Subtype.val hneg
          have htwoK : (2 : K) ≠ 0 := by
            intro htwo
            apply hnegK
            apply (neg_eq_iff_add_eq_zero).2
            simpa [show (1 : K) + 1 = 2 by norm_num] using htwo
          have hcardH :
              Nat.card H =
                (p ^ m + 1) * p ^ m * ((p ^ m - 1) / 2) := by
            rw [hhalf.2.2.2, show Nat.gcd (p ^ m - 1) 2 = 2 from
              Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
                (Nat.dvd_gcd hq_two_dvd (dvd_refl 2))]
            exact Nat.mul_div_assoc ((p ^ m + 1) * p ^ m)
              hq_two_dvd
          have hPGLcard :
              Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) =
                p ^ m * ((p ^ m) ^ 2 - 1) := by
            rw [h826_card_pgl2, hKcard]
          have hfactor :
              (p ^ m) ^ 2 - 1 = (p ^ m - 1) * (p ^ m + 1) := by
            simpa [mul_comm] using Nat.sq_sub_sq (p ^ m) 1
          have hPGLtwice :
              Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) =
                Nat.card H * 2 := by
            rw [hPGLcard, hfactor, hcardH]
            obtain ⟨r0, hr0⟩ := hq_two_dvd
            rw [hr0]
            simp
            ring
          have hRangeCard :
              Nat.card H = Nat.card phi.range :=
            Nat.card_congr (MonoidHom.ofInjective hphi).toEquiv
          letI : Fintype K := Fintype.ofFinite K
          letI : Finite (Matrix.ProjGenLinGroup (Fin 2) K) :=
            Finite.of_surjective Matrix.ProjGenLinGroup.mk
              Matrix.ProjGenLinGroup.mk_surjective
          letI : Finite phi.range :=
            Finite.of_injective phi.range.subtype
              phi.range.subtype_injective
          have hphiIndex : phi.range.index = 2 := by
            have hindex := phi.range.index_mul_card
            rw [← hRangeCard, hPGLtwice] at hindex
            apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := H))
            calc
              phi.range.index * Nat.card H = Nat.card H * 2 := hindex
              _ = 2 * Nat.card H := by ring
          have hPSLindex :=
            h826_pslToPGL_range_index_eq_two hnegK
          have hRangeEq :=
            h826_index_two_subgroup_eq_pslRange
              htwoK phi.range hphiIndex hPSLindex
          let eHRange : H ≃* phi.range :=
            MonoidHom.ofInjective hphi
          let ePSLRange :
              PSL2MatrixGroup K ≃*
                (h826_pslToPGL (K := K)).range :=
            MonoidHom.ofInjective h826_pslToPGL_injective
          let eHK : H ≃* PSL2MatrixGroup K :=
            eHRange.trans
              ((MulEquiv.subgroupCongr hRangeEq).trans ePSLRange.symm)
          let eK :=
            GaloisField.algEquivGaloisField p m hKcard
          exact Or.inr (Or.inr
            ⟨hmdiv, ⟨eHK.trans (h826_pslEquiv eK.toRingEquiv)⟩⟩)
      exact Or.inr htwo_torus_core
  have h826_semidirect_structure
      (hcard : Nat.card H =
        Nat.card (Subgroup.normalizer (P : Set H))) :
      ∃ t : ℕ,
        t ∣ p ^ m - 1 ∧
        t ∣ (p ^ f - 1) / Nat.gcd (p ^ f - 1) 2 ∧
        ∃ N C : Subgroup H,
          N.Normal ∧ IsElementaryAbelian p N ∧ Nat.card N = p ^ m ∧
          IsCyclic C ∧ Nat.card C = t ∧ Disjoint N C ∧ N ⊔ C = ⊤ := by
    have hPnormal : (P : Subgroup H).Normal := by
      apply Subgroup.normalizer_eq_top_iff.mp
      exact Subgroup.eq_top_of_card_eq
        (H := Subgroup.normalizer (P : Set H)) hcard.symm
    have hPelementary : IsElementaryAbelian p P :=
      h826_sylow_elementary hFcard H P
    have h826_cyclic_complement :
        ∃ C : Subgroup H,
          IsCyclic C ∧ Disjoint (P : Subgroup H) C ∧
            (P : Subgroup H) ⊔ C = ⊤ ∧
            Nat.card C ∣
              (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∧
            (∀ c : C, c ≠ 1 →
              ∀ x : (P : Subgroup H), x ≠ 1 →
              (c : H) * (x : H) * (c : H)⁻¹ ≠ (x : H)) := by
      classical
      let N : Subgroup H := Subgroup.normalizer (P : Set H)
      have hN : N = Subgroup.normalizer (P : Set H) := rfl
      have hNtop : N = ⊤ := by
        exact Subgroup.eq_top_of_card_eq (H := N) hcard.symm
      have hP_le_N : (P : Subgroup H) ≤ N := Subgroup.le_normalizer
      let PN : Subgroup N := (P : Subgroup H).subgroupOf N
      letI : PN.Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer (by
          simpa [N] : N ≤ Subgroup.normalizer (P : Set H))
      obtain ⟨hquotient_cyclic, hquotient_card_dvd,
          hNormalizer_fixedPointFree, _⟩ :=
        h821_borel_quotient_data hFcard H P
          (by rw [← Subgroup.one_lt_card_iff_ne_bot, hPm]
              exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr
                ⟨pow_ne_zero m (Fact.out : p.Prime).ne_zero,
                  fun h => hP_nontrivial (hPm.trans h)⟩)
          N hN PN rfl
      have hquotient_card_dvd_sub_one :
          Nat.card (N ⧸ PN) ∣ Nat.card F - 1 :=
        dvd_trans hquotient_card_dvd
          (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left (Nat.card F - 1) 2))
      have hf_ne_zero : f ≠ 0 :=
        huppert_II_8_27_field_exponent_ne_zero hFcard
      have hp_dvd_cardF : p ∣ Nat.card F := by
        rw [hFcard]
        exact dvd_pow_self p hf_ne_zero
      have hp_not_dvd_cardF_sub_one : ¬ p ∣ Nat.card F - 1 := by
        intro hp_sub
        have hp_one : p ∣ 1 := by
          have hd := Nat.dvd_sub hp_dvd_cardF hp_sub
          have hcard_pos : 0 < Nat.card F := Nat.card_pos
          have hsub : Nat.card F - (Nat.card F - 1) = 1 := by
            omega
          rwa [hsub] at hd
        exact (Fact.out : p.Prime).not_dvd_one hp_one
      have hcop_p_quotient :
          Nat.Coprime p (Nat.card (N ⧸ PN)) :=
        Nat.Coprime.of_dvd_right hquotient_card_dvd_sub_one
          ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
            hp_not_dvd_cardF_sub_one)
      have hPNcard : Nat.card PN = p ^ m := by
        calc
          Nat.card PN = Nat.card P :=
            Nat.card_congr
              (Subgroup.subgroupOfEquivOfLe hP_le_N).toEquiv
          _ = p ^ m := hPm
      have hPNindex : PN.index = Nat.card (N ⧸ PN) := rfl
      have hPN_coprime_index : Nat.Coprime (Nat.card PN) PN.index := by
        rw [hPNcard, hPNindex]
        exact hcop_p_quotient.pow_left m
      obtain ⟨CN, hcomp⟩ :=
        Subgroup.exists_right_complement'_of_coprime hPN_coprime_index
      have hCNcyclic : IsCyclic CN := by
        let eC : N ⧸ PN ≃* CN := hcomp.symm.QuotientMulEquiv
        letI : IsCyclic (N ⧸ PN) := hquotient_cyclic
        exact isCyclic_of_surjective eC.toMonoidHom eC.surjective
      let C : Subgroup H := CN.map N.subtype
      have hCcyclic : IsCyclic C := by
        let eC : CN ≃* C :=
          Subgroup.equivMapOfInjective CN N.subtype N.subtype_injective
        letI : IsCyclic CN := hCNcyclic
        exact isCyclic_of_surjective eC.toMonoidHom eC.surjective
      have hPNmap : PN.map N.subtype = (P : Subgroup H) := by
        exact Subgroup.map_subgroupOf_eq_of_le hP_le_N
      have hdisjoint : Disjoint (P : Subgroup H) C := by
        rw [← hPNmap]
        exact Subgroup.disjoint_map N.subtype_injective hcomp.disjoint
      have hsup : (P : Subgroup H) ⊔ C = ⊤ := by
        rw [← hPNmap, ← Subgroup.map_sup, hcomp.sup_eq_top]
        rw [← MonoidHom.range_eq_map, N.range_subtype, hNtop]
      have hCNcard : Nat.card CN = Nat.card (N ⧸ PN) := by
        calc
          Nat.card CN = PN.index := hcomp.symm.index_eq_card.symm
          _ = Nat.card (N ⧸ PN) := hPNindex
      have hCcard : Nat.card C = Nat.card (N ⧸ PN) := by
        calc
          Nat.card C = Nat.card CN :=
            Subgroup.card_map_of_injective N.subtype_injective
          _ = Nat.card (N ⧸ PN) := hCNcard
      have hCdiv : Nat.card C ∣
          (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 := by
        rw [hCcard]
        exact hquotient_card_dvd
      have hCfixedPointFree :
          ∀ c : C, c ≠ 1 →
            ∀ x : (P : Subgroup H), x ≠ 1 →
            (c : H) * (x : H) * (c : H)⁻¹ ≠ (x : H) := by
        intro c hc x hx
        rcases c.property with ⟨n, hnCN, hn⟩
        have hnPN : n ∉ PN := by
          intro hnmem
          have hn_one : n = 1 :=
            Subgroup.disjoint_def.mp hcomp.disjoint hnmem hnCN
          apply hc
          apply Subtype.ext
          change (c : H) = 1
          rw [← hn, hn_one]
          rfl
        have hnfree := hNormalizer_fixedPointFree n hnPN x hx
        intro hfix
        apply hnfree
        have hn' : (n : H) = (c : H) := hn
        rw [hn']
        exact hfix
      exact ⟨C, hCcyclic, hdisjoint, hsup, hCdiv,
        hCfixedPointFree⟩
    obtain ⟨C, hCcyclic, hPCdisjoint, hPCsup, hCdiv,
        hCfixedPointFree⟩ :=
      h826_cyclic_complement
    have h826_complement_order_divides_sylow :
        Nat.card C ∣ p ^ m - 1 := by
      letI : (P : Subgroup H).Normal := hPnormal
      letI : MulDistribMulAction C P :=
        MulDistribMulAction.compHom P
          ((MulAut.conjNormal (H := (P : Subgroup H))).comp C.subtype)
      have hfree :
          ∀ c : C, c ≠ 1 →
            ∀ x : (P : Subgroup H), c • x = x → x = 1 := by
        intro c hc x hfix
        by_contra hx
        have hconj :
            (c : H) * (x : H) * (c : H)⁻¹ = (x : H) := by
          have hconj' := congrArg Subtype.val hfix
          change (c : H) * (x : H) * (c : H)⁻¹ = (x : H) at hconj'
          exact hconj'
        exact hCfixedPointFree c hc x hx hconj
      have hdiv := h826_card_actor_dvd_group_card_sub_one hfree
      rwa [hPm] at hdiv
    have h826_complement_order_divides_ambient :
        Nat.card C ∣ (p ^ f - 1) / Nat.gcd (p ^ f - 1) 2 := by
      rw [← hFcard]
      exact hCdiv
    exact ⟨Nat.card C, h826_complement_order_divides_sylow,
      h826_complement_order_divides_ambient, P, C, hPnormal,
      hPelementary, hPm, hCcyclic, rfl, hPCdisjoint, hPCsup⟩
  have h826_A5_order_sixty
      (hcard60 : Nat.card H = 60)
      (hSylow5 : Nat.card (Sylow 5 H) = 6)
      (hfaithful : Function.Injective
        (MulAction.toPermHom H (Sylow 5 H))) :
      Nonempty (H ≃* alternatingGroup (Fin 5)) := by
    letI : Fact (Nat.Prime 5) := ⟨by decide⟩
    letI : FaithfulSMul H (Sylow 5 H) := by
      rw [faithfulSMul_iff]
      intro g hg
      apply hfaithful
      apply DFunLike.ext _ _
      intro Q
      simpa using hg Q
    exact huppert_II_8_25_transitive_degree_six_order_sixty
      (Sylow.isPretransitive_of_finite (p := 5) (G := H)) hSylow5 hcard60
  rcases h826_counting_shapes with hsemidirect | hA5 | hPGL | hPSL
  · obtain ⟨t, ht_subfield, ht_ambient, N, C, hNnormal, hNelem,
      hNcard, hCcyclic, hCcard, hdisjoint, hsup⟩ :=
      h826_semidirect_structure hsemidirect
    exact Or.inl ⟨m, t, ht_subfield, ht_ambient, N, C, hNnormal,
      hNelem, hNcard, hCcyclic, hCcard, hdisjoint, hsup⟩
  · rcases hA5 with
      ⟨hpm3, hcard60, hrestriction, hSylow5, hfaithful⟩
    have hHA5 := h826_A5_order_sixty hcard60 hSylow5 hfaithful
    exact Or.inr (Or.inl ⟨m, hpm3, hrestriction, hHA5⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨m, hm_ne_zero, hPGL.1, hPGL.2⟩))
  · exact Or.inr (Or.inr (Or.inr
      ⟨m, hm_ne_zero, hPSL.1, hPSL.2⟩))
/--
Huppert II, Main Theorem 8.27 (Dickson), stated as the direct subgroup
classification for `PSL(2,p^f)`.  The eight alternatives are written in the
statement itself rather than hidden behind a local classification-data type.
-/
public theorem huppert_II_8_27_dickson_psl2_subgroup_classification
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F)) :
    IsElementaryAbelian p H ∨
      (∃ z : ℕ,
        ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
        Nat.card H = z ∧ IsCyclic H) ∨
      (∃ z : ℕ,
        ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
        Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
      ((p ≠ 2 ∨ Even f) ∧ Nonempty (H ≃* alternatingGroup (Fin 4))) ∨
      ((16 ∣ p ^ (2 * f) - 1) ∧ Nonempty (H ≃* Equiv.Perm (Fin 4))) ∨
      ((p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) ∧
        Nonempty (H ≃* alternatingGroup (Fin 5))) ∨
      (∃ m t : ℕ,
        t ∣ p ^ m - 1 ∧
        t ∣ (p ^ f - 1) / Nat.gcd (p ^ f - 1) 2 ∧
        ∃ N C : Subgroup H,
          N.Normal ∧ IsElementaryAbelian p N ∧ Nat.card N = p ^ m ∧
          IsCyclic C ∧ Nat.card C = t ∧ Disjoint N C ∧ N ⊔ C = ⊤) ∨
      (∃ m : ℕ, m ≠ 0 ∧ m ∣ f ∧
        Nonempty (H ≃* PSL2MatrixGroup (GaloisField p m))) ∨
      (∃ m : ℕ, m ≠ 0 ∧ 2 * m ∣ f ∧
        Nonempty (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) := by
  let P : Sylow p H := default
  obtain ⟨m, hPm⟩ := P.isPGroup'.exists_card_eq
  by_cases hP_trivial : p ^ m = 1
  · have hp_not_dvd_card_H : ¬ p ∣ Nat.card H := by
      intro hpdiv
      have hpdvdP : p ∣ Nat.card P := P.dvd_card_of_dvd_card hpdiv
      rw [hPm, hP_trivial] at hpdvdP
      exact (Fact.out : p.Prime).not_dvd_one hpdvdP
    rcases huppert_II_8_24_dickson_case_no_p_part hFcard H hp_not_dvd_card_H with
      h | h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · have hP_nontrivial : Nat.card P ≠ 1 := by
      intro hPone
      apply hP_trivial
      rw [← hPm, hPone]
    by_cases hnormalizer :
        Subgroup.normalizer (P : Set H) = (P : Subgroup H)
    · have hpm : 1 < p ^ m := by
        exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr
          ⟨pow_ne_zero m (Fact.out : p.Prime).ne_zero, hP_trivial⟩
      rcases huppert_II_8_23_dickson_case_p_part_normalizer_self
          hFcard H P hPm hpm hnormalizer with h | h | h
      · exact Or.inl h.2
      · rcases h with ⟨hpm2, z, hzodd, hzdiv, hHcard, hHdihedral⟩
        exact Or.inr (Or.inr (Or.inl ⟨z, hzdiv, hHcard, hHdihedral⟩))
      · rcases h with ⟨hpm3, hHA4⟩
        have hp_ne_two : p ≠ 2 := by
          intro hp
          subst p
          cases m with
          | zero => norm_num at hpm3
          | succ m =>
              rw [pow_succ] at hpm3
              omega
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl hp_ne_two, hHA4⟩)))
    · rcases huppert_II_8_26_dickson_case_p_part_normalizer_large
          hFcard H P hP_nontrivial hnormalizer with h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · rcases h with ⟨m, _hpm3, hrestriction, hA5⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl ⟨hrestriction, hA5⟩)))))
      · exact Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
      · exact Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
end External
end BenderSuzuki
