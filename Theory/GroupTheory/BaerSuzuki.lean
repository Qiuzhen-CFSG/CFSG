module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.PGroup
import all Mathlib.GroupTheory.IsSubnormal
public import Theory.PGroupCore
public import FeitThompson.BGsection1.Defs
public import FeitThompson.BGsection1.PLengthLemmas
public import FeitThompson.GroupAction.Cardinalities
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Baer–Suzuki conjugate-pair criterion

This module exposes the finite-group Baer–Suzuki criterion in the p-core form needed by downward representation theory. For a p-element whose conjugate pairs generate p-groups, the Alperin–Lyons minimal-counterexample argument uses Sylow intersection cardinality, the normalizer condition in finite p-groups, and induction through the p-core quotient. The proof is extracted from `BenderSuzuki/SE/PStabilityReduction.lean`, Gorenstein Chapter 3, Theorem 8.2.

-/

noncomputable section

universe uG

open scoped Pointwise

namespace BenderSuzuki
private theorem isSubnormal_of_normalizerCondition
    {G : Type*} [Group G] [Finite G] (hnc : NormalizerCondition G)
    (H : Subgroup G) :
    Subgroup.IsSubnormal H := by
  classical
  let μ : Subgroup G → ℕ := fun H => Nat.card G - Nat.card H
  refine (measure μ).wf.induction H ?_
  intro H ih
  by_cases htop : H = ⊤
  · simp [htop]
  · have hlt : H < Subgroup.normalizer (H : Set G) := hnc H (lt_top_iff_ne_top.mpr htop)
    have hcard_lt : Nat.card H < Nat.card (Subgroup.normalizer (H : Set G)) := by
      have hset : (H : Set G) ⊂ (Subgroup.normalizer (H : Set G) : Set G) := hlt
      simpa using
        (Set.Finite.card_lt_card
          (Set.toFinite (Subgroup.normalizer (H : Set G) : Set G)) hset)
    have hnorm_card_le : Nat.card (Subgroup.normalizer (H : Set G)) ≤ Nat.card G :=
      Subgroup.card_le_card_group (H := Subgroup.normalizer (H : Set G))
    have hnorm_subnormal : Subgroup.IsSubnormal (Subgroup.normalizer (H : Set G)) := by
      exact ih (Subgroup.normalizer (H : Set G)) (by
        change Nat.card G - Nat.card (Subgroup.normalizer (H : Set G)) < Nat.card G - Nat.card H
        omega)
    exact Subgroup.IsSubnormal.step H (Subgroup.normalizer (H : Set G)) hlt.le hnorm_subnormal inferInstance



private theorem exists_conjClass_mem_normalizer_closure_inter
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {C S : Set G} {D : Subgroup G} (hD_eq : D = Subgroup.closure S)
    (hC_conj : ∀ a ∈ C, ∀ g : G, g * a * g⁻¹ ∈ C)
    (A B : Sylow p G)
    (hS_C : S ⊆ C)
    (hS_A : S ⊆ (A : Set G)) (hD_le_B : D ≤ (B : Subgroup G))
    {w : G} (hwC : w ∈ C) (hwA : w ∈ (A : Subgroup G))
    (hw_not_B : w ∉ (B : Subgroup G)) :
    ∃ a : G, a ∈ C ∧ a ∈ (A : Subgroup G) ∧ a ∉ D ∧
      a ∈ Subgroup.normalizer D := by
  classical
  have hw_not_D : w ∉ D := fun hwD => hw_not_B (hD_le_B hwD)
  let DA : Subgroup (A : Subgroup G) := D.subgroupOf (A : Subgroup G)
  have hDA_subnormal : Subgroup.IsSubnormal DA := by
    have : Group.IsNilpotent A :=
      IsPGroup.isNilpotent (G := A) (p := p) A.isPGroup'
    exact isSubnormal_of_normalizerCondition
      (G := (A : Subgroup G)) (Group.normalizerCondition_of_isNilpotent) DA
  rcases Subgroup.IsSubnormal.exists_chain hDA_subnormal with
    ⟨m, f, hmono, hnormal, hf0, hfm⟩
  let Bad : ℕ → Prop := fun i =>
    ∃ a : G, ∃ haA : a ∈ (A : Subgroup G),
      a ∈ C ∧ (⟨a, haA⟩ : A) ∈ f i ∧ a ∉ D
  have hBad_exists : ∃ i, Bad i := by
    refine ⟨m, w, hwA, hwC, ?_, hw_not_D⟩
    simp [hfm]
  let i : ℕ := Nat.find hBad_exists
  have hiBad : Bad i := Nat.find_spec hBad_exists
  have hi_min : ∀ j < i, ¬ Bad j := by
    intro j hj
    exact Nat.find_min hBad_exists hj
  have hi_pos : 0 < i := by
    by_contra hpos
    have hi0 : i = 0 := Nat.eq_zero_of_not_pos hpos
    rcases hiBad with ⟨a, haA, _haC, hai, ha_not_D⟩
    have haD : a ∈ D := by
      have haDA : (⟨a, haA⟩ : A) ∈ DA := by
        simpa [hi0, hf0, DA] using hai
      change a ∈ D at haDA
      exact haDA
    exact ha_not_D haD
  let j : ℕ := i - 1
  have hji : j + 1 = i := by
    dsimp [j]
    omega
  have hprev_no : ¬ Bad j := hi_min j (by
    dsimp [j]
    omega)
  have hC_fprev_le_D :
      ∀ z : G, ∀ hzA : z ∈ (A : Subgroup G),
        z ∈ C → (⟨z, hzA⟩ : A) ∈ f j → z ∈ D := by
    intro z hzA hzC hzf
    by_contra hzD
    exact hprev_no ⟨z, hzA, hzC, hzf, hzD⟩
  rcases hiBad with ⟨a, haA, haC, hai, ha_not_D⟩
  have ha_fsucc : (⟨a, haA⟩ : A) ∈ f (j + 1) := by
    simpa [hji] using hai
  have hconj_gen_of_mem :
      ∀ {g : G} (hgA : g ∈ (A : Subgroup G)),
        (⟨g, hgA⟩ : A) ∈ f i →
        ∀ d : G, d ∈ S → g * d * g⁻¹ ∈ D := by
    intro g hgA hgf d hdS
    have hdA : d ∈ (A : Subgroup G) := hS_A hdS
    have hdD : d ∈ D := by
      rw [hD_eq]
      exact Subgroup.subset_closure hdS
    have hdDA : (⟨d, hdA⟩ : A) ∈ DA := by
      change d ∈ D
      exact hdD
    have hdfj : (⟨d, hdA⟩ : A) ∈ f j := by
      have hDA_le_fj : DA ≤ f j := by
        simpa [hf0] using hmono (Nat.zero_le j)
      exact hDA_le_fj hdDA
    have hdf_succ : (⟨d, hdA⟩ : A) ∈ f (j + 1) :=
      (hmono (Nat.le_succ j)) hdfj
    have hgf_succ : (⟨g, hgA⟩ : A) ∈ f (j + 1) := by
      simpa [hji] using hgf
    let gF : f (j + 1) := ⟨⟨g, hgA⟩, hgf_succ⟩
    let dF : f (j + 1) := ⟨⟨d, hdA⟩, hdf_succ⟩
    have hd_sub : dF ∈ (f j).subgroupOf (f (j + 1)) := by
      change (dF : A) ∈ f j
      exact hdfj
    have hconj_sub :
        gF * dF * gF⁻¹ ∈ (f j).subgroupOf (f (j + 1)) :=
      Subgroup.Normal.conj_mem (hnormal j) dF hd_sub gF
    have hgdgA : g * d * g⁻¹ ∈ (A : Subgroup G) :=
      A.mul_mem (A.mul_mem hgA hdA) (A.inv_mem hgA)
    have hconj_fj : (⟨g * d * g⁻¹, hgdgA⟩ : A) ∈ f j := by
      have hconj_fj' : ((gF * dF * gF⁻¹ : f (j + 1)) : A) ∈ f j := by
        change ((gF * dF * gF⁻¹ : f (j + 1)) : A) ∈ f j at hconj_sub
        exact hconj_sub
      have heq : ((gF * dF * gF⁻¹ : f (j + 1)) : A) =
          (⟨g * d * g⁻¹, hgdgA⟩ : A) := by
        ext
        simp [gF, dF, mul_assoc]
      simpa [heq] using hconj_fj'
    exact hC_fprev_le_D (g * d * g⁻¹) hgdgA (hC_conj d (hS_C hdS) g) hconj_fj
  have hconj_all_of_mem :
      ∀ {g : G} (hgA : g ∈ (A : Subgroup G)),
        (⟨g, hgA⟩ : A) ∈ f i →
        ∀ d : G, d ∈ D → g * d * g⁻¹ ∈ D := by
    intro g hgA hgf d hd
    refine Subgroup.closure_induction
      (p := fun d : G => fun _hd => g * d * g⁻¹ ∈ D) ?_ ?_ ?_ ?_
      (by simpa [hD_eq] using hd)
    · intro d hdS
      exact hconj_gen_of_mem hgA hgf d hdS
    · simp
    · intro x y _hx _hy hx hy
      simpa [mul_assoc] using D.mul_mem hx hy
    · intro x _hx hx
      simpa [mul_assoc] using D.inv_mem hx
  have hainv_i : (⟨a⁻¹, A.inv_mem haA⟩ : A) ∈ f i := by
    have hinv : ((⟨a, haA⟩ : A)⁻¹) ∈ f i := (f i).inv_mem hai
    have heq : ((⟨a, haA⟩ : A)⁻¹) = (⟨a⁻¹, A.inv_mem haA⟩ : A) := by
      ext
      simp
    simpa [heq] using hinv
  have ha_norm : a ∈ Subgroup.normalizer D := by
    rw [Subgroup.mem_normalizer_iff]
    intro d
    constructor
    · intro hd
      exact hconj_all_of_mem haA hai d hd
    · intro hd
      have hback := hconj_all_of_mem (A.inv_mem haA) hainv_i (a * d * a⁻¹) hd
      simpa [mul_assoc] using hback
  exact ⟨a, haC, haA, ha_not_D, ha_norm⟩

/-- Gorenstein, Chapter 3, Theorem 8.2, Alperin--Lyons form:
if every two elements in the conjugacy class of a `p`-element generate a
`p`-group, then that conjugacy class is contained in `O_p(G)`. -/
public theorem gorenstein_3_8_2_conjugacy_class_le_pCore
    {G : Type uG} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {x : G}
    (hx_p : IsPElement (p := p) x)
    (hpair :
      ∀ y : G, (∃ g : G, y = g * x * g⁻¹) →
        IsPGroup p (Subgroup.closure ({x, y} : Set G))) :
    ∀ z : G, (∃ g : G, z = g * x * g⁻¹) → z ∈ pCore p G := by
  -- Source: Daniel Gorenstein, *Finite Groups*, Chapter 3, Theorem 8.2,
  -- using the shorter Alperin--Lyons proof recorded in
  -- `Gorenstein/Gorenstein_3_8_3.tex`.
  classical
  suffices hx_core : x ∈ pCore p G by
    intro z hz
    rcases hz with ⟨g, rfl⟩
    exact (inferInstance : (pCore p G).Normal).conj_mem x hx_core g
  let Pmain :
      ∀ {G : Type uG}, [Group G] → [Finite G] →
        ∀ {x : G}, IsPElement (p := p) x →
          (∀ y : G, (∃ g : G, y = g * x * g⁻¹) →
            IsPGroup p (Subgroup.closure ({x, y} : Set G))) →
          x ∈ pCore p G := by
    suffices hmain :
        ∀ n : ℕ,
          ∀ {G : Type uG}, [Group G] → [Finite G] →
            Nat.card G = n →
            ∀ {x : G}, IsPElement (p := p) x →
              (∀ y : G, (∃ g : G, y = g * x * g⁻¹) →
              IsPGroup p (Subgroup.closure ({x, y} : Set G))) →
              x ∈ pCore p G by
      intro G _ _ x hx_p hpair
      exact hmain (Nat.card G) (G := G) rfl hx_p hpair
    intro n
    refine Nat.strongRecOn n (motive := fun n =>
        ∀ {G : Type uG}, [Group G] → [Finite G] →
          Nat.card G = n →
          ∀ {x : G}, IsPElement (p := p) x →
            (∀ y : G, (∃ g : G, y = g * x * g⁻¹) →
              IsPGroup p (Subgroup.closure ({x, y} : Set G))) →
            x ∈ pCore p G) ?_
    intro n ih G _ _ hcard x hx_p hpair
    by_cases hcore : pCore p G = ⊥
    · let C : Set G := {y : G | ∃ g : G, y = g * x * g⁻¹}
      have hxC : x ∈ C := ⟨1, by simp⟩
      have hC_conj : ∀ a ∈ C, ∀ g : G, g * a * g⁻¹ ∈ C := by
        rintro a ⟨t, rfl⟩ g
        refine ⟨g * t, ?_⟩
        simp [mul_assoc]
      have hcl_normal : (Subgroup.closure C).Normal := by
        refine ⟨?_⟩
        intro a ha g
        refine Subgroup.closure_induction
          (p := fun a : G => fun _ha => g * a * g⁻¹ ∈ Subgroup.closure C)
          ?_ ?_ ?_ ?_ ha
        · intro a ha
          exact Subgroup.subset_closure (hC_conj a ha g)
        · simp
        · intro a b _ha _hb ha hb
          simpa [mul_assoc] using (Subgroup.closure C).mul_mem ha hb
        · intro a _ha ha
          have hginv : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by
            simp [mul_assoc]
          simpa [hginv] using (Subgroup.closure C).inv_mem ha
      by_cases hcl_p : IsPGroup p (Subgroup.closure C)
      · have hle_core : Subgroup.closure C ≤ pCore p G := by
          exact le_sSup (a := Subgroup.closure C) ⟨hcl_normal, hcl_p⟩
        exact hle_core (Subgroup.subset_closure hxC)
      · have hcl_not_p : ¬ IsPGroup p (Subgroup.closure C) := hcl_p
        have hnot_C_le_sylow : ∀ P : Sylow p G, ¬ C ⊆ (P : Set G) := by
          intro P hCP
          have hcl_le : Subgroup.closure C ≤ (P : Subgroup G) :=
            (Subgroup.closure_le (K := (P : Subgroup G))).2 hCP
          exact hcl_not_p (IsPGroup.to_le P.isPGroup' hcl_le)
        let P₀ : Sylow p G := default
        have hnot_CP₀ : ¬ C ⊆ (P₀ : Set G) := hnot_C_le_sylow P₀
        have hnot_forall_mem : ¬ ∀ z ∈ C, z ∈ (P₀ : Subgroup G) := by
          intro hmem
          apply hnot_CP₀
          intro z hz
          exact hmem z hz
        push Not at hnot_forall_mem
        rcases hnot_forall_mem with ⟨y, hyC, hy_not_P₀⟩
        have hy_p : IsPElement (p := p) y := by
          rcases hyC with ⟨g, rfl⟩
          rcases hx_p with ⟨k, hk⟩
          have horder : orderOf x = orderOf (g * x * g⁻¹) := by
            exact SemiconjBy.orderOf_eq g (by
              dsimp [SemiconjBy]
              simp [mul_assoc])
          exact ⟨k, by simpa [hk] using horder.symm⟩
        have hy_zpowers_p : IsPGroup p (Subgroup.zpowers y) := by
          rw [IsPGroup.iff_orderOf]
          intro a
          have hdiv_order : orderOf (a : G) ∣ orderOf y := orderOf_dvd_of_mem_zpowers a.property
          rcases hy_p with ⟨k, hk⟩
          have hdiv : orderOf (a : G) ∣ p ^ k := hdiv_order.trans (by simp [hk])
          rcases (Nat.dvd_prime_pow (Fact.out : Nat.Prime p)).1 hdiv with ⟨m, _hmle, hm⟩
          exact ⟨m, by simpa [Subgroup.orderOf_coe] using hm⟩
        rcases IsPGroup.exists_le_sylow (p := p) hy_zpowers_p with ⟨Q₀, hQ₀⟩
        have hyQ₀ : y ∈ (Q₀ : Subgroup G) := by
          exact hQ₀ (Subgroup.mem_zpowers y)
        have hPQ_nonempty :
            ({r : Sylow p G × Sylow p G |
                {z : G | z ∈ C ∧ z ∈ (r.1 : Subgroup G)} ≠
                  {z : G | z ∈ C ∧ z ∈ (r.2 : Subgroup G)}}).Nonempty := by
          refine ⟨(Q₀, P₀), ?_⟩
          intro hsets
          have : y ∈ {z : G | z ∈ C ∧ z ∈ (P₀ : Subgroup G)} := by
            simpa [hsets] using
              (show y ∈ {z : G | z ∈ C ∧ z ∈ (Q₀ : Subgroup G)} from ⟨hyC, hyQ₀⟩)
          exact hy_not_P₀ this.2
        have hPQ_finite :
            ({r : Sylow p G × Sylow p G |
                {z : G | z ∈ C ∧ z ∈ (r.1 : Subgroup G)} ≠
                  {z : G | z ∈ C ∧ z ∈ (r.2 : Subgroup G)}} :
                Set (Sylow p G × Sylow p G)).Finite :=
          Set.finite_univ.subset (by intro r _; simp)
        rcases Set.exists_max_image
            ({r : Sylow p G × Sylow p G |
                {z : G | z ∈ C ∧ z ∈ (r.1 : Subgroup G)} ≠
                  {z : G | z ∈ C ∧ z ∈ (r.2 : Subgroup G)}})
            (fun r : Sylow p G × Sylow p G =>
              Nat.card ({z : G | z ∈ C ∧ z ∈ (r.1 : Subgroup G) ∧ z ∈ (r.2 : Subgroup G)} : Set G))
            hPQ_finite hPQ_nonempty with ⟨r, hrPQ, hrmax⟩
        rcases r with ⟨P, Q⟩
        have hKcap_ne : {z : G | z ∈ C ∧ z ∈ (P : Subgroup G)} ≠
            {z : G | z ∈ C ∧ z ∈ (Q : Subgroup G)} := hrPQ
        have hcard_CP_eq_CQ :
            Nat.card ({z : G | z ∈ C ∧ z ∈ (P : Subgroup G)} : Set G) =
              Nat.card ({z : G | z ∈ C ∧ z ∈ (Q : Subgroup G)} : Set G) := by
          rcases MulAction.exists_smul_eq (M := G) P Q with ⟨g, hg⟩
          have hg_inv : g⁻¹ • Q = P := by
            rw [← hg]
            simp
          let e :
              ({z : G | z ∈ C ∧ z ∈ (P : Subgroup G)} : Set G) ≃
                ({z : G | z ∈ C ∧ z ∈ (Q : Subgroup G)} : Set G) := {
            toFun z := by
              refine ⟨g * (z : G) * g⁻¹, hC_conj (z : G) z.2.1 g, ?_⟩
              have hmem : g * (z : G) * g⁻¹ ∈ ((g • P : Sylow p G) : Subgroup G) := by
                rw [Sylow.coe_subgroup_smul]
                simpa [MulAut.conj_apply] using
                  (Subgroup.smul_mem_pointwise_smul (z : G) (MulAut.conj g)
                    (P : Subgroup G) z.2.2)
              simpa [hg] using hmem
            invFun z := by
              refine ⟨g⁻¹ * (z : G) * g, ?_, ?_⟩
              · simpa using hC_conj (z : G) z.2.1 g⁻¹
              · have hmem : g⁻¹ * (z : G) * g ∈ ((g⁻¹ • Q : Sylow p G) : Subgroup G) := by
                  rw [Sylow.coe_subgroup_smul]
                  simpa [MulAut.conj_apply, mul_assoc] using
                    (Subgroup.smul_mem_pointwise_smul (z : G) (MulAut.conj g⁻¹)
                      (Q : Subgroup G) z.2.2)
                simpa [hg_inv] using hmem
            left_inv z := by
              ext
              simp [mul_assoc]
            right_inv z := by
              ext
              simp [mul_assoc]
          }
          exact Nat.card_congr e
        have hP_not_le_Q :
            ¬ {z : G | z ∈ C ∧ z ∈ (P : Subgroup G)} ⊆
              {z : G | z ∈ C ∧ z ∈ (Q : Subgroup G)} := by
          intro hle
          apply hKcap_ne
          exact Set.Finite.eq_of_subset_of_card_le
            (Set.toFinite ({z : G | z ∈ C ∧ z ∈ (Q : Subgroup G)} : Set G)) hle
            (by rw [hcard_CP_eq_CQ])
        rcases Set.not_subset_iff_exists_mem_notMem.mp hP_not_le_Q with
          ⟨u, huPset, hu_not_Qset⟩
        rcases huPset with ⟨huC, huP⟩
        have hu_not_Q : u ∉ (Q : Subgroup G) := by
          intro huQ
          exact hu_not_Qset ⟨huC, huQ⟩
        have hQ_not_le_P :
            ¬ {z : G | z ∈ C ∧ z ∈ (Q : Subgroup G)} ⊆
              {z : G | z ∈ C ∧ z ∈ (P : Subgroup G)} := by
          intro hle
          apply hKcap_ne.symm
          exact Set.Finite.eq_of_subset_of_card_le
            (Set.toFinite ({z : G | z ∈ C ∧ z ∈ (P : Subgroup G)} : Set G)) hle
            (by rw [hcard_CP_eq_CQ])
        rcases Set.not_subset_iff_exists_mem_notMem.mp hQ_not_le_P with
          ⟨v, hvQset, hv_not_Pset⟩
        rcases hvQset with ⟨hvC, hvQ⟩
        have hv_not_P : v ∉ (P : Subgroup G) := by
          intro hvP
          exact hv_not_Pset ⟨hvC, hvP⟩
        let S : Set G := {z : G | z ∈ C ∧ z ∈ (P : Subgroup G) ∧ z ∈ (Q : Subgroup G)}
        let D : Subgroup G := Subgroup.closure S
        have hS_C : S ⊆ C := by
          intro z hz
          exact hz.1
        have hS_P : S ⊆ (P : Set G) := by
          intro z hz
          exact hz.2.1
        have hS_Q : S ⊆ (Q : Set G) := by
          intro z hz
          exact hz.2.2
        have hD_le_P : D ≤ (P : Subgroup G) := by
          dsimp [D]
          exact (Subgroup.closure_le (K := (P : Subgroup G))).2 hS_P
        have hD_le_Q : D ≤ (Q : Subgroup G) := by
          dsimp [D]
          exact (Subgroup.closure_le (K := (Q : Subgroup G))).2 hS_Q
        rcases exists_conjClass_mem_normalizer_closure_inter
            (p := p) (C := C) (S := S) (D := D) rfl hC_conj P Q
            hS_C hS_P hD_le_Q huC huP hu_not_Q with
          ⟨a, haC, haP, ha_not_D, ha_norm⟩
        rcases exists_conjClass_mem_normalizer_closure_inter
            (p := p) (C := C) (S := S) (D := D) rfl hC_conj Q P
            hS_C hS_Q hD_le_P hvC hvQ hv_not_P with
          ⟨b, hbC, hbQ, hb_not_D, hb_norm⟩
        have hpair_C :
            ∀ a : G, a ∈ C → ∀ b : G, b ∈ C →
              IsPGroup p (Subgroup.closure ({a, b} : Set G)) := by
          intro a ha b hb
          rcases ha with ⟨ga, hga⟩
          let y : G := ga⁻¹ * b * ga
          have hyC : ∃ g : G, y = g * x * g⁻¹ := by
            rcases hb with ⟨gb, hgb⟩
            refine ⟨ga⁻¹ * gb, ?_⟩
            simp [y, hgb, mul_assoc]
          have hxy_p : IsPGroup p (Subgroup.closure ({x, y} : Set G)) := hpair y hyC
          let c : G ≃* G := MulAut.conj ga
          have hmap_p : IsPGroup p ((Subgroup.closure ({x, y} : Set G)).map (c : G →* G)) :=
            IsPGroup.map (p := p) (H := Subgroup.closure ({x, y} : Set G)) hxy_p (c : G →* G)
          have hmap_eq :
              (Subgroup.closure ({x, y} : Set G)).map (c : G →* G) =
                Subgroup.closure ({a, b} : Set G) := by
            rw [MonoidHom.map_closure]
            congr 1
            ext z
            constructor
            · rintro ⟨w, hw, rfl⟩
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
              rcases hw with rfl | rfl
              · left
                simpa [c] using hga.symm
              · right
                simp [c, y, mul_assoc]
            · intro hz
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
              rcases hz with rfl | rfl
              · refine ⟨x, by simp, ?_⟩
                simpa [c] using hga.symm
              · refine ⟨y, by simp, ?_⟩
                simp [c, y, mul_assoc]
          rw [hmap_eq] at hmap_p
          exact hmap_p
        have hab_p : IsPGroup p (Subgroup.closure ({a, b} : Set G)) :=
          hpair_C a haC b hbC
        have hD_p : IsPGroup p D := IsPGroup.to_le P.isPGroup' hD_le_P
        have hab_le_norm :
            Subgroup.closure ({a, b} : Set G) ≤ Subgroup.normalizer (D : Set G) := by
          refine (Subgroup.closure_le (K := Subgroup.normalizer (D : Set G))).2 ?_
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl
          · exact ha_norm
          · exact hb_norm
        let J : Subgroup G := D ⊔ Subgroup.closure ({a, b} : Set G)
        have hjoin_p : IsPGroup p J := by
          dsimp [J]
          exact IsPGroup.to_sup_of_normal_left'
            (G := G) (p := p) (H := D) (K := Subgroup.closure ({a, b} : Set G))
            hD_p hab_p hab_le_norm
        rcases IsPGroup.exists_le_sylow (p := p) (P := J) hjoin_p with
          ⟨R, hRle⟩
        have hD_le_R : D ≤ (R : Subgroup G) :=
          le_trans (show D ≤ J from by dsimp [J]; exact le_sup_left) hRle
        have hab_le_R : Subgroup.closure ({a, b} : Set G) ≤ (R : Subgroup G) :=
          le_trans (show Subgroup.closure ({a, b} : Set G) ≤ J from by
            dsimp [J]
            exact le_sup_right) hRle
        have haR : a ∈ (R : Subgroup G) :=
          hab_le_R (Subgroup.subset_closure (by simp))
        have hbR : b ∈ (R : Subgroup G) :=
          hab_le_R (Subgroup.subset_closure (by simp))
        have hcard_RP_gt :
            Nat.card ({z : G | z ∈ C ∧ z ∈ (P : Subgroup G) ∧ z ∈ (Q : Subgroup G)} : Set G) <
              Nat.card ({z : G | z ∈ C ∧ z ∈ (R : Subgroup G) ∧ z ∈ (P : Subgroup G)} : Set G) := by
          refine Set.Finite.card_lt_card
            (Set.toFinite ({z : G | z ∈ C ∧ z ∈ (R : Subgroup G) ∧ z ∈ (P : Subgroup G)} : Set G)) ?_
          refine ⟨?_, ?_⟩
          · intro z hz
            exact ⟨hz.1, hD_le_R (Subgroup.subset_closure (by simpa [S] using hz)), hz.2.1⟩
          · intro hsub
            have haS : a ∈ S := by
              simpa [S] using hsub ⟨haC, haR, haP⟩
            exact ha_not_D (Subgroup.subset_closure haS)
        have hR_eq_P : R = P := by
          by_contra hne
          have hbad_RP :
              (R, P) ∈
                ({r : Sylow p G × Sylow p G |
                    {z : G | z ∈ C ∧ z ∈ (r.1 : Subgroup G)} ≠
                      {z : G | z ∈ C ∧ z ∈ (r.2 : Subgroup G)}} :
                    Set (Sylow p G × Sylow p G)) := by
            intro hsets
            have hbP' : b ∈ (P : Subgroup G) := by
              have hbPset : b ∈ {z : G | z ∈ C ∧ z ∈ (P : Subgroup G)} := by
                simpa [hsets] using
                  (show b ∈ {z : G | z ∈ C ∧ z ∈ (R : Subgroup G)} from ⟨hbC, hbR⟩)
              exact hbPset.2
            exact hb_not_D
              (Subgroup.subset_closure (by simpa [S] using ⟨⟨hbC, hbP'⟩, ⟨hbC, hbQ⟩⟩))
          have hmax := hrmax (R, P) hbad_RP
          exact (not_lt_of_ge hmax) hcard_RP_gt
        have hcard_RQ_gt :
            Nat.card ({z : G | z ∈ C ∧ z ∈ (P : Subgroup G) ∧ z ∈ (Q : Subgroup G)} : Set G) <
              Nat.card ({z : G | z ∈ C ∧ z ∈ (R : Subgroup G) ∧ z ∈ (Q : Subgroup G)} : Set G) := by
          refine Set.Finite.card_lt_card
            (Set.toFinite ({z : G | z ∈ C ∧ z ∈ (R : Subgroup G) ∧ z ∈ (Q : Subgroup G)} : Set G)) ?_
          refine ⟨?_, ?_⟩
          · intro z hz
            exact ⟨hz.1, hD_le_R (Subgroup.subset_closure (by simpa [S] using hz)), hz.2.2⟩
          · intro hsub
            have hbS : b ∈ S := by
              simpa [S] using hsub ⟨hbC, hbR, hbQ⟩
            exact hb_not_D (Subgroup.subset_closure hbS)
        have hR_eq_Q : R = Q := by
          by_contra hne
          have hbad_RQ :
              (R, Q) ∈
                ({r : Sylow p G × Sylow p G |
                    {z : G | z ∈ C ∧ z ∈ (r.1 : Subgroup G)} ≠
                      {z : G | z ∈ C ∧ z ∈ (r.2 : Subgroup G)}} :
                    Set (Sylow p G × Sylow p G)) := by
            intro hsets
            have haQ' : a ∈ (Q : Subgroup G) := by
              have haQset : a ∈ {z : G | z ∈ C ∧ z ∈ (Q : Subgroup G)} := by
                simpa [hsets] using
                  (show a ∈ {z : G | z ∈ C ∧ z ∈ (R : Subgroup G)} from ⟨haC, haR⟩)
              exact haQset.2
            exact ha_not_D
              (Subgroup.subset_closure (by simpa [S] using ⟨⟨haC, haP⟩, ⟨haC, haQ'⟩⟩))
          have hmax := hrmax (R, Q) hbad_RQ
          exact (not_lt_of_ge hmax) hcard_RQ_gt
        have hPQ : P = Q := by
          rw [← hR_eq_P, hR_eq_Q]
        exact False.elim (hKcap_ne (by rw [hPQ]))
    · let H : Subgroup G := pCore p G
      let q : G →* G ⧸ H := QuotientGroup.mk' H
      have : Finite (G ⧸ H) := inferInstance
      have hH_ne_bot : H ≠ ⊥ := by
        simpa [H] using hcore
      have hcard_lt : Nat.card (G ⧸ H) < n := by
        rw [← hcard]
        exact natCard_quotient_lt_natCard_of_ne_bot H hH_ne_bot
      have hH_p : IsPGroup p H := by
        dsimp [H]
        exact pCore_isPGroup (p := p) (G := G)
      have hxq_p : IsPElement (p := p) (q x) := by
        rcases hx_p with ⟨k, hk⟩
        have hdiv : orderOf (q x) ∣ p ^ k := by
          exact dvd_trans (orderOf_map_dvd (ψ := q) x) (by simp [hk])
        rcases (Nat.dvd_prime_pow (Fact.out : Nat.Prime p)).1 hdiv with ⟨m, _hmle, hm⟩
        exact ⟨m, hm⟩
      have hpair_q :
          ∀ y : G ⧸ H, (∃ g : G ⧸ H, y = g * q x * g⁻¹) →
            IsPGroup p (Subgroup.closure ({q x, y} : Set (G ⧸ H))) := by
        intro y hy
        rcases hy with ⟨gbar, rfl⟩
        rcases QuotientGroup.mk'_surjective H gbar with ⟨g, rfl⟩
        let y : G := g * x * g⁻¹
        have hy_conj : ∃ g : G, y = g * x * g⁻¹ := ⟨g, rfl⟩
        have hy_pgroup : IsPGroup p (Subgroup.closure ({x, y} : Set G)) := hpair y hy_conj
        have hmap_p : IsPGroup p ((Subgroup.closure ({x, y} : Set G)).map q) :=
          IsPGroup.map (p := p) (H := Subgroup.closure ({x, y} : Set G)) hy_pgroup q
        have hmap_eq :
            (Subgroup.closure ({x, y} : Set G)).map q =
              Subgroup.closure ({q x, q y} : Set (G ⧸ H)) := by
          rw [MonoidHom.map_closure]
          congr 1
          ext z
          constructor
          · rintro ⟨w, hw, rfl⟩
            simp at hw
            rcases hw with rfl | rfl <;> simp
          · intro hz
            simp at hz
            rcases hz with rfl | rfl
            · exact ⟨x, by simp, rfl⟩
            · exact ⟨y, by simp, rfl⟩
        have : IsPGroup p (Subgroup.closure ({q x, q y} : Set (G ⧸ H))) := by
          rw [← hmap_eq]
          exact hmap_p
        exact this
      have hxq_core : q x ∈ pCore p (G ⧸ H) := by
        exact ih (Nat.card (G ⧸ H)) hcard_lt (G := G ⧸ H) rfl hxq_p hpair_q
      have hmap :
          H.map q = pCore p (G ⧸ H) := by
        simpa [H, q] using
          pCore_map_mk'_eq_of_normal_isPGroup (G := G) (p := p) H hH_p
      have hquot_core_bot : pCore p (G ⧸ H) = ⊥ := by
        calc
          pCore p (G ⧸ H) = H.map q := hmap.symm
          _ = ⊥ := by
            simp [q]
      have hxq_one : q x = 1 := by
        have : q x ∈ (⊥ : Subgroup (G ⧸ H)) := by
          simpa [hquot_core_bot] using hxq_core
        simpa using this
      have hxH : x ∈ H := (QuotientGroup.eq_one_iff (N := H) (x := x)).1 hxq_one
      simpa [H] using hxH
  exact Pmain hx_p hpair

end BenderSuzuki

namespace Subgroup

public theorem mem_pCore_of_conjugate_pairs_isPGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (a : G) (ha : IsPGroup p (Subgroup.zpowers a))
    (hall : ∀ g : G, IsPGroup p (Subgroup.closure ({a, g * a * g⁻¹} : Set G))) :
    a ∈ pCore p G := by
  have ha_p : IsPElement (p := p) a := by
    rcases IsPGroup.iff_card.mp ha with ⟨n, hn⟩
    rw [Nat.card_zpowers] at hn
    exact ⟨n, hn⟩
  have hclass := BenderSuzuki.gorenstein_3_8_2_conjugacy_class_le_pCore ha_p
      (by rintro y ⟨g, rfl⟩; exact hall g) a ⟨1, by simp⟩
  exact hclass

end Subgroup
