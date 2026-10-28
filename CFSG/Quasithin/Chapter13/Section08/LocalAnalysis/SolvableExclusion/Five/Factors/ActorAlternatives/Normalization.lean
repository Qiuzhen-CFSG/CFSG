module

public import CFSG.Quasithin.ChapterD.Section02.SmallSupportDecomposition.Rigidity
public import Theory.GroupAction.Quadratic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.ActorAlternatives.Reindex
public import Mathlib.Tactic

/-!
# Normalizing the five-factors before the actor alternatives

The supplied cyclic five-factors generate a normal abelian subgroup of H/O₂(H).
Their actual supports have order sixteen. The checked small-support rigidity
lemma identifies every conjugate factor with a supplied factor: an additional
factor inside their join would fix its own support, contradicting faithfulness.
Thus the ambient group permutes the one or two factors.

If a quadratic actor swaps the two disjoint supports, every actor preserving
both supports fixes them pointwise. Coprime splitting makes each five-factor
faithful on its own support. Consequently an actor normalizing a factor and
fixing its support centralizes that factor. Joint faithfulness on P* now makes
each support-preserving actor trivial, even if the action has a P*-fixed
complement. There are at most two actors. But the swapped support injects into
the quotient by the common fixed subgroup, giving index at least sixteen,
contrary to the quadratic offender bound of four.

This is a conditional algebraic prerequisite: the source assembly supplies the
faithful star action, factorization, joint faithfulness, and quadratic offender
conditions. It derives factor normalization without either actor alternative.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed p.951 / PDF p.968. The quadratic offender convention is D.2.1,
printed p.178. The support argument follows the elementary calculation in
`Theory.GroupAction.QuadraticComplementPair`, with joint faithfulness on P*
replacing faithfulness on the sum of the supports.
-/

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.ActorAlternatives.Normalization
variable {K W : Type*} [Group K] [Finite K] [Group W] [Finite W]
  [IsElementaryAbelian 2 W] [MulDistribMulAction K W] [FaithfulSMul K W]

/-- A normalizing actor fixing the support centralizes the coprime factor.
The commutator lies in the factor, so its own support faithfulness suffices. -/
private theorem centralizes_of_fixes_support (Q : Subgroup K)
    (hcop : Nat.Coprime (Nat.card Q) (Nat.card W)) (b : K)
    (hn : b ∈ normalizer (Q : Set K))
    (hf : ∀ w ∈ commutatorAction Q W, b • w = w) :
    b ∈ centralizer (Q : Set K) := by
  intro q hq
  have hq' : b * q * b⁻¹ * q⁻¹ ∈ Q :=
    Q.mul_mem ((mem_normalizer_iff.mp hn q).mp hq) (Q.inv_mem hq)
  have he : b * q * b⁻¹ * q⁻¹ = 1 := by
    apply ActionSupport.eq_one_of_fixes_support Q hcop ⟨_, hq'⟩
    intro w hw
    let _ : IsInvariant Q W (commutatorAction Q W) := commutatorAction_isInvariant
    have hqi : q⁻¹ • w ∈ commutatorAction Q W :=
      (IsInvariant.invariant (⟨q⁻¹, Q.inv_mem hq⟩ : Q) w).mp hw
    have hbi : b⁻¹ • (q⁻¹ • w) = q⁻¹ • w := by
      exact inv_smul_eq_iff.mpr (hf _ hqi).symm
    change (b * q * b⁻¹ * q⁻¹) • w = w
    rw [mul_smul, mul_smul, mul_smul, hbi, smul_inv_smul, hf w hw]
  have he' : b * q = q * b := by
    have := mul_inv_eq_one.mp he
    exact mul_inv_eq_iff_eq_mul.mp this
  exact he'.symm

/-- Local small-support rigidity detects the supplied factors inside their
normal abelian join; no stability of the supplied family is assumed. -/
private theorem permutes_factors {n : ℕ} (Q : Fin n → Subgroup K)
    (P : Subgroup K) [P.Normal] (hgen : P = ⨆ i, Q i)
    (hcomm : P ≤ centralizer (P : Set K))
    (hQ : ∀ i, Q i ∈ CFSG.Quasithin.ChapterD.smallSupportFactors K W 2)
    (g : K) (i : Fin n) : ∃ j, (Q i).conjBy g = Q j := by
  classical
  let X := (Q i).conjBy g
  have hX := CFSG.Quasithin.ChapterD.smallSupportFactors_conjBy (hQ i) g
  have hXP : X ≤ P := by
    rintro x ⟨q, hq, rfl⟩
    exact (inferInstance : P.Normal).conj_mem q (hgen ▸ le_iSup Q i hq) g
  by_contra! hne
  have hfix : P ≤ fixingSubgroup K (commutatorAction X W : Set W) := by
    rw [hgen]
    apply iSup_le
    intro j q hq
    rw [mem_fixingSubgroup_iff]
    intro w hw
    have hjP : Q j ≤ P := hgen ▸ le_iSup Q j
    have hc : Q j ≤ centralizer (X : Set K) :=
      hjP.trans (hcomm.trans (centralizer_le hXP))
    exact CFSG.Quasithin.ChapterD.smallSupportFactors_cross_fixed_of_commuting
      (Or.inr rfl) (hQ j) hX (hne j).symm hc hw ⟨q, hq⟩
  have hbot : X = ⊥ := by
    apply bot_unique
    intro x hx
    exact ActionSupport.eq_one_of_fixes_support X
      (CFSG.Quasithin.ChapterD.smallSupportFactor_coprime (Or.inr rfl) hX)
      ⟨x, hx⟩ ((mem_fixingSubgroup_iff (M := K)).mp (hfix (hXP hx)))
  have hc := hX.2.1
  change Nat.card X = 5 at hc
  rw [hbot, card_bot] at hc
  omega

/-- A swapped pair forces an actor of order at most two and fixed index at
least sixteen, contradicting the offender bound. -/
private theorem quadratic_pair_normalized (A B E : Subgroup K)
    [IsElementaryAbelian 2 E]
    (hcopA : Nat.Coprime (Nat.card A) (Nat.card W))
    (hcopB : Nat.Coprime (Nat.card B) (Nat.card W))
    (hd : Disjoint (commutatorAction A W) (commutatorAction B W))
    (hcard : Nat.card (commutatorAction A W) = 16)
    (hfaith : E ⊓ centralizer ((A ⊔ B : Subgroup K) : Set K) = ⊥)
    (hquad : commutatorAction₂ E W = ⊥)
    (hindex : (FixedPoints.subgroup E W).index ≤ (Nat.card E)^2)
    (hperm : ∀ b ∈ E,
      ((A.conjBy b = A) ∧ (B.conjBy b = B)) ∨
      ((A.conjBy b = B) ∧ (B.conjBy b = A))) :
    E ≤ normalizer (A : Set K) ∧ E ≤ normalizer (B : Set K) := by
  classical
  have hstable : ∀ b ∈ E, A.conjBy b = A ∧ B.conjBy b = B := by
    intro c hc
    rcases hperm c hc with hs | hswap
    · exact hs
    exfalso
    have hsA : ∀ w ∈ commutatorAction A W, c • w ∈ commutatorAction B W := by
      intro w hw
      rw [← hswap.1, ← ActionSupport.commutatorAction_conjBy]
      exact mem_map_of_mem _ hw
    have hsB : ∀ w ∈ commutatorAction B W, c • w ∈ commutatorAction A W := by
      intro w hw
      rw [← hswap.2, ← ActionSupport.commutatorAction_conjBy]
      exact mem_map_of_mem _ hw
    have hfixed := commutatorAction_le_fixedPoints_of_commutatorAction₂_eq_bot hquad
    have stable_trivial (b : E) (hbA : A.conjBy (b : K) = A)
        (hbB : B.conjBy (b : K) = B) : b = 1 := by
      have fixes (Q R : Subgroup K) (hdis : Disjoint (commutatorAction Q W) (commutatorAction R W))
          (hn : Q.conjBy (b : K) = Q)
          (hs : ∀ w ∈ commutatorAction Q W, c • w ∈ commutatorAction R W) :
          ∀ w ∈ commutatorAction Q W, (b : K) • w = w := by
        intro w hw
        have hbw : (b : K) • w ∈ commutatorAction Q W := by
          rw [← hn, ← ActionSupport.commutatorAction_conjBy]
          exact mem_map_of_mem _ hw
        have hdelta : w⁻¹ * ((b : K) • w) ∈ commutatorAction Q W :=
          (commutatorAction Q W).mul_mem ((commutatorAction Q W).inv_mem hw) hbw
        have hdeltaE : w⁻¹ * ((b : K) • w) ∈ commutatorAction E W :=
          subset_closure ⟨b, w, mem_top w, rfl⟩
        have hcf : c • (w⁻¹ * ((b : K) • w)) = w⁻¹ * ((b : K) • w) :=
          hfixed hdeltaE ⟨c, hc⟩
        have hone : w⁻¹ * ((b : K) • w) = 1 :=
          hdis.le_bot ⟨hdelta, hcf ▸ hs _ hdelta⟩
        exact (inv_mul_eq_one.mp hone).symm
      have hbcentA := centralizes_of_fixes_support (W := W) A hcopA (b : K)
        (mem_normalizer_iff_map_conj_eq.mpr hbA) (fixes A B hd hbA hsA)
      have hbcentB := centralizes_of_fixes_support (W := W) B hcopB (b : K)
        (mem_normalizer_iff_map_conj_eq.mpr hbB) (fixes B A hd.symm hbB hsB)
      apply Subtype.ext
      have hbcent : (b : K) ∈ centralizer ((A ⊔ B : Subgroup K) : Set K) := by
        have hle : A ⊔ B ≤ centralizer ({(b : K)} : Set K) := by
          apply sup_le
          · intro q hq
            exact mem_centralizer_singleton_iff.mpr (hbcentA q hq)
          · intro q hq
            exact mem_centralizer_singleton_iff.mpr (hbcentB q hq)
        intro q hq
        exact (mem_centralizer_singleton_iff.mp (hle hq))
      exact hfaith.le ⟨b.property, hbcent⟩
    have hcover (b : E) : b = 1 ∨ b = ⟨c, hc⟩ := by
      rcases hperm b b.property with hs | ht
      · exact Or.inl (stable_trivial b hs.1 hs.2)
      · right
        have he : b * ⟨c, hc⟩ = 1 := by
          apply stable_trivial
          · rw [coe_mul, Subgroup.conjBy_mul, hswap.1, ht.2]
          · rw [coe_mul, Subgroup.conjBy_mul, hswap.2, ht.1]
        have hc2 : (⟨c, hc⟩ : E) * ⟨c, hc⟩ = 1 := by
          simpa only [pow_two] using
            (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
              (IsElementaryAbelian.exponent_dvd_p 2 E) ⟨c, hc⟩)
        exact mul_right_cancel (he.trans hc2.symm)
    have hE : Nat.card E ≤ 2 := by
      let f : E → Bool := fun b => decide (b = 1)
      have hf : Function.Injective f := by
        intro b d he
        have he' : b = 1 ↔ d = 1 := decide_eq_decide.mp he
        rcases hcover b with hb | hb
        · exact hb.trans (he'.mp hb).symm
        · rcases hcover d with hd | hd
          · exact (he'.mpr hd).trans hd.symm
          · exact hb.trans hd.symm
      simpa using Nat.card_le_card_of_injective f hf
    let F := FixedPoints.subgroup E W
    have hdis : Disjoint (commutatorAction A W) F := by
      apply disjoint_iff_inf_le.mpr
      intro w hw
      have hcw : c • w = w := hw.2 ⟨c, hc⟩
      exact hd.le_bot ⟨hw.1, hcw ▸ hsA w hw.1⟩
    let _ : F.Normal := normal_of_isMulCommutative F
    let q : commutatorAction A W →* W ⧸ F :=
      (QuotientGroup.mk' F).comp (commutatorAction A W).subtype
    have hq : Function.Injective q := by
      apply (injective_iff_map_eq_one q).mpr
      intro w hw
      apply Subtype.ext
      exact hdis.le_bot ⟨w.property, (QuotientGroup.eq_one_iff _).mp hw⟩
    have hbound : 16 ≤ F.index := by
      rw [← hcard]
      exact Nat.card_le_card_of_injective q hq
    have : (Nat.card E)^2 ≤ 4 := by nlinarith
    change 16 ≤ (FixedPoints.subgroup E W).index at hbound
    omega
  exact ⟨fun b hb => mem_normalizer_iff_map_conj_eq.mpr (hstable b hb).1,
    fun b hb => mem_normalizer_iff_map_conj_eq.mpr (hstable b hb).2⟩

private theorem normalizes_generated_five {n : ℕ} (hnpos : 0 < n) (hnle : n ≤ 2)
    (Q : Fin n → Subgroup K) (P E : Subgroup K) [P.Normal]
    [IsElementaryAbelian 2 E]
    (hgen : P = ⨆ i, Q i) (hcomm : P ≤ centralizer (P : Set K))
    (hQ : ∀ i, Q i ∈ CFSG.Quasithin.ChapterD.smallSupportFactors K W 2)
    (hd : ∀ i j, i ≠ j → Disjoint (commutatorAction (Q i) W) (commutatorAction (Q j) W))
    (hfaith : E ⊓ centralizer (P : Set K) = ⊥)
    (hquad : commutatorAction₂ E W = ⊥)
    (hindex : (FixedPoints.subgroup E W).index ≤ (Nat.card E)^2) :
    ∀ i, E ≤ normalizer (Q i : Set K) := by
  classical
  by_cases hone : n = 1
  · intro i
    have he : P = Q i := by
      rw [hgen]
      apply le_antisymm
      · apply iSup_le
        intro j
        have hji : j = i := Fin.ext (by have := j.isLt; have := i.isLt; omega)
        exact hji ▸ le_rfl
      · exact le_iSup Q i
    rw [← he]
    exact le_normalizer_of_normal
  have htwo : n = 2 := by omega
  let z : Fin n := ⟨0, hnpos⟩
  let j : Fin n := ⟨1, by omega⟩
  have hcases (i : Fin n) : i = z ∨ i = j := by
    have := i.isLt
    by_cases hi : i.val = 0
    · exact Or.inl (Fin.ext hi)
    · exact Or.inr (Fin.ext (by dsimp [j]; omega))
  have hzj : z ≠ j := by intro he; have := congrArg Fin.val he; change 0 = 1 at this; omega
  have hAB : Q z ≠ Q j := by
    intro he
    have hdis := hd z j hzj
    rw [he] at hdis
    have hb := disjoint_self.mp hdis
    have hc := (hQ j).2.2
    rw [hb, card_bot] at hc
    norm_num at hc
  have hsup : P = Q z ⊔ Q j := by
    rw [hgen]
    apply le_antisymm
    · apply iSup_le
      intro i
      rcases hcases i with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup Q z) (le_iSup Q j)
  have hperm (b : K) (_hb : b ∈ E) :
      ((Q z).conjBy b = Q z ∧ (Q j).conjBy b = Q j) ∨
      ((Q z).conjBy b = Q j ∧ (Q j).conjBy b = Q z) := by
    obtain ⟨u, hu⟩ := permutes_factors (W := W) Q P hgen hcomm hQ b z
    obtain ⟨v, hv⟩ := permutes_factors (W := W) Q P hgen hcomm hQ b j
    have hne : (Q z).conjBy b ≠ (Q j).conjBy b := by
      intro he
      exact hAB (Subgroup.map_injective (MulAut.conj b).injective he)
    rcases hcases u with rfl | rfl <;> rcases hcases v with rfl | rfl
    · exact (hne (hu.trans hv.symm)).elim
    · exact Or.inl ⟨hu, hv⟩
    · exact Or.inr ⟨hu, hv⟩
    · exact (hne (hu.trans hv.symm)).elim
  have hnorm := quadratic_pair_normalized (W := W) (Q z) (Q j) E
    (CFSG.Quasithin.ChapterD.smallSupportFactor_coprime (Or.inr rfl) (hQ z))
    (CFSG.Quasithin.ChapterD.smallSupportFactor_coprime (Or.inr rfl) (hQ j))
    (hd z j hzj) (by simpa using (hQ z).2.2)
    (by simpa only [← hsup] using hfaith) hquad hindex hperm
  intro i
  rcases hcases i with rfl | rfl
  · exact hnorm.1
  · exact hnorm.2
end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.ActorAlternatives.Normalization

namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five

private theorem commutatorSubgroup_image {K W : Type*} [Group K] [Group W]
    (ρ : K →* MulAut W) (Q : Subgroup K) (S : Subgroup W) :
    let _ := MulDistribMulAction.compHom W ρ
    commutatorSubgroup (Q.map ρ) W S = commutatorSubgroup Q W S := by
  let _ := MulDistribMulAction.compHom W ρ
  unfold commutatorSubgroup
  congr 1
  ext x
  constructor
  · rintro ⟨b, w, hw, rfl⟩
    obtain ⟨q, hq, he⟩ := b.property
    refine ⟨⟨q, hq⟩, w, hw, ?_⟩
    change w⁻¹ * (b : MulAut W) w = w⁻¹ * ρ q w
    rw [he]
  · rintro ⟨q, w, hw, rfl⟩
    exact ⟨⟨ρ q, mem_map_of_mem ρ q.property⟩, w, hw, rfl⟩

private theorem fixedPoints_image {K W : Type*} [Group K] [Group W]
    (ρ : K →* MulAut W) (Q : Subgroup K) :
    let _ := MulDistribMulAction.compHom W ρ
    FixedPoints.subgroup (Q.map ρ) W = FixedPoints.subgroup Q W := by
  let _ := MulDistribMulAction.compHom W ρ
  ext w
  constructor
  · intro hw q
    exact hw ⟨ρ q, mem_map_of_mem ρ q.property⟩
  · intro hw b
    obtain ⟨q, hq, he⟩ := b.property
    change (b : MulAut W) w = w
    rw [← he]
    exact hw ⟨q, hq⟩

variable {G : Type*} [Group G] [Finite G]
variable {H UH V₁ : Subgroup G} [(V₁.subgroupOf UH).Normal]
  [IsElementaryAbelian 2 (UH ⧸ V₁.subgroupOf UH)]

/-- The quadratic offender conditions force normalization of every supplied
five-factor. No actor order, permutation stability or normalization is assumed. -/
public theorem Factorization.star_normalizes_of_quadratic_offender
    (a : StarAction H UH V₁) (ha : Function.Injective a.action)
    {P : Subgroup G} (f : Factorization a P) (hPH : P ≤ H)
    (hPn : (Source.starImage H P).Normal)
    (E : Subgroup (Source.Hstar H)) [IsElementaryAbelian 2 E] (_hne : E ≠ ⊥)
    (hfaith : E ⊓ centralizer (Source.starImage H P : Set _) = ⊥)
    (hquad : commutatorAction₂ (E.map a.action) (UH ⧸ V₁.subgroupOf UH) = ⊥)
    (hindex : (FixedPoints.subgroup (E.map a.action) (UH ⧸ V₁.subgroupOf UH)).index ≤
      (Nat.card E)^2) :
    ∀ i : Fin f.count, E ≤ normalizer (Source.starImage H (f.factor i) : Set _) := by
  let W := UH ⧸ V₁.subgroupOf UH
  let K := Source.Hstar H
  let : MulDistribMulAction K W := MulDistribMulAction.compHom W a.action
  let : FaithfulSMul K W := ⟨fun {b c} h => ha (MulEquiv.ext h)⟩
  let Q : Fin f.count → Subgroup K := fun i => Source.starImage H (f.factor i)
  let R : Subgroup K := Source.starImage H P
  let : R.Normal := hPn
  have hgen : R = ⨆ i, Q i := f.star_generated hPH
  have hcomm (i j : Fin f.count) : ⁅Q i, Q j⁆ = ⊥ := by
    by_cases hij : i = j
    · subst j
      let : Fact (Nat.Prime 5) := ⟨by decide⟩
      let : IsCyclic (Q i) := isCyclic_of_prime_card (f.star_card i)
      exact commutator_self_eq_bot_iff.mpr inferInstance
    · have hsub : ⁅(f.factor i).subgroupOf H, (f.factor j).subgroupOf H⁆ = ⊥ := by
        apply Subgroup.map_injective H.subtype_injective
        rw [map_commutator, map_subgroupOf_eq_of_le ((f.factor_le i).trans hPH),
          map_subgroupOf_eq_of_le ((f.factor_le j).trans hPH), f.commute i j hij,
          Subgroup.map_bot]
      change ⁅((f.factor i).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)),
        ((f.factor j).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))⁆ = ⊥
      rw [← map_commutator, hsub, Subgroup.map_bot]
  have hRc : R ≤ centralizer (R : Set K) := by
    rw [hgen]
    apply iSup_le
    intro i
    apply le_centralizer_iff.mpr
    apply iSup_le
    intro j
    exact commutator_eq_bot_iff_le_centralizer.mp (hcomm j i)
  let : IsMulCommutative R := le_centralizer_iff_isMulCommutative.mp hRc
  have hfit : R ≤ fittingSubgroup K := le_sSup ⟨inferInstance, inferInstance⟩
  have hs (i : Fin f.count) : commutatorAction (Q i) W = f.support i :=
    (commutatorSubgroup_image a.action (Q i) ⊤).symm
  have hQ (i : Fin f.count) : Q i ∈ CFSG.Quasithin.ChapterD.smallSupportFactors K W 2 := by
    refine ⟨(hgen ▸ le_iSup Q i).trans hfit, f.star_card i, ?_⟩
    rw [hs i]
    exact f.support_card i
  have hquad' : commutatorAction₂ E W = ⊥ := by
    change commutatorSubgroup (E.map a.action) W
      (commutatorSubgroup (E.map a.action) W ⊤) = ⊥ at hquad
    rw [commutatorSubgroup_image, commutatorSubgroup_image] at hquad
    exact hquad
  have hindex' : (FixedPoints.subgroup E W).index ≤ (Nat.card E)^2 := by
    rw [fixedPoints_image] at hindex
    exact hindex
  exact ActorAlternatives.Normalization.normalizes_generated_five f.count_pos f.count_le_two
    Q R E hgen hRc hQ (fun i j hij => by rw [hs i, hs j]; exact f.support_disjoint i j hij)
    hfaith hquad' hindex'
end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
