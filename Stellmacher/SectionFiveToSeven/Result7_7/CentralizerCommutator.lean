module

public import Stellmacher.SectionFiveToSeven.Result7_6
public import Theory.GroupTheory.PGroup.SubnormalCore

/-!
# Stellmacher (7.7)(a): centralizer commutators

Suppose the next residual is subnormal in the centralizer of `Ω₁(Z(S))`
and that this centralizer's 2-core lies in `S`. Then the centralizer of
the initial vertex center commutes with `E_a O₂(E_{a+1})` modulo `Q_a`.

Subnormal monotonicity puts `O₂(E_{a+1})` in `O₂(C)`. Its commutators
with `C_G(Z_a)` lie in both `O₂(C) ≤ S` and `C_G(Z_a)`, so (7.4)
puts them in `Q_a`. The initial stabilizer normalizes both `C_G(Z_a)`
and `Q_a`; conjugate-closure induction therefore propagates this bound
to all local conjugates of `O₂(E_{a+1})`. Their join contains `E_a`
by (7.6)(b), giving the desired conclusion.

Source: B. Stellmacher, Journal of Algebra 190 (1997), (7.7)(a), p.36;
`refs/latex/stellmacher-n-group.tex`.
-/

open scoped Pointwise commutatorElement

namespace Stellmacher.SectionsFiveToSeven

open CosetGraphContext SevenSix

universe u v

private theorem omega_sylow_le_z
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    (d : Gamma.Vertex) (hS : IsSylowTwoIn S (stabilizer Gamma d)) :
    omegaOneCenter S ≤ z Gamma d := by
  obtain ⟨_, T, hT⟩ := hS
  rw [z, Gamma.zAt_def]
  apply le_sSup
  exact ⟨T, congrArg omegaOneCenter hT.symm⟩

private theorem centralizer_commutator_next_core
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (C : Subgroup G)
    (hC : C = Subgroup.centralizer (omegaOneCenter S : Set G))
    (hcore : twoCoreIn C ≤ S)
    (hRcore : twoCoreIn (e Gamma cp.firstStep) ≤ twoCoreIn C) :
    ⁅Subgroup.centralizer (z Gamma cp.a : Set G),
      twoCoreIn (e Gamma cp.firstStep)⁆ ≤ q Gamma cp.a := by
  let D := Subgroup.centralizer (z Gamma cp.a : Set G)
  let R := twoCoreIn (e Gamma cp.firstStep)
  have hOmegaZa : omegaOneCenter S ≤ z Gamma cp.a :=
    omega_sylow_le_z Gamma cp.a (edge_sylow_data h Gamma cp).1
  have hDC : D ≤ C := by
    rw [hC]
    exact Subgroup.centralizer_le hOmegaZa
  have hRleS : R ≤ S := hRcore.trans hcore
  have hCnormCore : C ≤ Subgroup.normalizer (twoCoreIn C) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (twoCoreIn_le C)).mp
      (twoCoreIn_normal C)
  have hDRcore : ⁅D, R⁆ ≤ twoCoreIn C :=
    (Subgroup.commutator_mono le_rfl hRcore).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp
        (hDC.trans hCnormCore))
  have hGaNormZ := stabilizer_le_normalizer_z Gamma cp.a
  have hRNormZ : R ≤ Subgroup.normalizer (z Gamma cp.a : Set G) :=
    hRleS.trans ((edge_sylow_data h Gamma cp).1.1.trans hGaNormZ)
  have hNormZNormD : Subgroup.normalizer (z Gamma cp.a : Set G) ≤
      Subgroup.normalizer D :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (z Gamma cp.a : Set G))).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  have hDRD : ⁅D, R⁆ ≤ D :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hRNormZ.trans hNormZNormD)
  rw [← (lemma_seven_four h Gamma cp).edge_centralizer]
  exact le_inf (hDRcore.trans hcore) hDRD

private theorem commutator_conjugateClosure_le
    {G : Type u} [Group G] (D R P Q : Subgroup G)
    (hRP : R ≤ P) (hPD : P ≤ Subgroup.normalizer D)
    (hPQ : P ≤ Subgroup.normalizer Q) (hDR : ⁅D, R⁆ ≤ Q) :
    ⁅D, conjugateClosure R P⁆ ≤ Q := by
  have hconjQ : ∀ p ∈ P, ∀ q ∈ Q, p * q * p⁻¹ ∈ Q :=
    (Subgroup.le_normalizer_iff.mp hPQ)
  have hconjD : ∀ p ∈ P, ∀ d ∈ D, p * d * p⁻¹ ∈ D :=
    (Subgroup.le_normalizer_iff.mp hPD)
  have hprop : ∀ x ∈ conjugateClosure R P,
      x ∈ P ∧ ∀ d ∈ D, ⁅d, x⁆ ∈ Q := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨p, r, rfl⟩ := hx
      refine ⟨P.mul_mem (P.mul_mem p.2 (hRP r.2)) (P.inv_mem p.2), ?_⟩
      intro d hd
      have hc : ⁅(p : G)⁻¹ * d * (p : G), (r : G)⁆ ∈ Q :=
        hDR (Subgroup.commutator_mem_commutator
          (by simpa using hconjD (p : G)⁻¹ (P.inv_mem p.2) d hd) r.2)
      have heq : ⁅d, (p : G) * (r : G) * (p : G)⁻¹⁆ =
          (p : G) * ⁅(p : G)⁻¹ * d * (p : G), (r : G)⁆ * (p : G)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [heq]
      exact hconjQ (p : G) p.2 _ hc
    | one => simp
    | mul x y hx hy ihx ihy =>
      refine ⟨P.mul_mem ihx.1 ihy.1, ?_⟩
      intro d hd
      rw [commutatorElement_mul_right_eq_mul_conj]
      simpa only [mul_assoc] using
        Q.mul_mem (ihx.2 d hd) (hconjQ x ihx.1 _ (ihy.2 d hd))
    | inv x hx ih =>
      refine ⟨P.inv_mem ih.1, ?_⟩
      intro d hd
      rw [commutatorElement_inv_right, ← commutatorElement_inv]
      simpa using hconjQ x⁻¹ (P.inv_mem ih.1) _ (Q.inv_mem (ih.2 d hd))
  exact Subgroup.commutator_le.mpr fun d hd x hx => (hprop x hx).2 d hd

private theorem centralizer_commutator_all_of_core_le
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (C : Subgroup G)
    (hC : C = Subgroup.centralizer (omegaOneCenter S : Set G))
    (hcore : twoCoreIn C ≤ S)
    (hRcore : twoCoreIn (e Gamma cp.firstStep) ≤ twoCoreIn C) :
    ⁅Subgroup.centralizer (z Gamma cp.a : Set G),
      e Gamma cp.a ⊔ twoCoreIn (e Gamma cp.firstStep)⁆ ≤ q Gamma cp.a := by
  let D := Subgroup.centralizer (z Gamma cp.a : Set G)
  let R := twoCoreIn (e Gamma cp.firstStep)
  let P := stabilizer Gamma cp.a
  let Q := q Gamma cp.a
  have hDR : ⁅D, R⁆ ≤ Q := centralizer_commutator_next_core h Gamma cp C hC hcore hRcore
  have hRP : R ≤ P := hRcore.trans (hcore.trans (edge_sylow_data h Gamma cp).1.1)
  have hPD : P ≤ Subgroup.normalizer D :=
    (stabilizer_le_normalizer_z Gamma cp.a).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.centralizer_le_normalizer (z Gamma cp.a : Set G))).mp
          (Subgroup.normal_subgroupOf_centralizer_normalizer _))
  have hPQ : P ≤ Subgroup.normalizer Q := stabilizer_le_normalizer_q Gamma cp.a
  have hclosure := commutator_conjugateClosure_le D R P Q hRP hPD hPQ hDR
  have hRclosure : R ≤ conjugateClosure R P := by
    intro r hr
    exact Subgroup.subset_closure ⟨1, ⟨r, hr⟩, by simp⟩
  have hjoin : e Gamma cp.a ⊔ R ≤ conjugateClosure R P :=
    sup_le (lemma_seven_six h Gamma cp).next_residual_core.2 hRclosure
  exact (Subgroup.commutator_mono le_rfl hjoin).trans hclosure

/-- The first conclusion of Stellmacher (7.7). -/
public theorem lemma_seven_seven_centralizer_commutator
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (C : Subgroup G)
    (hC : C = Subgroup.centralizer (omegaOneCenter S : Set G))
    (hsubnormal : SubnormalIn (e Gamma cp.firstStep) C)
    (hcore : twoCoreIn C ≤ S) :
    ⁅Subgroup.centralizer (z Gamma cp.a : Set G),
      e Gamma cp.a ⊔ twoCoreIn (e Gamma cp.firstStep)⁆ ≤ q Gamma cp.a := by
  exact centralizer_commutator_all_of_core_le h Gamma cp C hC hcore
    (pCoreAmbient_mono_of_isSubnormalIn (e Gamma cp.firstStep) C 2
      hsubnormal.1 hsubnormal.2)

end Stellmacher.SectionsFiveToSeven

