module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentActionSource
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.Alternating.Aut
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic
public import Theory.GroupTheory.PResidual.Quotient

/-!
# The odd-permutation component rows cannot contain the original cubic actor

A two-perfect group acts on A₆ or A₇ through inner automorphisms because the
outer quotient is a two-group. The same holds after descent from a perfect
central cover. The odd-permutation markings in 1.1.5(c,d) contradict this
when the marked actor lies in the original first cubic block. The actual
source application retains both fixed involutions and literal conjugation.

Source: Aschbacher–Smith, the component inspection before 2.4.32, p.547.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.DoubleA3
open Chapter15.Section03.Candidates.ComponentStructure
open AlternatingSix.ShadowLocal

private theorem pPerfect_image_mem_of_pquotient
    {L A : Type*} [Group L] [Group A] (hL : IsPPerfect 2 L)
    (f : L →* A) (N : Subgroup A) [N.Normal] (hN : IsPGroup 2 (A ⧸ N))
    (l : L) : f l ∈ N := by
  have hh := pResidual_le_ker_of_isPGroup 2 ((QuotientGroup.mk' N).comp f) hN
  have hp := (pResidual_eq_top_iff 2 L).mpr hL
  exact (QuotientGroup.eq_one_iff (f l)).mp (hh (hp.symm ▸ mem_top l))

private theorem twoPerfect_a6_action_inner
    {L : Type*} [Group L] (hL : IsPPerfect 2 L) (f : L →* AutA6) (l : L) :
    f l ∈ (MulAut.conj : A6 →* AutA6).range := by
  have hp : IsPGroup 2 (AutA6 ⧸ AlternatingSix.ShadowLocal.inner) := IsPGroup.of_card (n := 2) (by
    rw [←AlternatingSix.ShadowLocal.inner.index_eq_card,inner_index]; decide)
  exact pPerfect_image_mem_of_pquotient hL f AlternatingSix.ShadowLocal.inner hp l

private theorem twoPerfect_a7_action_inner
    {L : Type*} [Group L] (hL : IsPPerfect 2 L)
    (f : L →* MulAut (alternatingGroup (Fin 7))) (l : L) :
    f l ∈ (MulAut.conj : alternatingGroup (Fin 7) →* _).range := by
  let e : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 7)))
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide))
  have hp : IsPGroup 2 (Equiv.Perm (Fin 7) ⧸ alternatingGroup (Fin 7)) :=
    IsPGroup.of_card (n := 1) (by rw [←index_eq_card,alternatingGroup.index_eq_two]; decide)
  have he : e.symm (f l) ∈ alternatingGroup (Fin 7) :=
    pPerfect_image_mem_of_pquotient hL (e.symm.toMonoidHom.comp f) _ hp l
  refine ⟨⟨e.symm (f l),he⟩,?_⟩
  rw [←MulAut.conjNormal_val]
  exact e.apply_symm_apply (f l)

private theorem odd_permutation_action_not_inner
    {n : ℕ} (hn : 4 ≤ n) (σ : Equiv.Perm (Fin n))
    (hs : Equiv.Perm.sign σ = -1)
    (a : MulAut (alternatingGroup (Fin n)))
    (ha : ∀ x : alternatingGroup (Fin n), (a x : Equiv.Perm (Fin n)) = σ*x*σ⁻¹) :
    a ∉ (MulAut.conj : alternatingGroup (Fin n) →* _).range := by
  rintro ⟨k,rfl⟩
  have he : MulAut.conjNormal (H := alternatingGroup (Fin n)) (k : Equiv.Perm (Fin n)) =
      MulAut.conjNormal (H := alternatingGroup (Fin n)) σ := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact ha x
  have hk := GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n hn he
  have hsign : Equiv.Perm.sign σ = 1 := hk ▸ k.property
  rw [hs] at hsign
  norm_num at hsign

/-- A two-perfect subgroup cannot contain the odd-permutation actor of
1.1.5(c,d), including the genuine triple-cover actions. -/
theorem alternating_action_excluded_by_twoPerfect_actor
    {L K : Type*} [Group L] [Group K] [Group.IsPerfect K]
    (hL : IsPPerfect 2 L) (f : L →* MulAut K) (l : L)
    (n : ℕ) (hn : n = 6 ∨ n = 7) (σ : Equiv.Perm (Fin n))
    (hs : Equiv.Perm.sign σ = -1) (ha : AlternatingAction (f l) n σ) : False := by
  have inner_image (b : L →* MulAut (alternatingGroup (Fin n))) :
      b l ∈ (MulAut.conj : alternatingGroup (Fin n) →* _).range := by
    rcases hn with rfl | rfl
    · exact twoPerfect_a6_action_inner hL b l
    · exact twoPerfect_a7_action_inner hL b l
  have hn4 : 4 ≤ n := by rcases hn with rfl | rfl <;> decide
  rcases ha with ⟨e,he⟩ | ⟨_,_,e,he⟩
  · let b := (MulAut.congr e).toMonoidHom.comp f
    apply odd_permutation_action_not_inner hn4 σ hs (b l) ?_ (inner_image b)
    intro x
    change (e (f l (e.symm x)) : Equiv.Perm (Fin n)) = _
    simpa only [e.apply_symm_apply] using he (e.symm x)
  · let b := (MulAut.centralQuotientAction e).comp f
    apply odd_permutation_action_not_inner hn4 σ hs (b l) ?_ (inner_image b)
    intro x
    obtain ⟨y,rfl⟩ := e.surjective x
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (center K) y
    rw [show b l = MulAut.centralQuotientAction e (f l) from rfl,
      MulAut.centralQuotientAction_apply]
    exact he k

variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}

/-- The original cubic block excludes both odd-permutation catalogue rows,
with their actual actions on the component or its central quotient. -/
theorem SourceCentralizerGeometry.alternating_component_action_false
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : Theory.GroupTheory.IsComponent (involutionCentralizer g.z₂) K)
    (α : MulAut K)
    (hα : ∀ k : K, ((α k : involutionCentralizer g.z₂) : G) =
      (g.z₁*g.z₂)*(k:G)*(g.z₁*g.z₂)⁻¹)
    (n : ℕ) (hn : n = 6 ∨ n = 7) (σ : Equiv.Perm (Fin n))
    (hs : Equiv.Perm.sign σ = -1) (ha : AlternatingAction α n σ) : False := by
  let H := involutionCentralizer g.z₂
  let L := d.block.map d.H.subtype
  let : Theory.GroupTheory.IsQuasisimple K := hK.2
  obtain ⟨f,_,hact⟩ := g.faithful_first_block_action hG h K hK
  have hz := g.first_mem
  change g.z₁ ∈ (ChapterC.blockU L).map L.subtype at hz
  obtain ⟨a,_,he⟩ := hz
  have hea : (a:G) = g.z₁ := he
  have hf : f a = α := by
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    apply Subtype.ext
    have hkc : g.z₂*(k:G)*g.z₂⁻¹ = (k:G) := by
      rw [←mem_centralizer_singleton_iff.mp (k : H).property,mul_inv_cancel_right]
    calc
      ((f a k : H) : G) = g.z₁*(k:G)*g.z₁⁻¹ := by rw [hact,hea]
      _ = g.z₁*(g.z₂*(k:G)*g.z₂⁻¹)*g.z₁⁻¹ := by rw [hkc]
      _ = ((α k : H) : G) := by rw [hα]; group
  exact alternating_action_excluded_by_twoPerfect_actor c.first.short.twoPerfect f a
    n hn σ hs (hf.symm ▸ ha)

/-- Exact elimination of the six-letter constructor of ModelAction115. -/
theorem SourceCentralizerGeometry.six_component_action_false
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : Theory.GroupTheory.IsComponent (involutionCentralizer g.z₂) K)
    (α : MulAut K)
    (hα : ∀ k : K, ((α k : involutionCentralizer g.z₂) : G) =
      (g.z₁*g.z₂)*(k:G)*(g.z₁*g.z₂)⁻¹)
    (σ : Equiv.Perm (Fin 6)) (hs : σ.IsSwap)
    (ha : AlternatingAction α 6 σ) : False :=
  g.alternating_component_action_false hG h K hK α hα 6 (.inl rfl) σ hs.sign_eq ha

/-- Exact elimination of the seven-letter constructor of ModelAction115. -/
theorem SourceCentralizerGeometry.seven_component_action_false
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : Theory.GroupTheory.IsComponent (involutionCentralizer g.z₂) K)
    (α : MulAut K)
    (hα : ∀ k : K, ((α k : involutionCentralizer g.z₂) : G) =
      (g.z₁*g.z₂)*(k:G)*(g.z₁*g.z₂)⁻¹)
    (σ : Equiv.Perm (Fin 7)) (hs : σ.cycleType = {2,2,2})
    (ha : AlternatingAction α 7 σ) : False := by
  apply g.alternating_component_action_false hG h K hK α hα 7 (.inr rfl) σ ?_ ha
  rw [Equiv.Perm.sign_of_cycleType,hs]
  norm_num

end CFSG.Quasithin.Chapter2.DoubleA3
