module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.WeylPinning
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.RootIntersections
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.NormalGeneration
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.MarkedQuotient

/-!
# Generation by the constructed signed triality roots

The negative roots are conjugates of the positive roots by the original
longest word. Their closure is therefore U joined with that conjugate of U.
The full Cartan normalizes both subgroups. Once the two source rank-one Weyl
words are placed over the two marked simple reflections, quotient generation
shows that N normalizes the signed closure; B = UH and BN generation make it
normal in the entire source group. It is exactly the normal closure of U,
and hence the prime-to-two quotient residual O^{2′}.

This removes ambient signed generation as an independent source obligation.
It uses no perfectness, so applies at q=2. The compatible pinning, positive
root construction and placement of the two Weyl words remain earlier inputs.
Source: Fong--Seitz I, ambient hypotheses and §1; II §7 and §9B;
Carter 2.5.10--2.5.17 in refs/KGroup/GLS3/Chapter2Ca2.tex.
-/

@[expose] public noncomputable section
open Subgroup
open Triality.Standard Triality.Standard.RootPresentationRecognition
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
open RootCoordinates
variable {F Y : Type*} [Field F] [CharP F 2] [Group Y] {σ : F ≃+* F}

namespace RankOnePair
variable (p : RankOnePair σ Y) {n : ℕ} {hn : 0 < n}
  (e : ScalarMarking (binaryParameters n hn) σ)

theorem signedClosure_eq_positive_sup_conjugate :
    (p.signedRoots e).signedClosure =
      (p.signedRoots e).positive.positiveClosure ⊔
        rightConjugate (p.signedRoots e).positive.positiveClosure p.dihedral.longest := by
  have hmap : ((p.signedRoots e).positive.positiveClosure).map p.dihedral.W.toMonoidHom =
      rightConjugate (p.signedRoots e).positive.positiveClosure p.dihedral.longest := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      change p.dihedral.W (p.dihedral.W y) ∈ (p.signedRoots e).positive.positiveClosure
      rwa [p.dihedral.W_W]
    · intro hx
      exact ⟨p.dihedral.W x, hx, p.dihedral.W_W x⟩
  rw [← hmap, SignedRoots.signedClosure]
  congr 1
  rw [PositiveRoots.positiveClosure, MonoidHom.map_closure, ← Set.range_comp]
  congr 1
  ext x
  constructor
  · rintro (⟨⟨i,t⟩,rfl⟩ | ⟨⟨i,t⟩,rfl⟩)
    · fin_cases i
      · exact ⟨(0,(fun _ => t,0)),rfl⟩
      · exact ⟨(2,(fun _ => t,0)),rfl⟩
      · exact ⟨(3,(fun _ => t,0)),rfl⟩
    · fin_cases i
      · exact ⟨(1,(0,fun _ => t)),rfl⟩
      · exact ⟨(4,(0,fun _ => t)),rfl⟩
      · exact ⟨(5,(0,fun _ => t)),rfl⟩
  · rintro ⟨⟨i,v⟩,rfl⟩
    fin_cases i
    · exact Or.inl ⟨(0,v.1 0),rfl⟩
    · exact Or.inr ⟨(0,v.2 0),rfl⟩
    · exact Or.inl ⟨(1,v.1 1),rfl⟩
    · exact Or.inl ⟨(2,v.1 2),rfl⟩
    · exact Or.inr ⟨(1,v.2 1),rfl⟩
    · exact Or.inr ⟨(2,v.2 2),rfl⟩
end RankOnePair

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)

theorem N_le_of_torus_le_of_simple_lifts (M : Subgroup (X ⧸ Q.D))
    (hH : Q.tits.B ⊓ Q.tits.N ≤ M) (v : Fin 2 → Q.tits.N)
    (indices : Fin 2 ≃ Fin 2)
    (hv : ∀ i, QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) (v i) = Q.simple (indices i))
    (hM : ∀ i, (v i : X ⧸ Q.D) ∈ M) : Q.tits.N ≤ M := by
  let π := QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N)
  have hk : π.ker ≤ M.subgroupOf Q.tits.N := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact hH hx
  have htop : (M.subgroupOf Q.tits.N).map π = ⊤ := by
    apply top_unique
    rw [← Q.tits.quotient_generate]
    apply (closure_le _).mpr
    intro s hs
    obtain ⟨i,rfl⟩ := Q.simple_range ▸ hs
    exact ⟨v (indices.symm i),hM _, by simpa only [Equiv.apply_symm_apply] using hv (indices.symm i)⟩
  have hc := congrArg (Subgroup.comap π) htop
  rw [comap_map_eq_self hk, comap_top] at hc
  intro x hx
  exact show (⟨x,hx⟩ : Q.tits.N) ∈ M.subgroupOf Q.tits.N from hc ▸ mem_top _

/-- The actual two rank-one Weyl elements lie in N and represent the two
marked simple reflections, in either source orientation. -/
structure WeylPlacement {σ : F ≃+* F} (p : RankOnePair σ (X ⧸ Q.D)) where
  indices : Fin 2 ≃ Fin 2
  lift : Fin 2 → Q.tits.N
  short : (lift 0 : X ⧸ Q.D) = p.dihedral.a
  long : (lift 1 : X ⧸ Q.D) = p.dihedral.b
  simple : ∀ i, QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N)
    (lift i) = Q.simple (indices i)

namespace WeylPlacement
variable (split : SplitData Q.tits) {σ : F ≃+* F}
  (p : RankOnePair σ (X ⧸ Q.D)) {n : ℕ} {hn : 0 < n}
  (e : ScalarMarking (binaryParameters n hn) σ)
  (w : WeylPlacement Q p)
  (hpositive : (p.signedRoots e).positive.positiveClosure = split.U)

include w in
theorem longest_mem_N : p.dihedral.longest ∈ Q.tits.N := by
  have ha : p.dihedral.a ∈ Q.tits.N := w.short ▸ (w.lift 0).property
  have hb : p.dihedral.b ∈ Q.tits.N := w.long ▸ (w.lift 1).property
  exact Q.tits.N.pow_mem (Q.tits.N.mul_mem ha hb) 3

include w hpositive in
theorem torus_normalizes_signedClosure :
    Q.tits.B ⊓ Q.tits.N ≤ normalizer ((p.signedRoots e).signedClosure : Set (X ⧸ Q.D)) := by
  rw [p.signedClosure_eq_positive_sup_conjugate e, hpositive]
  have hU : Q.tits.B ⊓ Q.tits.N ≤ normalizer (split.U : Set (X ⧸ Q.D)) :=
    inf_le_left.trans split.normalizes
  exact (le_inf hU (torus_normalizes_rightConjugate split.U hU
    ⟨p.dihedral.longest,w.longest_mem_N Q p⟩)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

include w hpositive in
theorem signedClosure_normal : (p.signedRoots e).signedClosure.Normal := by
  have hU : split.U ≤ (p.signedRoots e).signedClosure := by
    rw [← hpositive]
    exact le_sup_left
  have ha : p.dihedral.a ∈ (p.signedRoots e).signedClosure := by
    rw [SignedRoots.signedClosure_eq_simpleClosure _ (p.actions e)]
    change p.dihedral.a ∈ (p.signedRoots e).positive.positiveClosure ⊔ _
    apply mem_sup_right
    apply Subgroup.subset_closure
    rw [p.nA_one, p.nB_one]
    simp
  have hb : p.dihedral.b ∈ (p.signedRoots e).signedClosure := by
    rw [SignedRoots.signedClosure_eq_simpleClosure _ (p.actions e)]
    change p.dihedral.b ∈ (p.signedRoots e).positive.positiveClosure ⊔ _
    apply mem_sup_right
    apply Subgroup.subset_closure
    rw [p.nA_one, p.nB_one]
    simp
  have hH := w.torus_normalizes_signedClosure Q split p e hpositive
  have hN : Q.tits.N ≤ normalizer ((p.signedRoots e).signedClosure : Set (X ⧸ Q.D)) := by
    apply N_le_of_torus_le_of_simple_lifts Q _ hH w.lift w.indices w.simple
    intro i
    apply le_normalizer
    fin_cases i
    · exact w.short.symm ▸ ha
    · exact w.long.symm ▸ hb
  have hB : Q.tits.B ≤ normalizer ((p.signedRoots e).signedClosure : Set (X ⧸ Q.D)) := by
    rw [← split.factorization]
    exact sup_le (hU.trans le_normalizer) hH
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← Q.tits.generate]
  exact (closure_le _).mpr (Set.union_subset hB hN)

include w hpositive in
theorem signedClosure_eq_unipotentClosure :
    (p.signedRoots e).signedClosure = split.unipotentClosure := by
  let := w.signedClosure_normal Q split p e hpositive
  apply le_antisymm
  · rw [p.signedClosure_eq_positive_sup_conjugate e, hpositive]
    refine sup_le le_normalClosure ?_
    intro x hx
    have hc := (inferInstance : split.unipotentClosure.Normal).conj_mem
      (p.dihedral.W x) (le_normalClosure hx) p.dihedral.longest
    change p.dihedral.W (p.dihedral.W x) ∈ split.unipotentClosure at hc
    rwa [p.dihedral.W_W] at hc
  · apply normalClosure_le_normal
    exact hpositive ▸ (show (p.signedRoots e).positive.positiveClosure ≤
      (p.signedRoots e).signedClosure from le_sup_left)

include w hpositive in
theorem signedClosure_eq_primeToResidual :
    (p.signedRoots e).signedClosure = primeToResidual 2 (X ⧸ Q.D) :=
  (w.signedClosure_eq_unipotentClosure Q split p e hpositive).trans
    split.unipotentClosure_eq_primeToResidual

end WeylPlacement
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
