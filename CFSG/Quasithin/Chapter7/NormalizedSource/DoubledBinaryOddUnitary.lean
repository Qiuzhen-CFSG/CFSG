module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddPlacement
public import Theory.GroupTheory.SylowOuterSimpleSections
public import Theory.SpecificGroups.ClassicalUnitary.FourSylowStructure.Transport
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.Flag.Automorphisms

/-!
# Even unitary outer exclusions for the actual binary-three residual

The root-parameter kernel for a unitary-four Sylow group is solvable. At
fixed-field order two its parameter group has order four, so its automorphism
group embeds in the solvable symmetric group on four letters. Together with
the existing larger-field calculation this proves outer solvability for every
PSU₄(2ⁿ). For PSU₅(4), the seven-free Sylow automorphism calculation excludes
the actual SL₃(2) section. Both arguments descend through the entire center
of the original quasisimple component.

The final model inspection and its chosen-module consumer retain the remaining
B-models explicitly; they do not assert full odd-normalizer control.
Source: Aschbacher–Smith 4.4.10–12, printed pp.621–622, used by 7.3.4
and 7.6.1, printed pp.699,702, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddUnitary
open Theory.SpecificGroups BenderSuzuki.MatrixGroups ChapterA.Section02
open ClassificationModels BinaryLinearThree

private instance : IsSimpleGroup BinaryLinearThree.Group := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  exact Matrix.PSL3Two.equiv.isSimpleGroup

private instance : _root_.Group.IsPerfect BinaryLinearThree.Group := Atlas.sl_perfect 3 (by decide)

private theorem small_mulAut_solvable {X : Type*} [_root_.Group X] [Finite X]
    (hX : Nat.card X = 4) : _root_.Group.IsSolvable (MulAut X) := by
  let e : X ≃ Fin 4 := Finite.equivFinOfCardEq hX
  let : _root_.Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : _root_.Group.IsSolvable (Equiv.Perm X) :=
    _root_.Group.isSolvable_of_isSolvable_injective
      (f := (Equiv.permCongrHom e).toMonoidHom) (Equiv.permCongrHom e).injective
  exact _root_.Group.isSolvable_of_isSolvable_injective
    (f := MulAut.toPerm X) (fun a b he => MulEquiv.ext (fun x => Equiv.congr_fun he x))

private theorem binary_rootNormalizer_solvable
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (σ : F ≃+* F) (hσ : Function.Involutive σ)
    (hnt : ∃ u, σ u ≠ u) (hF : Nat.card F = 4) :
    _root_.Group.IsSolvable (ClassicalUnitary.FourSylowNormalizer.rootNormalizer F σ hσ) := by
  let r := ClassicalUnitary.FourSylowNormalizer.parameterAction F σ hσ
  let : _root_.Group.IsSolvable (MulAut (Multiplicative F)) := small_mulAut_solvable
    ((Nat.card_congr Multiplicative.toAdd).trans hF)
  let : _root_.Group.IsSolvable r.ker :=
    ClassicalUnitary.FourSylowNormalizer.parameterKernel_isSolvable F σ hσ hnt
  exact _root_.Group.isSolvable_of_ker_le_range r.ker.subtype r (by rw [range_subtype])

/-- The binary endpoint has solvable full Sylow automorphisms, using the
literal root-parameter action and the original arbitrary Hermitian form. -/
theorem unitary_four_two_sylow_solvable
    {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 4 F) (hF : Nat.card F = 4)
    (hconj : ∀ x, J.conj x = x ^ 2)
    [Finite (ProjectiveSpecialUnitaryMatrixGroup J)]
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    _root_.Group.IsSolvable (MulAut P) := by
  have hc : Nat.card F = (2 ^ 1) ^ 2 := by simpa using hF
  let : CharP F 2 := ClassicalUnitary.UnitaryFourFormTransport.charP_two 1 (by decide) hc
  have hfixed : Nat.card (FixedBy.subfield F J.conj) = 2 := by
    simpa using ClassicalUnitary.UnitaryFourFormTransport.fixed_card J 1 (by decide) hc hconj
  have hnt : ∃ u, J.conj u ≠ u := by
    by_contra! hh
    let e : FixedBy.subfield F J.conj ≃ F := Equiv.ofBijective Subtype.val
      ⟨Subtype.val_injective, fun x => ⟨⟨x,hh x⟩,rfl⟩⟩
    have he := Nat.card_congr e
    rw [hfixed,hF] at he
    omega
  obtain ⟨j⟩ := ClassicalUnitary.UnitaryFourFormTransport.nonempty_projectiveEquiv_standardSU
    J 1 (by decide) hc hconj
  let Q := P.mapSurjective (f := j.toMonoidHom) j.surjective
  let e : P ≃* Q := P.equivMapOfInjective j.toMonoidHom j.injective
  let : _root_.Group.IsSolvable (MulAut Q) :=
    ClassicalUnitary.FourSylowStructure.sylow_mulAut_isSolvable_of_rootNormalizer
      F J.conj J.conj_involutive hnt (binary_rootNormalizer_solvable J.conj J.conj_involutive hnt hF) Q
  exact _root_.Group.isSolvable_of_surjective (f := (MulAut.congr e.symm).toMonoidHom)
    (MulAut.congr e.symm).surjective

/-- Every simple binary unitary-four model has solvable outer automorphisms,
including the three-generator endpoint where a dimension bound alone fails. -/
theorem unitary_four_outer_solvable
    {Q : Type*} [_root_.Group Q] [Finite Q] [IsSimpleGroup Q]
    {n : ℕ} (hn : 1 ≤ n) (hm : ClassicalGroup.IsPSU Q 4 (2 ^ n)) :
    _root_.Group.IsSolvable (MulAut.Outer Q) := by
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv Q e.toEquiv
  let P : Sylow 2 Q := default
  let R := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let a : P ≃* R := P.equivMapOfInjective e.toMonoidHom e.injective
  have hR : _root_.Group.IsSolvable (MulAut R) := by
    by_cases he : n = 1
    · subst n
      exact unitary_four_two_sylow_solvable J (by simpa using hF) hconj R
    · exact ClassicalUnitary.FourSylowStructure.projective_sylow_mulAut_isSolvable
        F J (by omega) hF hconj R
  let := hR
  let : _root_.Group.IsSolvable (MulAut P) := _root_.Group.isSolvable_of_surjective
    (f := (MulAut.congr a.symm).toMonoidHom) (MulAut.congr a.symm).surjective
  let : _root_.Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  exact MulAut.outer_isSolvable_of_sylow_aut P

/-- The seven-free Sylow automorphism group excludes the actual binary-three
outer section in PSU₅(4). -/
theorem unitary_five_no_outer_section
    {Q : Type*} [_root_.Group Q] [Finite Q] [IsSimpleGroup Q]
    (hm : ClassicalGroup.IsPSU Q 5 4)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* BinaryLinearThree.Group) :
    ¬ Function.Surjective f := by
  intro hf
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
  let : CharP F 2 := UnitaryFive.charP_two_of_card_sixteen hF
  obtain ⟨a⟩ := UnitaryFive.projective_equiv_identity_four J hF hconj
  let P : Sylow 2 Q := default
  let : _root_.Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  have hd := MulAut.simple_outer_section_card_dvd_sylow_aut P
    (_root_.Group.IsPerfect.not_isSolvable BinaryLinearThree.Group) U f hf
  apply UnitaryFive.Flag.Automorphisms.not_seven_dvd_sylow_aut_of_equiv
    (HermitianForm.IdentityGram.identityGram J) hF hconj rfl (e.trans a) P
  apply dvd_trans ?_ hd
  rw [Matrix.PSL3Two.card_SL]
  decide

/-- Both even-unitary exclusions retain the full original quasisimple cover. -/
theorem cover_exclusions
    {K : Type*} [_root_.Group K] [Finite K] [IsQuasisimple K]
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinearThree.Group,
      Function.Surjective f) :
    (∀ n : ℕ, 1 ≤ n → ¬ ClassicalGroup.IsPSU (K ⧸ center K) 4 (2 ^ n)) ∧
      ¬ ClassicalGroup.IsPSU (K ⧸ center K) 5 4 := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  obtain ⟨U,f,hf⟩ := ho
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let a := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  let g := f.comp a.symm.toMonoidHom
  have hg : Function.Surjective g := hf.comp a.symm.surjective
  refine ⟨?_, fun hm => unitary_five_no_outer_section hm _ g hg⟩
  intro n hn hm
  let := unitary_four_outer_solvable hn hm
  exact _root_.Group.IsPerfect.not_isSolvable BinaryLinearThree.Group
    (_root_.Group.isSolvable_of_surjective hg)

/-- The actual B-models still possible for a binary-three outer section after
shared C, alternating, odd linear-two and even-unitary exclusion. -/
inductive RemainingOuterModel (Q : Type*) [_root_.Group Q] : Prop
  | linear_three_square (p : ℕ) (hp : p.Prime) (ho : Odd p)
      (iso : ClassicalGroup.IsPSL Q 3 (p ^ 2))
  | unitary_three_square (p : ℕ) (hp : p.Prime) (ho : Odd p)
      (iso : ClassicalGroup.IsPSU Q 3 (p ^ 2))
  | symplectic_odd (p : ℕ) (hp : p.Prime) (ho : Odd p)
      (iso : ClassicalGroup.IsPSp Q 2 p)
  | g2_odd (p : ℕ) (hp : p.Prime) (ho : Odd p) (iso : IsG2At Q p)
  | linear_four (p : ℕ) (hp : p.Prime) (hf : ∃ k : ℕ, p = 2 ^ (2 ^ k) + 1)
      (iso : ClassicalGroup.IsPSL Q 4 p)
  | unitary_four (p : ℕ) (hp : p.Prime) (hm : ∃ k : ℕ, p + 1 = 2 ^ k)
      (iso : ClassicalGroup.IsPSU Q 4 p)
  | symplectic_binary (iso : ClassicalGroup.IsPSp Q 3 2)
  | janko_three (iso : Nonempty (Q ≃* Sporadic.Janko3.Model))
  | mcl (iso : Nonempty (Q ≃* Sporadic.LeechRelated.McL.Carrier))

/-- Inspect the complete literal B catalogue against the original section.
In the odd degree-three rows the prime-field case is already excluded,
and field order one is impossible, so only square fields remain. -/
theorem remaining_outer_models
    {K : Type*} [_root_.Group K] [Finite K] [IsQuasisimple K]
    (hm : IsTheoremBModel (K ⧸ center K))
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinearThree.Group,
      Function.Surjective f) : RemainingOuterModel (K ⧸ center K) := by
  obtain ⟨hC,hAlt,hTwo⟩ := DoubledBinaryOddPlacement.outer_section_exclusions ho
  obtain ⟨hFour,hFive⟩ := cover_exclusions ho
  cases hm with
  | alternating n _ e => exact (hAlt n e).elim
  | odd h =>
    cases h with
    | linear_two q hq e => exact (hTwo q hq e).elim
    | linear_three p a hp hq ha e =>
      interval_cases a
      · obtain ⟨F,_,_,hc,_⟩ := e
        have hh : 1 < Nat.card F := Finite.one_lt_card
        simp only [pow_zero] at hc
        omega
      · exact (hC (.odd (.linear_three p hp hq (by simpa using e)))).elim
      · exact .linear_three_square p hp hq e
    | unitary_three p a hp hq ha e =>
      interval_cases a
      · obtain ⟨F,_,_,J,hc,_,_⟩ := e
        have hh : 1 < Nat.card F := Finite.one_lt_card
        simp only [pow_zero,one_pow] at hc
        omega
      · exact (hC (.odd (.unitary_three p hp hq (by simpa using e)))).elim
      · exact .unitary_three_square p hp hq e
    | symplectic p hp hq e => exact .symplectic_odd p hp hq e
    | g2 p hp hq e => exact .g2_odd p hp hq e
    | linear_four p hp hf e => exact .linear_four p hp hf e
    | unitary_four p hp hf e => exact .unitary_four p hp hf e
  | bender h => exact (hC (.bender h)).elim
  | linear_binary n hn h => exact (hC (.linear_binary n hn h)).elim
  | symplectic_binary h => exact .symplectic_binary h
  | rank_two n h =>
    cases h with
    | linear hn h => exact (hC (.rank_two n (.linear hn h))).elim
    | unitary_four hn h => exact (hFour n hn h).elim
    | unitary_five hn h => exact (hFive (by simpa [hn] using h)).elim
    | symplectic hn h => exact (hC (.rank_two n (.symplectic hn h))).elim
    | g2 hn h => exact (hC (.rank_two n (.g2 hn h))).elim
    | triality hn h => exact (hC (.rank_two n (.triality hn h))).elim
    | ree_f4 m hm hn h => exact (hC (.rank_two n (.ree_f4 m hm hn h))).elim
    | symplectic_derived hn h => exact (hC (.rank_two n (.symplectic_derived hn h))).elim
    | g2_derived hn h => exact (hC (.rank_two n (.g2_derived hn h))).elim
    | tits hn h => exact (hC (.rank_two n (.tits hn h))).elim
  | sporadic h =>
    rcases h with ⟨name,e⟩ | e | e
    · by_cases hj : name = .j3
      · subst name; exact .janko_three e
      · exact (hC (.sporadic (.inl ⟨name,hj,e⟩))).elim
    · exact (hC (.sporadic (.inr e))).elim
    · exact .mcl e

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddUnitary
