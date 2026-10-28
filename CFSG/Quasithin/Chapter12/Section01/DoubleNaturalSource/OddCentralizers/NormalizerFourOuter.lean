module
public import Theory.SpecificGroups.OddThreeFrattini
public import Theory.SpecificGroups.SymplecticFour.OddFrattiniEight
public import Theory.SpecificGroups.PSL4.FermatFrattini
public import Theory.SpecificGroups.ClassicalUnitary.MersenneFrattini
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerFourPlacement
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremB.Basic
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FrattiniExact
public import Theory.SpecificGroups.ClassicalUnitary.FourSylowStructure.Transport

/-!
# Excluding small outer actions in the original degree-four branch

The actual GL₄(2) section has order 20160. A Sylow Frattini quotient of
order at most eight has too small an automorphism group to contain that
section. The determinant-one degree-three calculation therefore excludes
every odd PSL₃ and PSU₃ row. The binary PSU₄ family is excluded by its
three-generator endpoint and solvable Sylow automorphisms at larger fields.
The odd-prime symplectic four-space is excluded by the cyclic/quaternion
base and the swap in its plane-pair wreath product.
The Fermat linear-four family is excluded by its actual two-generator GL₂
base and the determinant-one block swap.
Together with the completed Theorem C and alternating outer calculations,
this leaves six literal B-model families, with full central covers retained.
The sharper Mersenne unitary-four calculation below removes that row too;
the separate reduced interface retains the five remaining families while
preserving the original six-family API.

The final theorem applies the inspection to the component selected in the
original odd normalizer. No full Schreier property or replacement action is
assumed. Source: Aschbacher--Smith 4.4.10--11 and 12.1.9, pp.621 and 793.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.FourOuterModels
open ClassificationModels Theory.SpecificGroups BenderSuzuki.MatrixGroups
local notation "Target" => alternatingGroup (Fin 8)
private instance : IsSimpleGroup Target := alternatingGroup.isSimpleGroup (by simp)

private theorem no_small_frattini_section
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (P : Sylow 2 Q) (hP : Nat.card (P ⧸ frattini P) ≤ 8)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) : ¬ Function.Surjective f := by
  intro hf
  let : Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  have hd := MulAut.simple_outer_section_card_dvd_frattini_aut P
    (Group.IsPerfect.not_isSolvable Target) U f hf
  let : Fact (IsPGroup 2 P) := ⟨P.isPGroup'⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  obtain ⟨n,hn⟩ := (P.isPGroup'.to_quotient (frattini P)).exists_card_eq
  have hn3 : n ≤ 3 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
    simpa only [←hn] using hP
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ n hn,
    nat_card_alternatingGroup] at hd
  interval_cases n <;> norm_num [Fin.prod_univ_succ,Nat.factorial] at hd

/-- Odd linear-three sections are excluded using determinant one on the actual cover. -/
theorem linear_three_odd
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {q : ℕ} (ho : Odd q) (hm : ClassicalGroup.IsPSL Q 3 q)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) : ¬ Function.Surjective f := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let P : Sylow 2 Q := default
  apply no_small_frattini_section P ?_ U f
  rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup Q))]
  exact OddThreeFrattini.projective_linear
    (OddThreeRank.two_ne_zero_of_odd_card (k := 1) ho (by simpa using hF))
    (P.mapSurjective e.surjective)

/-- The unitary calculation retains the literal Hermitian/projective marking. -/
theorem unitary_three_odd
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {q : ℕ} (ho : Odd q) (hm : ClassicalGroup.IsPSU Q 3 q)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) : ¬ Function.Surjective f := by
  obtain ⟨F,_,_,J,hF,_,⟨e⟩⟩ := hm
  let P : Sylow 2 Q := default
  apply no_small_frattini_section P ?_ U f
  rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup Q))]
  exact OddThreeFrattini.projective_unitary J
    (OddThreeRank.two_ne_zero_of_odd_card ho hF) (P.mapSurjective e.surjective)

/-- Both the binary unitary-four endpoint and every larger field are excluded. -/
theorem unitary_four_binary
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {n : ℕ} (hn : 1 ≤ n) (hm : ClassicalGroup.IsPSU Q 4 (2 ^ n))
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) : ¬ Function.Surjective f := by
  intro hf
  obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := hm
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv Q e.toEquiv
  let P : Sylow 2 Q := default
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let a : P ≃* P' := P.equivMapOfInjective e.toMonoidHom e.injective
  by_cases hn1 : n = 1
  · apply no_small_frattini_section P ?_ U f hf
    rw [SylowFrattiniBounds.card_congr a,
      ClassicalUnitary.UnitaryFourSylow.FrattiniExact.projective_frattini_card
        F J (by omega) hcard hconj P', hn1]
    norm_num
  · let : Group.IsSolvable (MulAut P') :=
      ClassicalUnitary.FourSylowStructure.projective_sylow_mulAut_isSolvable
        F J (by omega) hcard hconj P'
    let : Group.IsSolvable (MulAut P) := Group.isSolvable_of_surjective
      (f := (MulAut.congr a.symm).toMonoidHom) (MulAut.congr a.symm).surjective
    let : Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
      ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
    let : Group.IsSolvable (MulAut.Outer Q) := MulAut.outer_isSolvable_of_sylow_aut P
    exact Group.IsPerfect.not_isSolvable Target (Group.isSolvable_of_surjective hf)

/-- The odd-prime symplectic plane-pair stabilizer has three Frattini generators. -/
theorem symplectic_four_odd
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : ClassicalGroup.IsPSp Q 2 p)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) : ¬ Function.Surjective f := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let P : Sylow 2 Q := default
  apply no_small_frattini_section P ?_ U f
  rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup Q))]
  exact SymplecticFour.OddFrattiniEight.projective_frattini_card_le
    ho hF (P.mapSurjective e.surjective)

/-- The symplectic exclusion retains the full original perfect central cover. -/
theorem symplectic_four_odd_cover_exclusion
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* Target, Function.Surjective f) :
    ∀ p : ℕ, p.Prime → Odd p → ¬ ClassicalGroup.IsPSp (K ⧸ center K) 2 p := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  obtain ⟨U,f,hf⟩ := ho
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let a := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  intro p hp hpodd hm
  exact symplectic_four_odd hp hpodd hm _ (f.comp a.symm.toMonoidHom)
    (hf.comp a.symm.surjective)

/-- The determinant-one two-block subgroup has three Frattini generators
over every field in the original Fermat family. -/
theorem linear_four_fermat
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {p : ℕ} (hp : ∃ k : ℕ, p = 2 ^ (2 ^ k) + 1) (hm : ClassicalGroup.IsPSL Q 4 p)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) : ¬ Function.Surjective f := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let P : Sylow 2 Q := default
  apply no_small_frattini_section P ?_ U f
  rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup Q))]
  apply PSL4.FermatFrattini.projective_frattini_le ?_ (P.mapSurjective e.surjective)
  obtain ⟨k,hk⟩ := hp
  exact ⟨k,hF.trans hk⟩

/-- Central descent excludes the Fermat linear-four row without discarding
any part of the component's center. -/
theorem linear_four_fermat_cover_exclusion
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* Target, Function.Surjective f) :
    ∀ p : ℕ, (∃ k : ℕ, p = 2 ^ (2 ^ k) + 1) →
      ¬ ClassicalGroup.IsPSL (K ⧸ center K) 4 p := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  obtain ⟨U,f,hf⟩ := ho
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let a := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  intro p hp hm
  exact linear_four_fermat hp hm _ (f.comp a.symm.toMonoidHom)
    (hf.comp a.symm.surjective)

/-- Perfect central descent keeps the original component and its entire center. -/
theorem cover_exclusions {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* Target, Function.Surjective f) :
    (∀ q : ℕ, Odd q → ¬ ClassicalGroup.IsPSL (K ⧸ center K) 3 q) ∧
    (∀ q : ℕ, Odd q → ¬ ClassicalGroup.IsPSU (K ⧸ center K) 3 q) ∧
    (∀ n : ℕ, 1 ≤ n → ¬ ClassicalGroup.IsPSU (K ⧸ center K) 4 (2 ^ n)) := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  obtain ⟨U,f,hf⟩ := ho
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let a := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  let g := f.comp a.symm.toMonoidHom
  have hg : Function.Surjective g := hf.comp a.symm.surjective
  exact ⟨fun _ hq hm => linear_three_odd hq hm _ g hg,
    fun _ hq hm => unitary_three_odd hq hm _ g hg,
    fun _ hn hm => unitary_four_binary hn hm _ g hg⟩

/-- The actual Mersenne unitary-four Sylow group has three Frattini generators,
so its outer automorphism group has no GL₄(2) section. -/
theorem unitary_four_mersenne
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {p : ℕ} (hp : p.Prime) (hm : ∃ k : ℕ, p+1 = 2^k)
    (hmodel : ClassicalGroup.IsPSU Q 4 p)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) : ¬ Function.Surjective f := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨k,hk⟩ := hm
    have hk2 : k < 2 := by
      by_contra! h
      have hh := Nat.pow_le_pow_right (by decide : 0 < 2) h
      omega
    interval_cases k <;> norm_num at hk
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hmodel
  let P : Sylow 2 Q := default
  apply no_small_frattini_section P ?_ U f
  rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup Q))]
  exact ClassicalUnitary.MersenneFrattini.projective_frattini_le J
    (hp.odd_of_ne_two hp2) hm hF hconj (P.mapSurjective e.surjective)

/-- Descent through the full center preserves the Mersenne unitary exclusion. -/
theorem unitary_four_mersenne_cover_exclusion
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* Target, Function.Surjective f) :
    ∀ p : ℕ, p.Prime → (∃ k : ℕ, p+1 = 2^k) →
      ¬ ClassicalGroup.IsPSU (K ⧸ center K) 4 p := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  obtain ⟨U,f,hf⟩ := ho
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let a := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  intro p hp hm hmodel
  exact unitary_four_mersenne hp hm hmodel _ (f.comp a.symm.toMonoidHom)
    (hf.comp a.symm.surjective)

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.FourOuterModels

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
open ChapterA.Section02 ClassificationModels
open BinaryLinear.OuterCyclic

/-- The surviving models are actual central-quotient identifications. -/
inductive FourRemainingOuterModel (Q : Type*) [Group Q] : Prop
  | g2 (p : ℕ) (hp : p.Prime) (ho : Odd p) (iso : IsG2At Q p)
  | unitary_four (p : ℕ) (hp : p.Prime) (hm : ∃ k : ℕ, p + 1 = 2 ^ k)
      (iso : ClassicalGroup.IsPSU Q 4 p)
  | symplectic_binary (iso : ClassicalGroup.IsPSp Q 3 2)
  | unitary_five_four (iso : ClassicalGroup.IsPSU Q 5 4)
  | janko_three (iso : Nonempty (Q ≃* Sporadic.Janko3.Model))
  | mcl (iso : Nonempty (Q ≃* Sporadic.LeechRelated.McL.Carrier))

/-- Inspect every B-model against the literal GL₄(2) outer section, excluding
all shared C rows, alternating rows, odd degree-three, odd symplectic-four
and binary unitary-four rows, and the Fermat linear-four family. -/
theorem four_remaining_outer_models
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hm : IsTheoremBModel (K ⧸ center K))
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* LinearGroup 4,
      Function.Surjective f) : FourRemainingOuterModel (K ⧸ center K) := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
  have hna := Group.IsPerfect.not_isMulCommutative (K ⧸ center K)
  have ha : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* alternatingGroup (Fin 8),
      Function.Surjective f := by
    obtain ⟨U,f,hf⟩ := ho
    let e := Chapter12.Section02.ChosenModule.doubledFour_linearEquiv
    exact ⟨U,e.toMonoidHom.comp f,e.surjective.comp hf⟩
  have hns : ¬ Group.IsSolvable (MulAut.Outer (K ⧸ center K)) := by
    intro hs
    let := hs
    let : Group.IsSolvable (MulAut.Outer K) := Group.isSolvable_of_isSolvable_injective
      (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
    obtain ⟨U,f,hf⟩ := ha
    let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 8))
      (Group.isSolvable_of_surjective hf)
  have hC (hc : IsTheoremCModel (K ⧸ center K)) : False :=
    hns (ChapterA.Section03.SourceComponents.TheoremBOuter.of_theoremC hna hc)
  obtain ⟨hlin,huni,hfour⟩ := FourOuterModels.cover_exclusions ha
  have hsp := FourOuterModels.symplectic_four_odd_cover_exclusion ha
  have hlf := FourOuterModels.linear_four_fermat_cover_exclusion ha
  cases hm with
  | alternating n _ e =>
    exact (hns (ChapterA.Section03.SourceComponents.TheoremBOuter.alternating hna e)).elim
  | odd h =>
    cases h with
    | linear_two q hq e =>
      exact (hns (ChapterA.Section03.SourceComponents.TheoremBOuter.linear_two_odd hna hq e)).elim
    | linear_three p a _ hq _ e => exact (hlin _ hq.pow e).elim
    | unitary_three p a _ hq _ e => exact (huni _ hq.pow e).elim
    | symplectic p hp hq e => exact (hsp p hp hq e).elim
    | g2 p hp hq e => exact .g2 p hp hq e
    | linear_four p _ hf e => exact (hlf p hf e).elim
    | unitary_four p hp hf e => exact .unitary_four p hp hf e
  | bender h => exact (hC (.bender h)).elim
  | linear_binary n hn h => exact (hC (.linear_binary n hn h)).elim
  | symplectic_binary h => exact .symplectic_binary h
  | rank_two n h =>
    cases h with
    | linear hn h => exact (hC (.rank_two n (.linear hn h))).elim
    | unitary_four hn h => exact (hfour n hn h).elim
    | unitary_five hn h => exact .unitary_five_four (by simpa [hn] using h)
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

/-- The five actual central-quotient families surviving the Mersenne exclusion. -/
inductive FourReducedOuterModel (Q : Type*) [Group Q] : Prop
  | g2 (p : ℕ) (hp : p.Prime) (ho : Odd p) (iso : IsG2At Q p)
  | symplectic_binary (iso : ClassicalGroup.IsPSp Q 3 2)
  | unitary_five_four (iso : ClassicalGroup.IsPSU Q 5 4)
  | janko_three (iso : Nonempty (Q ≃* Sporadic.Janko3.Model))
  | mcl (iso : Nonempty (Q ≃* Sporadic.LeechRelated.McL.Carrier))

/-- The literal outer section excludes the remaining unitary-four row of
Theorem B. The component and its entire center are unchanged. -/
theorem four_reduced_outer_models
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hm : IsTheoremBModel (K ⧸ center K))
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* LinearGroup 4,
      Function.Surjective f) : FourReducedOuterModel (K ⧸ center K) := by
  have ha : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* alternatingGroup (Fin 8),
      Function.Surjective f := by
    obtain ⟨U,f,hf⟩ := ho
    let e := Chapter12.Section02.ChosenModule.doubledFour_linearEquiv
    exact ⟨U,e.toMonoidHom.comp f,e.surjective.comp hf⟩
  have hunitary := FourOuterModels.unitary_four_mersenne_cover_exclusion ha
  cases four_remaining_outer_models hm ho with
  | g2 p hp hpodd e => exact .g2 p hp hpodd e
  | unitary_four p hp hm e => exact (hunitary p hp hm e).elim
  | symplectic_binary e => exact .symplectic_binary e
  | unitary_five_four e => exact .unitary_five_four e
  | janko_three e => exact .janko_three e
  | mcl e => exact .mcl e

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
