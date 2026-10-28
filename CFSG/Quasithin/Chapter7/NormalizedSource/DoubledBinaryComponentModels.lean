module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryInnerAction
public import Theory.SpecificGroups.BinaryComponentFixers
public import Theory.SpecificGroups.Triality.ElementarySylowFixers
public import Theory.SpecificGroups.OddThreeRank
public import Theory.SpecificGroups.PSL2.OddAutomorphismRank
public import Theory.GroupTheory.PrimeRankOrderBound
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.Mathieu.M11.Properties.ElementarySylowFixers
public import Theory.Mathieu.M12.OrdinaryLocal
public import Theory.Mathieu.M22.Properties.ElementarySylowFixers
public import Theory.Mathieu.M23.Properties.ElementarySylowFixers
public import Theory.Mathieu.M24.Properties.ElementarySylowFixers
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ElementarySylowFixers
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrdinaryLocal
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations
public import Theory.SpecificGroups.Rudvalis.Model.SylowCenter
public import Theory.SpecificGroups.Janko4.Model.ElementarySylowFixers

/-!
# Component models for the binary doubled orbit

The faithful inner moving sixteen forces two-rank at least four in the
actual central quotient. This excludes the odd-characteristic and small
alternating rows of Theorem C, and J₁. The noncyclic Sylow center excludes
A₈, all binary linear and sporadic rows, and the small derived and triality
rows. Every surviving model is a Lie group over a field larger than F₂.

All alternatives retain actual model isomorphisms, including the graph-field
triality carrier and the original Ree fixed-group convention. The SQTK
component theorem supplies the full Theorem C catalogue from the original
overgroup; the chosen-module application is in
NonFFSourceDoubledBinaryComponentModels.

Source: Aschbacher–Smith, proof of 7.7.6, printed p.706,
refs/quasithin.pdf. Root-group and Cartan exclusion remain separate steps.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryComponentModels
open Chapter1.Section02.LocalModels ClassificationModels

/-- The actual nonbinary Lie carriers surviving the rank and Sylow-center tests. -/
@[expose] def NonbinaryLieModel (S : Type*) [Group S] : Prop :=
  IsBenderModel S ∨
  (∃ f : ℕ, 2 ≤ f ∧ (ClassicalGroup.IsPSL S 3 (2 ^ f) ∨
    ClassicalGroup.IsPSp S 2 (2 ^ f) ∨ IsG2At S (2 ^ f) ∨
    Triality.Standard.IsTrialityGroupAt (2 ^ f) S)) ∨
  ∃ m : ℕ, 1 ≤ m ∧ IsReeF4At S m

private theorem cyclic_of_card_le_two {X : Type*} [Group X] [Finite X]
    (h : Nat.card X ≤ 2) : IsCyclic X := by
  apply isCyclic_of_card_dvd_prime (p := 2)
  have hp : 0 < Nat.card X := Nat.card_pos
  have he : Nat.card X = 1 ∨ Nat.card X = 2 := by omega
  rcases he with he | he <;> simp [he]

private theorem cyclic_center_of_equiv {X Y : Type*} [Group X] [Group Y]
    [Finite X] (e : X ≃* Y) (h : ∀ P : Sylow 2 Y, IsCyclic (center P))
    (P : Sylow 2 X) : IsCyclic (center P) := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let f : P ≃* Q := e.subgroupMap (P : Subgroup X)
  exact (centerCongr f).isCyclic.mpr (h Q)

private theorem tits_cyclic_center (P : Sylow 2 Tits.Atlas1600Group) :
    IsCyclic (center P) := by
  let f : center P →* MulAut Tits.Atlas1600Group :=
    MulAut.conj.comp ((P : Subgroup Tits.Atlas1600Group).subtype.comp (center P).subtype)
  have hf : Function.Injective f :=
    (MulAut.conj_injective_of_center_eq_bot Tits.RelativeSylowMarking.atlas_center_eq_bot).comp
      ((P : Subgroup Tits.Atlas1600Group).subtype_injective.comp (center P).subtype_injective)
  have hb := Theory.SpecificGroups.BinaryComponentResidual.tits_fixers P f.range (by
    rintro _ ⟨z,rfl⟩ x hx
    change (z.val : Tits.Atlas1600Group) * x * (z.val : Tits.Atlas1600Group)⁻¹ = x
    apply mul_inv_eq_iff_eq_mul.mpr
    exact congrArg Subtype.val ((mem_center_iff.mp z.property (⟨x,hx⟩ : P)).symm))
  exact (MonoidHom.ofInjective hf).isCyclic.mpr (cyclic_of_card_le_two hb)

private theorem binary_linear_cyclic_center {S : Type*} [Group S] [Finite S]
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSL S n 2)
    (P : Sylow 2 S) : IsCyclic (center P) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let k : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  exact cyclic_center_of_equiv (e.trans (Atlas.fieldEquivPSL n k))
    (fun Q => cyclic_of_card_le_two (BinaryLinear.psl_sylow_center_card_le_two hn Q)) P

private theorem binary_triality_cyclic_center {S : Type*} [Group S] [Finite S]
    (hm : Triality.Standard.IsTrialityGroupAt 2 S)
    (P : Sylow 2 S) : IsCyclic (center P) := by
  obtain ⟨R,hq,⟨e⟩⟩ := hm
  have hp : R.prime = 2 := by
    apply (Nat.prime_dvd_prime_iff_eq R.prime_prime Nat.prime_two).mp
    rw [←hq]
    exact dvd_pow_self R.prime (Nat.ne_of_gt R.exponent_pos)
  apply cyclic_center_of_equiv e _ P
  intro Q
  let U := Triality.Standard.Parabolics.unipotentSylow R hp
  have hc : Nat.card (center U) = 2 :=
    (Triality.Standard.RadicalCoordinates.Centers.card_center_unipotent R hp).trans hq
  have hQ : Nat.card (center Q) = 2 :=
    (Nat.card_congr (centerCongr (Q.equiv U)).toEquiv).trans hc
  exact cyclic_of_card_le_two hQ.le

private theorem binary_g2_cyclic_center
    (P : Sylow 2 (commutator (Atlas.G2.Model (ZMod 2)))) : IsCyclic (center P) := by
  let Q := Atlas.G2.BinaryParabolicPair.derivedSylow
  have hQ : Nat.card (omega₁ (center Q) (p := 2)) = 2 := by
    have hh := congrArg (fun B : Subgroup Atlas.G2.BinaryParabolicPair.DerivedModel => Nat.card B)
      Atlas.G2.BinaryParabolicPair.derivedSylow_omega_center_in_model
    rw [card_map_of_injective Atlas.G2.BinaryParabolicPair.derivedSylow.toSubgroup.subtype_injective,
      card_map_of_injective (center Atlas.G2.BinaryParabolicPair.derivedSylow).subtype_injective,
      Atlas.G2.BinaryParabolicPair.card_derivedDistinguished] at hh
    exact hh
  let : IsCyclic (center Q) :=
    (Q.isPGroup'.to_subgroup (center Q)).isCyclic_of_card_omega_one_le_two hQ.le
  exact (centerCongr (Q.equiv P)).isCyclic.mp inferInstance

private theorem small_alternating_rank {n : ℕ} (hn : 5 ≤ n ∧ n ≤ 7) :
    primeRank 2 (alternatingGroup (Fin n)) ≤ 3 := by
  apply primeRank_le_of_prime_pow_not_dvd
  have : n.AtLeastTwo := ⟨by omega⟩
  rw [nat_card_alternatingGroup]
  obtain ⟨hn5,hn7⟩ := hn
  interval_cases n <;> norm_num [Nat.factorial]

private theorem sporadic_cyclic_center (name : SporadicName) [Finite name.Carrier] (hne : name ≠ .j3)
    (P : Sylow 2 name.Carrier) : IsCyclic (center P) := by
  cases name with
  | m11 => exact Sporadic.Mathieu.m11_sylow_center_isCyclic P
  | m12 => exact cyclic_of_card_le_two (Sporadic.Mathieu.OrdinaryTwelve.sylow_center_card_two P).le
  | m22 => exact Sporadic.Mathieu.m22_sylow_center_isCyclic P
  | m23 => exact Sporadic.Mathieu.m23_sylow_center_isCyclic P
  | m24 => exact Sporadic.Mathieu.m24_sylow_center_isCyclic P
  | j2 => exact cyclic_of_card_le_two (Sporadic.LeechRelated.J2.sylow_center_card_two P).le
  | hs => exact cyclic_of_card_le_two (Sporadic.LeechRelated.HS.OrdinaryLocal.sylow_center_card_two P).le
  | he => exact cyclic_of_card_le_two (Held.LocalPairs.SylowGeometry.Calculations.inner_center_card P).le
  | ru => exact cyclic_of_card_le_two (Rudvalis.SylowCenter.sylow_center_card_le_two P)
  | j4 => exact Janko4.sylow_center_isCyclic P
  | j3 => exact (hne rfl).elim

/-- The full Theorem C catalogue reduces to actual nonbinary Lie models
when the two-rank is at least four and a Sylow center is noncyclic. -/
theorem nonbinary_of_rank_center {S : Type*} [Group S] [Finite S]
    (hm : TheoremCModel S) (hr : 4 ≤ primeRank 2 S)
    (hc : ∃ P : Sylow 2 S, ¬ IsCyclic (center P)) : NonbinaryLieModel S := by
  obtain ⟨P,hP⟩ := hc
  cases hm with
  | alternating n hn he =>
    obtain ⟨e⟩ := he
    by_cases h8 : n = 8
    · subst n
      exact (hP (cyclic_center_of_equiv
        (e.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm)
        (fun Q => cyclic_of_card_le_two (BinaryLinear.psl_sylow_center_card_le_two (by decide) Q)) P)).elim
    · have hb := small_alternating_rank (n := n) (by omega)
      rw [←primeRank_equiv 2 e] at hb
      omega
  | linear_odd p k hp ho hk hlarge he =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
    let : Finite (GorensteinWalter.PGL2 F) :=
      Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
    have hb : primeRank 2 PSL(2,F) ≤ 2 :=
      (_root_.primeRank_le_of_injective 2 Matrix.ProjectiveSpecialLinearGroup.toPGL
        Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).trans
          (Theory.PSL2.odd_pgl_two_rank F ⟨p,k,hp,ho,by omega,hF⟩)
    rw [←primeRank_equiv 2 e] at hb
    omega
  | three_odd p hp ho unitary he =>
    cases unitary with
    | false =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
      have hb := Theory.SpecificGroups.OddThreeRank.psl3_primeRank_two_le hp ho hF
      rw [←primeRank_equiv 2 e] at hb
      omega
    | true =>
      obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := he
      have hb := Theory.SpecificGroups.OddThreeRank.psu3_primeRank_two_le J hp ho hF hconj
      rw [←primeRank_equiv 2 e] at hb
      omega
  | rank_one he => exact Or.inl he
  | rank_two he =>
    cases he with
    | linear n hn he =>
      by_cases hn2 : 2 ≤ n
      · exact Or.inr (Or.inl ⟨n,hn2,Or.inl he⟩)
      · have he1 : n = 1 := by omega
        subst n
        exact (hP (binary_linear_cyclic_center (n := 3) (by decide) (by simpa using he) P)).elim
    | symplectic n hn he => exact Or.inr (Or.inl ⟨n,hn,Or.inr (Or.inl he)⟩)
    | g2 n hn he => exact Or.inr (Or.inl ⟨n,hn,Or.inr (Or.inr (Or.inl he))⟩)
    | triality n hn he =>
      by_cases hn2 : 2 ≤ n
      · exact Or.inr (Or.inl ⟨n,hn2,Or.inr (Or.inr (Or.inr he))⟩)
      · have he1 : n = 1 := by omega
        subst n
        exact (hP (binary_triality_cyclic_center (by simpa using he) P)).elim
    | ree m hm he => exact Or.inr (Or.inr ⟨m,hm,he⟩)
    | symplectic_derived he =>
      let e := he.some.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix
      have hb := small_alternating_rank (n := 6) (by omega)
      rw [←primeRank_equiv 2 e] at hb
      omega
    | g2_derived he => exact (hP (cyclic_center_of_equiv he.some binary_g2_cyclic_center P)).elim
    | tits he => exact (hP (cyclic_center_of_equiv
        (he.some.trans Tits.parrottFiniteImageEquiv) tits_cyclic_center P)).elim
  | binary_linear n hn he => exact (hP (binary_linear_cyclic_center (by omega) he P)).elim
  | sporadic name hn he =>
    let : Finite name.Carrier := Finite.of_equiv S he.some.toEquiv
    exact (hP (cyclic_center_of_equiv he.some (sporadic_cyclic_center name hn) P)).elim
  | janko_one he =>
    have hb : primeRank 2 Janko1.Model ≤ 3 := by
      apply primeRank_le_of_prime_pow_not_dvd
      rw [Janko1.card_model]
      norm_num
    rw [←primeRank_equiv 2 he.some] at hb
    omega

/-- In an actual SQTK overgroup, the rank-four and noncyclic-center
restrictions force every ordinary component onto the nonbinary Lie list. -/
theorem component_nonbinary
    {G : Type*} [Group G] [Finite G] (H K : Subgroup G)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hK : IsComponentIn K H)
    (hr : 4 ≤ primeRank 2 (K ⧸ center K))
    (hc : ∃ P : Sylow 2 (K ⧸ center K), ¬ IsCyclic (center P)) :
    NonbinaryLieModel (K ⧸ center K) := by
  let := hK.quasisimple
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hs : IsSQTK KnownSimple.IsKnownSimple K :=
    ⟨hH.stronglyQuasithin.of_injective (inclusion hK.1) (inclusion_injective hK.1),
      hH.isKGroup.of_injective (inclusion hK.1) (inclusion_injective hK.1)⟩
  have hm := Chapter1.QuasisimpleInvolutions.quotient_model hs
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremC_knownSimple
  exact nonbinary_of_rank_center
    (ChapterA.Section03.SourceComponents.sourceTheoremC_to_local
      (Group.IsPerfect.not_isMulCommutative _) hm) hr hc

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryComponentModels
