module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.OrthogonalTransport
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.OrthogonalSeed
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.OrthogonalCore
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Exclusions
public import Theory.SpecificGroups.SymmetricEight.CentralPair
public import Theory.GroupTheory.PrimeRankSquareFree

/-!
# Excluding the original orthogonal-six row

The original seed supplies a nonzero Sylow-fixed quotient vector. Its full
permutation stabilizer is a conjugate four-block stabilizer. The image of
KS ∩ XQI contains a Sylow subgroup of A₈ and has cubic rank at least two,
so its order is divisible by 64·9 = 576. It is therefore normal in the
four-block stabilizer of order 1152. The image of QI, a normal two-subgroup
of this original normalizer, lies in its intrinsic two-core. The genuine
Thompson offender constructed on U survives on U/C_U(X), contradicting
B.3.2(6). All action, core and parabolic transports are discharged here.

The earlier component clauses are supplied by
`qt-e-152-char2-component-models`; the S₃-square clause belongs to
`qt-e-152-small-parabolic`. Their final discharge remains with
`qt-e-152-plane-uniqueness`. The original-U classification and the other
two terminal rows are not asserted here.

Source: Aschbacher--Smith 15.2.23(c), printed p.1117.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open Section01 PlaneUniquenessPreceding ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

/-- The orthogonal row is impossible on the original quotient action, with
only the earlier component and small-parabolic source clauses explicit. -/
theorem not_orthogonalSix_canonical
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    (hpair : Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    letI := U_elementary d hI hfit hXI
    ∀ (C : Subrepresentation (U_representation d hI hfit hXI hn)),
      C.toSubmodule = fixedSpace (U_representation d hI hfit hXI hn) ⊤ →
      ¬ Nonempty (ActionEquiv C.quotientRepresentation (alternatingNatural 8)) := by
  let := U_elementary d hI hfit hXI
  intro C hC ⟨e⟩
  let E := X ⊔ QI H T ZS
  let N := (KS H T ZS).subgroupOf E
  let R := (QI H T ZS).subgroupOf E
  let K := (pResidual 2 H).map H.subtype
  let : (X.subgroupOf I).Normal := normal_subgroupOf_of_le_normalizer hn
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    (d.sylow_in_escape hI) hXI (inferInstance : (X.subgroupOf I).Normal).isSubnormal
  have hPS : (P : Subgroup X).map X.subtype ≤ planeSylow T ZS := hP.le.trans inf_le_left
  obtain ⟨u,hu,_,r,hr⟩ := exists_orthogonal_seed_marking d hI hfit hXI hn P hPS C e
  obtain ⟨f,hker,hfX,hf,A,hA,hoff⟩ :=
    exists_orthogonal_permutation_offender d hI hfit hXI hn hout hKX C hC e
  let c := (MulAut.conj r.val).toMonoidHom
  let f' := c.comp f
  let J := N.map f'
  let B := R.map f'
  have hJ : J ≤ Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.fourStabilizer := by
    rintro _ ⟨g,hg,rfl⟩
    apply (hr (f g)).mp
    have hgZ : (g : G) ∈ centralizer (ZS : Set G) :=
      (sup_le d.residual_centralizes inf_le_right) hg
    have hgu : U_extensionRepresentation d hI hn g u = u := by
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [U_extensionRepresentation_apply d hI hn]
      have hc : (u.toMul : G) * (g : G) = (g : G) * (u.toMul : G) :=
        hgZ u.toMul hu
      rw [← hc, mul_inv_cancel_right]
    exact (hf g u).symm.trans (congrArg (fun v => e.linearEquiv (C.toSubmodule.mkQ v)) hgu)
  have hfaith := faithful_of_orthogonalSix_quotient C e
  have hp : IsPGroup 2 (E ⊓ centralizer (U X ZS : Set G) : Subgroup G) :=
    extension_kernel_isTwoGroup d hI hXI hn
      (U_centralizer_le_core_of_faithful d hI hfit hXI hn hfaith)
  have hpker : IsPGroup 2 f'.ker := by
    let j : f'.ker →* (E ⊓ centralizer (U X ZS : Set G) : Subgroup G) :=
      (E.subtype.comp f'.ker.subtype).codRestrict _ (by
        intro x
        refine ⟨x.val.property, ?_⟩
        have hx : f x.val = 1 := (MulAut.conj r.val).map_eq_one_iff.mp x.property
        exact (hker ▸ hx : x.val ∈ (centralizer (U X ZS : Set G)).subgroupOf E))
    exact hp.of_injective j (by
      intro a b he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg
        (fun z : (E ⊓ centralizer (U X ZS : Set G) : Subgroup G) => (z : G)) he)
  have hKE : K ≤ E := hKX.trans le_sup_left
  have hKN : K.subgroupOf E ≤ N := fun _ hx => mem_sup_left hx
  have hrN : 2 ≤ primeRank 3 N := by
    have h := primeRank_mono 3 hKN
    rw [primeRank_equiv 3 (subgroupOfEquivOfLe hKE)] at h
    exact (K_threeRank_ge_two d hpair).trans h
  have hrJ : 2 ≤ primeRank 3 J := by
    rw [show J = N.map f' from rfl,
      ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) f' hpker]
    exact hrN
  have h9 : 9 ∣ Nat.card J := by
    by_contra hh
    have h := primeRank_le_one_of_square_not_dvd (p := 3) hh
    omega
  let q := e.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  let Q := P.mapSurjective (f := q)
    (e.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _))
  let a := c.comp (alternatingGroup (Fin 8)).subtype
  have ha : Function.Injective a :=
    (MulAut.conj r.val).injective.comp (alternatingGroup (Fin 8)).subtype_injective
  have hQJ : (Q : Subgroup (alternatingGroup (Fin 8))).map a ≤ J := by
    rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    refine ⟨inclusion le_sup_left x, ?_, ?_⟩
    · exact mem_sup_right (hPS (mem_map_of_mem X.subtype hx))
    · exact congrArg c (hfX x)
  have h64 : 64 ∣ Nat.card J := by
    have h := card_dvd_of_le hQJ
    rw [card_map_of_injective ha,
      Theory.SpecificGroups.SymmetricEight.CentralPair.sylow_card Q] at h
    exact h
  have hcard : 576 ∣ Nat.card J :=
    (show Nat.Coprime 64 9 by decide).mul_dvd_of_dvd_of_dvd h64 h9
  have hRN : R ≤ N := fun _ hx => pCoreIn_le 2 (KS H T ZS) hx
  have hnR : N ≤ normalizer (R : Set E) := by
    have hnQI : KS H T ZS ≤ normalizer (QI H T ZS : Set G) :=
      (KS H T ZS).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
    apply le_normalizer_iff.mpr
    intro g hg x hx
    exact (mem_normalizer_iff.mp (hnQI hg) (x : G)).mp hx
  have hnB : J ≤ normalizer (B : Set (Equiv.Perm (Fin 8))) :=
    (map_mono hnR).trans (R.le_normalizer_map f')
  have hB : IsPGroup 2 B :=
    ((isPGroup_pCoreIn 2 (KS H T ZS)).comap_subtype).map f'
  have hc := OrthogonalModel.le_fourBlockCore_of_large_normalizer J B hJ hcard
    (map_mono hRN) hB hnB
  have hmodel : IsOffender (BinaryPermutation.naturalRepresentation (Fin 8))
      ((A.map f).map c) := by
    refine ⟨hoff.1.map_conj r.val, ?_⟩
    rw [fixedCodim_map_conj, rank_map_conj]
    exact hoff.2
  rw [Subgroup.map_map] at hmodel
  change IsOffender (BinaryPermutation.naturalRepresentation (Fin 8))
    (A.map f') at hmodel
  exact OrthogonalModel.not_isOffender_of_le_fourBlockCore _
    ((map_mono hA.1).trans hc) hmodel

/-- The literal four-row consumer now leaves only the repeated-natural and
exterior-five branches. Recognition of the rows and these final two exclusions
remain with this theorem family's assembly owner. -/
theorem remaining_rows_after_orthogonal
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    (hpair : Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    letI := U_elementary d hI hfit hXI
    let σ := U_representation d hI hfit hXI hn
    ModuleRow σ →
      (∃ n r : ℕ, (n = 4 ∨ n = 5) ∧ 0 < r ∧ r ≤ n - 1 ∧
        Nonempty (ActionEquiv σ (repeated (linearNatural BinaryField.two n) r))) ∨
      (∃ r : ℕ, (r = 2 ∨ r = 3) ∧ IsIrreducible σ ∧
        Module.finrank (ZMod 2) (Additive (U X ZS)) = 10 ∧
        Nonempty (ActionEquiv σ (Representation.SL5TenDimensional.exteriorAction r))) := by
  let := U_elementary d hI hfit hXI
  dsimp only
  intro hrow
  rcases remaining_rows_of_source d hI hfit hXI hn hKX hpair hrow with h | h | h
  · exact Or.inl h
  · obtain ⟨C,hC,he⟩ := h
    exact (not_orthogonalSix_canonical d hI hfit hXI hn hout hKX hpair C hC he).elim
  · exact Or.inr h

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
