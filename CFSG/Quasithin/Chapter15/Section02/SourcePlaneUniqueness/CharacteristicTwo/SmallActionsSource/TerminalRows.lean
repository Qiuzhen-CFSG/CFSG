module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.TerminalExterior
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.TerminalExclusion

/-!
# Terminal row exclusions from the original wreath residual

The actual K = O²(H) has three-rank two by the original wreath quotient.
This is the only use of the S₃-square KS quotient in the natural-plus-dual,
repeated-natural-four and orthogonal-six exclusions. Apply the existing
seed geometry and offender calculations directly with that rank.
Together with the already proved exterior-five exclusion, the literal
binary component therefore has the degree-five repeated-natural action,
its original point-parabolic marking and K_I/O₂(K_I) ≅ SL₄(2).

No pair-quotient or S-reducibility premise is used in this reduction.
The natural-five S-action and marked-factor assembly remain separate
obligations in SmallActionsSource. Earlier component and plane premises
retain their existing source producers and final discharge by plane uniqueness.

Source: Aschbacher--Smith15.2.23(a)--(d), printed pp.1116--1117,
refs/quasithin.pdf. The proofs specialize the existing TerminalLinear
row calculations with their rank premise discharged by the wreath residual.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open Section01 PlaneUniquenessPreceding ChapterB.QuasisimpleSource

/-- The generating natural-dual seed contradicts the actual wreath residual rank. -/
theorem false_of_naturalDual_generated_on_U_from_wreath
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {M Mc V H ZS X : Subgroup G}
    {hsource : ChosenSmallSource T M Mc V}
    (d : PlaneUniquenessPreceding hsource H ZS)
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    [IsElementaryAbelian 2 (U X ZS)]
    (σ : Representation (ZMod 2) (X ⧸ pCore 2 X) (Additive (U X ZS)))
    (hσ : ∀ (x : X) (u : Additive (U X ZS)),
      ((σ (QuotientGroup.mk' (pCore 2 X) x) u).toMul : G) =
        (x : G) * (u.toMul : G) * (x : G)⁻¹)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hnat : IsNaturalPlusDual σ n)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype ≤ planeSylow T ZS)
    (hgen :
      let Z := AddSubgroup.toZModSubmodule 2 (ZS.subgroupOf (U X ZS)).toAddSubgroup
      (⨆ g : X ⧸ pCore 2 X, Z.map (σ g)) = ⊤) : False := by
  let q := QuotientGroup.mk' (pCore 2 X)
  let P := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let Z := AddSubgroup.toZModSubmodule 2 (ZS.subgroupOf (U X ZS)).toAddSubgroup
  have hfix (x : X) (hc : (x : G) ∈ centralizer (ZS : Set G))
      (u : Additive (U X ZS)) (hu : u ∈ Z) : σ (q x) u = u := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hσ]
    have hh : (u.toMul : G) * (x : G) = (x : G) * (u.toMul : G) := hc _ hu
    rw [← hh, mul_inv_cancel_right]
  have hZ : Z ≤ fixedSpace σ P := by
    intro u hu p
    obtain ⟨x,hx,he⟩ := p.property
    change σ (p : X ⧸ pCore 2 X) u = u
    rw [← he]
    exact hfix x (hS (mem_map_of_mem X.subtype hx)).2 u hu
  let A := (((pResidual 2 H).map H.subtype).subgroupOf X).map q
  have hr : 2 ≤ primeRank 3 A := by
    rw [Theory.GroupTheory.ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) q
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup),
      primeRank_equiv 3 (subgroupOfEquivOfLe hKX)]
    exact (PlaneUniquenessPreceding.LinearThree.residual_rank_two d).symm.le
  apply naturalDual_not_le_seedCentralizer hn hnat P Z hZ hgen A hr
  rintro _ ⟨x,hx,rfl⟩
  exact ⟨mem_top _, hfix x (d.residual_centralizes hx)⟩

/-- The degree-four natural row contradicts the actual wreath residual rank. -/
theorem not_repeatedNatural_four_canonical_from_wreath
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
    {hsource : ChosenSmallSource T M Mc V}
    (d : PlaneUniquenessPreceding hsource H ZS)
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    (r : ℕ) (hr : 0 < r) :
    letI := U_elementary d hI hfit hXI
    ¬ Nonempty (ActionEquiv (U_representation d hI hfit hXI hn)
      (repeated (linearNatural BinaryField.two 4) r)) := by
  let := U_elementary d hI hfit hXI
  rintro ⟨e⟩
  let σ := U_representation d hI hfit hXI hn
  let q := QuotientGroup.mk' (pCore 2 X)
  let Z := AddSubgroup.toZModSubmodule 2 (ZS.subgroupOf (U X ZS)).toAddSubgroup
  let A := (((pResidual 2 H).map H.subtype).subgroupOf X).map q
  have hA : 2 ≤ primeRank 3 A := by
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) q
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup),
      primeRank_equiv 3 (subgroupOfEquivOfLe hKX)]
    exact (PlaneUniquenessPreceding.LinearThree.residual_rank_two d).symm.le
  apply repeatedNatural_four_not_le_seedCentralizer σ r hr e Z
    (U_seed_module_generates d hI hfit hXI hn σ
      (U_representation_apply d hI hfit hXI hn)) A hA
  rintro _ ⟨x,hx,rfl⟩
  refine ⟨mem_top _, ?_⟩
  intro u hu
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [U_representation_apply]
  have hh : (u.toMul : G) * (x : G) = (x : G) * (u.toMul : G) :=
    d.residual_centralizes hx _ hu
  rw [← hh, mul_inv_cancel_right]

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

/-- The original orthogonal offender contradiction uses the actual residual rank. -/
theorem not_orthogonalSix_canonical_from_wreath
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
 :
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
    exact ((PlaneUniquenessPreceding.LinearThree.residual_rank_two d).symm.le).trans h
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

include d
/-- The canonical natural-plus-dual row is excluded by the actual residual rank. -/
theorem not_naturalDual_from_wreath
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    (n : ℕ) (hdegree : n = 4 ∨ n = 5) :
    letI := U_elementary d hI hfit hXI
    ¬ IsNaturalPlusDual (U_representation d hI hfit hXI hn) n := by
  let := U_elementary d hI hfit hXI
  intro he
  let : (X.subgroupOf I).Normal := normal_subgroupOf_of_le_normalizer hn
  obtain ⟨S,hS⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    (d.sylow_in_escape hI) hXI (inferInstance : (X.subgroupOf I).Normal).isSubnormal
  exact false_of_naturalDual_generated_on_U_from_wreath d hKX
    (U_representation d hI hfit hXI hn) (U_representation_apply d hI hfit hXI hn)
    hdegree he S (hS.le.trans inf_le_left)
    (U_seed_module_generates d hI hfit hXI hn _ (U_representation_apply d hI hfit hXI hn))

/-- All other original module rows are excluded without the KS pair quotient. -/
theorem repeatedNatural_of_rows_from_wreath
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (hX : X = (primeToResidual 3 I).map I.subtype)
    (hKX : (pResidual 2 H).map H.subtype ≤ X) :
    letI := U_elementary d hI hfit hXI
    let σ := U_representation d hI hfit hXI hn
    ModuleRow σ →
      Nonempty ((KI X ZS ⧸ pCore 2 (KI X ZS)) ≃*
        Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
      ∃ r : ℕ, 0 < r ∧ r ≤ 4 ∧
        ∃ e : ActionEquiv σ (repeated (linearNatural BinaryField.two 5) r),
        ∃ v : Fin 5 → ZMod 2, v ≠ 0 ∧
          (((M1 X ZS).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
            e.groupEquiv.toMonoidHom =
              MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) v := by
  let := U_elementary d hI hfit hXI
  dsimp only
  intro hrow
  cases hrow with
  | repeatedNatural n r hd hp hb e =>
    rcases hd with rfl | rfl
    · exact (not_repeatedNatural_four_canonical_from_wreath d hI hfit hXI hn hKX r hp ⟨e⟩).elim
    · obtain ⟨v,hv,hm⟩ := M1_image_pointStabilizer_of_repeatedNatural d hI hfit hXI hn (by decide) hp e
      exact ⟨KI_quotient_of_point_image e.groupEquiv v hv hm,r,hp,hb,e,v,hv,hm⟩
  | naturalDual n hd he => exact (not_naturalDual_from_wreath d hI hfit hXI hn hKX n hd he).elim
  | orthogonalSix C hc e =>
    exact (not_orthogonalSix_canonical_from_wreath d hI hfit hXI hn hout hKX C hc ⟨e⟩).elim
  | exteriorFive r hd hi hf e =>
    exact (not_exteriorFive_from_preceding d hI hfit hXI hn hX hKX hd ⟨e⟩).elim

/-- Actual terminal binary component, retaining its literal U, M₁ and K_I.
The module classification and all other rows are discharged without hpair. -/
theorem binaryBranch_repeatedNatural_from_wreath
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    {n : ℕ} (b : BinaryBranch M I X n)
    (hX : X = (primeToResidual 3 I).map I.subtype)
    (hKX : (pResidual 2 H).map H.subtype ≤ X) :
    letI := U_elementary d hI hfit b.source.component.1
    let σ := U_representation d hI hfit b.source.component.1 hn
    Nonempty ((KI X ZS ⧸ pCore 2 (KI X ZS)) ≃*
      Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
      ∃ r : ℕ, 0 < r ∧ r ≤ 4 ∧
        ∃ e : ActionEquiv σ (repeated (linearNatural BinaryField.two 5) r),
        ∃ v : Fin 5 → ZMod 2, v ≠ 0 ∧
          (((M1 X ZS).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
            e.groupEquiv.toMonoidHom =
              MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) v := by
  let := U_elementary d hI hfit b.source.component.1
  exact repeatedNatural_of_rows_from_wreath d hI hfit b.source.component.1 hn hout hX hKX
    (moduleRow_of_binaryBranch d hI hfit hn hout b)

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
