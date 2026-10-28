module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.Models
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.ActorGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.Models
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.EscapeTransport
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.FixedCentralizer
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.CentralizerPair
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.QuotientFamily
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.NormalizerDiagonal.Overgroups
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.OddSections
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.CentralizerContainment.FiveGeneration.Calculation
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.SimpleSocle
public import GorensteinWalter.LinearThreeEquiv
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup

/-!
# The subfield-centralizer route in the canonical inner extension

Projective descent identifies the pure-field involution centralizer with
PGL₂ of its actual fixed field times the cyclic field factor. Quotient lifting
passes E-generation of that smaller PGL₂ through the normal two-group factor.
For p=3 the smaller group is S₄ and is solvable. For p>5, concrete prime-field
placement combines with the whole-group E2 case to give its E-generation.

Two such literal centralizers generating the model and containing one Sylow
then give escape for every invariant family, by E.1.8 inheritance and the
E-generation identity. This preserves all intrinsic quotients and the actual
Sylow intersections. No chosen actor is asserted to belong to an arbitrary
family.

The final theorem `escape` discharges the centralizer-pair and prime-field
placement premises. In characteristic five it instead uses the proved actor
fusion and centralizer/normalizer joins together with positioned outer-four
generation in S₅. Thus the canonical-model escape conclusion holds for every
odd prime, including 3 and 5, with no additional geometric or generation input.

Source: Aschbacher--Smith, A.2.3(2), E.1.2, E.1.8 and E.1.14(6), printed
pp.33, 210--211 and 214; the last cites Aschbacher (1982), Lemma 4.10.
-/

public section
noncomputable section
open Subgroup GorensteinWalter Matrix
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape
variable {F : Type*} [Field F] [Finite F]

/-- Finiteness used in the smaller projective model input. -/
theorem finiteProjectiveGroup (K : Type*) [Field K] [Finite K] : Finite (PGL2 K) :=
  Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective

attribute [local instance] finiteProjectiveGroup

/-- A direct two-group factor does not increase the E-generation bound. -/
private theorem product_isEGenerated {K C : Type*} [Group K] [Finite K]
    [Group C] [Finite C] (hC : IsPGroup 2 C) (hK : IsEGenerated 1 K) :
    IsEGenerated 1 (K × C) := by
  let f : K × C →* K := MonoidHom.fst K C
  let j : f.ker →* C := (MonoidHom.snd K C).comp f.ker.subtype
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Prod.ext
    · exact x.property.trans y.property.symm
    · exact h
  have hf : Function.Surjective f := fun k => ⟨(k, 1), rfl⟩
  exact IsEGenerated.of_normal_two_subgroup f.ker (hC.of_injective j hj)
    (hK.map_equiv (QuotientGroup.quotientKerEquivOfSurjective f hf).symm)

/-- Application of fixed-subfield descent to the literal pure-field
centralizer. The only generation input is for the smaller prime-field PGL₂. -/
theorem pureCentralizer_isEGenerated {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hσ : orderOf σ = 2)
    [Finite (innerModel F σ)]
    (hK : IsEGenerated 1 (PGL2 (FixedPoints.subfield (zpowers σ) F))) :
    IsEGenerated 1 (centralizer ({pure σ} : Set (innerModel F σ))) := by
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun a : F ≃+* F => (a : F → F)) DFunLike.coe_injective
  have hC : IsPGroup 2 (zpowers σ) := IsPGroup.of_card (n := 1)
    (by simpa only [Nat.card_zpowers, pow_one] using hσ)
  exact (product_isEGenerated hC hK).map_equiv
    (pureCentralizerEquiv hp hodd hF σ hσ).symm

/-- At p=3 the descended PGL₂ is S₄, so the centralizer is solvable and its
rank-one E-generation requires no perfectness assumption. -/
theorem pureCentralizer_isEGenerated_three (hF : Nat.card F = 3 ^ 2)
    (σ : F ≃+* F) (hσ : orderOf σ = 2) [Finite (innerModel F σ)] :
    IsEGenerated 1 (centralizer ({pure σ} : Set (innerModel F σ))) := by
  apply pureCentralizer_isEGenerated Nat.prime_three (by decide) hF σ hσ
  let K := FixedPoints.subfield (zpowers σ) F
  let : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact fixedSubfield_card hF σ ((orderOf_eq_prime_iff (x := σ)).mp hσ).1
      ((orderOf_eq_prime_iff (x := σ)).mp hσ).2
  let e : K ≃+* ZMod 3 := (ZMod.ringEquivOfPrime K Nat.prime_three hc).symm
  let g : PGL2 K ≃* Equiv.Perm (Fin 4) :=
    (pgl2RingEquiv e).trans pgl2_three_equiv_perm
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (PGL2 K) :=
    Group.isSolvable_of_isSolvable_injective (f := g.toMonoidHom) g.injective
  exact isEGenerated_one_of_solvable

/-- Extract a genuine escaping E-member from the literal E-generation
identity, retaining the original invariant family and Sylow subgroup. -/
private theorem escape_of_generated {G : Type*} [Group G] [Finite G]
    (hG : IsEGenerated 1 G) (T : Sylow 2 G) : LargeFamilyEscapeAt T := by
  classical
  intro Ω hΩ _ M _ hM hNM
  by_contra h
  have hEM : eFamilySubgroup 1 (T : Subgroup G) Ω ≤ M := by
    apply iSup_le
    intro B
    apply sSup_le
    intro H hH
    by_contra hHM
    exact h ⟨B.val, B.property.1, B.property.2, H, hH, hHM⟩
  apply hM
  apply top_unique
  rw [← hG T Ω hΩ]
  exact sup_le hEM hNM

omit [Finite F] in
/-- Conditional subfield assembly. The pair consists of the two literal
involution centralizers, both containing one Sylow; their generation and
comparison are separate geometric obligations. No family is replaced by a
chosen rank-three actor. -/
theorem escape_of_subfield_centralizer_pair (σ : F ≃+* F)
    [Finite (innerModel F σ)]
    (hC : IsEGenerated 1 (centralizer ({pure σ} : Set (innerModel F σ))))
    (hpair : HasSubfieldCentralizerPair σ) :
    ∀ T : Sylow 2 (innerModel F σ), LargeFamilyEscapeAt T := by
  obtain ⟨T, z, _, hTC, hTD, hgen, ⟨e⟩⟩ := hpair
  have hD := hC.map_equiv e.symm
  have hS : IsEGenerated 1 (innerModel F σ) := by
    apply IsEGeneratedAt.isEGenerated (T := T)
    intro Ω hΩ
    apply top_unique
    change ⊤ ≤ ChiefOrbit.generationTarget 1 T Ω
    rw [← hgen]
    exact sup_le (ChiefOrbit.overgroup_le_generationTarget T _ hTC hΩ hC)
      (ChiefOrbit.overgroup_le_generationTarget T _ hTD hΩ hD)
  exact escape_of_generated hS

/-- Concrete PGL₂ placement discharges the smaller-field generation input.
The normal simple PSL₂ layer supplies the whole-group E2 member for rank-one
actors; the marked local models supply the other actors' E1 members. -/
theorem projective_isEGenerated_of_geometry (K : Type*) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (hgeometry : ∀ T : Sylow 2 (PGL2 K), PrimeGeometry.ConcreteLocalGeometryAt T) :
    IsEGenerated 1 (PGL2 K) := by
  let i : PSL2 K →* PGL2 K := ProjectiveSpecialLinearGroup.toPGL
  have hi : Function.Injective i := ProjectiveSpecialLinearGroup.toPGL_injective
  have hindex : i.range.index = 2 := pgl2_psl2Range_index_eq_two K hK
  let : i.range.Normal := normal_of_index_eq_two hindex
  let : IsSimpleGroup (PSL2 K) := ProjectiveSpecialLinearGroup.rank_two_simple hcard
  let : Group.IsPerfect (PSL2 K) := psl2_isPerfect_of_card_gt_three K hcard
  let : IsSimpleGroup i.range := (MonoidHom.ofInjective hi).symm.isSimpleGroup
  let : Group.IsPerfect i.range := Group.IsPerfect.ofSurjective
    (f := (MonoidHom.ofInjective hi).toMonoidHom) (MonoidHom.ofInjective hi).surjective
  have hC : centralizer (i.range : Set (PGL2 K)) = ⊥ :=
    pgl2_psl2Range_centralizer_eq_bot K hK
  have hcore : pCore 2 (PGL2 K) = ⊥ :=
    Theory.GroupTheory.SimpleSocle.pCore_eq_bot
      (Theory.GroupTheory.SimpleSocle.radical_eq_bot i.range hC) 2
  let : Theory.GroupTheory.IsQuasisimple (PSL2 K) := ⟨
    ((QuotientGroup.quotientMulEquivOfEq (psl2_center_eq_bot K)).trans
      QuotientGroup.quotientBot).isSimpleGroup⟩
  have hfit := Theory.GroupTheory.generalizedFitting_eq_range_of_quasisimple_index_two
    i hi hindex hcore
  let e : Theory.GroupTheory.generalizedFitting (PGL2 K) ≃* PSL2 K :=
    (MulEquiv.subgroupCongr hfit).trans (MonoidHom.ofInjective hi).symm
  let : IsSimpleGroup (Theory.GroupTheory.generalizedFitting (PGL2 K)) := e.isSimpleGroup
  let : Group.IsPerfect (Theory.GroupTheory.generalizedFitting (PGL2 K)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hquot : IsPGroup 2 (PGL2 K ⧸ i.range) :=
    IsPGroup.of_card (n := 1) (by simpa only [← index_eq_card, pow_one] using hindex)
  apply isEGenerated_of_component_and_large_escape
  · intro T A _ _ hne
    have hgen : Theory.GroupTheory.generalizedFitting (PGL2 K) ⊔
        (T : Subgroup (PGL2 K)) = ⊤ := by
      rw [hfit, sup_comm]
      exact T.sup_eq_top_of_quotient_isPGroup i.range hquot
    exact ValuesEvenClassical.RankOneUpper.eCaseComponent_top
      (Group.IsPerfect.not_isMulCommutative _) T hgen _ A hne
  · intro T
    exact PrimeGeometry.largeFamilyEscapeAt_of_concrete_localModels T hcore
      (fun A hA => pgl2_kleinFour_centralizer_eq_self K hK A hA) (hgeometry T)

/-- The fixed field has p elements, so the existing prime-field placement
producer is precisely the remaining local input for this actual centralizer. -/
theorem pureCentralizer_isEGenerated_of_prime_geometry {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hp5 : 5 < p)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hσ : orderOf σ = 2)
    [Finite (innerModel F σ)]
    (hgeometry : ∀ T : Sylow 2 (PGL2 (FixedPoints.subfield (zpowers σ) F)),
      PrimeGeometry.ConcreteLocalGeometryAt T) :
    IsEGenerated 1 (centralizer ({pure σ} : Set (innerModel F σ))) := by
  apply pureCentralizer_isEGenerated hp hodd hF σ hσ
  have hcard := fixedSubfield_card hF σ ((orderOf_eq_prime_iff (x := σ)).mp hσ).1
    ((orderOf_eq_prime_iff (x := σ)).mp hσ).2
  exact projective_isEGenerated_of_geometry _
    ⟨p, 1, hp, hodd, le_rfl, by simpa using hcard⟩ (by omega) hgeometry

/-- All non-five characteristics reduce to the actual centralizer pair and
prime-field PGL₂ placement. At p=3 solvability discharges the smaller model;
for p>5 the independent prime-field geometry producer supplies it. -/
theorem escape_of_pair_and_prime_geometry {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hpne : p ≠ 5) (hF : Nat.card F = p ^ 2)
    (σ : F ≃+* F) (hσ : orderOf σ = 2) [Finite (innerModel F σ)]
    (hpair : HasSubfieldCentralizerPair σ)
    (hgeometry : 5 < p → ∀ T : Sylow 2 (PGL2 (FixedPoints.subfield (zpowers σ) F)),
      PrimeGeometry.ConcreteLocalGeometryAt T) :
    ∀ T : Sylow 2 (innerModel F σ), LargeFamilyEscapeAt T := by
  apply escape_of_subfield_centralizer_pair σ _ hpair
  by_cases hp3 : p = 3
  · subst p
    exact pureCentralizer_isEGenerated_three hF σ hσ
  · have hp5 : 5 < p := by
      have hp2 := hp.two_le
      obtain ⟨k, hk⟩ := hodd
      omega
    exact pureCentralizer_isEGenerated_of_prime_geometry hp hodd hp5 hF σ hσ
      (hgeometry hp5)

/-- Escape in the canonical extension of PSL₂(p²) by the supplied pure field
involution, for every odd prime p and every Sylow two-subgroup. This discharges
the inner-model input of the pure-field model assembly. All invariant families
and proper overgroups in `LargeFamilyEscapeAt` are retained, including both
rank-two and rank-three actors. The source bound p² > 5 follows already from
p being an odd prime; no generation, placement or escape premise remains. -/
theorem escape {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hsq : σ ^ 2 = 1) (hne : σ ≠ 1)
    [Finite (innerModel F σ)] :
    ∀ T : Sylow 2 (innerModel F σ), LargeFamilyEscapeAt T := by
  by_cases hp5 : p = 5
  · subst p
    exact TwentyFive.escape hF σ hsq hne
      PSUThreeGeneration.OuterFamilies.EightActors.FiveGeneration.positioned_four_generation
  · have hσ : orderOf σ = 2 := (orderOf_eq_prime_iff (x := σ)).mpr ⟨hsq, hne⟩
    apply escape_of_pair_and_prime_geometry hp hodd hp5 hF σ hσ
      (CentralizerPair.hasSubfieldCentralizerPair hp hodd hF σ hσ)
    intro hlarge T
    exact PrimeGeometry.Diagonal.concreteLocalGeometryAt_of_prime_field hp hodd hlarge
      (fixedSubfield_card hF σ hsq hne) (MulEquiv.refl _) T

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape
