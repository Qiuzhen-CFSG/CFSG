module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Contracts
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.NormalizerRows
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex.CentralizerSylow
public import Theory.GroupTheory.PGroup.NormalSubgroupUpperCentralBound
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.Proper
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixCatalogue
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.SylowEightRigidity.ProfileCertificates

/-!
# Recognizing maximal J₄ normal-eight overgroups by concrete normalizers

The certified reference matrix two-subgroup and the supplied ambient Sylow
have the same full two-part. They are both Sylow in the actual model, so
Sylow conjugacy gives an ambient conjugating element. Pulling the supplied
normal eight back along this conjugation preserves its relative normality,
elementary structure, cardinality, and literal ambient image. The general
normal p-subgroup bound places it in the third upper central term.

The exhaustive intrinsic catalogue selects one of three normal eights.
`Eight.MatrixCatalogue` identifies its marked subgroups with the literal
matrix-word subgroups in the ambient normalizer calculation. Those bounds
either place the normalizer in a conjugate of literal max4, or put it strictly
inside a proper subgroup. Maximality gives the actual max4 isomorphism in
the first case and a contradiction in the second. `Eight.Proper` discharges
properness of max4 without any simplicity hypothesis.

The final `normalEightRecognition` supplies both the catalogue and normalizer
bounds to the retained conditional assembly. Its normal elementary eight is
the explicit input in the published contract; structural existence in an
arbitrary maximal subgroup and max4 quotient identification are separate.

Source: Aschbacher–Smith A.3.12, printed pp.47–48, citing Aschbacher,
*Overgroups of Sylow subgroups in sporadic groups* (1986); Kleidman–Wilson,
*The maximal subgroups of J4* (1988), pp.484–510. The literal ATLAS program
and its attribution are in `SymmetricLinear.Model`.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
open Janko4 Janko4.LocalStructure.SymmetricLinear Janko4.OuterReduction.OddIndex
open CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover
attribute [local irreducible] Janko4.modelGroup matrixA matrixB

/-- Transport to the actual fixed Sylow, including the ambient image and Z3 bound. -/
theorem normal_eight_reference_transport
    (S : Sylow 2 Model) (M : Subgroup Model) (hSM : S.toSubgroup ≤ M)
    (E : Subgroup M) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 8) :
    ∃ (g : Model) (A : Subgroup SylowEightModel),
      A.Normal ∧ IsElementaryAbelian 2 A ∧ Nat.card A = 8 ∧
      A ≤ Subgroup.upperCentralSeries SylowEightModel 3 ∧
      (A.map SylowEightModel.subtype).map (MulAut.conj g).toMonoidHom = E.map M.subtype := by
  let Q : Sylow 2 Model := Sylow.ofCard twoSubgroup
    (twoSubgroup_card.trans ((ambient_sylow_card S).symm.trans S.card_eq_multiplicity))
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Model Q S
  have hQS : twoSubgroup.map (MulAut.conj g).toMonoidHom = S.toSubgroup :=
    congrArg Sylow.toSubgroup hg
  let j : SylowEightModel →* Model :=
    (MulAut.conj g).toMonoidHom.comp SylowEightModel.subtype
  let f : SylowEightModel →* M := j.codRestrict M (by
    intro p
    apply hSM
    rw [← hQS]
    exact mem_map_of_mem _ p.property)
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext ((MulAut.conj g).injective (congrArg Subtype.val hxy))
  have hEP : E ≤ (S.subtype hSM).toSubgroup :=
    (IsElementaryAbelian.isPGroup 2 E).le_sylow_of_normal _
  have hErange : E ≤ f.range := by
    intro e he
    have heS : (e : Model) ∈ S.toSubgroup := hEP he
    rw [← hQS] at heS
    obtain ⟨p, hp, heq⟩ := heS
    exact ⟨⟨p, hp⟩, Subtype.ext heq⟩
  let A : Subgroup SylowEightModel := E.comap f
  have hAf : A.map f = E := map_comap_eq_self hErange
  have hAelem : IsElementaryAbelian 2 A := {
    toIsMulCommutative := E.comap_injective_isMulCommutative hf
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Subtype.ext
      apply hf
      change f ((x : SylowEightModel) ^ 2) = f 1
      rw [map_pow, map_one]
      exact elemPow_eq_one_of_isElementaryAbelian (f x) x.property) }
  have hAcard : Nat.card A = 8 := by
    calc
      Nat.card A = Nat.card (A.map f) := (card_map_of_injective hf).symm
      _ = 8 := by rw [hAf, hE]
  have hAZ : A ≤ Subgroup.upperCentralSeries SylowEightModel 3 :=
    le_upperCentralSeries_of_card_eq_prime_pow twoSubgroup_isPGroup A (by
      simpa using hAcard)
  refine ⟨g, A, inferInstance, hAelem, hAcard, hAZ, ?_⟩
  rw [map_map]
  change A.map (M.subtype.comp f) = E.map M.subtype
  rw [← map_map, hAf]

private theorem map_ne_top (H : Subgroup Model) (hH : H ≠ ⊤) (e : Model ≃* Model) :
    H.map e.toMonoidHom ≠ ⊤ := by
  intro ht
  apply hH
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [ht, map_top_of_surjective _ e.surjective]

/-- A bound on the actual ambient normalizer recognizes a maximal overgroup. -/
theorem recognition_of_eight_normalizer_alternative
    (M : Subgroup Model) (hM : IsCoatom M) (E : Subgroup M) [E.Normal]
    (U : Subgroup Model) (g : Model)
    (himage : U.map (MulAut.conj g).toMonoidHom = E.map M.subtype)
    (hU : EightNormalizerAlternative U) : Nonempty (M ≃* max4Subgroup) := by
  have hMN : M ≤ (normalizer (U : Set Model)).map (MulAut.conj g).toMonoidHom := by
    rw [map_equiv_normalizer_eq, himage]
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      E.le_normalizer_map M.subtype
  rcases hU with ⟨k, hNk⟩ | ⟨H, hNH, hH⟩
  · let K := max4Subgroup.map (MulAut.conj k).toMonoidHom
    have hK : K ≠ ⊤ := map_ne_top max4Subgroup literal_max4_ne_top (MulAut.conj k)
    have hKM : K.map (MulAut.conj g).toMonoidHom = M :=
      (hM.le_iff_eq (map_ne_top K hK (MulAut.conj g))).mp
        (hMN.trans (map_mono hNk))
    exact ⟨(MulEquiv.subgroupCongr hKM.symm).trans
      (((MulAut.conj g).subgroupMap K).symm.trans
        ((MulAut.conj k).subgroupMap max4Subgroup).symm)⟩
  · have hHM : H.map (MulAut.conj g).toMonoidHom = M :=
      (hM.le_iff_eq (map_ne_top H hH (MulAut.conj g))).mp
        (hMN.trans (map_mono hNH.le))
    have hHN : H ≤ normalizer (U : Set Model) := by
      apply (map_le_map_iff_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).mp
      rw [hHM]
      exact hMN
    exact (hNH.not_ge hHN).elim

/-- Assembly from exhaustive intrinsic profiles and independent ambient normalizer bounds. -/
theorem normalEightRecognition_of_catalogue_and_normalizerRows
    (hcatalogue : Max4SylowEightCentralizerCertificates)
    (hrows : SylowEightNormalizerRows) : NormalEightRecognition := by
  intro S M hM hSM E hEn hEe hEc
  let := hEn
  let := hEe
  obtain ⟨g, A, hAn, hAe, hAc, hAZ, himage⟩ :=
    normal_eight_reference_transport S M hSM E hEc
  obtain ⟨family, hcover, hprofile⟩ := hcatalogue
  obtain ⟨i, hi⟩ := hcover A hAn hAe hAc hAZ
  have hAi : centralizerLowerCentralCard A 2 = normalEightCentralizerOrder i := by
    rw [hi]
    exact hprofile i
  exact recognition_of_eight_normalizer_alternative M hM E _ g himage
    (hrows A hAn hAe hAc hAZ i hAi)

/-- The checked literal catalogue discharges the ambient-normalizer row contract. -/
theorem sylowEightNormalizerRows : SylowEightNormalizerRows :=
  MatrixNormalizerBounds.sylowEightNormalizerRows_of_coverage
    MatrixNormalizerBounds.literal_family_coverage

/-- A maximal Sylow overgroup with a normal elementary eight is isomorphic
to the literal ATLAS max4 subgroup, with all catalogue and normalizer inputs discharged. -/
theorem normalEightRecognition : NormalEightRecognition :=
  normalEightRecognition_of_catalogue_and_normalizerRows
    max4SylowEightCentralizerCertificates sylowEightNormalizerRows

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
