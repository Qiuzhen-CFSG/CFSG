module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.PSL2Recognition
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Orthogonal
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Natural.Generation
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.SourceCase

/-!
# Source assembly for the rank-one module families

The PSL₂ recognition theorem constructs the actual natural or Hermitian
intertwiner. Applying the model calculations now gives the natural branch's
unique Sylow offender and global offender subgroup, and the orthogonal
branch's exact odd/even-extension ratios. The two A₅ modules retain distinct
Schur fields; the orthogonal endpoint includes the actual S₅ action and its
commuting-transposition best offenders. The recognized orthogonal model also
supplies the re-exported Sylow partition, transvection, centralizer and actor
calculations, with no further recognition premise.

For PSU₃, the only explicit earlier input is the group-only covering theorem:
the given projective model must present the layer as a central quotient of
its full SU₃ group. Recognition then proves the covering kernel trivial and
supplies the natural coordinates. The assembly retains the cubic center,
the fixed-field parameter, both ratios, the literal omega subgroup, and the
compatible outer involution action on both matrices and columns. Producing
the cover remains with `qt-b01-ff-classical-even-cover-lifting`; the conditional
unitary theorem below does not assert that this source obligation is finished.

The orthogonal threshold family retains D.2.1's definition. As explained in
`Orthogonal`, the printed universal conjugacy assertion at the end of K.3.1.2
is incompatible with the preceding rank-s, ratio-two subgroup. The correct
threshold and minimizing classifications are re-exported separately.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.3.1 and K.3.3,
printed pp.453–454 and 456. The representation-theoretic inputs corresponding
to Guralnick–Malle [GM04] are proved in the imported recognition modules.
-/

public section
open scoped MatrixGroups MonoidAlgebra ENNReal
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterK.RankOne
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The natural source branch, with the field degree and the global
best-offender subgroup expressed in the original group. -/
theorem SourceHypotheses.natural_source_case
    {K : Type*} [Field K] [Finite K] [Algebra (ZMod 2) K]
    (h : SourceHypotheses ρ L) (M : NaturalModel (F := K) ρ L)
    {r : ℕ} (hr : 2 ≤ r) (hc : Nat.card K = 2 ^ r) :
    quadraticRatio ρ = 1 ∧ cubicRatio ρ = 1 ∧ offenderSubgroup ρ = L ∧
    (∀ T : Sylow 2 G,
      IsQuadratic ρ ((T : Subgroup G) ⊓ L) ∧
      rank ((T : Subgroup G) ⊓ L) = r ∧
      fixedCodim ρ ((T : Subgroup G) ⊓ L) = r ∧
      subspaceCommutator ρ ⊤ ((T : Subgroup G) ⊓ L) =
        fixedSpace ρ ((T : Subgroup G) ⊓ L) ∧
      (∀ A : Subgroup G, A ≤ T →
        (IsOffender ρ A ↔ A = (T : Subgroup G) ⊓ L)) ∧
      generatedBy {A | IsBestOffender ρ A} (T : Subgroup G) = (T : Subgroup G) ⊓ L) ∧
    (∀ g : G, ∃ σ : K ≃+* K, ∀ (c : K) (v : Fin 2 → K),
      M.coordinateAction g (c • v) = σ c • M.coordinateAction g v) ∧
    (∀ t : G, t ^ 2 = 1 → t ∉ L →
      ∃ σ : K ≃+* K, σ ≠ RingEquiv.refl K ∧ ∀ (c : K) (v : Fin 2 → K),
        M.coordinateAction t (c • v) = σ c • M.coordinateAction t v) := by
  let : L.Normal := h.layer_normal
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  have hKr : Module.finrank (ZMod 2) K = r :=
    Nat.pow_right_injective (by decide : 2 ≤ 2)
      ((FiniteField.pow_finrank_eq_natCard 2 K).trans hc)
  have hK : 2 < Nat.card K := by
    rw [hc]
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hr
    norm_num at this ⊢
    omega
  have hrat := M.ratios_eq_one hK h.faithful
  refine ⟨hrat.1, hrat.2, h.natural_offenderSubgroup_eq_layer M hK,
    ?_, M.semilinear, fun t ht htL => M.outer_involution_field_part h.faithful ht htL⟩
  intro T
  have hcalc := M.sylowInf_calculation T
  rw [hKr] at hcalc
  exact ⟨hcalc.1, hcalc.2.1, hcalc.2.2, M.sylowInf_commutator_eq_fixedSpace T,
    fun _ hAT => M.offender_iff_eq_sylowInf hK h.faithful T hAT,
    M.generatedBy_bestOffenders_sylow hK h.faithful T⟩

/-- K.3.1 with both recognition and the ratio calculations discharged.
The two branches retain their actual intertwiners and Schur fields. The
orthogonal endpoint is the genuine alternating/symmetric five-point action,
so it is never merged with the natural module at field order four. -/
theorem SourceHypotheses.psl2_case
    (h : SourceHypotheses ρ L) {r : ℕ} (hr : 2 ≤ r)
    (hq : ClassicalGroup.IsPSL (L ⧸ Subgroup.center L) 2 (2 ^ r)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2 ^ r ∧ ∃ e : L ≃* SL(2,K),
      let σ : Representation (ZMod 2) SL(2,K) V :=
        (ρ.comp L.subtype).comp e.symm.toMonoidHom
      let E := Module.End (ZMod 2)[SL(2,K)] σ.asModule
      let d := Module.finrank (ZMod 2) E
      letI : Algebra (ZMod 2) K := ZMod.algebra K 2
      Module.finrank (ZMod 2) V = 2 * r ∧
      ((d = r ∧ Nonempty (E ≃+* K) ∧ ∃ M : NaturalModel (F := K) ρ L,
        quadraticRatio ρ = 1 ∧ cubicRatio ρ = 1 ∧ offenderSubgroup ρ = L ∧
        (∀ T : Sylow 2 G,
          IsQuadratic ρ ((T : Subgroup G) ⊓ L) ∧
          rank ((T : Subgroup G) ⊓ L) = r ∧
          fixedCodim ρ ((T : Subgroup G) ⊓ L) = r ∧
          subspaceCommutator ρ ⊤ ((T : Subgroup G) ⊓ L) =
            fixedSpace ρ ((T : Subgroup G) ⊓ L) ∧
          (∀ A : Subgroup G, A ≤ T →
            (IsOffender ρ A ↔ A = (T : Subgroup G) ⊓ L)) ∧
          generatedBy {A | IsBestOffender ρ A} (T : Subgroup G) = (T : Subgroup G) ⊓ L) ∧
        (∀ g : G, ∃ τ : K ≃+* K, ∀ (c : K) (v : Fin 2 → K),
          M.coordinateAction g (c • v) = τ c • M.coordinateAction g v) ∧
        (∀ t : G, t ^ 2 = 1 → t ∉ L →
          ∃ τ : K ≃+* K, τ ≠ RingEquiv.refl K ∧ ∀ (c : K) (v : Fin 2 → K),
            M.coordinateAction t (c • v) = τ c • M.coordinateAction t v)) ∨
      ∃ s : ℕ, r = 2 * s ∧ d = s ∧ ∃ hs : 0 < s,
        letI : NeZero s := ⟨hs.ne'⟩
        Nonempty (E ≃+* OrthogonalFourMinus.FiniteModel.fixedField s) ∧
        SL2.BinarySmall.IsHermitian σ s ∧ ∃ _ : OrthogonalModel s ρ L,
          (Odd L.index → quadraticRatio ρ = 2 ∧ cubicRatio ρ = 3 / 2) ∧
          (1 < s →
            (Even L.index → quadraticRatio ρ = (2 * s : ℕ) / (s + 1 : ℝ≥0∞) ∧
              cubicRatio ρ = min (3 / 2) ((2 * s : ℕ) / (s + 1 : ℝ≥0∞))) ∧
            ¬ IsFFModule ρ) ∧
          (s = 1 →
            (L = ⊤ ∧ Nonempty (ChapterB.QuasisimpleSource.ActionEquiv ρ
              ((BinaryPermutation.naturalRepresentation (Fin 5)).comp
                (alternatingGroup (Fin 5)).subtype)) ∧
              quadraticRatio ρ = 2 ∧ cubicRatio ρ = 3 / 2) ∨
            ∃ a : ChapterB.QuasisimpleSource.ActionEquiv ρ (BinaryPermutation.naturalRepresentation (Fin 5)),
              L.map a.groupEquiv.toMonoidHom = alternatingGroup (Fin 5) ∧
              quadraticRatio ρ = 1 ∧ offenderSubgroup ρ = ⊤ ∧
              (∀ A : Subgroup G, IsBestOffender ρ A ↔
                ChapterB.Offenders.CaseAFamily 5 (A.map a.groupEquiv.toMonoidHom)) ∧
              ∀ A : Subgroup G, IsBestOffender ρ A →
                A = Subgroup.closure {x | x ∈ A ∧ (a.groupEquiv x).IsSwap} ∧
                ∀ x ∈ A, ∀ y ∈ A, Commute x y)) := by
  obtain ⟨K, hK, hfin, hchar, hc, e, hd, halt⟩ := h.psl2_module_recognition hr hq
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  refine ⟨K, hK, hfin, hchar, hc, e, hd, ?_⟩
  rcases halt with ⟨hdeg, hfield, ⟨M⟩⟩ | ⟨s, hrs, hdeg, hs, hfield, hherm, ⟨M⟩⟩
  · exact Or.inl ⟨hdeg, hfield, M, h.natural_source_case M hr hc⟩
  · let : NeZero s := ⟨hs.ne'⟩
    let : L.Normal := h.layer_normal
    refine Or.inr ⟨s, hrs, hdeg, hs, hfield, hherm, M,
      M.odd_extension_ratios, ?_, ?_⟩
    · intro hs1
      exact ⟨(h.orthogonal_ambient_ratios M hs1).2.1, h.orthogonal_not_ff M hs1⟩
    · rintro rfl
      exact h.orthogonal_fivePoint_case M


open BenderSuzuki.MatrixGroups Subgroup
open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
open ChapterB.ComponentRecognition.KnownFFTypes.Classical

/-- K.3.3 assembled from the actual PSU quotient and the earlier group-only
covering theorem. The latter is the sole remaining input, owned by
`qt-b01-ff-classical-even-cover-lifting`. Recognition proves its kernel trivial;
all module, center, outer-action, ratio and uniqueness clauses are derived.
The standard coordinates are obtained by simultaneous Hermitian basis change. -/
theorem SourceHypotheses.unitary_case_of_cover_lifting
    (h : SourceHypotheses ρ L) {s : ℕ} (hs : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (L ⧸ center L) 3 (2 ^ s))
    (hcover : ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
      Nat.card F = (2 ^ s) ^ 2 → (∀ x : F, J.conj x = x ^ (2 ^ s)) →
      (L ⧸ center L) ≃* ProjectiveSpecialUnitaryMatrixGroup J →
      IsCentralQuotient L J.specialSubgroup) (T : Sylow 2 G) :
    let : L.Normal := h.layer_normal
    (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : Algebra (ZMod 2) F)
        (J : HermitianForm 3 F),
      Nat.card F = (2 ^ s) ^ 2 ∧ (∀ x : F, J.conj x = x ^ (2 ^ s)) ∧
      Nat.card {x : F // J.conj x = x} = 2 ^ s ∧ Nonempty (UnitaryModel J ρ L) ∧
      ∃ N : UnitaryModel (standardForm J) ρ L, ∀ t : G, t ^ 2 = 1 → t ∉ L →
        (∀ (c : F) (v : Fin 3 → F),
          N.coordinateAction t (c • v) = c ^ (2 ^ s) • N.coordinateAction t v) ∧
        (∃ u : (standardForm J).unitarySubgroup, ∀ l : L,
          (N.groupEquiv (MulAut.conjNormal t l)).val =
            u.val * Matrix.GeneralLinearGroup.map J.conj.toRingHom (N.groupEquiv l).val * u.val⁻¹) ∧
        fixedCodim ρ (Subgroup.zpowers t) = 3 * s) ∧
    Nat.card (center L) = Nat.gcd 3 (2 ^ s + 1) ∧
    quadraticRatio ρ = 2 ∧ cubicRatio ρ = 2 ∧ Module.finrank (ZMod 2) V = 6 * s ∧
    IsElementaryTwo (omegaOneAmbient ((T : Subgroup G) ⊓ L)) ∧
    rank (omegaOneAmbient ((T : Subgroup G) ⊓ L)) = s ∧
    Module.finrank (ZMod 2) (fixedSpace ρ (omegaOneAmbient ((T : Subgroup G) ⊓ L))) = 4 * s ∧
    IsQuadratic ρ (omegaOneAmbient ((T : Subgroup G) ⊓ L)) ∧
    actionRatio ρ (omegaOneAmbient ((T : Subgroup G) ⊓ L)) = 2 ∧
    (∀ A : Subgroup G, A ≤ T →
      ((IsElementaryTwo A ∧ actionRatio ρ A ≤ 2) ↔
        A = omegaOneAmbient ((T : Subgroup G) ⊓ L))) := by
  let : L.Normal := h.layer_normal
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hq
  let : CharP F 2 := Theory.SpecificGroups.UnitaryRootNormalizer.charP_binary (by omega) hcard
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hc := hcover F J hcard hconj e
  obtain ⟨M⟩ := UnitaryRecognition.source_naturalModel_of_centralQuotient J hs hcard hconj h hc
  have hcenter : Nat.card (center L) = Nat.gcd 3 (2 ^ s + 1) := by
    rw [Nat.card_congr (centerCongr M.groupEquiv).toEquiv]
    exact UnitaryRecognition.special_center_card J (by omega) hcard hconj
  refine ⟨?_, hcenter, h.unitary_case M.toUnitaryModel hs hcard hconj T⟩
  obtain ⟨N⟩ := M.toUnitaryModel.exists_standard (by omega) hcard hconj
  exact ⟨F, hF, hfin, inferInstance, J, hcard, hconj,
    UnitaryRecognition.fixedField_card J (by omega) hcard hconj, ⟨M.toUnitaryModel⟩,
    N, fun t ht htL => N.outer_involution_action h rfl hs hcard hconj ht htL⟩

end CFSG.Quasithin.ChapterK.RankOne
