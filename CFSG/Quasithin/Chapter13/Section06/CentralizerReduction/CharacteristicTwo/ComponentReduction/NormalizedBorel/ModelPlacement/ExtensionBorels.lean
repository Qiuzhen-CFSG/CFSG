module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ModelPlacement.ExtensionBorels.Alignment
public import Theory.SpecificGroups.PSL3.ExtensionBorel
public import Theory.SpecificGroups.SU3.ExtensionBorel

/-!
# Compatible Borels in the degree-three extensions

The alignment interface retains an actual equivalence on K*Lᵥ* and the
component embedding, and constructs the model marking for the supplied Sylow.
Its outer-preimage application uses the literal Aut → Out map, allowing the
mixed field–diagonal preimages of A.3.16 without replacing them by split
extensions. The source-facing theorems below feed the literal Sylow images and
normalizer identities from the concrete linear and unitary calculations into
the same whole-overgroup alignment. In particular, the mixed extensions remain
literal outer-quotient preimages; no complement or splitting is chosen here.

Source: Aschbacher–Smith, Notation A.3.16, Lemma A.3.18, and proof of 13.6.6,
printed pp.51–52 and 927.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel.ExtensionBorels
open Subgroup Theory.GroupTheory A5Module
open AutomorphismExtensionBorel

variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}

/-! ### Linear three-model assembly -/

/-- The diagonal `PGL₃` calculation supplies the exact model Borel data needed
by the relative placement theorem. The model equivalence is on the whole
relative overgroup, and `hcompat` retains the original component embedding. -/
theorem exists_linear_diagonal_model_borel
    {F : Type*} [Field F] [CharP F 2] [Finite F] {n : ℕ} (hn : 1 < n)
    (_hmod : 2 ^ n % 3 = 1) (hF : Nat.card F = 2 ^ n)
    (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s)))
    (e : (NormalizerAction.componentImage K ⊔ residualStar s K :
      Subgroup (XStar K)) ≃*
      Matrix.PSL3.OuterSolvable.innerDiagonal F)
    (k : NormalizerAction.componentImage K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (hcompat : ∀ x : NormalizerAction.componentImage K,
      e ⟨x.val, Subgroup.mem_sup_left x.property⟩ =
        innerEmbedding (Matrix.PSL3.OuterSolvable.innerDiagonal F)
          (Matrix.PSL3.OuterSolvable.inner_le_innerDiagonal F) (k x))
    (hk : IsPGroup 2 s.action.ker) (hTL : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (Gv (markedV s)))
    (hS : (S : Subgroup (Gv (markedV s))) = localT T (markedV s))
    (hDN : residual s ≤ X K)
    (hTN : localT T (markedV s) ≤ X K)
    (hcontrol : SolvableSylowControl 2 (NormalizerAction.componentImage K)) :
    ∃ (m : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
      (d : CompatibleBorelData s T K
        (innerEmbedding (Matrix.PSL3.OuterSolvable.innerDiagonal F)
          (Matrix.PSL3.OuterSolvable.inner_le_innerDiagonal F))
        (Matrix.PSL3.LinearThree.unipotentSylow F (by omega) hF)
        ((Matrix.PSL3.ExtensionBorel.linearBorel F).subgroupOf
          (Matrix.PSL3.OuterSolvable.innerDiagonal F))),
      d.overgroupEquiv = e.trans (MulAut.conj
        (innerEmbedding (Matrix.PSL3.OuterSolvable.innerDiagonal F)
          (Matrix.PSL3.OuterSolvable.inner_le_innerDiagonal F) m)) ∧
      d.componentEquiv = k.trans (MulAut.conj m) := by
  have hn :
      normalizer (((Matrix.PSL3.LinearThree.unipotentSylow F (by omega) hF :
        Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)).map
        (innerEmbedding (Matrix.PSL3.OuterSolvable.innerDiagonal F)
          (Matrix.PSL3.OuterSolvable.inner_le_innerDiagonal F))) :
        Set (Matrix.PSL3.OuterSolvable.innerDiagonal F)) =
        (Matrix.PSL3.ExtensionBorel.linearBorel F).subgroupOf
          (Matrix.PSL3.OuterSolvable.innerDiagonal F) := by
    rw [Matrix.PSL3.LinearThree.coe_unipotentSylow, ← rootIn_eq_map]
    exact Matrix.PSL3.ExtensionBorel.normalizer_diagonal_root F
  exact exists_compatibleBorelData s T K _ e k hcompat
    (Matrix.PSL3.LinearThree.unipotentSylow F (by omega) hF)
    ((Matrix.PSL3.ExtensionBorel.linearBorel F).subgroupOf
      (Matrix.PSL3.OuterSolvable.innerDiagonal F)) hn hk hTL S hS hDN hTN
    hcontrol

/-- The literal mixed field--diagonal preimage in the linear model gives the
same compatible data. `MixedData` retains the source restrictions `6 ∣ n`,
the order-three actors, commutation and independence; this theorem does not
replace that preimage by a split extension. -/
theorem exists_linear_mixed_model_borel
    {F : Type*} [Field F] [Finite F] {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2 ^ n)
    (D : Matrix.PSL3.ExtensionBorel.MixedData F n)
    (s : Marking L V) (T : Subgroup G) (K : Subgroup (Gv (markedV s)))
    (e : (NormalizerAction.componentImage K ⊔ residualStar s K :
      Subgroup (XStar K)) ≃*
      Matrix.PSL3.ExtensionBorel.mixedExtension F D.coefficient D.diagonal)
    (k : NormalizerAction.componentImage K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (hcompat : ∀ x : NormalizerAction.componentImage K,
      e ⟨x.val, Subgroup.mem_sup_left x.property⟩ =
        innerEmbedding
          (Matrix.PSL3.ExtensionBorel.mixedExtension F D.coefficient D.diagonal)
          (Matrix.PSL3.ExtensionBorel.inner_le_mixedExtension F D.coefficient
            D.diagonal) (k x))
    (hk : IsPGroup 2 s.action.ker) (hTL : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (Gv (markedV s)))
    (hS : (S : Subgroup (Gv (markedV s))) = localT T (markedV s))
    (hDN : residual s ≤ X K)
    (hTN : localT T (markedV s) ≤ X K)
    (hcontrol : SolvableSylowControl 2 (NormalizerAction.componentImage K)) :
    ∃ (m : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
      (d : CompatibleBorelData s T K
        (innerEmbedding
          (Matrix.PSL3.ExtensionBorel.mixedExtension F D.coefficient D.diagonal)
          (Matrix.PSL3.ExtensionBorel.inner_le_mixedExtension F D.coefficient
            D.diagonal))
        (Matrix.PSL3.LinearThree.unipotentSylow F (by omega) hF)
        ((Matrix.PSL3.ExtensionBorel.actorBorel F).subgroupOf
          (Matrix.PSL3.ExtensionBorel.mixedExtension F D.coefficient D.diagonal))),
      d.overgroupEquiv = e.trans (MulAut.conj
        ((innerEmbedding
          (Matrix.PSL3.ExtensionBorel.mixedExtension F D.coefficient D.diagonal)
          (Matrix.PSL3.ExtensionBorel.inner_le_mixedExtension F D.coefficient
            D.diagonal)) m)) ∧
      d.componentEquiv = k.trans (MulAut.conj m) := by
  have hn := Matrix.PSL3.ExtensionBorel.normalizer_source_mixed F hn hF D
  exact exists_compatibleBorelData s T K _ e k hcompat
    (Matrix.PSL3.LinearThree.unipotentSylow F (by omega) hF)
    ((Matrix.PSL3.ExtensionBorel.actorBorel F).subgroupOf
      (Matrix.PSL3.ExtensionBorel.mixedExtension F D.coefficient D.diagonal))
    hn hk hTL S hS hDN hTN
    hcontrol

/-! ### Unitary three-model assembly -/

/-- The unitary-conjugation range contains the natural inner automorphisms.
This is the component embedding used by the diagonal unitary model. -/
theorem unitary_conj_range_inner_le
    {E : Type*} [Field E] [Finite E]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E) :
    MulAut.innerSubgroup
        (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) ≤
      J.unitaryConjHom.range := by
  rintro a ⟨x, rfl⟩
  obtain ⟨u, rfl⟩ := J.specialToProjective_surjective x
  exact ⟨⟨u, u.property.1⟩, by
    rw [J.unitaryConjHom_apply, J.unitaryConj_special_is_inner]⟩

/-- Every unitary conjugation actor belongs to the concrete semilinear group. -/
theorem unitary_conj_range_le_semilinear
    {E : Type*} [Field E] [Finite E]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    J.unitaryConjHom.range ≤
      BenderSuzuki.MatrixGroups.HermitianForm.ExtensionBorel.semilinearGroup J hJ := by
  rintro _ ⟨u, rfl⟩
  simpa only [J.unitaryConjHom_apply] using
    BenderSuzuki.MatrixGroups.HermitianForm.ExtensionBorel.unitary_mem_semilinear J hJ u

/-- The diagonal unitary (`PGU₃`) model supplies the same compatible Borel
data.  The underlying actor group is the actual range of unitary conjugation,
so its component embedding is retained literally. -/
theorem exists_unitary_diagonal_model_borel
    {E : Type*} [Field E] [Finite E]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {n : ℕ} (hn : 1 < n)
    (_hmod : 2 ^ n % 3 = 2) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
    (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s)))
    (e : (NormalizerAction.componentImage K ⊔ residualStar s K :
      Subgroup (XStar K)) ≃* J.unitaryConjHom.range)
    (k : NormalizerAction.componentImage K ≃*
      BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (hcompat : ∀ x : NormalizerAction.componentImage K,
      e ⟨x.val, Subgroup.mem_sup_left x.property⟩ =
        (innerEmbedding J.unitaryConjHom.range
          (unitary_conj_range_inner_le J)) (k x))
    (hk : IsPGroup 2 s.action.ker) (hTL : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (Gv (markedV s)))
    (hS : (S : Subgroup (Gv (markedV s))) = localT T (markedV s))
    (hDN : residual s ≤ X K)
    (hTN : localT T (markedV s) ≤ X K)
    (hcontrol : SolvableSylowControl 2 (NormalizerAction.componentImage K)) :
    ∃ (m : BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
      (d : CompatibleBorelData s T K
        (innerEmbedding J.unitaryConjHom.range (unitary_conj_range_inner_le J))
        (BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank.rootSylow J hJ
          (by omega) hcard
          (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega)
            hcard hconj))
        (Subgroup.subgroupOf
          (BenderSuzuki.MatrixGroups.HermitianForm.ExtensionBorel.actorBorel J hJ)
          J.unitaryConjHom.range)),
      d.overgroupEquiv = e.trans (MulAut.conj
        ((innerEmbedding J.unitaryConjHom.range
          (unitary_conj_range_inner_le J)) m)) ∧
      d.componentEquiv = k.trans (MulAut.conj m) := by
  let hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcard hconj
  let P := BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank.rootSylow J hJ
    (by omega) hcard hfixed
  have hsem := unitary_conj_range_le_semilinear J hJ
  have hn :=
    BenderSuzuki.MatrixGroups.HermitianForm.ExtensionBorel.normalizer_semilinear_extension
      J hJ hn hcard hconj J.unitaryConjHom.range
      (unitary_conj_range_inner_le J) hsem
  have hn' :
      normalizer (((P : Subgroup
        (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)).map
        (innerEmbedding J.unitaryConjHom.range (unitary_conj_range_inner_le J))) :
        Set J.unitaryConjHom.range) =
        (Subgroup.subgroupOf
          (BenderSuzuki.MatrixGroups.HermitianForm.ExtensionBorel.actorBorel J hJ)
          J.unitaryConjHom.range) := by
    rw [BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank.rootSylow_coe,
      ← rootIn_eq_map]
    exact hn
  exact exists_compatibleBorelData s T K _ e k hcompat P
    (Subgroup.subgroupOf
      (BenderSuzuki.MatrixGroups.HermitianForm.ExtensionBorel.actorBorel J hJ)
      J.unitaryConjHom.range) hn' hk hTL S hS hDN hTN hcontrol

/-- The literal mixed unitary preimage from A.3.16 supplies compatible model
Borel data. The hypotheses retain the source sign condition
`2 ^ n ≡ -1 [MOD 3]` (written as `2 ^ n % 3 = 2`) and the actual order-three
field and diagonal actors. -/
theorem exists_unitary_mixed_model_borel
    {E : Type*} [Field E] [Finite E]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {n : ℕ} (hn : 1 < n)
    (hthree : 3 ∣ n) (hmod : 2 ^ n % 3 = 2)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
    (σ : E ≃+* E) (hfield : orderOf σ = 3)
    (d₀ : J.unitarySubgroup)
    (hdiag : ∀ i j, i ≠ j → d₀.val.val i j = 0)
    (houter : orderOf
      (QuotientGroup.mk'
        (MulAut.innerSubgroup
          (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J))
        (J.unitaryConj d₀)) = 3)
    (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s)))
    (e : (NormalizerAction.componentImage K ⊔ residualStar s K :
      Subgroup (XStar K)) ≃*
      BenderSuzuki.MatrixGroups.HermitianForm.ExtensionBorel.mixedPreimage
        J hJ σ d₀)
    (k : NormalizerAction.componentImage K ≃*
      BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (hcompat : ∀ x : NormalizerAction.componentImage K,
      e ⟨x.val, Subgroup.mem_sup_left x.property⟩ =
        ((innerEmbedding
          (BenderSuzuki.MatrixGroups.HermitianForm.ExtensionBorel.mixedPreimage
            J hJ σ d₀)
          (BenderSuzuki.MatrixGroups.HermitianForm.ExtensionBorel.inner_le_mixedPreimage
            J hJ σ d₀)) (k x)))
    (hk : IsPGroup 2 s.action.ker) (hTL : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (Gv (markedV s)))
    (hS : (S : Subgroup (Gv (markedV s))) = localT T (markedV s))
    (hDN : residual s ≤ X K)
    (hTN : localT T (markedV s) ≤ X K)
    (hcontrol : SolvableSylowControl 2 (NormalizerAction.componentImage K)) :
    ∃ (m : BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
      (d : CompatibleBorelData s T K
        (innerEmbedding
          (BenderSuzuki.MatrixGroups.HermitianForm.ExtensionBorel.mixedPreimage
            J hJ σ d₀)
          (BenderSuzuki.MatrixGroups.HermitianForm.ExtensionBorel.inner_le_mixedPreimage
            J hJ σ d₀))
        (BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank.rootSylow J hJ
          (by omega) hcard
          (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega)
            hcard hconj))
        (Subgroup.subgroupOf
          (BenderSuzuki.MatrixGroups.HermitianForm.ExtensionBorel.actorBorel J hJ)
          (BenderSuzuki.MatrixGroups.HermitianForm.ExtensionBorel.mixedPreimage
            J hJ σ d₀))),
      d.overgroupEquiv = e.trans (MulAut.conj
        ((innerEmbedding
          (BenderSuzuki.MatrixGroups.HermitianForm.ExtensionBorel.mixedPreimage
            J hJ σ d₀)
          (BenderSuzuki.MatrixGroups.HermitianForm.ExtensionBorel.inner_le_mixedPreimage
            J hJ σ d₀)) m)) ∧
      d.componentEquiv = k.trans (MulAut.conj m) := by
  let hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcard hconj
  let P := BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank.rootSylow J hJ
    (by omega) hcard hfixed
  have hn :=
    BenderSuzuki.MatrixGroups.HermitianForm.ExtensionBorel.source_mixed_rootSylow_normalizer
      J hJ hn hthree hmod hcard hconj σ hfield d₀ hdiag houter
  exact exists_compatibleBorelData s T K _ e k hcompat P
    (Subgroup.subgroupOf
      (BenderSuzuki.MatrixGroups.HermitianForm.ExtensionBorel.actorBorel J hJ)
      (BenderSuzuki.MatrixGroups.HermitianForm.ExtensionBorel.mixedPreimage
        J hJ σ d₀)) hn hk hTL S hS hDN hTN hcontrol

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel.ExtensionBorels
