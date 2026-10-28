module

public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Amalgam
public import CFSG.Quasithin.ChapterF.Section01.SourceDefs

/-!
# The corrected Aut(M₁₂) alternative in F.1.12

The literal involution centralizer and natural-four normalizer give L₁,L₂.
Both local Borels equal their common Sylow subgroup S, so the source's entire
B = B₁B₂S is exactly their intersection. The compatible inclusion amalgam is
also realized inside the full abstract automorphism group, using the proved
surjective automorphism equivalence, with the inner M₁₂ marking preserved.

Both local quotients are PSL₂(2), and both two-cores have order 64. The first
core's residual commutator is Q₈ * Q₈; its quotient by the marked
Z = Ω₁(Z(S)) is E₄ wr C₂. Its center has order two, ruling out the printed
C₄ * Q₈² expression, and its twenty square-one elements distinguish it from
the split quaternion-swap group. The second core is the actual centralizer
of the natural four. These are proved calculations, not recognition premises.

The model predicate requires a full amalgam isomorphism to the model inside
Aut(M₁₂), including both commuting squares. No uniqueness theorem is asserted.
Sources: Aschbacher--Smith, F.1.12(I)(13), printed p.263, E.2.16, p.228,
and 14.2.21, p.988 (refs/quasithin.pdf).
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.AutMathieuTwelve
open Theory.GroupTheory Sporadic.Mathieu Sporadic.Mathieu.M12ExceptionalExtension
open scoped Pointwise

/-- The source L₁,L₂, with L₁ centralizing the distinguished involution. -/
def L : Fin 2 → Subgroup Carrier := ![firstParabolic, secondParabolic]

/-- The actual common Sylow two-subgroup. -/
def S : Sylow 2 Carrier := VerifiedPair.commonSylow

/-- The source's entire B₁B₂S, prior to simplifying either local normalizer. -/
def B : Subgroup Carrier := Source.commonBorel L (S : Subgroup Carrier)

/-- The full source parabolic LᵢB. -/
def P (i : Fin 2) : Subgroup Carrier := L i ⊔ B

theorem S_le_L (i : Fin 2) : (S : Subgroup Carrier) ≤ L i := by
  fin_cases i
  · exact inf_le_left
  · exact inf_le_right

theorem local_borel (i : Fin 2) : Source.borel (L i) (S : Subgroup Carrier) = S := by
  rw [Source.borel, inf_eq_left.mpr (S_le_L i)]
  fin_cases i
  · exact VerifiedPair.first_sylow_normalizer
  · exact SecondCoordinates.second_sylow_normalizer innerModel

theorem B_eq_S : B = (S : Subgroup Carrier) := by
  rw [B, Source.commonBorel, local_borel, local_borel, sup_idem, sup_idem]

theorem B_le_L (i : Fin 2) : B ≤ L i := B_eq_S ▸ S_le_L i

theorem P_eq_L (i : Fin 2) : P i = L i := sup_eq_left.mpr (B_le_L i)

theorem borel_normalizes (i : Fin 2) : B ≤ Subgroup.normalizer (L i : Set Carrier) :=
  (B_le_L i).trans (L i).le_normalizer

theorem P_coe_eq_product (i : Fin 2) :
    (P i : Set Carrier) = (L i : Set Carrier) * (B : Set Carrier) :=
  Subgroup.coe_mul_of_right_le_normalizer_left _ _ (borel_normalizes i)

theorem overlap : P 0 ⊓ P 1 = B := by
  rw [P_eq_L, P_eq_L, B_eq_S]
  rfl

theorem generated : L 0 ⊔ L 1 ⊔ (S : Subgroup Carrier) = ⊤ := by
  change firstParabolic ⊔ secondParabolic ⊔ (S : Subgroup Carrier) = ⊤
  rw [SecondCoordinates.parabolic_sup_eq_top innerModel, top_sup_eq]

theorem P_generate : P 0 ⊔ P 1 = ⊤ := by
  rw [P_eq_L, P_eq_L]
  exact SecondCoordinates.parabolic_sup_eq_top innerModel

/-- The full source inclusion amalgam, with the literal B₁B₂S as middle group. -/
def amalgam : RankTwoAmalgam (P 0) B (P 1) :=
  RankTwoAmalgam.ofSubgroups _ _ _ le_sup_right le_sup_right

/-- Its identification with the checked intrinsic pair preserves both inclusions. -/
def concreteIso : RankTwoAmalgam.Iso amalgam VerifiedPair.amalgam :=
  RankTwoAmalgam.ofSubgroupsIso (MulEquiv.refl Carrier)
    le_sup_right le_sup_right inf_le_left inf_le_right
    (by simpa [P, L] using P_eq_L 0)
    (by simpa [S, VerifiedPair.commonSylow, SecondCoordinates.commonSylow,
      M12ExceptionalExtension.overlap] using B_eq_S)
    (by simpa [P, L] using P_eq_L 1)

theorem left_injective : Function.Injective amalgam.left :=
  Subgroup.inclusion_injective le_sup_right

theorem right_injective : Function.Injective amalgam.right :=
  Subgroup.inclusion_injective le_sup_right


/-- Both core quotients and the corrected, marked first-core structure. -/
theorem local_calculations :
    ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 2 ∧
    Nat.card (pCore 2 (L 0)) = 64 ∧
    Nonempty (Subgroup.QuaternionCentralProductData
      (⁅pCore 2 (L 0), pResidual 2 (L 0)⁆ : Subgroup (L 0))) ∧
    Nonempty ((pCore 2 (L 0)) ⧸ FirstParabolic.intrinsicDistinguished ≃*
      QuaternionSwapModel.W) ∧
    ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 2 ∧
    Nat.card (pCore 2 (L 1)) = 64 := by
  refine ⟨?_, FirstParabolic.card_pCore innerModel,
    ⟨VerifiedPair.residualQuaternionData⟩, ⟨VerifiedPair.markedCoreQuotient⟩,
    ?_, SecondCoordinates.card_secondCore innerModel⟩
  · exact ⟨ZMod 2, inferInstance, inferInstance, by simp, ⟨VerifiedPair.firstPSLQuotient⟩⟩
  · exact ⟨ZMod 2, inferInstance, inferInstance, by simp, ⟨VerifiedPair.secondPSLQuotient⟩⟩

/-- The quotient's denominator is exactly the source's central first omega. -/
theorem marked_Z :
    (omega₁ (Subgroup.center (S : Subgroup Carrier)) (p := 2)).map
      ((S : Subgroup Carrier).subtype.comp (Subgroup.center (S : Subgroup Carrier)).subtype) =
        distinguished := VerifiedPair.source_Z

/-- The embedding of the second core remains the natural-four centralizer. -/
theorem secondCore_image : (pCore 2 (L 1)).map (L 1).subtype =
    Subgroup.centralizer (natural : Set Carrier) := VerifiedPair.secondCore_image

/-- The full automorphism carrier, with no remaining coverage assumption. -/
def ambientEquiv : Carrier ≃* MulAut M12 := automorphismEquiv

theorem ambientEquiv_inner (g : M12) :
    ambientEquiv (innerModel.embedding g) = MulAut.conj g :=
  automorphismEquiv_embedding g

def autL (i : Fin 2) : Subgroup (MulAut M12) := (L i).map ambientEquiv.toMonoidHom

def autS : Sylow 2 (MulAut M12) :=
  S.mapSurjective (f := ambientEquiv.toMonoidHom) ambientEquiv.surjective

def autB : Subgroup (MulAut M12) := B.map ambientEquiv.toMonoidHom

def autP (i : Fin 2) : Subgroup (MulAut M12) := (P i).map ambientEquiv.toMonoidHom

private theorem borel_map (H T : Subgroup Carrier) :
    (Source.borel H T).map ambientEquiv.toMonoidHom =
      Source.borel (H.map ambientEquiv.toMonoidHom) (T.map ambientEquiv.toMonoidHom) := by
  rw [Source.borel, Subgroup.map_inf _ _ _ ambientEquiv.injective,
    Subgroup.map_equiv_normalizer_eq, Subgroup.map_inf _ _ _ ambientEquiv.injective]
  rfl

/-- The same full source Borel inside the abstract automorphism group. -/
theorem autB_commonBorel : autB = Source.commonBorel autL (autS : Subgroup (MulAut M12)) := by
  change (Source.commonBorel L (S : Subgroup Carrier)).map ambientEquiv.toMonoidHom = _
  simp only [Source.commonBorel, Subgroup.map_sup, borel_map]
  rfl

theorem autP_eq_product_join (i : Fin 2) : autP i = autL i ⊔ autB :=
  Subgroup.map_sup _ _ _

theorem aut_overlap : autP 0 ⊓ autP 1 = autB := by
  rw [autP, autP, ← Subgroup.map_inf _ _ _ ambientEquiv.injective, overlap]
  rfl

theorem aut_generated : autP 0 ⊔ autP 1 = ⊤ := by
  rw [autP, autP, ← Subgroup.map_sup, P_generate,
    Subgroup.map_top_of_surjective _ ambientEquiv.surjective]

/-- The actual inclusion amalgam inside the full automorphism group. -/
def autAmalgam : RankTwoAmalgam (autP 0) autB (autP 1) :=
  RankTwoAmalgam.ofSubgroups _ _ _ (Subgroup.map_mono le_sup_right)
    (Subgroup.map_mono le_sup_right)

/-- Both inclusion squares commute under the full automorphism identification. -/
def ambientIso : RankTwoAmalgam.Iso amalgam autAmalgam :=
  RankTwoAmalgam.ofSubgroupsIso ambientEquiv le_sup_right le_sup_right
    (Subgroup.map_mono le_sup_right) (Subgroup.map_mono le_sup_right) rfl rfl rfl

variable {G₁ D G₂ : Type*} [Group G₁] [Group D] [Group G₂]

/-- The model is the verified amalgam in the full automorphism group, with both squares. -/
def IsAutM12Amalgam (α : RankTwoAmalgam G₁ D G₂) : Prop :=
  Nonempty (RankTwoAmalgam.Iso α autAmalgam)

/-- Exact first-core type and residual structure; local data alone assert no uniqueness. -/
def AutM12LocalStructure (_α : RankTwoAmalgam G₁ D G₂) : Prop :=
  ClassicalGroup.IsPSL (G₁ ⧸ pCore 2 G₁) 2 2 ∧
  Nonempty (pCore 2 G₁ ≃* FirstParabolic.outerCore) ∧
  Nonempty (Subgroup.QuaternionCentralProductData
    (⁅pCore 2 G₁, pResidual 2 G₁⁆ : Subgroup G₁)) ∧
  ClassicalGroup.IsPSL (G₂ ⧸ pCore 2 G₂) 2 2 ∧
  Nat.card (pCore 2 G₂) = 64

/-- All stated invariants follow from a compatible isomorphism to the actual model. -/
theorem localStructure_of_isAutM12Amalgam {α : RankTwoAmalgam G₁ D G₂}
    (h : IsAutM12Amalgam α) : AutM12LocalStructure α := by
  obtain ⟨e⟩ := h
  let f := (e.trans ambientIso.symm).trans concreteIso
  let r : (⁅pCore 2 G₁, pResidual 2 G₁⁆ : Subgroup G₁) ≃*
      (⁅pCore 2 firstParabolic, pResidual 2 firstParabolic⁆ : Subgroup firstParabolic) :=
    LocalCoreTransport.subgroupEquiv f.left (by
    rw [Subgroup.map_commutator, pCore_map_iso, Subgroup.map_pResidual])
  refine ⟨?_, ⟨(LocalCoreTransport.coreEquiv 2 f.left).trans
    (FirstParabolic.intrinsicCoreEquiv innerModel)⟩,
    ⟨VerifiedPair.residualQuaternionData.map r.symm⟩, ?_, ?_⟩
  · exact ⟨ZMod 2, inferInstance, inferInstance, by simp,
      ⟨(LocalCoreTransport.quotientEquiv 2 f.left).trans VerifiedPair.firstPSLQuotient⟩⟩
  · exact ⟨ZMod 2, inferInstance, inferInstance, by simp,
      ⟨(LocalCoreTransport.quotientEquiv 2 f.right).trans VerifiedPair.secondPSLQuotient⟩⟩
  · rw [LocalCoreTransport.core_card 2 f.right, SecondCoordinates.card_secondCore innerModel]

end CFSG.Quasithin.ChapterF.GreenBook.AutMathieuTwelve
