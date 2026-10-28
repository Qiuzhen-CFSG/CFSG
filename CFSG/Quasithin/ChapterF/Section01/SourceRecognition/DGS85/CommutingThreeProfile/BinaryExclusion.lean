module

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.SuzukiContainment.ReducedPair
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import BenderSuzuki.External.Huppert.XI.theorem_3_6

/-!
# Binary exclusions for the commuting distance-three branch

DGS85 (13.1)(a)--(e), printed p.191, recalls the genuine Chapter 9
conclusions. Its two local SL₂(2) quotients rule out the nonbinary linear,
nonbinary Suzuki and quintic consumers without reconstructing M₁₂.

Here the binary quotient conclusions remain explicit earlier inputs. Their
original local Sylows have index three and are self-normalizing. Consequently
the full original Borel equals S when both endpoints are binary, and both
original parabolic indices are three. A quintic index is impossible.
Cardinality excludes a nonbinary linear quotient; solvability excludes a
nonbinary Suzuki quotient.

The final applications pull the markings back through the actual reduced
completion and starred-parabolic inclusions. The representative formula
retains the original quotient map. No finite ambient completion is assumed.
These are conditional consumers of Chapter 9, not a proof of (13.1) from
Hypothesis B′. Its graph hypotheses and Chapter 12 remain with the source
assembly and this theorem-family owner.

Sources: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, (13.1), p.191; Aschbacher--Smith, F.1.9 and F.1.12, pp.261--264.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The original local Sylow has index three over a binary local quotient. -/
theorem binary_local_sylow_index (h : HypothesisF11 L S) (i : Fin 2)
    (e : (L i ⧸ pCore 2 (L i)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : S.relIndex (L i) = 3 := by
  let := h.finite_local i
  obtain ⟨P, hP⟩ := h.sylow i
  have htop : (⊤ : Subgroup (L i)).map (L i).subtype = L i := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  have hi := relIndex_map_map_of_injective (P : Subgroup (L i)) ⊤
    (L i).subtype_injective
  rw [hP, htop, inf_relIndex_right, relIndex_top_right] at hi
  exact hi.trans (SymmetricThreeTwoCore.sylow_index_three
    (e.trans SLTwoPermThree.sl2Two_equiv_perm_three.some) P)

/-- A binary local quotient makes its original local Sylow self-normalizing. -/
theorem binary_local_borel (h : HypothesisF11 L S) (i : Fin 2)
    (e : (L i ⧸ pCore 2 (L i)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : borel (L i) S = S ⊓ L i := by
  let := h.finite_local i
  obtain ⟨P, hP⟩ := h.sylow i
  have hP' : (P : Subgroup (L i)) = (S ⊓ L i).subgroupOf (L i) := by
    apply map_injective (L i).subtype_injective
    rw [hP, map_subgroupOf_eq_of_le inf_le_right]
  have hn := SymmetricThreeTwoCore.sylow_self_normalizing
    (e.trans SLTwoPermThree.sl2Two_equiv_perm_three.some) P
  change normalizer ((P : Subgroup (L i)) : Set (L i)) = (P : Subgroup (L i)) at hn
  rw [hP', ← subgroupOf_normalizer_eq (show S ⊓ L i ≤ L i from inf_le_right)] at hn
  apply le_antisymm
  · rintro x ⟨hx, hxn⟩
    change (⟨x, hx⟩ : L i) ∈ (S ⊓ L i).subgroupOf (L i)
    exact hn ▸ (show (⟨x, hx⟩ : L i) ∈
      (normalizer ((S ⊓ L i : Subgroup G) : Set G)).subgroupOf (L i) from hxn)
  · exact le_inf inf_le_right (S ⊓ L i).le_normalizer

/-- The full original Borel has index three in this parabolic. -/
theorem binary_parabolic_borel_index (h : HypothesisF11 L S) (i : Fin 2)
    (e : (L i ⧸ pCore 2 (L i)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :
    (commonBorel L S).relIndex (parabolic L S i) = 3 := by
  let := h.finite_commonBorel
  rw [parabolic_eq_sup_commonBorel,
    relIndex_sup_of_normalizes _ _ (h.commonBorel_normalizes_local i),
    ← inf_relIndex_right (commonBorel L S) (L i), inf_comm,
    h.local_inf_commonBorel i, binary_local_borel h i e, inf_relIndex_right]
  exact binary_local_sylow_index h i e

/-- Both binary quotients force the full original Borel to equal S. -/
theorem both_binary_commonBorel (h : HypothesisF11 L S)
    (e : ∀ i, (L i ⧸ pCore 2 (L i)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : commonBorel L S = S := by
  change borel (L 0) S ⊔ borel (L 1) S ⊔ S = S
  rw [binary_local_borel h 0 (e 0), binary_local_borel h 1 (e 1)]
  exact sup_eq_right.mpr (sup_le inf_le_left inf_le_left)

/-- Either original parabolic has index three over the original S. -/
theorem both_binary_parabolic_index (h : HypothesisF11 L S)
    (e : ∀ i, (L i ⧸ pCore 2 (L i)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (i : Fin 2) :
    S.relIndex (parabolic L S i) = 3 := by
  simpa only [both_binary_commonBorel h e] using binary_parabolic_borel_index h i (e i)

/-- The both-binary branch cannot occur at an original quintic endpoint. -/
theorem no_both_binary_of_quintic (h : HypothesisF11 L S) (i : Fin 2)
    (hfive : S.relIndex (parabolic L S i) = 5)
    (e : ∀ j, (L j ⧸ pCore 2 (L j)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : False := by
  have hi := both_binary_parabolic_index h e i
  omega

/-- A binary local quotient makes the original local factor solvable. -/
theorem binary_local_solvable (h : HypothesisF11 L S) (i : Fin 2)
    (e : (L i ⧸ pCore 2 (L i)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : Group.IsSolvable (L i) := by
  let := h.finite_local i
  exact SymmetricThreeTwoCore.solvable (e.trans SLTwoPermThree.sl2Two_equiv_perm_three.some)

/-- A field of order at least four cannot give a binary linear quotient. -/
theorem no_binary_of_nonbinary_linear {H : Type*} [Group H] {n : ℕ} (hn : 1 < n)
    (hlinear : ClassicalGroup.IsPSL H 2 (2 ^ n))
    (e : H ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : False := by
  obtain ⟨F, _, _, hF, ⟨f⟩⟩ := hlinear
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  have hc := BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
  rw [BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
    (CharTwo.neg_eq 1), mul_one, hF] at hc
  have hs : Nat.card H = 6 := by
    rw [Nat.card_congr (e.trans SLTwoPermThree.sl2Two_equiv_perm_three.some).toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hh := (Nat.card_congr f.toEquiv).trans hc
  have hq : 4 ≤ 2 ^ n := by
    have := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 2 ≤ n by omega)
    norm_num at this ⊢
    exact this
  have hsq : 16 ≤ (2 ^ n) ^ 2 := by nlinarith only [hq]
  have hq2 : 15 ≤ (2 ^ n) ^ 2 - 1 := by omega
  have hbound := Nat.mul_le_mul hq hq2
  rw [hs] at hh
  omega

/-- A nonbinary Suzuki quotient cannot be a binary linear group. -/
theorem no_binary_of_nonbinary_suzuki {H : Type*} [Group H] {m : ℕ} (hm : 0 < m)
    (f : H ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (e : H ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : False := by
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
    Group.isSolvable_of_isSolvable_injective
      (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
  let : Group.IsSolvable H := Group.isSolvable_of_isSolvable_injective
    (f := (e.trans SLTwoPermThree.sl2Two_equiv_perm_three.some).toMonoidHom)
    (e.trans SLTwoPermThree.sl2Two_equiv_perm_three.some).injective
  exact BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm
    (Group.isSolvable_of_surjective (f := f.toMonoidHom) f.surjective)

open SuzukiContainment

/-- The literal starred endpoint inside the existing reduced generated group. -/
abbrev reducedGeneratedStarred (L : Fin 2 → Subgroup G) (S : Subgroup G)
    (i : Fin 2) : Subgroup (generated L (reducedSylow L S)) :=
  starredParabolic
    (fun j => (L j).subgroupOf (generated L (reducedSylow L S)))
    ((reducedSylow L S).subgroupOf (generated L (reducedSylow L S))) i

/-- Pull the supplied source marking back to the original local core quotient. -/
@[expose] def originalBinaryQuotient (h : HypothesisF11 L S) (i : Fin 2)
    (e : (reducedGeneratedStarred L S i ⧸ pCore 2 (reducedGeneratedStarred L S i)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :
    (L i ⧸ pCore 2 (L i)) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
  ((reduced_hypothesis h).generatedStarredQuotientEquiv i).trans e

/-- Both original inclusion maps are retained on each representative. -/
theorem originalBinaryQuotient_mk (h : HypothesisF11 L S) (i : Fin 2)
    (e : (reducedGeneratedStarred L S i ⧸ pCore 2 (reducedGeneratedStarred L S i)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (x : L i) :
    originalBinaryQuotient h i e (QuotientGroup.mk x) =
      e (QuotientGroup.mk (inclusion (local_le_starredParabolic i)
        ((subgroupOfEquivOfLe (local_le_generated (L := L)
          (S := reducedSylow L S) i)).symm x))) := rfl

/-- The actual reduced starred quotients exclude the original quintic branch. -/
theorem no_reduced_binary_of_quintic (h : HypothesisF11 L S) (i : Fin 2)
    (hfive : S.relIndex (parabolic L S i) = 5)
    (e : ∀ j, (reducedGeneratedStarred L S j ⧸ pCore 2 (reducedGeneratedStarred L S j)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : False :=
  no_both_binary_of_quintic h i hfive (fun j => originalBinaryQuotient h j (e j))

/-- The quintic F.1.12 local-factor premise uses [K : S] = 5, without
replacing K by its larger full-Borel parabolic. Only this endpoint is needed. -/
theorem no_reduced_binary_of_local_quintic {K R : Subgroup G}
    (h : HypothesisF11 ![K, R] S) (hfive : S.relIndex K = 5)
    (e : (reducedGeneratedStarred ![K, R] S 0 ⧸
      pCore 2 (reducedGeneratedStarred ![K, R] S 0)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : False := by
  have hi : S.relIndex K = 3 :=
    binary_local_sylow_index h 0 (originalBinaryQuotient h 0 e)
  omega

/-- A nonbinary original linear quotient excludes a reduced binary endpoint. -/
theorem no_reduced_binary_of_linear (h : HypothesisF11 L S) (i : Fin 2)
    {n : ℕ} (hn : 1 < n) (hlinear : ClassicalGroup.IsPSL (L i ⧸ pCore 2 (L i)) 2 (2 ^ n))
    (e : (reducedGeneratedStarred L S i ⧸ pCore 2 (reducedGeneratedStarred L S i)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : False :=
  no_binary_of_nonbinary_linear hn hlinear (originalBinaryQuotient h i e)

/-- A nonbinary original Suzuki quotient excludes a reduced binary endpoint. -/
theorem no_reduced_binary_of_suzuki (h : HypothesisF11 L S) (i : Fin 2)
    {m : ℕ} (hm : 0 < m)
    (f : (L i ⧸ pCore 2 (L i)) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (e : (reducedGeneratedStarred L S i ⧸ pCore 2 (reducedGeneratedStarred L S i)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : False :=
  no_binary_of_nonbinary_suzuki hm f (originalBinaryQuotient h i e)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
