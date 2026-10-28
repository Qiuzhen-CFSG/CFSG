module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.LinearProjection.Levi
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.LinearProjection.LeviProduct.BinaryRankOne
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.LinearProjection.LeviProduct.RootMatrices

public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# The binary end-node Levi is SL₂(2) × SL₂(2)

The actual signed F₄ root matrices at each end node satisfy the binary A₁
presentation. A Cartan-column entry proves that the first rank-one map is
faithful; the exceptional twist transfers faithfulness to the other node.
Orthogonality makes the factors commute, and their trivial centers make their
intersection trivial. Their image is exactly the published root-generated
`splitLevi 0`, since every binary root parameter is zero or one.

The same marked SL₂ comparison is used on both factors. The twist changes
node 0 to node 3 and conversely without changing the binary parameters, so the
resulting product equivalence intertwines it with factor exchange. The fixed
point descent is provided separately by `LinearProjection.Descent`.

Source: the end-node A₁ × A₁ subsystem in the standard F₄ root datum, and
Aschbacher–Smith F.1.12(I)(5), printed pp.263–264 of `refs/quasithin.pdf`.
-/

public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.Parabolics.BinaryLinear
noncomputable section
private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
namespace LeviProductProof

private def rankHom (i : Fin 4) : DihedralGroup 3 →* SplitGroup 0 :=
  wordHom (pos i) (neg i) (pos_sq i) (neg_sq i) (pos_neg_braid i)

private lemma twist_rankHom (i : Fin 4) (x : DihedralGroup 3) :
    reeTwist 0 (rankHom i x) = rankHom (Fin.revPerm i) x := by
  change reeTwist 0 (word (pos i) (neg i) x) = word _ _ x
  exact (map_word (reeTwist 0) (pos i) (neg i) x).trans
    (congrArg₂ (fun a b => word a b x) (twist_pos i) (twist_neg i))

/-- The rank-one map from the actual binary SL₂ to the F₄ root matrices. -/
def slRankHom (i : Fin 4) : SL →* SplitGroup 0 :=
  (rankHom i).comp slEquiv.symm.toMonoidHom

lemma slRankHom_upper (i : Fin 4) : slRankHom i slUpper = pos i := by
  change rankHom i (slEquiv.symm slUpper) = pos i
  rw [← slEquiv_sr0, slEquiv.symm_apply_apply]
  rfl

lemma slRankHom_lower (i : Fin 4) : slRankHom i slLower = neg i := by
  change rankHom i (slEquiv.symm slLower) = neg i
  rw [← slEquiv_sr1, slEquiv.symm_apply_apply]
  rfl

private lemma rankHom_injective_zero : Function.Injective (rankHom 0) :=
  wordHom_injective _ _ _ _ _ pos_neg_ne

private lemma rankHom_injective_three : Function.Injective (rankHom 3) := by
  intro x y h
  apply rankHom_injective_zero
  have hh := congrArg (reeTwist 0) h
  simpa only [twist_rankHom, show Fin.revPerm (3 : Fin 4) = 0 from rfl] using hh

lemma slRankHom_injective_zero : Function.Injective (slRankHom 0) :=
  rankHom_injective_zero.comp slEquiv.symm.injective

lemma slRankHom_injective_three : Function.Injective (slRankHom 3) :=
  rankHom_injective_three.comp slEquiv.symm.injective

private lemma commute_word {G : Type*} [Group G] (a b c : G)
    (ha : Commute a c) (hb : Commute b c) (x : DihedralGroup 3) :
    Commute (word a b x) c := by
  rcases x with i | i <;> fin_cases i <;> dsimp [word, ZMod.val]
  · exact Commute.one_left c
  · exact ha.mul_left hb
  · exact hb.mul_left ha
  · exact ha
  · exact hb
  · exact (ha.mul_left hb).mul_left ha

private lemma rankHom_commute (x y : DihedralGroup 3) :
    Commute (rankHom 0 x) (rankHom 3 y) := by
  apply commute_word
  · exact (commute_word _ _ _ commute_pos_pos.symm commute_pos_neg.symm y).symm
  · exact (commute_word _ _ _ commute_neg_pos.symm commute_neg_neg.symm y).symm

private lemma rankHom_disjoint : Disjoint (rankHom 0).range (rankHom 3).range := by
  apply Subgroup.disjoint_def.mpr
  rintro g ⟨x, rfl⟩ ⟨y, hy⟩
  have hx : x ∈ Subgroup.center (DihedralGroup 3) := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply rankHom_injective_zero
    simp only [map_mul]
    rw [← hy]
    exact (rankHom_commute z y).eq
  have hx1 : x = 1 := by
    simpa only [DihedralGroup.center_eq_bot_of_odd_ne_one (by decide : Odd 3)
      (by decide : 3 ≠ 1), Subgroup.mem_bot] using hx
  simp [hx1]

private def productHom : DihedralGroup 3 × DihedralGroup 3 →* SplitGroup 0 :=
  (rankHom 0).noncommCoprod (rankHom 3) rankHom_commute

private lemma productHom_injective : Function.Injective productHom :=
  (MonoidHom.noncommCoprod_injective _ _ _).mpr
    ⟨rankHom_injective_zero, rankHom_injective_three, rankHom_disjoint⟩

private lemma pos_mem_levi (i : Fin 4) (hi : i ∈ LargeLocalSeeds.leviNodes .linear) :
    pos i ∈ splitLevi 0 := root_mem_splitLevi 0 _ _ ⟨i, hi, Or.inl rfl⟩
private lemma neg_mem_levi (i : Fin 4) (hi : i ∈ LargeLocalSeeds.leviNodes .linear) :
    neg i ∈ splitLevi 0 := root_mem_splitLevi 0 _ _ ⟨i, hi, Or.inr rfl⟩

private lemma rankHom_mem_levi (i : Fin 4) (hi : i ∈ LargeLocalSeeds.leviNodes .linear)
    (x : DihedralGroup 3) : rankHom i x ∈ splitLevi 0 :=
  wordHom_mem _ _ _ _ _ _ (pos_mem_levi i hi) (neg_mem_levi i hi) x

private lemma productHom_range : productHom.range = splitLevi 0 := by
  apply le_antisymm
  · rintro g ⟨⟨x, y⟩, rfl⟩
    exact (splitLevi 0).mul_mem
      (rankHom_mem_levi 0 (by simp [LargeLocalSeeds.leviNodes]) x)
      (rankHom_mem_levi 3 (by simp [LargeLocalSeeds.leviNodes]) y)
  · apply (Subgroup.closure_le _).mpr
    rintro g ⟨r, t, ⟨i, hi, hr⟩, rfl⟩
    rcases binary_scalar t with rfl | rfl
    · have h0 : rootGeneratorInGroup 0 r 0 = 1 := by
        apply Subtype.ext
        exact F4Chevalley.rootCurve_zero r
      rw [h0]
      exact productHom.range.one_mem
    · have hi' : i = 0 ∨ i = 3 := by
        simpa [LargeLocalSeeds.leviNodes] using hi
      rcases hi' with rfl | rfl <;> rcases hr with rfl | rfl
      · refine ⟨(.sr 0, 1), ?_⟩
        change rankHom 0 (.sr 0) * rankHom 3 1 = pos 0
        simp [rankHom]
      · refine ⟨(.sr 1, 1), ?_⟩
        change rankHom 0 (.sr 1) * rankHom 3 1 = neg 0
        simp [rankHom]
      · refine ⟨(1, .sr 0), ?_⟩
        change rankHom 0 1 * rankHom 3 (.sr 0) = pos 3
        simp [rankHom]
      · refine ⟨(1, .sr 1), ?_⟩
        change rankHom 0 1 * rankHom 3 (.sr 1) = neg 3
        simp [rankHom]

private def productToLevi : DihedralGroup 3 × DihedralGroup 3 →* splitLevi 0 :=
  productHom.codRestrict (splitLevi 0) fun x => productHom_range.le ⟨x, rfl⟩

private lemma productToLevi_bijective : Function.Bijective productToLevi := by
  constructor
  · intro x y h
    exact productHom_injective (congrArg Subtype.val h)
  · intro l
    obtain ⟨x, hx⟩ := productHom_range.ge l.property
    exact ⟨x, Subtype.ext hx⟩

private def dihedralProductEquiv : DihedralGroup 3 × DihedralGroup 3 ≃* splitLevi 0 :=
  MulEquiv.ofBijective productToLevi productToLevi_bijective

private lemma dihedralProductEquiv_twist (x : DihedralGroup 3 × DihedralGroup 3) :
    leviTwist 0 (dihedralProductEquiv x) = dihedralProductEquiv x.swap := by
  apply Subtype.ext
  rw [leviTwist_coe]
  change reeTwist 0 (rankHom 0 x.1 * rankHom 3 x.2) =
    rankHom 0 x.2 * rankHom 3 x.1
  rw [map_mul, twist_rankHom, twist_rankHom]
  exact (rankHom_commute x.2 x.1).symm.eq

end LeviProductProof
open LeviProductProof

/-- The concrete end-node Levi is the product of its two binary rank-one factors. -/
def leviProductEquiv : splitLevi 0 ≃*
    Matrix.SpecialLinearGroup (Fin 2) (CoefficientField 0) ×
      Matrix.SpecialLinearGroup (Fin 2) (CoefficientField 0) :=
  dihedralProductEquiv.symm.trans (slEquiv.prodCongr slEquiv)

/-- The exceptional Ree twist exchanges the two marked SL₂ factors. -/
lemma leviProductEquiv_twist (l : splitLevi 0) :
    leviProductEquiv (leviTwist 0 l) = (leviProductEquiv l).swap := by
  obtain ⟨x, rfl⟩ := dihedralProductEquiv.surjective l
  rw [dihedralProductEquiv_twist]
  simp only [leviProductEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl
end
end ReeF4.Parabolics.BinaryLinear
