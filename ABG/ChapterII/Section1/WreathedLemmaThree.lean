module
public import ABG.ChapterII.Section1.WreathedCentricQuotientFour
public import ABG.ChapterII.Section1.WreathedSmallCentralExtensions
public import ABG.ChapterII.Section1.WreathedModularAutomorphisms
public import ABG.ChapterII.Section1.WreathedCentralProductCopies
public import ABG.ChapterII.Section1.WreathedCentralProductNormalizer
public import ABG.ChapterII.Section1.WreathedBaseStructure
public import ABG.ChapterII.Section1.WreathedAbelianCentric

/-!
# Exceptional centric subgroups of a wreathed group

Alperin--Brauer--Gorenstein, Chapter II Section 1 Lemma 3, article p.10,
classifies subgroups X of a wreathed group S which contain their ambient
centralizer and whose automorphism group is not a two-group. Such X is
the abelian base U or is isomorphic to a quaternion central product with
Z(S); its index in its normalizer is two, and every isomorphic subgroup
of S is conjugate to X. These three conclusions are assembled in
`lemma_three`. Source: `refs/latex/alperin-brauer-gorenstein-pages/page-011.tex`.

The abelian case follows from the outer-centralizer models. In the
nonabelian case the characteristic-center automorphism kernel and the
dihedral central quotient force X/Z(X) to be Klein four. Thus X has order
2^(n+2) and the small-central-extension classification makes it conjugate
to either the canonical quaternion central product V or the modular
extension. The latter has a two-group of automorphisms and is excluded.
The normalizer index and conjugacy statements then transport from V;
for U, normality and uniqueness among abelian subgroups of its order suffice.

The sharper companion results retain a conjugator to V and an actual
quaternion subgroup whose join with the ambient center is X. These supply
the embedded subgroup choices required by the subsequent fusion analysis.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

private theorem nonabelian_exception_conjugate (X : Subgroup S)
    (hc : Subgroup.centralizer (X : Set S) ≤ X)
    (hna : ¬ IsMulCommutative X) (hAut : ¬ IsPGroup 2 (MulAut X)) :
    ∃ g : S, P.V.map (MulAut.conj g).toMonoidHom = X := by
  have hfour := P.centric_quotient_isFourGroup X hc hna hAut
  have hcard : Nat.card X = 2 ^ (n + 2) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X),
      hfour.card_four, (P.centric_center_structure X hc hna).2, pow_add]
    ring
  have hnot : ¬ X ≤ P.U := by
    intro h
    apply hna
    apply IsMulCommutative.of_comm
    intro a b
    apply Subtype.ext
    exact (P.commute_of_mem_U (h a.property) (h b.property)).eq
  obtain ⟨g, hg | hg⟩ := P.small_central_extension_conjugacy X
    ((Subgroup.center_le_centralizer _).trans hc) hcard hnot
  · exact ⟨g, hg⟩
  · exfalso
    apply hAut
    let e : P.modularOvergroup ≃* X :=
      ((MulAut.conj g).subgroupMap P.modularOvergroup).trans (MulEquiv.subgroupCongr hg)
    exact P.modular_aut_isPGroup.of_equiv (MulAut.congr e)

private theorem conjugate_normalizer_index (X : Subgroup S)
    (hX : ∃ g : S, P.V.map (MulAut.conj g).toMonoidHom = X) :
    X.relIndex (Subgroup.normalizer (X : Set S)) = 2 := by
  obtain ⟨g, rfl⟩ := hX
  rw [← Subgroup.map_normalizer_eq_of_bijective P.V
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).bijective,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  exact P.V_normalizer_index

private theorem base_normalizer_index :
    P.U.relIndex (Subgroup.normalizer (P.U : Set S)) = 2 := by
  let : P.U.Normal := Subgroup.normal_of_index_eq_two P.index_U
  rw [Subgroup.normalizer_eq_top, Subgroup.relIndex_top_right, P.index_U]

private theorem base_isomorphic_eq (X : Subgroup S) (hX : Nonempty (X ≃* P.U)) :
    X = P.U := by
  let : Finite S := Nat.finite_of_card_ne_zero (by rw [P.card]; positivity)
  obtain ⟨e⟩ := hX
  apply P.abelian_eq_U_of_card_eq X
  · apply IsMulCommutative.of_comm
    intro a b
    apply e.injective
    simp only [map_mul]
    exact P.base_structure.2.2.1.is_comm.comm _ _
  · exact Nat.card_congr e.toEquiv

private theorem exceptional_isomorphic_conjugate (X Z : Subgroup S)
    (hX : Nonempty (X ≃* P.V)) (hZ : Nonempty (Z ≃* X)) :
    ∃ g : S, X.map (MulAut.conj g).toMonoidHom = Z := by
  obtain ⟨e⟩ := hX
  obtain ⟨f⟩ := hZ
  obtain ⟨a, ha⟩ := P.V_isomorphic_conjugate X ⟨e⟩
  obtain ⟨b, hb⟩ := P.V_isomorphic_conjugate Z ⟨f.trans e⟩
  refine ⟨b * a⁻¹, ?_⟩
  rw [← ha, Subgroup.map_map]
  convert hb using 2
  ext x
  simp [MulAut.conj_apply]
  group

end ABG.Wreathed.Presentation

namespace ABG.Wreathed
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

/-- An exceptional centric subgroup is the base or a conjugate of the canonical central product. -/
public theorem exceptional_centric_classification (X : Subgroup S)
    (hc : Subgroup.centralizer (X : Set S) ≤ X)
    (hAut : ¬ IsPGroup 2 (MulAut X)) :
    X = P.U ∨ ∃ g : S, P.V.map (MulAut.conj g).toMonoidHom = X := by
  by_cases hab : IsMulCommutative X
  · exact Or.inl (P.abelian_centric_exception_eq_U X hc hab hAut)
  · exact Or.inr (P.nonabelian_exception_conjugate X hc hab hAut)

/-- The nonabelian alternative retains an actual quaternion subgroup in the ambient group. -/
public theorem exceptional_centric_quaternion_join (X : Subgroup S)
    (hc : Subgroup.centralizer (X : Set S) ≤ X)
    (hAut : ¬ IsPGroup 2 (MulAut X)) :
    X = P.U ∨ ∃ Q : Subgroup S, IsQuaternionGroup Q ∧
      X = Q ⊔ Subgroup.center S := by
  rcases exceptional_centric_classification P X hc hAut with h | ⟨g, hg⟩
  · exact Or.inl h
  · right
    exact P.V_isomorphic_quaternion_join X
      ⟨(MulEquiv.subgroupCongr hg.symm).trans ((MulAut.conj g).subgroupMap P.V).symm⟩

/-- All three clauses of ABG Chapter II Section 1 Lemma 3. -/
public theorem lemma_three (X : Subgroup S)
    (hc : Subgroup.centralizer (X : Set S) ≤ X)
    (hAut : ¬ IsPGroup 2 (MulAut X)) :
    (X = P.U ∨ ∃ Y Q : Subgroup S, IsQuaternionGroup Q ∧
      Stellmacher.Later.IsCentralProductModel Y Q (Subgroup.center S) ∧
      Nonempty (X ≃* Y)) ∧
    X.relIndex (Subgroup.normalizer (X : Set S)) = 2 ∧
    ∀ Z : Subgroup S, Nonempty (Z ≃* X) →
      ∃ g : S, X.map (MulAut.conj g).toMonoidHom = Z := by
  rcases exceptional_centric_classification P X hc hAut with rfl | hX
  · refine ⟨Or.inl rfl, P.base_normalizer_index, ?_⟩
    intro Z hZ
    have hZU := P.base_isomorphic_eq Z hZ
    refine ⟨1, ?_⟩
    have hid : (MulAut.conj (1 : S)).toMonoidHom = MonoidHom.id S := by
      ext a
      simp
    rw [hid, Subgroup.map_id, hZU]
  · obtain ⟨g, hg⟩ := hX
    have he : Nonempty (X ≃* P.V) :=
      ⟨(MulEquiv.subgroupCongr hg.symm).trans ((MulAut.conj g).subgroupMap P.V).symm⟩
    exact ⟨Or.inr ⟨P.V, P.quaternionCore, P.quaternion_core_model.1,
      P.central_product_model, he⟩, P.conjugate_normalizer_index X ⟨g, hg⟩,
      fun Z hZ => P.exceptional_isomorphic_conjugate X Z he hZ⟩

end ABG.Wreathed
