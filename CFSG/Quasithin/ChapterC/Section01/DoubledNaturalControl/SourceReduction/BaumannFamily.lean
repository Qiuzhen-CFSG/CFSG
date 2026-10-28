module

public import CFSG.Quasithin.ChapterC.Section01.DoubledNaturalControl.SourceReduction.Contracts
public import CFSG.Quasithin.ChapterC.Section01.DoubledNaturalControl.SourceReduction.BaumannFamily.Geometry

/-!
# The three-conjugate Baumann family for the doubled-natural source

The action quotient is identified with the supplied SL₃(2) marking. The
module marking then gives an equivalence from each actual fixed subgroup to
its doubled matrix fixed space. The shear calculation proves that every
nontrivial subgroup of the radical image has fixed codimension two, without
requiring an elementary lift to the source group.

Three matrix conjugators lift through L. Their conjugates of J(R) generate
the action image, have full two-rank, and have codimension sum six, equal to
the full component codimension. The first conjugator is the identity, giving
the separate J(R) containment. The remaining Baumann premises follow from
C_K(U) = O₂(K) and O²(K) = L, retaining the literal Frattini preimage.

Source: Aschbacher--Smith C.1.37, printed pp.142--143, and B.2.18(a)--(e),
printed pp.80--81. The offender comparison is the explicit `OffenderData`
input; this module supplies its independent Baumann-family consequence.
-/

@[expose] public section

open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.DoubledNaturalControl.SourceReduction
open ChapterB ChapterB.BaumannArgument BaumannGeometry
universe u
variable {K : Type u} [Group K]
  {κ : GroupClass.{u}} {L P U : Subgroup K} [L.Normal] [U.Normal]
  {T : Sylow 2 K} (d : SourceData κ L P U T)
namespace SourceData

/-- The actual faithful action quotient, in the prescribed matrix coordinates. -/
noncomputable def actionEquiv : (K ⧸ centralizer (U : Set K)) ≃* SL :=
  (QuotientGroup.quotientMulEquivOfEq d.centralizer_eq_core).trans d.eK

/-- This quotient identification agrees with the original ambient projection. -/
theorem actionEquiv_apply (k : K) :
    d.actionEquiv (actionMap U k) = d.ρK k := by
  change d.eK ((QuotientGroup.quotientMulEquivOfEq d.centralizer_eq_core)
    (QuotientGroup.mk k)) = d.eK (QuotientGroup.mk k)
  rw [QuotientGroup.quotientMulEquivOfEq_mk]

/-- Subgroup images use the same projection under the action identification. -/
theorem action_image_eq (A : Subgroup K) :
    (A.map (actionMap U)).map d.actionEquiv.toMonoidHom = A.map d.ρK := by
  rw [map_map]
  congr 1

/-- Orders of action images are preserved by the marked quotient equivalence. -/
theorem action_image_card (A : Subgroup K) :
    Nat.card (A.map (actionMap U)) = Nat.card (A.map d.ρK) := by
  rw [← d.action_image_eq A, card_map_of_injective (f := d.actionEquiv.toMonoidHom) d.actionEquiv.injective]

/-- Centralizing the actual acting subgroup is exactly matrix fixedness. -/
theorem fixed_iff_model (A : Subgroup K) (u : U) :
    (u : K) ∈ centralizer (A : Set K) ↔
      ∀ g ∈ A.map d.ρK, ∀ i,
        g • Multiplicative.toAdd (d.eU u) i = Multiplicative.toAdd (d.eU u) i := by
  constructor
  · intro hu g hg i
    obtain ⟨a, ha, rfl⟩ := hg
    have hc : MulAut.conjNormal a u = u := by
      apply Subtype.ext
      change a * (u : K) * a⁻¹ = (u : K)
      rw [mem_centralizer_iff.mp hu a ha, mul_inv_cancel_right]
    have h := congrFun (d.action a u) i
    rw [hc] at h
    exact h.symm
  · intro hf
    apply mem_centralizer_iff.mpr
    intro a ha
    have hc : MulAut.conjNormal a u = u := by
      apply d.eU.injective
      apply Multiplicative.toAdd.injective
      rw [d.action]
      funext i
      exact hf (d.ρK a) (mem_map_of_mem _ ha) i
    have h := congrArg Subtype.val hc
    change a * (u : K) * a⁻¹ = (u : K) at h
    exact mul_inv_eq_iff_eq_mul.mp h

/-- The original module marking restricts to an equivalence of fixed sets. -/
noncomputable def fixedModelEquiv (A : Subgroup K) :
    ↥(U ⊓ centralizer (A : Set K)) ≃ modelFixed (A.map d.ρK) where
  toFun x := ⟨Multiplicative.toAdd (d.eU ⟨x, x.property.1⟩),
    (d.fixed_iff_model A ⟨x, x.property.1⟩).mp x.property.2⟩
  invFun v :=
    ⟨d.eU.symm (Multiplicative.ofAdd v.val),
      (d.eU.symm (Multiplicative.ofAdd v.val)).property,
      (d.fixed_iff_model A (d.eU.symm (Multiplicative.ofAdd v.val))).mpr (by
        rw [MulEquiv.apply_symm_apply]
        exact v.property)⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv v := by apply Subtype.ext; simp

/-- The matrix fixed-set count is the order of the actual fixed subgroup. -/
theorem fixed_card_model (A : Subgroup K) :
    Nat.card ↥(U ⊓ centralizer (A : Set K)) = Nat.card (modelFixed (A.map d.ρK)) :=
  Nat.card_congr (d.fixedModelEquiv A)

/-- Every nontrivial subgroup of a conjugate shear radical has doubled codimension two. -/
theorem fixedCodim_of_image (A : Subgroup K) (g : SL)
    (hA : A.map d.ρK ≤ BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom)
    (hne : A.map d.ρK ≠ ⊥) : fixedCodim U A = 2 := by
  rw [fixedCodim, d.source_module_card, d.fixed_card_model,
    card_fixed_of_le_conjugate (A.map d.ρK) g hA hne]
  decide

/-- The bound tests all subgroups of R, including elementary images without elementary lifts. -/
theorem noStrongOffenders_of_plane (ho : OffenderData d) : NoStrongOffenders U (R P) := by
  intro A hA _ hne
  obtain ⟨g, hg⟩ := ho.plane_radical
  have hle : A.map d.ρK ≤ BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom :=
    (map_mono hA).trans_eq hg
  have hn : A.map d.ρK ≠ ⊥ := by
    intro he
    apply hne
    apply (map_injective (f := d.actionEquiv.toMonoidHom) d.actionEquiv.injective)
    rw [d.action_image_eq, he, Subgroup.map_bot]
  rw [d.action_image_card, d.fixedCodim_of_image A g hle hn]
  have hc := card_le_four_of_le_conjugate (A.map d.ρK) g hle
  exact (Nat.log_mono_right hc).trans_eq (by decide : Nat.log 2 4 = 2)

variable [Finite K]

include d in
/-- The full component has no fixed vectors in either natural summand. -/
theorem residual_fixedCodim : fixedCodim U (pResidual 2 K) = 6 := by
  rw [d.residual_eq, fixedCodim, d.source_module_card, d.source_module_fixed]
  simp only [Nat.card_unique, Nat.log_one_right, Nat.sub_zero]
  decide

include d in
private theorem baumann_structural :
    IsPGroup 2 (R P) ∧ U ≤ R P ∧
    (pCore 2 (pResidual 2 K)).map (pResidual 2 K).subtype ≤
      R P ⊓ centralizer (U : Set K) ∧
    pResidual 2 K ≤ normalizer (R P ⊓ centralizer (U : Set K) : Set K) ∧
    pResidual 2 K ⊓ centralizer (U : Set K) ≤ coreFrattini (pResidual 2 K) := by
  rw [d.residual_eq, d.centralizer_eq_core, inf_eq_right.mpr d.core_le_radical]
  have hcore : pCore 2 L = Q.comap L.subtype :=
    pCore_subnormal_eq_comap 2 (show L.IsSubnormal from (show L.Normal from inferInstance).isSubnormal)
  refine ⟨pCore_isPGroup.map P.subtype, d.source_module_le_radical, ?_, ?_, ?_⟩
  · rw [hcore, map_comap_eq, range_subtype]
    exact inf_le_right
  · change L ≤ normalizer ((R P ⊓ Q : Subgroup K) : Set K)
    rw [inf_eq_right.mpr d.core_le_radical, normalizer_eq_top]
    exact le_top
  · rintro x ⟨hxL, hxQ⟩
    refine ⟨⟨x, hxL⟩, ?_, rfl⟩
    have hx : (⟨x, hxL⟩ : L) ∈ pCore 2 L := by rwa [hcore]
    change QuotientGroup.mk' (pCore 2 L) (⟨x, hxL⟩ : L) ∈ frattini (L ⧸ pCore 2 L)
    have hx1 : QuotientGroup.mk' (pCore 2 L) (⟨x, hxL⟩ : L) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hx
    rw [hx1]
    exact one_mem _

private theorem thompson_self (S : Subgroup K) :
    elementaryAbelianMaxJ (elementaryAbelianMaxJ S) = elementaryAbelianMaxJ S := by
  have hle : elementaryAbelianMaxJ S ≤ S := sSup_le fun _ hA => hA.1
  have h := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le S
    (elementaryAbelianMaxJ S) le_rfl
  have he : elementaryAbelianMaxOrder S = elementaryAbelianMaxOrder (elementaryAbelianMaxJ S) :=
    le_antisymm h.1 (elementaryAbelianMaxOrder_le_and_j_le_of_eq _ _ hle).1
  exact le_antisymm (sSup_le fun _ hA => hA.1) (h.2 he)

omit [Finite K] in
private theorem lift_coordinate_conjugators (g : SL) :
    ∃ l : Fin 3 → L, l 0 = 1 ∧
      ∀ i, d.ρK (l i) = g * coordinateConjugator i * g⁻¹ := by
  classical
  let l : Fin 3 → L := fun i => if i = 0 then 1 else
    (d.component_surjective (g * coordinateConjugator i * g⁻¹)).choose
  refine ⟨l, by simp [l], ?_⟩
  intro i
  by_cases hi : i = 0
  · subst i
    simp [l, coordinateConjugator]
  · simp only [l, if_neg hi]
    exact (d.component_surjective (g * coordinateConjugator i * g⁻¹)).choose_spec

/-- The family starts at J(R), consists of actual L-conjugates, and satisfies all Baumann premises. -/
theorem baumann_family_with_first (ho : OffenderData d) :
    ∃ f : BaumannFamily d, f.X 0 = elementaryAbelianMaxJ (R P) ∧
      ∀ i, ∃ l ∈ L,
        f.X i = (elementaryAbelianMaxJ (R P)).map (MulAut.conj l).toMonoidHom := by
  classical
  obtain ⟨g, hg⟩ := ho.plane_radical
  obtain ⟨l, hl0, hl⟩ := d.lift_coordinate_conjugators g
  let X : Fin 3 → Subgroup K := fun i =>
    (elementaryAbelianMaxJ (R P)).map (MulAut.conj (l i : K)).toMonoidHom
  have hX0 : X 0 = elementaryAbelianMaxJ (R P) := by
    change (elementaryAbelianMaxJ (R P)).map (MulAut.conj (l 0 : K)).toMonoidHom = _
    rw [hl0]
    exact map_conj_one _
  have hJR : elementaryAbelianMaxJ (R P) ≤ R P := sSup_le fun _ hA => hA.1
  have himage (i : Fin 3) : (X i).map d.ρK =
      BinaryLinearThree.R.map (MulAut.conj (g * coordinateConjugator i)).toMonoidHom := by
    dsimp only [X]
    rw [map_conjugate, ho.thompson_image, hg, hl, map_conj_mul]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  have hgen : (⨆ i, (X i).map d.ρK) = ⊤ := by
    simp_rw [himage]
    exact conjugate_coordinate_generation g
  have hcodim (i : Fin 3) : fixedCodim U (X i) = 2 := by
    apply d.fixedCodim_of_image (X i) (g * coordinateConjugator i)
    · exact (himage i).le
    · rw [himage]
      intro hz
      have hc := card_map_of_injective (K := BinaryLinearThree.R)
        (f := (MulAut.conj (g * coordinateConjugator i)).toMonoidHom)
        (MulAut.conj (g * coordinateConjugator i)).injective
      rw [hz, BinaryLinearThree.card_R] at hc
      simp at hc
  obtain ⟨htwo, hU, hcore, hnorm, hfrat⟩ := d.baumann_structural
  refine ⟨⟨X, ⟨htwo, hU, hcore, hnorm, hfrat, d.noStrongOffenders_of_plane ho,
    ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, hX0, ?_⟩
  · intro i
    refine ⟨(l i : K)⁻¹, ?_, ?_⟩
    · rw [d.residual_eq]
      exact L.inv_mem (l i).property
    · change ((elementaryAbelianMaxJ (R P)).map (MulAut.conj (l i : K)).toMonoidHom).map
        (MulAut.conj (l i : K)⁻¹).toMonoidHom ≤ R P
      rw [map_conj_mul, inv_mul_cancel]
      exact (map_conj_one _).le.trans hJR
  · intro i
    dsimp only [X]
    rw [elementaryAbelianMaxJ_map_equiv, thompson_self]
  · intro i
    dsimp only [X]
    rw [twoRank_map_equiv]
    exact twoRank_eq_of_intermediate (R P) (elementaryAbelianMaxJ (R P)) le_rfl hJR
  · apply (map_le_map_iff_of_injective (f := d.actionEquiv.toMonoidHom) d.actionEquiv.injective).mp
    rw [Subgroup.map_iSup]
    simp_rw [d.action_image_eq]
    rw [hgen]
    exact le_top
  · simp_rw [hcodim]
    rw [d.residual_fixedCodim]
    decide
  · rw [← hX0]
    exact le_iSup X 0
  · intro i
    exact ⟨l i, (l i).property, rfl⟩

/-- The doubled-natural offender data supplies the complete Baumann family. -/
theorem baumann_family (ho : OffenderData d) : Nonempty (BaumannFamily d) := by
  obtain ⟨f, _⟩ := d.baumann_family_with_first ho
  exact ⟨f⟩

end SourceData
end CFSG.Quasithin.ChapterC.DoubledNaturalControl.SourceReduction
