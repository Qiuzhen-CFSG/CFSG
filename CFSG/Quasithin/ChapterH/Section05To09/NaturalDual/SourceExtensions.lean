module

public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceSylowMarking
public import Theory.ElementaryAbelian.Quotient


/-!
# Actual source stabilizer extensions in H.9.1

The constructed source comparison restricts to the pure point stabilizer.
Its intrinsic two-core is elementary, and the quotient identification retains
its literal action on the annihilator hyperplane. For a nonsingular vector,
every independently chosen stabilizer Sylow contains an outer involution.
It complements the relative layer stabilizer with the actual conjugation
semidirect product, and the embedded full two-residual is the source residual.

Source: Aschbacher–Smith H.9.1(3–4), printed pp.389–390, with the corrected
Sylow marking of 6 October 2026.
-/

@[expose] public section

open BinaryNaturalDual BinaryNaturalDual.ModelOrbits BinaryNaturalDual.VectorStabilizers
open BinaryLinear.OuterCyclic Theory.GroupTheory
namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
variable {n : ℕ} {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]
  (S : SourceSetup n M V)

theorem naturalCoordinates_ne_zero (u : S.natural) (hu : (u : V) ≠ 0) :
    S.naturalCoordinates u ≠ 0 := by
  intro h
  exact hu (congrArg Subtype.val (S.naturalCoordinates.injective (h.trans (map_zero _).symm)))

noncomputable def pureInnerEquiv (u : S.natural) (hu : (u : V) ≠ 0) :
    S.stabilizer u ≃* VectorStabilizers.innerStabilizer
      (AutomorphismModel.coordinateAction S.degree) (S.naturalCoordinates u,0) :=
  (S.stabilizerEquiv u).trans (MulEquiv.subgroupCongr
    ((congrArg (fullStabilizer _) (S.model.natural_marking u)).trans
      (pure_fullStabilizer_eq_innerStabilizer S.degree _ (S.naturalCoordinates_ne_zero u hu))))

@[simp] theorem pureInnerEquiv_apply (u : S.natural) (hu : (u : V) ≠ 0)
    (g : S.stabilizer u) : (S.pureInnerEquiv u hu g).val = S.model.group g :=
  S.stabilizerEquiv_apply u g

noncomputable def purePointEquiv (u : S.natural) (hu : (u : V) ≠ 0) :
    S.stabilizer u ≃* Pure.pointStabilizer (S.naturalCoordinates u) :=
  (S.pureInnerEquiv u hu).trans (Pure.innerEquivPoint _ _)

/-- The elementary radical is the intrinsic two-core of the source stabilizer. -/
theorem pure_twoCore (u : S.natural) (hu : (u : V) ≠ 0) :
    IsElementaryAbelian 2 (pCore 2 (S.stabilizer u)) ∧
    Nat.card (pCore 2 (S.stabilizer u)) = 2 ^ (n - 1) := by
  let e := S.pureInnerEquiv u hu
  have hm : (pCore 2 (S.stabilizer u)).map e.toMonoidHom =
      Pure.innerRadical (AutomorphismModel.coordinateAction S.degree) (S.naturalCoordinates u) :=
    (pCore_map_iso 2 e).trans (Pure.inner_twoCore _ _)
  let E := (e.subgroupMap (pCore 2 (S.stabilizer u))).trans (MulEquiv.subgroupCongr hm)
  let := Pure.innerRadical_elementary (AutomorphismModel.coordinateAction S.degree) (S.naturalCoordinates u)
  exact ⟨IsElementaryAbelian.of_surjective E.symm.toMonoidHom E.symm.surjective,
    (Nat.card_congr E.toEquiv).trans (Pure.innerRadical_card _ (S.naturalCoordinates_ne_zero u hu))⟩

/-- The quotient identification is induced by the action on the annihilator. -/
noncomputable def pureQuotientEquiv (u : S.natural) (hu : (u : V) ≠ 0) :
    (S.stabilizer u ⧸ pCore 2 (S.stabilizer u)) ≃*
      BinaryLinear.GL (annihilator (S.naturalCoordinates u)) :=
  (QuotientGroup.congr _ _ (S.purePointEquiv u hu)
    (pCore_map_iso 2 (S.purePointEquiv u hu))).trans
      (Pure.pointQuotientTwoCoreEquivAnnihilator _)

theorem pureQuotientEquiv_action (u : S.natural) (hu : (u : V) ≠ 0)
    (g : S.stabilizer u) (f : annihilator (S.naturalCoordinates u)) :
    S.representation g.val (S.model.dualCoordinates.symm f.val : V) =
      (S.model.dualCoordinates.symm
        ((S.pureQuotientEquiv u hu (QuotientGroup.mk' _ g) f).val) : V) := by
  apply S.model.coordinates.injective
  rw [S.model.equivariant, S.model.dual_marking, LinearEquiv.apply_symm_apply,
    S.model.dual_marking, LinearEquiv.apply_symm_apply]
  have h := Pure.inner_annihilator_action _ _ (S.pureInnerEquiv u hu g) f
  rw [S.pureInnerEquiv_apply] at h
  exact h

/-- The actual pure stabilizer modulo O₂ is L_(n−1)(2). -/
theorem pure_quotient_projective (u : S.natural) (hu : (u : V) ≠ 0) :
    Nonempty ((S.stabilizer u ⧸ pCore 2 (S.stabilizer u)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin (n - 1)) (ZMod 2)) := by
  let d := AutomorphismModel.coordinateAction S.degree
  let e := S.pureInnerEquiv u hu
  exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    ((QuotientGroup.quotientMulEquivOfEq (Pure.inner_twoCore d _)).trans
      ((Pure.innerQuotientEquivLinear d (S.naturalCoordinates_ne_zero u hu)).trans
        (projectiveEquivLinear (by have := S.degree; omega)).symm))⟩

/-- The inner subgroup of a source vector stabilizer, as a relative subgroup. -/
def innerInStabilizer (v : V) : Subgroup (S.stabilizer v) :=
  (componentLayer M).comap (S.stabilizer v).subtype

instance innerInStabilizer_normal (v : V) : (S.innerInStabilizer v).Normal :=
  ⟨by
    intro a ha b
    apply (S.model.inner_iff _).mp
    change S.model.group (b.val * a.val * b.val⁻¹) ∈ _
    simp only [map_mul, map_inv]
    exact Subgroup.Normal.conj_mem inferInstance _ ((S.model.inner_iff a.val).mpr ha) _⟩

theorem innerInStabilizer_map (v : V) :
    (S.innerInStabilizer v).map (S.stabilizerEquiv v).toMonoidHom =
      innerInFull (AutomorphismModel.coordinateAction S.degree) (S.model.coordinates v) := by
  ext a
  constructor
  · rintro ⟨g,hg,rfl⟩
    apply (mem_innerInFull _ _ _).mpr
    change (S.stabilizerEquiv v g).val ∈ _
    rw [S.stabilizerEquiv_apply]
    exact (S.model.inner_iff g).mpr hg
  · intro ha
    refine ⟨(S.stabilizerEquiv v).symm a, ?_, (S.stabilizerEquiv v).apply_symm_apply a⟩
    apply (S.model.inner_iff _).mp
    have he : S.model.group ((S.stabilizerEquiv v).symm a).val = a.val :=
      by simpa only [S.stabilizerEquiv_apply] using
        congrArg Subtype.val ((S.stabilizerEquiv v).apply_symm_apply a)
    change S.model.group ((S.stabilizerEquiv v).symm a).val ∈ _
    rw [he]
    exact (mem_innerInFull _ _ _).mp ha

private theorem complement_of_map {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (A B : Subgroup G)
    (h : (A.map e.toMonoidHom).IsComplement' (B.map e.toMonoidHom)) : A.IsComplement' B := by
  have hd : Disjoint A B := by
    apply Subgroup.disjoint_def.mpr
    intro a ha hb
    apply e.injective
    simpa using (Subgroup.disjoint_def.mp h.disjoint)
      (Subgroup.mem_map_of_mem e.toMonoidHom ha) (Subgroup.mem_map_of_mem e.toMonoidHom hb)
  refine ⟨Subgroup.mul_injective_of_disjoint hd, ?_⟩
  intro g
  obtain ⟨⟨a,b⟩,hab⟩ := h.2 (e g)
  obtain ⟨a',ha,ea⟩ := a.property
  obtain ⟨b',hb,eb⟩ := b.property
  refine ⟨(⟨a',ha⟩,⟨b',hb⟩),e.injective ?_⟩
  change e (a' * b') = e g
  change e a' = a.val at ea
  change e b' = b.val at eb
  rw [map_mul, ea, eb]
  exact hab

/-- Every outer involution in the source stabilizer gives its internal split extension. -/
theorem nonsingular_outer_complement {v : V} (hv : S.quadratic v = 1)
    (s : S.stabilizer v) (hout : s.val ∉ componentLayer M) (hs : s ^ 2 = 1) :
    (S.innerInStabilizer v).IsComplement' (Subgroup.zpowers s) := by
  apply complement_of_map (S.stabilizerEquiv v)
  rw [S.innerInStabilizer_map, MonoidHom.map_zpowers]
  exact outer_isComplement S.degree _ (by simpa [S.quadratic_apply, BinaryNaturalDual.quadratic_apply] using hv)
    _ (by
      intro h
      apply hout
      apply (S.model.inner_iff s).mp
      change (S.stabilizerEquiv v s).val ∈ _ at h
      rwa [S.stabilizerEquiv_apply] at h)
    (by simp [← map_pow, hs])

/-- The semidirect product uses the actual conjugation action in the source stabilizer. -/
noncomputable def nonsingularSemidirectEquiv {v : V} (hv : S.quadratic v = 1)
    (s : S.stabilizer v) (hout : s.val ∉ componentLayer M) (hs : s ^ 2 = 1) :
    (S.innerInStabilizer v) ⋊[(S.innerInStabilizer v).normalizerMonoidHom.comp
      (Subgroup.inclusion ((S.innerInStabilizer v).normalizer_eq_top ▸ le_top))]
      (Subgroup.zpowers s) ≃* S.stabilizer v :=
  SemidirectProduct.mulEquivSubgroup (S.nonsingular_outer_complement hv s hout hs)

/-- Every independently chosen source stabilizer Sylow contains an outer involution. -/
theorem nonsingular_sylow_outer {v : V} (hv : S.quadratic v = 1)
    (P : Sylow 2 (S.stabilizer v)) :
    ∃ s : S.stabilizer v, s ∈ P ∧ s.val ∉ componentLayer M ∧ s ^ 2 = 1 ∧
      (S.innerInStabilizer v).IsComplement' (Subgroup.zpowers s) := by
  let := S.finite_group
  let e := S.stabilizerEquiv v
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨a,ha,hout,hs,_⟩ := sylow_exists_outer_involution S.degree _
    (by simpa [S.quadratic_apply, BinaryNaturalDual.quadratic_apply] using hv) P'
  let s := e.symm a
  have he : S.model.group s.val = a.val := by
    simpa only [e, S.stabilizerEquiv_apply] using congrArg Subtype.val (e.apply_symm_apply a)
  have ho : s.val ∉ componentLayer M := by
    intro h
    exact hout (he ▸ (S.model.inner_iff s.val).mpr h)
  have hs' : s ^ 2 = 1 := by simp [s, ← map_pow, hs]
  refine ⟨s, ?_, ho, hs', S.nonsingular_outer_complement hv s ho hs'⟩
  change a ∈ (P : Subgroup _).map e.toMonoidHom at ha
  change e.symm a ∈ (P : Subgroup _)
  simpa only [Subgroup.mem_map_equiv] using ha

/-- Both the full and inner point centralizers have the same embedded two-residual. -/
theorem nonsingular_full_residual {v : V} (hv : S.quadratic v = 1) :
    (pResidual 2 (S.stabilizer v)).map (S.stabilizer v).subtype = S.residual v := by
  let := S.finite_group
  apply Subgroup.map_injective (f := S.model.group.toMonoidHom) S.model.group.injective
  rw [Subgroup.map_embedded_pResidual, S.stabilizer_map, S.residual_map,
    innerResidual_eq_innerStabilizer S.degree _
      (by simpa [S.quadratic_apply, BinaryNaturalDual.quadratic_apply] using hv)]
  exact fullStabilizer_embedded_twoResidual S.degree _
    (by simpa [S.quadratic_apply, BinaryNaturalDual.quadratic_apply] using hv)

end CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
