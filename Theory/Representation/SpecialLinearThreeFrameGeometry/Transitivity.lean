module
public import Theory.Representation.SpecialLinearThreeFrameGeometry.Basis
public import Theory.Representation.SpecialLinearThreeTransitivity
public import Mathlib.LinearAlgebra.Projectivization.Action

/-!
# Projective transitivity for the concrete special linear group in dimension three

Choose nonzero vectors in an ordered direct frame to obtain a basis. A change
of bases maps the frame, and a dilation of one source basis vector corrects
its determinant without changing any projective point. Completing two points
to a frame then gives flag transitivity and the orbit of the flag stabilizer
on the other points in its plane. The projective two-transitivity instance is
also connected explicitly to the literal natural matrix representation.

All statements hold over every field, in particular over finite fields of
characteristic two including F₂. Every actor belongs to SL₃ itself.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, G.1.1 and
Remark G.1.4, printed pp.327–328, PDF pp.338–339.
-/

@[expose] public section
noncomputable section
open Matrix Module Submodule
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup.FrameGeometry
variable {F : Type*} [Field F]

/-- Correct a change of frame by a dilation of its first line. -/
theorem exists_frame_map (b c : Frame F) :
    ∃ a : SL(3, F), ∀ i, (b.point i).map (natural a) = c.point i := by
  classical
  obtain ⟨e, he⟩ := b.exists_basis_lines
  obtain ⟨f, hf⟩ := c.exists_basis_lines
  let g := e.equiv f (Equiv.refl _)
  let u : Fˣ := g.det⁻¹
  let k : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F) :=
    LinearEquiv.dilatransvection (f := e.coord 0) (v := (u.val - 1) • e 0) (by simp)
  have hk : k.det = u := by
    apply Units.ext
    simp [k, LinearEquiv.coe_det, LinearMap.transvection.det]
  let a : SL(3, F) := ⟨LinearMap.toMatrix' (g * k).toLinearMap, by
    rw [LinearMap.det_toMatrix', ← LinearEquiv.coe_det, map_mul, hk]
    simp [u]⟩
  have ha (v : Fin 3 → F) : natural a v = g (k v) :=
    LinearMap.toMatrix'_mulVec _ v
  refine ⟨a, fun i => ?_⟩
  rw [he i, hf i, Submodule.map_span]
  simp only [Set.image_singleton]
  rw [ha]
  by_cases hi : i = 0
  · subst i
    have hk0 : k (e 0) = u.val • e 0 := by
      simp only [k, LinearEquiv.dilatransvection.apply, Basis.coord_apply, Basis.repr_self,
        Finsupp.single_eq_same, one_smul]
      module
    rw [hk0, map_smul]
    simp only [g, Basis.equiv_apply, Equiv.refl_apply]
    exact Submodule.span_singleton_smul_eq u.isUnit _
  · have hki : k (e i) = e i := by
      simp [k, LinearEquiv.dilatransvection.apply, Basis.coord_apply, Ne.symm hi]
    rw [hki]
    simp [g]

private theorem point_pair_disjoint {A B : Submodule F (Fin 3 → F)}
    (hA : finrank F A = 1) (hB : finrank F B = 1) (hAB : A ≠ B) : Disjoint A B :=
  (Submodule.isAtom_iff_finrank_eq_one.mpr hA).disjoint_of_ne
    (Submodule.isAtom_iff_finrank_eq_one.mpr hB) hAB

private theorem point_pair_dimension {A B : Submodule F (Fin 3 → F)}
    (hA : finrank F A = 1) (hB : finrank F B = 1) (hAB : A ≠ B) :
    finrank F (A ⊔ B : Submodule F (Fin 3 → F)) = 2 := by
  have ht := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [(point_pair_disjoint hA hB hAB).eq_bot, finrank_bot, hA, hB, add_zero] at ht
  exact ht

/-- Complete two distinct points to an ordered direct frame. -/
theorem exists_frame_of_pair (A B : Submodule F (Fin 3 → F))
    (hA : finrank F A = 1) (hB : finrank F B = 1) (hAB : A ≠ B) :
    ∃ b : Frame F, b.point 0 = A ∧ b.point 1 = B := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (A ⊔ B)
  have hdim := Submodule.finrank_add_eq_of_isCompl hC
  rw [point_pair_dimension hA hB hAB] at hdim
  have hCdim : finrank F C = 1 := by
    simp only [Module.finrank_fin_fun] at hdim
    omega
  exact ⟨⟨![A, B, C], by intro i; fin_cases i <;> assumption,
    point_pair_disjoint hA hB hAB, hC.disjoint, hC.sup_eq_top⟩, rfl, rfl⟩

/-- Choose a second point of an incident point-plane flag. -/
theorem exists_point_complement (A B : Submodule F (Fin 3 → F))
    (hA : finrank F A = 1) (hB : finrank F B = 2) (hAB : A ≤ B) :
    ∃ C : Submodule F (Fin 3 → F), finrank F C = 1 ∧ A ≠ C ∧ A ⊔ C = B := by
  have hBA : ¬ B ≤ A := by
    intro h
    have he := le_antisymm hAB h
    rw [he, hB] at hA
    contradiction
  obtain ⟨v, hvB, hvA⟩ := SetLike.not_le_iff_exists.mp hBA
  have hv0 : v ≠ 0 := by intro h; subst v; exact hvA A.zero_mem
  let C : Submodule F (Fin 3 → F) := F ∙ v
  have hC : finrank F C = 1 := finrank_span_singleton hv0
  have hAC : A ≠ C := by
    intro he
    apply hvA
    rw [he]
    exact mem_span_singleton_self v
  refine ⟨C, hC, hAC, ?_⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · exact sup_le hAB (span_le.mpr (Set.singleton_subset_iff.mpr hvB))
  · rw [point_pair_dimension hA hC hAC, hB]

/-- SL₃ is transitive on incident point-plane flags. -/
theorem exists_flag_map (A B C D : Submodule F (Fin 3 → F))
    (hA : finrank F A = 1) (hB : finrank F B = 2) (hAB : A ≤ B)
    (hC : finrank F C = 1) (hD : finrank F D = 2) (hCD : C ≤ D) :
    ∃ a : SL(3, F), A.map (natural a) = C ∧ B.map (natural a) = D := by
  obtain ⟨A', hA', hAA', hB'⟩ := exists_point_complement A B hA hB hAB
  obtain ⟨C', hC', hCC', hD'⟩ := exists_point_complement C D hC hD hCD
  obtain ⟨b, hb0, hb1⟩ := exists_frame_of_pair A A' hA hA' hAA'
  obtain ⟨c, hc0, hc1⟩ := exists_frame_of_pair C C' hC hC' hCC'
  obtain ⟨a, ha⟩ := exists_frame_map b c
  have h0 := ha 0
  have h1 := ha 1
  rw [hb0, hc0] at h0
  rw [hb1, hc1] at h1
  exact ⟨a, h0, by rw [← hB', ← hD', Submodule.map_sup, h0, h1]⟩

/-- The flag stabilizer is transitive on the other points of its plane. -/
theorem exists_flag_stabilizer_map (A B C D : Submodule F (Fin 3 → F))
    (hA : finrank F A = 1) (hB : finrank F B = 2) (hAB : A ≤ B)
    (hC : finrank F C = 1) (hD : finrank F D = 1)
    (hCB : C ≤ B) (hDB : D ≤ B) (hAC : A ≠ C) (hAD : A ≠ D) :
    ∃ a ∈ stabilizer A ⊓ stabilizer B, C.map (natural a) = D := by
  have hACB : A ⊔ C = B := Submodule.eq_of_le_of_finrank_eq (sup_le hAB hCB)
    ((point_pair_dimension hA hC hAC).trans hB.symm)
  have hADB : A ⊔ D = B := Submodule.eq_of_le_of_finrank_eq (sup_le hAB hDB)
    ((point_pair_dimension hA hD hAD).trans hB.symm)
  obtain ⟨b, hb0, hb1⟩ := exists_frame_of_pair A C hA hC hAC
  obtain ⟨c, hc0, hc1⟩ := exists_frame_of_pair A D hA hD hAD
  obtain ⟨a, ha⟩ := exists_frame_map b c
  have h0 := ha 0
  have h1 := ha 1
  rw [hb0, hc0] at h0
  rw [hb1, hc1] at h1
  refine ⟨a, ⟨(mem_stabilizer_iff A a).mpr h0, (mem_stabilizer_iff B a).mpr ?_⟩, h1⟩
  calc
    B.map (natural a) = (A ⊔ C).map (natural a) := by rw [hACB]
    _ = A ⊔ D := by rw [Submodule.map_sup, h0, h1]
    _ = B := hADB

/-- Single-point transitivity from the actual nonzero-vector theorem. -/
theorem exists_point_map (A B : Submodule F (Fin 3 → F))
    (hA : finrank F A = 1) (hB : finrank F B = 1) :
    ∃ a : SL(3, F), A.map (natural a) = B := by
  let p := Projectivization.mk'' A hA
  let q := Projectivization.mk'' B hB
  obtain ⟨a, ha⟩ := exists_mulVec_eq_three p.rep q.rep p.rep_nonzero q.rep_nonzero
  refine ⟨a, ?_⟩
  have hp : A = F ∙ p.rep := (Projectivization.submodule_mk'' A hA).symm.trans p.submodule_eq
  have hq : B = F ∙ q.rep := (Projectivization.submodule_mk'' B hB).symm.trans q.submodule_eq
  rw [hp, hq, Submodule.map_span, Set.image_singleton]
  exact congrArg (fun v => F ∙ v) ha

private theorem submodule_smul (a : SL(3, F))
    (p : Projectivization F (Fin 3 → F)) :
    (a • p).submodule = p.submodule.map (natural a) := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [Projectivization.smul_mk, Projectivization.submodule_mk,
      Projectivization.submodule_mk, Submodule.map_span, Set.image_singleton]
    rfl

/-- The projective two-transitivity instance acts by the literal natural matrix maps. -/
theorem exists_point_pair_map (A B C D : Submodule F (Fin 3 → F))
    (hA : finrank F A = 1) (hB : finrank F B = 1)
    (hC : finrank F C = 1) (hD : finrank F D = 1) (hAB : A ≠ B) (hCD : C ≠ D) :
    ∃ a : SL(3, F), A.map (natural a) = C ∧ B.map (natural a) = D := by
  let p := Projectivization.mk'' A hA
  let q := Projectivization.mk'' B hB
  let r := Projectivization.mk'' C hC
  let s := Projectivization.mk'' D hD
  have hpq : p ≠ q := by
    intro he
    apply hAB
    simpa [p, q] using congrArg Projectivization.submodule he
  have hrs : r ≠ s := by
    intro he
    apply hCD
    simpa [r, s] using congrArg Projectivization.submodule he
  obtain ⟨a, ha, hb⟩ :=
    (MulAction.is_two_pretransitive_iff (G := SL(3, F)) (α := Projectivization F (Fin 3 → F))).mp
      inferInstance hpq hrs
  refine ⟨a, ?_, ?_⟩
  · have he := congrArg Projectivization.submodule ha
    simpa only [submodule_smul, p, r, Projectivization.submodule_mk''] using he
  · have he := congrArg Projectivization.submodule hb
    simpa only [submodule_smul, q, s, Projectivization.submodule_mk''] using he

end Matrix.SpecialLinearGroup.FrameGeometry
