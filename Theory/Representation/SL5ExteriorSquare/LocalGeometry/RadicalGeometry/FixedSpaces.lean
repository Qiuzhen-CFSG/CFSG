module
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.RadicalGeometry.Shears
public import Theory.Representation.BinaryOffender.SubspaceAction
import Mathlib.Tactic.FinCases

/-!
# Fixed spaces of the last-column shear subgroup

The quotient coordinate of a vector fixed by a nonidentity shear lies on the
line of its parameter. Thus any parameter space of dimension at least two fixes
exactly Λ²Γ₄, while the individual fixed spaces span the exterior square.
Reference: Aschbacher--Smith 12.5.7 and 12.5.10, printed pp.820--821.
-/

@[expose] public section
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

/-- Embed the four-dimensional parameter space as Γ₄ in the natural module. -/
def shearNatural (w : ShearParameter) : Fin 5 → ZMod 2 := ![w 0,w 1,w 2,w 3,0]

/-- The coordinate formula used above is the literal exterior product. -/
theorem shearWedge_eq_exterior (w u : ShearParameter) :
    shearWedge w u = exteriorPower.ιMulti (ZMod 2) 2 ![shearNatural w, shearNatural u] := by
  apply coordinates.injective
  ext i
  simp only [shearWedge, LinearEquiv.apply_symm_apply]
  rw [coordinates_apply]
  simp only [exteriorCoordinates, Module.Basis.equivFun_apply, exteriorBasis,
    exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti,
    Module.Basis.coord_apply, Pi.basisFun_repr, index_order, pairEmbedding,
    Matrix.det_fin_two]
  fin_cases i <;> simp [shearNatural, pair, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]


/-- The section really is w ∧ e₅ in the exterior square. -/
theorem shearSection_eq_exterior (w : ShearParameter) :
    shearSection w = exteriorPower.ιMulti (ZMod 2) 2
      ![shearNatural w, Pi.single 4 1] := by
  apply coordinates.injective
  ext i
  simp only [shearSection, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply]
  rw [coordinates_apply]
  simp only [exteriorCoordinates, Module.Basis.equivFun_apply, exteriorBasis,
    exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti,
    Module.Basis.coord_apply, Pi.basisFun_repr, index_order, pairEmbedding,
    Matrix.det_fin_two]
  fin_cases i <;> simp [shearNatural, pair]

/-- In particular, the displacement of w ∧ e₅ is w ∧ u. -/
theorem shear_displacement_section (w u : ShearParameter) :
    displacement (shear u) (shearSection w) =
      exteriorPower.ιMulti (ZMod 2) 2 ![shearNatural w, shearNatural u] := by
  rw [shear_displacement, shearQuotient_section, shearWedge_eq_exterior]


/-- Over F₂, two vectors have zero wedge exactly when one is zero or they agree. -/
theorem shearWedge_eq_zero_iff (w u : ShearParameter) :
    shearWedge w u = 0 ↔ w = 0 ∨ u = 0 ∨ w = u := by
  have hcoord : shearWedge w u = 0 ↔
      w 0 * u 1 = w 1 * u 0 ∧ w 0 * u 2 = w 2 * u 0 ∧
      w 0 * u 3 = w 3 * u 0 ∧ w 1 * u 2 = w 2 * u 1 ∧
      w 1 * u 3 = w 3 * u 1 ∧ w 2 * u 3 = w 3 * u 2 := by
    rw [← coordinates.injective.eq_iff]
    simp [shearWedge, funext_iff, Fin.forall_fin_succ, -coordinates_apply,
      add_eq_zero_iff_eq_neg, ZMod.neg_eq_self_mod_two]
  rw [hcoord]
  constructor
  · intro h
    by_cases hu : u = 0
    · exact Or.inr (Or.inl hu)
    have hm : ∀ i j, w i * u j = w j * u i := by
      intro i j
      fin_cases i <;> fin_cases j <;> simp_all
    obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra h
      push Not at h
      exact hu (funext h)
    have hi1 : u i = 1 :=
      ((by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (u i)).resolve_left hi
    have hwj (j) : w j = w i * u j := by simpa [hi1] using (hm i j).symm
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (w i) with h0 | h1
    · left
      funext j
      simp [hwj j, h0]
    · right; right
      funext j
      simp [hwj j, h1]
  · rintro (rfl | rfl | rfl) <;> simp [mul_comm]

/-- The exact fixed-vector formula for a nonidentity shear. -/
theorem fixed_shear_iff (u : ShearParameter) (hu : u ≠ 0) (v : V) :
    v ∈ fixedSpace (shear u) ↔ shearQuotient v = 0 ∨ shearQuotient v = u := by
  change displacement (shear u) v = 0 ↔ _
  rw [shear_displacement, shearWedge_eq_zero_iff]
  simp [hu]

/-- A binary line consists of zero and its generator. -/
theorem mem_parameterLine (u w : ShearParameter) :
    w ∈ Submodule.span (ZMod 2) {u} ↔ w = 0 ∨ w = u := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) c with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩

/-- C_V(u) is the inverse image of the line of u in the natural quotient. -/
theorem fixedSpace_shear (u : ShearParameter) (hu : u ≠ 0) :
    fixedSpace (shear u) = (Submodule.span (ZMod 2) {u}).comap shearQuotient := by
  ext v
  rw [fixed_shear_iff u hu, Submodule.mem_comap, mem_parameterLine]

/-- Each nonidentity shear fixes strictly more than V₆. -/
theorem V₆_lt_fixedSpace_shear (u : ShearParameter) (hu : u ≠ 0) :
    V₆ < fixedSpace (shear u) := by
  apply lt_iff_le_not_ge.mpr
  constructor
  · intro v hv
    exact (fixed_shear_iff u hu v).mpr (Or.inl ((mem_V₆_iff_shearQuotient v).mp hv))
  · intro h
    have hs : shearSection u ∈ fixedSpace (shear u) :=
      (fixed_shear_iff u hu _).mpr (Or.inr (shearQuotient_section u))
    have hz := (mem_V₆_iff_shearQuotient _).mp (h hs)
    exact hu ((shearQuotient_section u).symm.trans hz)

/-- The literal quotient identification with Γ₄. -/
noncomputable def shearQuotientEquiv : (V ⧸ V₆) ≃ₗ[ZMod 2] ShearParameter :=
  (Submodule.quotEquivOfEq _ _ ker_shearQuotient.symm).trans
    (shearQuotient.quotKerEquivOfSurjective (fun w => ⟨shearSection w, shearQuotient_section w⟩))

@[simp] theorem shearQuotientEquiv_mk (v : V) :
    shearQuotientEquiv (V₆.mkQ v) = shearQuotient v := rfl

/-- The image of C_V(u) in V/V₆ is precisely the line corresponding to u. -/
theorem fixedSpace_shear_quotient (u : ShearParameter) (hu : u ≠ 0) :
    ((fixedSpace (shear u)).map V₆.mkQ).map shearQuotientEquiv.toLinearMap =
      Submodule.span (ZMod 2) {u} := by
  rw [← Submodule.map_comp]
  have he : shearQuotientEquiv.toLinearMap.comp V₆.mkQ = shearQuotient := by ext v; rfl
  rw [he, fixedSpace_shear u hu, Submodule.map_comap_eq]
  have hs : LinearMap.range shearQuotient = ⊤ :=
    LinearMap.range_eq_top.mpr (fun w => ⟨shearSection w, shearQuotient_section w⟩)
  rw [hs, top_inf_eq]

/-- The genuine subgroup of U attached to a parameter subspace. -/
def parameterShears (P : Submodule (ZMod 2) ShearParameter) : Subgroup Group :=
  (shearHom.comp P.subtype.toAddMonoidHom.toMultiplicative).range

theorem mem_parameterShears (P : Submodule (ZMod 2) ShearParameter) (g : Group) :
    g ∈ parameterShears P ↔ ∃ u ∈ P, shear u = g := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u.toAdd.val, u.toAdd.property, hu⟩
  · rintro ⟨u, hu, hg⟩
    exact ⟨Multiplicative.ofAdd (⟨u, hu⟩ : P), hg⟩

theorem parameterShears_le (P : Submodule (ZMod 2) ShearParameter) :
    parameterShears P ≤ shearSubgroup := by
  intro g hg
  obtain ⟨u, _, rfl⟩ := (mem_parameterShears P g).mp hg
  exact shear_mem u

theorem parameterShears_top : parameterShears ⊤ = shearSubgroup := by
  ext g
  simp [mem_parameterShears, mem_shearSubgroup]

/-- Fixed vectors for the actual subgroup are exactly those fixed by its parameters. -/
theorem mem_fixedSpace_parameterShears (P : Submodule (ZMod 2) ShearParameter) (v : V) :
    v ∈ BinaryOffender.fixedSpace (exteriorAction 2) (parameterShears P) ↔
      ∀ u ∈ P, shearWedge (shearQuotient v) u = 0 := by
  change (∀ g : parameterShears P, exteriorAction 2 g.val v = v) ↔ _
  constructor
  · intro h u hu
    have he := h ⟨shear u, (mem_parameterShears P _).mpr ⟨u, hu, rfl⟩⟩
    simpa [shear_action] using he
  · intro h g
    obtain ⟨u, hu, he⟩ := (mem_parameterShears P _).mp g.property
    rw [← he, shear_action, h u hu, add_zero]

/-- Every parameter space of dimension at least two fixes exactly V₆. -/
theorem fixedSpace_parameterShears (P : Submodule (ZMod 2) ShearParameter)
    (hP : 2 ≤ Module.finrank (ZMod 2) P) :
    BinaryOffender.fixedSpace (exteriorAction 2) (parameterShears P) = V₆ := by
  ext v
  rw [mem_fixedSpace_parameterShears, mem_V₆_iff_shearQuotient]
  constructor
  · intro h
    by_contra hw
    have hle : P ≤ Submodule.span (ZMod 2) {shearQuotient v} := by
      intro u hu
      rw [mem_parameterLine]
      rcases (shearWedge_eq_zero_iff _ _).mp (h u hu) with h0 | h0 | he
      · exact (hw h0).elim
      · exact Or.inl h0
      · exact Or.inr he.symm
    have hd := Submodule.finrank_mono hle
    rw [finrank_span_singleton hw] at hd
    omega
  · intro h u _
    exact (shearWedge_eq_zero_iff _ _).mpr (Or.inl h)

/-- The common fixed space of U is Λ²Γ₄. -/
theorem fixedSpace_shearSubgroup :
    BinaryOffender.fixedSpace (exteriorAction 2) shearSubgroup = V₆ := by
  rw [← parameterShears_top]
  apply fixedSpace_parameterShears
  simp

/-- Every exterior vector is fixed by some nonidentity shear. -/
theorem exists_nonzero_shear_fixed (v : V) :
    ∃ u : ShearParameter, u ≠ 0 ∧ v ∈ fixedSpace (shear u) := by
  by_cases h : shearQuotient v = 0
  · refine ⟨![1,0,0,0], by decide, ?_⟩
    exact (fixed_shear_iff _ (by decide) v).mpr (Or.inl h)
  · exact ⟨shearQuotient v, h, (fixed_shear_iff _ h v).mpr (Or.inr rfl)⟩

/-- The sum of the fixed spaces of the nonidentity elements of U is all of V. -/
theorem iSup_fixedSpace_shears :
    (⨆ (u : ShearParameter) (_ : u ≠ 0), fixedSpace (shear u)) = ⊤ := by
  apply top_unique
  intro v _
  obtain ⟨u, hu, hv⟩ := exists_nonzero_shear_fixed v
  have hle : fixedSpace (shear u) ≤
      (⨆ (w : ShearParameter) (_ : w ≠ 0), fixedSpace (shear w)) :=
    le_iSup_of_le u (le_iSup_of_le hu le_rfl)
  exact hle hv


/-- Shear displacement always lies in Λ²Γ₄. -/
theorem shearWedge_mem_V₆ (w u : ShearParameter) : shearWedge w u ∈ V₆ := by
  rw [mem_V₆_iff_shearQuotient]
  ext i
  fin_cases i <;> simp [shearQuotient, shearWedge, -coordinates_apply]

/-- The actual module commutator [V,U] is Λ²Γ₄. -/
theorem commutator_shearSubgroup :
    BinaryOffender.subspaceCommutator (exteriorAction 2) ⊤ shearSubgroup = V₆ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨g, hg, w, _, rfl⟩
    obtain ⟨u, rfl⟩ := (mem_shearSubgroup g).mp hg
    change displacement (shear u) w ∈ V₆
    rw [shear_displacement]
    exact shearWedge_mem_V₆ _ _
  · have hw (w u : ShearParameter) : shearWedge w u ∈
        BinaryOffender.subspaceCommutator (exteriorAction 2) ⊤ shearSubgroup := by
      have h : displacement (shear u) (shearSection w) ∈
          BinaryOffender.subspaceCommutator (exteriorAction 2) ⊤ shearSubgroup :=
        Submodule.subset_span ⟨shear u, shear_mem u, shearSection w, Submodule.mem_top, rfl⟩
      rwa [shear_displacement, shearQuotient_section] at h
    change coordinateSpan _ ≤ _
    apply Submodule.span_le.mpr
    rintro v ⟨i, hi, rfl⟩
    have hb : basis i = shearWedge (Pi.single (Fin.ofNat 4 (pair i 0).val) 1)
        (Pi.single (Fin.ofNat 4 (pair i 1).val) 1) := by
      apply coordinates.injective
      ext j
      change basis.equivFun (basis i) j = _
      rw [Module.Basis.equivFun_self]
      fin_cases i <;> simp_all [-coordinates_apply]
      all_goals fin_cases j <;> simp [shearWedge, pair, Pi.single_apply, -coordinates_apply] <;> decide
    rw [hb]
    exact hw _ _

/-- The fixed-space clause in E.3.8, on the actual exterior action.
The full source family additionally requires k > 0 and a nontrivial elementary
abelian subgroup. Relative index records the literal quotient A/B. -/
def HasSmallIndexFixedSpaceProperty (k : ℕ) (A : Subgroup Group) : Prop :=
  ∀ B ≤ A, Nat.log 2 (B.relIndex A) < k →
    BinaryOffender.fixedSpace (exteriorAction 2) A =
      BinaryOffender.fixedSpace (exteriorAction 2) B

end Representation.SL5ExteriorSquare
