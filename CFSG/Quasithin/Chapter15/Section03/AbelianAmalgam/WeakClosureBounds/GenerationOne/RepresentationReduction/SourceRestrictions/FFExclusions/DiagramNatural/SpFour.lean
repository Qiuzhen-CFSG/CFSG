module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.DiagramNatural.CoreInvariant
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.OuterQuotient.ParabolicClasses

/-!
# The natural Sp₄ module detects both parabolic types

On the literal symplectic matrix module the two parabolic two-cores fix
respectively the standard point and plane. Restriction to the binary field
preserves their strict dimension inequality. The intrinsic permutation of
parabolic conjugacy classes therefore excludes an intertwiner across every
automorphism moving one of these classes.

The coordinate checks follow the private fixed-vector calculations in
`Theory.SpecificGroups.SymplecticFour.LocalStructure.ParabolicCores`;
the core identities and automorphism action are reused from that development.
Source: Aschbacher--Smith, combined manuscript (1 March 2004), B.4.2(3),
E.2.2(2)(b), and the diagram case of 15.3.65, printed pp.86, 215--216, 1152.
-/

@[expose] public section
open Matrix Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
noncomputable section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.DiagramNatural
variable {F : Type*} [Field F] [CharP F 2]
private theorem point_element_mem (u v z : F) :
    (pointRadicalElement u v z).val ∈ pointRadicalAmbient :=
  Subgroup.mem_map_of_mem _ (pointRadicalElement_mem u v z)

omit [CharP F 2] in
private theorem plane_shear_mem (B : Plane.symmetricMatrices F) :
    (Plane.shear B).val ∈ planeRadicalAmbient :=
  Subgroup.mem_map_of_mem planeLocal.subtype
    (show Plane.shear B ∈ Plane.radical from Plane.quotientMap_shear B)

private def diagShear (i : Fin 2) : Plane.symmetricMatrices F :=
  ⟨Matrix.diagonal (Pi.single i 1), Matrix.isSymm_diagonal _⟩

private theorem point_fixed (x : Vector F) :
    (∀ q ∈ pointRadicalAmbient (F := F), q • x = x) ↔ x ∈ point F := by
  constructor
  · intro h
    have h₀ := congrFun (h _ (point_element_mem 0 0 (1 : F))) (.inl 0)
    have h₁ := congrFun (h _ (point_element_mem 1 0 (0 : F))) (.inl 0)
    have h₂ := congrFun (h _ (point_element_mem 0 1 (0 : F))) (.inl 0)
    simp [pointRadicalElement, pointRadicalMatrix, mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two] at h₀ h₁ h₂
    exact (mem_point_iff x).mpr ⟨h₂, by intro i; fin_cases i <;> assumption⟩
  · intro hx q hq
    obtain ⟨q, _, rfl⟩ := hq
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    change toLinear q.val (a • e 0) = a • e 0
    rw [map_smul]
    exact congrArg (a • ·) ((mem_pointLocal_iff_fixed q.val).mp q.property)

omit [CharP F 2] in
private theorem plane_fixed (x : Vector F) :
    (∀ q ∈ planeRadicalAmbient (F := F), q • x = x) ↔ x ∈ plane F := by
  constructor
  · intro h i
    have hi := congrFun (h _ (plane_shear_mem (diagShear i))) (.inl i)
    fin_cases i <;>
      simpa [Theory.SpecificGroups.SymplecticFour.smul_eq_mulVec, Plane.shear, Plane.shearSp, diagShear, mulVec, dotProduct,
        Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.diagonal, Pi.single_apply] using hi
  · intro hx q hq
    have hx' : ∀ i, x (.inr i) = 0 := hx
    obtain ⟨q, hq, rfl⟩ := hq
    have hm := Plane.radical_matrix (⟨q, hq⟩ : Plane.radical)
    change q.val.val *ᵥ x = x
    rw [hm]
    funext i
    cases i with
    | inl i => simp [mulVec, dotProduct, Fintype.sum_sum_type, one_apply, hx']
    | inr i => simp [mulVec, dotProduct, Fintype.sum_sum_type, one_apply, hx']


variable [Finite F] [Algebra (ZMod 2) F]

/-- The point parabolic two-core fixes precisely the binary restriction of the point. -/
theorem spFour_pointCore_fixedSpace {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 1 < f) :
    fixedSpace (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2))
      ((pointParabolic (F := F)).pCoreIn 2) = (point F).restrictScalars (ZMod 2) := by
  change fixedSpace _ ((pCore 2 pointParabolic).map pointParabolic.subtype) = _
  rw [pointParabolic_core_map_eq_radical hF hf]
  ext x
  exact (show (∀ q : pointRadicalAmbient (F := F), q.val • x = x) ↔ x ∈ point F from
    (Subtype.forall.trans (point_fixed x)))

/-- The plane parabolic two-core fixes precisely the binary restriction of the plane. -/
theorem spFour_planeCore_fixedSpace {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 1 < f) :
    fixedSpace (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2))
      ((planeParabolic (F := F)).pCoreIn 2) = (plane F).restrictScalars (ZMod 2) := by
  change fixedSpace _ ((pCore 2 planeParabolic).map planeParabolic.subtype) = _
  rw [planeParabolic_core_map_eq_radical hF hf]
  ext x
  exact (show (∀ q : planeRadicalAmbient (F := F), q.val • x = x) ↔ x ∈ plane F from
    (Subtype.forall.trans (plane_fixed x)))

/-- The two intrinsic two-cores have strictly different fixed dimensions. -/
theorem spFour_coreFixedRank_lt {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 1 < f) :
    coreFixedRank (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2))
      pointParabolic < coreFixedRank
        (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)) planeParabolic := by
  unfold coreFixedRank
  rw [spFour_pointCore_fixedSpace hF hf, spFour_planeCore_fixedSpace hF hf]
  exact Submodule.finrank_lt_finrank_of_lt
    ((Submodule.restrictScalars_lt (ZMod 2)).mpr point_lt_plane)

/-- A genuine diagram action cannot extend the binary natural Sp₄ module.
Neither Borel preservation nor odd field degree is needed for this obstruction. -/
theorem spFour_not_intertwines {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    (γ : MulAut (Sp F)) (hmoves : MovesParabolicClasses γ pointParabolic planeParabolic) :
    let σ := restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)
    ¬ ∃ e : Vector F ≃ₗ[ZMod 2] Vector F, ∀ g v, e (σ g v) = σ (γ g) (e v) := by
  apply not_intertwines_of_coreFixedRank _ γ pointParabolic planeParabolic
    (DiagramAutomorphisms.map_parabolic_eq_conjugate (field_card_gt_two hF hf) γ)
    (ne_of_lt (spFour_coreFixedRank_lt hF hf)) hmoves

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.DiagramNatural
