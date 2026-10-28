module
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.SplitModel
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
public import Theory.SpecificGroups.SymplecticFour.BorelActionGeometry.Normalizers

/-!
# The plane-parabolic residual as the split maximal natural cover

The full radical coordinates identify the actual radical with the universal
binary natural cover over its original projection. The split model preserves
the intrinsic two-core and maps the whole center to the fixed coordinate axis.
The existing determinant-kernel residual theorem then gives the model for the
literal solvable residual and derived subgroup of the plane parabolic. Its
proved maximality makes this the concrete comparison used in 2.4.8(4b).

Source: Aschbacher--Smith, 2.4.8(4), printed pp.529--531; F.1.12(I)(2),
printed pp.262--264; and I.2.3, printed p.413, in the 1 March 2004 manuscript.
The abstract source extension and its splitting remain with the Chapter2
consumer; this module supplies the entire concrete model comparison.
-/

public section
noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalCover
open Representation.SL2OrthogonalCover Representation.OneCohomology
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

section Universal
variable [Algebra (ZMod 2) F]

/-- The full radical is the maximal binary natural cover, over the original projection. -/
theorem universal_radical_equiv {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    ∃ e : Module.Dual (ZMod 2) (cocycles (binaryNatural (F := F)).dual) ≃ₗ[ZMod 2]
        Additive (radical (F := F)),
      (∀ g u, e ((universalAction (binaryNatural (F := F)).dual).dual g u) =
        Additive.ofMul (conjugate (levi g) (e u).toMul)) ∧
      ∀ u, (naturalCoordinates (e u).toMul).toAdd =
        universalCoverProjection (binaryNatural (F := F)) u := by
  obtain ⟨e,he,hp⟩ := universal_equiv n hn hF
  refine ⟨e.trans radicalLinearCoordinates.symm, ?_, ?_⟩
  · intro g u
    apply radicalLinearCoordinates.injective
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [radicalLinearCoordinates_conjugate, quotientMap_levi]
    change e ((universalAction (binaryNatural (F := F)).dual).dual g u) =
      binaryAction g (radicalLinearCoordinates (radicalLinearCoordinates.symm (e u)))
    rw [LinearEquiv.apply_symm_apply, he]
  · intro u
    rw [← radicalCoordinates_projection]
    change projection (radicalLinearCoordinates (radicalLinearCoordinates.symm (e u))) = _
    rw [LinearEquiv.apply_symm_apply]
    exact hp u
end Universal

/-- The original two-core is precisely the left factor of the split model. -/
theorem planeLocalEquiv_core_iff {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (g : planeLocal (F := F)) :
    g ∈ pCore 2 (planeLocal (F := F)) ↔ (planeLocalEquiv g).right = 1 := by
  rw [planeLocal_core_eq hF hn, planeLocalEquiv_quotient]
  rfl

/-- The whole original center corresponds to the fixed first coordinate axis. -/
theorem planeLocalEquiv_center_iff {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (g : planeLocal (F := F)) :
    g ∈ center (planeLocal (F := F)) ↔
      (planeLocalEquiv g).right = 1 ∧
      (planeLocalEquiv g).left.toAdd 1 = 0 ∧ (planeLocalEquiv g).left.toAdd 2 = 0 := by
  have hcent : center (planeLocal (F := F)) ≤ radical :=
    (center_le_centralizer _).trans (planeNaturalExtension hF hn).centralizer_eq.le
  constructor
  · intro hg
    let q : radical (F := F) := ⟨g,hcent hg⟩
    have he : planeLocalEquiv g = SemidirectProduct.inl (radicalCoordinates q) :=
      planeLocalEquiv_radical q
    have hc := (radicalCoordinates_central_iff q).mp hg
    rw [LinearMap.mem_ker] at hc
    have hh : projection (radicalCoordinates q).toAdd = 0 := hc
    rw [he]
    exact ⟨rfl, congrFun hh 0, congrFun hh 1⟩
  · rintro ⟨hquot,h₁,h₂⟩
    have hrad : g ∈ radical := by
      change quotientMap g = 1
      rwa [planeLocalEquiv_quotient] at hquot
    let q : radical (F := F) := ⟨g,hrad⟩
    have he : planeLocalEquiv g = SemidirectProduct.inl (radicalCoordinates q) :=
      planeLocalEquiv_radical q
    apply (radicalCoordinates_central_iff q).mpr
    change projection (radicalCoordinates q).toAdd = 0
    rw [he] at h₁ h₂
    ext i
    fin_cases i
    · exact h₁
    · exact h₂

/-- The relative derived subgroup is exactly the original determinant kernel. -/
theorem plane_derived_eq_local {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    commutator (planeParabolic (F := F)) = (planeLocal (F := F)).subgroupOf planeParabolic := by
  apply le_antisymm
  · change commutator (planeParabolic (F := F)) ≤
      (determinantKernel (plane F)).subgroupOf (stabilizer (plane F))
    rw [determinantKernel_subgroupOf]
    exact Abelianization.commutator_subset_ker _
  · rw [← planeParabolic_solvableResidual_relative hF hn]
    exact (solvableResidual_le_derivedSeries 1).trans (derivedSeries_one _).le

/-- The actual residual-to-local equivalence retains the matrix embedding. -/
def residualLocalEquiv {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    solvableResidual (planeParabolic (F := F)) ≃* planeLocal (F := F) :=
  (MulEquiv.subgroupCongr (planeParabolic_solvableResidual_relative hF hn)).trans
    (subgroupOfEquivOfLe planeLocal_le)

theorem residualLocalEquiv_coe {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (q : solvableResidual (planeParabolic (F := F))) :
    ((residualLocalEquiv hF hn q : planeLocal) : Sp F) = ((q : planeParabolic (F := F)) : Sp F) := by rfl

/-- The literal parabolic solvable residual is the split maximal binary natural cover. -/
def residualEquiv {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    solvableResidual (planeParabolic (F := F)) ≃* SplitGroup F :=
  (residualLocalEquiv hF hn).trans planeLocalEquiv

/-- Its quotient is still the original upper-left matrix block. -/
theorem residualEquiv_quotient {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (q : solvableResidual (planeParabolic (F := F))) :
    ((residualEquiv hF hn q).right).val = q.val.val.val.toBlocks₁₁ := by
  change (planeLocalEquiv (residualLocalEquiv hF hn q)).right.val = _
  rw [planeLocalEquiv_quotient, quotientMap_val]
  rfl

/-- The actual derived subgroup has the same split model. -/
def derivedEquiv {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    commutator (planeParabolic (F := F)) ≃* SplitGroup F :=
  ((MulEquiv.subgroupCongr (plane_derived_eq_local hF hn)).trans
    (subgroupOfEquivOfLe planeLocal_le)).trans planeLocalEquiv

/-- Literal maximal-parabolic model used in the source 2.4.8(4) comparison. -/
theorem maximal_parabolic_residual_model {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    IsCoatom (planeParabolic (F := F)) ∧
      Nonempty (solvableResidual (planeParabolic (F := F)) ≃* SplitGroup F) ∧
      Nonempty (commutator (planeParabolic (F := F)) ≃* SplitGroup F) :=
  ⟨BorelActionGeometry.planeParabolic_isCoatom, ⟨residualEquiv hF hn⟩, ⟨derivedEquiv hF hn⟩⟩

/-- The same concrete consumer needs only the original nonbinary field-size bound. -/
theorem maximal_parabolic_residual_model_of_four_le (hF : 4 ≤ Nat.card F) :
    IsCoatom (planeParabolic (F := F)) ∧
      Nonempty (solvableResidual (planeParabolic (F := F)) ≃* SplitGroup F) ∧
      Nonempty (commutator (planeParabolic (F := F)) ≃* SplitGroup F) := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨n,_,hn⟩ := FiniteField.card F 2
  have hcard : Nat.card F = 2 ^ (n : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hn
  have hn' : 1 < (n : ℕ) := by
    by_contra h
    have he : 2 ^ (n : ℕ) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) (by omega)
    rw [← hcard] at he
    norm_num at he
    omega
  exact maximal_parabolic_residual_model hcard hn'

end Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalCover
