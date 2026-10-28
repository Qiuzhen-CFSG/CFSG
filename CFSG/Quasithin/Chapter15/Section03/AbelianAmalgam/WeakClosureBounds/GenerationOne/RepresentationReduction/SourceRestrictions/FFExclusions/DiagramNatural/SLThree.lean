module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.DiagramNatural.CoreInvariant
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.Coverage.RootOrientation.Planes
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient

/-!
# Natural SL₃ modules distinguish the two diagram types

The two elementary abelian root planes fix respectively the coordinate
point and line on the actual natural SL₃ module. These binary fixed spaces
have strictly different dimensions. A Borel-preserving automorphism preserves
the Borel two-core, hence permutes its two root planes. An intertwiner forces
both planes to be fixed, so it fixes their actual parabolic normalizers.

Dimensions double for two identical summands, giving the additional
obstruction needed in B.5.1(1)(ii). All group actions remain on SL₃ itself;
no projective carrier or automorphism-coverage hypothesis is substituted.
The geometry and marked unipotent action are reused from `RootPlaneGeometry`
and `Coverage.RootOrientation.Planes`.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), B.4.2(2),
B.5.1(1)(ii), E.2.2(2)(b), and 15.3.65, printed pp.86, 99--100, 215--216, 1152.
-/

@[expose] public section
noncomputable section
open scoped MatrixGroups
open Matrix Representation Representation.BinaryOffender Subgroup
open Matrix.PSL3.LinearThree Matrix.PSL3.RootPlaneGeometry
open Matrix.PSL3Even.UnipotentGeometry
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.DiagramNatural
variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

private theorem slThree_point_fixed (v : Fin 3 → F) :
    v ∈ fixedSpace (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3))
      (rootPlaneSL F true) ↔ v 1 = 0 ∧ v 2 = 0 := by
  constructor
  · intro hv
    have h1 := congrFun (hv ⟨specialLinear F ⟨1,0,0⟩,
      (mem_rootPlaneSL_point F _).mpr ⟨1,0,rfl⟩⟩) 0
    have h2 := congrFun (hv ⟨specialLinear F ⟨0,0,1⟩,
      (mem_rootPlaneSL_point F _).mpr ⟨0,1,rfl⟩⟩) 0
    change (matrix F ⟨1,0,0⟩ *ᵥ v) 0 = v 0 at h1
    change (matrix F ⟨0,0,1⟩ *ᵥ v) 0 = v 0 at h2
    simp [matrix, mulVec, dotProduct, Fin.sum_univ_three] at h1 h2
    exact ⟨h1,h2⟩
  · rintro ⟨h1,h2⟩ ⟨g,hg⟩
    obtain ⟨a,c,rfl⟩ := (mem_rootPlaneSL_point F g).mp hg
    change matrix F ⟨a,0,c⟩ *ᵥ v = v
    ext i
    fin_cases i <;> simp [matrix, mulVec, dotProduct, Fin.sum_univ_three, h1,h2]

private theorem slThree_line_fixed (v : Fin 3 → F) :
    v ∈ fixedSpace (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3))
      (rootPlaneSL F false) ↔ v 2 = 0 := by
  constructor
  · intro hv
    have h2 := congrFun (hv ⟨specialLinear F ⟨0,0,1⟩,
      (mem_rootPlaneSL_line F _).mpr ⟨0,1,rfl⟩⟩) 0
    change (matrix F ⟨0,0,1⟩ *ᵥ v) 0 = v 0 at h2
    simpa [matrix, mulVec, dotProduct, Fin.sum_univ_three] using h2
  · intro h2 ⟨g,hg⟩
    obtain ⟨b,c,rfl⟩ := (mem_rootPlaneSL_line F g).mp hg
    change matrix F ⟨0,b,c⟩ *ᵥ v = v
    ext i
    fin_cases i <;> simp [matrix, mulVec, dotProduct, Fin.sum_univ_three, h2]

/-- The two concrete root planes have strictly nested binary fixed spaces. -/
theorem slThree_rootPlane_fixedSpace_lt :
    let σ := restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3)
    fixedSpace σ (rootPlaneSL F true) < fixedSpace σ (rootPlaneSL F false) := by
  dsimp only
  apply lt_of_le_of_ne
  · intro v hv
    exact (slThree_line_fixed v).mpr ((slThree_point_fixed v).mp hv).2
  · intro he
    have hv := (slThree_line_fixed (![0,1,0] : Fin 3 → F)).mpr rfl
    rw [← he] at hv
    have hh := ((slThree_point_fixed _).mp hv).1
    exact one_ne_zero hh


variable [Finite F]

/-- The Borel two-core and its two maximal elementary abelian planes are intrinsic. -/
theorem slThree_borel_preserving_rootPlane_pair {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (γ : MulAut SL(3,F))
    (hB : (borelSL F).map γ.toMonoidHom = borelSL F) :
    ((rootPlaneSL F true).map γ.toMonoidHom = rootPlaneSL F true ∧
      (rootPlaneSL F false).map γ.toMonoidHom = rootPlaneSL F false) ∨
      (rootPlaneSL F true).map γ.toMonoidHom = rootPlaneSL F false := by
  let : CharP F 2 := (Algebra.charP_iff (ZMod 2) F 2).mp inferInstance
  have hcore : (borelSL F).pCoreIn 2 = unipotentSL F := by
    rw [pCoreIn, PSL3.CartanActions.BorelQuotient.twoCoreSL_eq F hF,
      map_subgroupOf_eq_of_le (unipotentSL_le_borelSL F)]
  have hU : (unipotentSL F).map γ.toMonoidHom = unipotentSL F := by
    rw [← hcore, map_pCoreIn_of_injective 2 _ γ.toMonoidHom γ.injective, hB]
  obtain ⟨b,hpoint,hline⟩ :=
    PSL3Even.AutomorphismCoverage.RootOrientation.marked_plane_permutation F
      (unipotentSL F) (unipotentSLEquiv F) γ hU
  have hmarked : markedHom F (unipotentSL F) (unipotentSLEquiv F) = specialLinear F := rfl
  rw [hmarked] at hpoint hline
  change (rootPlaneSL F true).map γ.toMonoidHom = rootPlaneSL F b at hpoint
  change (rootPlaneSL F false).map γ.toMonoidHom = rootPlaneSL F (!b) at hline
  cases b
  · exact Or.inr hpoint
  · exact Or.inl ⟨hpoint,hline⟩

/-- The natural binary SL₃ module cannot extend across a genuine diagram action. -/
theorem slThree_not_intertwines {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (γ : MulAut SL(3,F))
    (hB : (borelSL F).map γ.toMonoidHom = borelSL F)
    (hmoves : MovesParabolicClasses γ (pointParabolicSL F) (lineParabolicSL F)) :
    let σ := restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3)
    ¬ ∃ e : (Fin 3 → F) ≃ₗ[ZMod 2] (Fin 3 → F),
      ∀ g v, e (σ g v) = σ (γ g) (e v) := by
  apply not_intertwines_of_fixedSpace_normalizers _ γ (rootPlaneSL F true)
    (rootPlaneSL F false) (slThree_borel_preserving_rootPlane_pair hF γ hB)
    (ne_of_lt (Submodule.finrank_lt_finrank_of_lt (slThree_rootPlane_fixedSpace_lt (F := F))))
  simpa [normalizer_rootPlaneSL, parabolicSL] using hmoves

/-- Two identical natural summands also cannot extend across a genuine diagram action. -/
theorem slThree_prod_self_not_intertwines {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (γ : MulAut SL(3,F))
    (hB : (borelSL F).map γ.toMonoidHom = borelSL F)
    (hmoves : MovesParabolicClasses γ (pointParabolicSL F) (lineParabolicSL F)) :
    let σ := restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3)
    ¬ ∃ e : ((Fin 3 → F) × (Fin 3 → F)) ≃ₗ[ZMod 2] ((Fin 3 → F) × (Fin 3 → F)),
      ∀ g v, e (σ.prod σ g v) = σ.prod σ (γ g) (e v) := by
  apply not_intertwines_prod_self_of_fixedSpace_normalizers _ γ (rootPlaneSL F true)
    (rootPlaneSL F false) (slThree_borel_preserving_rootPlane_pair hF γ hB)
    (ne_of_lt (Submodule.finrank_lt_finrank_of_lt (slThree_rootPlane_fixedSpace_lt (F := F))))
  simpa [normalizer_rootPlaneSL, parabolicSL] using hmoves

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.DiagramNatural
