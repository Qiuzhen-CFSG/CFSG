module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Coordinates
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.QuotientTools

/-!
# The marked component in the tensor quotient

For the actual quotient H/O₂(H), the embedded terminal derived subgroup has
image exactly 1 × A₅ in every prescribed S₃ × D marking containing A₅.
Perfectness gives one containment, and projection to the solvable three-point
factor and the sign quotient gives the other. No module geometry is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
case 14.4.2(5), printed p.1006, and Lemma 14.4.10(1), printed p.1010.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
private theorem three_solvable : Group.IsSolvable Three := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  apply Group.isSolvable_of_ker_le_range
    (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
  rw [range_subtype, ← alternatingGroup_eq_sign_ker]

private theorem five_residual : solvableResidual Five = AltFive := by
  let : Group.IsPerfect AltFive := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  apply le_antisymm _ (le_solvableResidual_of_isPerfect _)
  calc
    solvableResidual Five ≤ _root_.commutator Five := solvableResidual_le_derivedSeries 1
    _ = AltFive := alternatingGroup.commutator_perm_eq (by simp)

private theorem marked_second_residual {D : Subgroup Five} (hAD : AltFive ≤ D) :
    solvableResidual D = AltFive.subgroupOf D := by
  let : Group.IsPerfect AltFive := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let ea := subgroupOfEquivOfLe hAD
  let : Group.IsPerfect (AltFive.subgroupOf D) :=
    Group.IsPerfect.ofSurjective (f := ea.symm.toMonoidHom) ea.symm.surjective
  apply le_antisymm _ (le_solvableResidual_of_isPerfect _)
  have hu := map_solvableResidual_le D.subtype
  rw [five_residual] at hu
  intro x hx
  exact hu (mem_map_of_mem _ hx)

private theorem product_residual {D : Subgroup Five} (hAD : AltFive ≤ D) :
    solvableResidual (Three × D) = (⊥ : Subgroup Three).prod (AltFive.subgroupOf D) := by
  let : Group.IsSolvable Three := three_solvable
  let : Group.IsPerfect AltFive := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let A := AltFive.subgroupOf D
  let ea := subgroupOfEquivOfLe hAD
  let : Group.IsPerfect A :=
    Group.IsPerfect.ofSurjective (f := ea.symm.toMonoidHom) ea.symm.surjective
  let e : (⊥ : Subgroup Three).prod A ≃* A := (prodEquiv _ _).trans .uniqueProd
  let : Group.IsPerfect ((⊥ : Subgroup Three).prod A) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  apply le_antisymm _ (le_solvableResidual_of_isPerfect _)
  apply le_prod_iff.mpr
  constructor
  · simpa only [solvableResidual_eq_bot] using map_solvableResidual_le (MonoidHom.fst Three D)
  · simpa only [marked_second_residual hAD] using map_solvableResidual_le (MonoidHom.snd Three D)
variable {G : Type*} [Group G] [Finite G]

/-- The literal component image, in any prescribed three-times-five marking.
The second factor is the actual inclusion of A₅ in D. -/
theorem star_component_marked {H : Subgroup G} {D : Subgroup Five}
    (hAD : AltFive ≤ D) (e : coreQuotient H ≃* Three × D) :
    (star H (component H)).map e.toMonoidHom =
      (⊥ : Subgroup Three).prod (AltFive.subgroupOf D) := by
  rw [star_component, map_solvableResidual_eq e.toMonoidHom e.surjective]
  exact product_residual hAD

/-- The same marked image written as the image of the inclusion A₅ → D.
The domain subgroup of this inclusion is the whole carrier A₅. -/
theorem star_component_marked_inclusion {H : Subgroup G} {D : Subgroup Five}
    (hAD : AltFive ≤ D) (e : coreQuotient H ≃* Three × D) :
    (star H (component H)).map e.toMonoidHom =
      (⊥ : Subgroup Three).prod ((⊤ : Subgroup AltFive).map (inclusion hAD)) := by
  rw [star_component_marked hAD e]
  congr 1
  ext x
  constructor
  · intro hx
    exact ⟨⟨x.val, hx⟩, mem_top _, rfl⟩
  · rintro ⟨a, _, rfl⟩
    exact a.property

/-- The component's quotient image is A₅ through the prescribed marking. -/
noncomputable def starComponentEquiv {H : Subgroup G} {D : Subgroup Five}
    (hAD : AltFive ≤ D) (e : coreQuotient H ≃* Three × D) :
    star H (component H) ≃* AltFive :=
  (e.subgroupMap _).trans ((MulEquiv.subgroupCongr (star_component_marked hAD e)).trans
    ((prodEquiv _ _).trans (MulEquiv.uniqueProd.trans (subgroupOfEquivOfLe hAD))))

/-- Either source quotient model supplies an actual A₅ component image. -/
theorem exists_starComponentEquiv {H : Subgroup G}
    (hmodel : Nonempty (coreQuotient H ≃* Three × Five) ∨
      Nonempty (coreQuotient H ≃* Three × AltFive)) :
    Nonempty (star H (component H) ≃* AltFive) := by
  rcases hmodel with h | h
  · obtain ⟨e⟩ := h
    exact ⟨starComponentEquiv (D := ⊤) le_top
      (e.trans (MulEquiv.prodCongr (MulEquiv.refl _) topEquiv.symm))⟩
  · obtain ⟨e⟩ := h
    exact ⟨starComponentEquiv le_rfl e⟩

omit [Finite G] in
/-- The quotient kernel lies in the supplied Sylow subgroup, in ambient G. -/
theorem twoCore_le_of_sylow {H T : Subgroup G} (P : Sylow 2 H)
    (hP : (P : Subgroup H).map H.subtype = T) : twoCore H ≤ T := by
  rw [← hP]
  exact map_mono (pCore_isPGroup.le_sylow_of_normal P)

/-- The actual star image of T is a Sylow subgroup of H/O₂(H). -/
theorem exists_star_sylow {H T : Subgroup G} (P : Sylow 2 H)
    (hP : (P : Subgroup H).map H.subtype = T) :
    ∃ Q : Sylow 2 (coreQuotient H), (Q : Subgroup (coreQuotient H)) = star H T := by
  refine ⟨P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H)), ?_⟩
  rw [star, ← hP, ← comap_subtype,
    comap_map_eq_self_of_injective H.subtype_injective]
  rfl

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
end
