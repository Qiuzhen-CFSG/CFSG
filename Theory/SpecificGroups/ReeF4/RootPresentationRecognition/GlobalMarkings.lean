module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.SourceFaithfulness
public import Theory.SpecificGroups.ReeF4.Octagon.Binary

/-!
# Full marked Ree subgroups

The same constructed comparison maps U, the entire Cartan and Borel, and both oriented parabolics. The native binary linear generation theorem handles m = 0.
Source: GLS3 2.3.5--8 and Steinberg section 11, Theorem 33 and Lemma 62.
-/

@[expose] public noncomputable section
namespace ReeF4.RootPresentationRecognition.Global
open Subgroup Theory.GroupTheory OrderedRootPresentation
open SignedGeometry WeylPresentation CentralCovers.TwoPrimary
open CentralCovers.OddPrimary.Order
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)
variable {m : ℕ} (d : SourcePositive.Charts Q split m)
variable (T : SourceBorel.TorusData Q split d) (W : SourceNormalizer.WeylData Q split d T)
variable (E : SourceAngular.Equations Q split d)
variable (R : SourceSigned.Equations Q split d T W) (A : SourceGauss Q split d T W)

/-- The full marked positive subgroup has exactly its native image. -/
theorem comparison_unipotent : split.U.map (comparison Q split d T W E R A).toMonoidHom =
    Parabolics.unipotent m := by
  have he : (comparison Q split d T W E R A).toMonoidHom.comp (SourceAngular.eval Q split d E) =
      OrderedRootPresentation.eval (AngularPresentation.table m) (AngularPresentation.native_equations m) := by
    apply PresentedGroup.ext
    rintro ⟨i,a⟩
    change comparison Q split d T W E R A
      (SourceAngular.eval Q split d E (OrderedRootPresentation.root (AngularPresentation.table m) i a)) = _
    rw [SourceAngular.eval_root]
    exact (comparison_root Q split d T W E R A true i a).trans
      (OrderedRootPresentation.eval_root _ _ i a).symm
  rw [← SourceAngular.eval_range Q split d E, ← MonoidHom.range_comp, he]
  exact AngularPresentation.nativeEval_range m

/-- The entire H = B ∩ N maps to the full two-unit Cartan. -/
theorem comparison_cartan : (Q.tits.B ⊓ Q.tits.N).map (comparison Q split d T W E R A).toMonoidHom =
    Parabolics.fixedTorus m := by
  apply le_antisymm
  · rintro y ⟨x,hx,rfl⟩
    rw [← T.range_eq] at hx
    obtain ⟨t,rfl⟩ := hx
    have he := comparison_torus Q split d T W E R A (fixedTorusEquiv m t)
    change comparison Q split d T W E R A (T.h ((fixedTorusEquiv m).symm (fixedTorusEquiv m t))) = _ at he
    rw [MulEquiv.symm_apply_apply] at he
    change comparison Q split d T W E R A (T.h t) ∈ _
    rw [he]
    exact (fixedTorusEquiv m t).property
  · intro t ht
    refine ⟨SourceNormalizer.torus Q split d T ⟨t,ht⟩,?_,comparison_torus Q split d T W E R A ⟨t,ht⟩⟩
    rw [← T.range_eq]
    exact ⟨_,rfl⟩

/-- The full Borel, including both independent Cartan coordinates, is marked. -/
theorem comparison_borel : Q.tits.B.map (comparison Q split d T W E R A).toMonoidHom =
    Parabolics.borel m := by
  rw [← split.factorization,Subgroup.map_sup,comparison_unipotent,comparison_cartan]
  exact (SectionGeometry.BNPair.borel_eq_unipotent_sup_fixedTorus m).symm

private theorem source_endpoint_generation (s : Bool) :
    Q.tits.standardParabolic {Q.simple (SourceNormalizer.index d.orientation s)} =
      Q.tits.B ⊔ zpowers (W.n s : X ⧸ Q.D) := by
  apply le_antisymm
  · apply Q.tits.standardParabolic_le _ le_sup_left
    intro r hr
    obtain rfl := Set.mem_singleton_iff.mp hr
    intro x hx
    have hc := Q.tits.representative_mem_bruhatCell _ (W.n s) (W.placement s)
    exact Q.tits.bruhatCell_subset_of_mem _ le_sup_left hc (mem_sup_right (mem_zpowers _)) hx
  · apply sup_le (Q.tits.B_le_standardParabolic _)
    apply zpowers_le.mpr
    exact Q.tits.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton _)
      (Q.tits.representative_mem_bruhatCell _ (W.n s) (W.placement s))

/-- Both native parabolic generation statements, with the binary linear case retained. -/
theorem native_parabolic_generation (m : ℕ) (s : Bool) :
    Parabolics.parabolic m (NormalizerPresentation.side s) =
      Parabolics.borel m ⊔ zpowers (NormalizerPresentation.weyl m (simple s)) := by
  rw [NormalizerPresentation.weyl_simple]
  cases s
  · cases m with
    | zero => exact Octagon.Binary.linear_parabolic_generation
    | succ m => exact SectionGeometry.BNPair.linear_parabolic_eq_borel_sup_weyl (m+1) (by omega)
  · exact MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.suzuki_parabolic_eq_borel_sup_weyl m

/-- The two ordered source endpoints map to the actual full native parabolics. -/
theorem comparison_parabolic (s : Bool) :
    (Q.tits.standardParabolic {Q.simple (SourceNormalizer.index d.orientation s)}).map
      (comparison Q split d T W E R A).toMonoidHom = Parabolics.parabolic m (NormalizerPresentation.side s) := by
  rw [source_endpoint_generation Q split d T W, Subgroup.map_sup, comparison_borel, MonoidHom.map_zpowers]
  have he := comparison_weyl Q split d T W E R A (simple s)
  rw [SourceSigned.weyl_simple] at he
  rw [MulEquiv.coe_toMonoidHom,he,← native_parabolic_generation]

end ReeF4.RootPresentationRecognition.Global
