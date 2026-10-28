module
public import Theory.Representation.BinaryNaturalDual.Transport
public import Theory.Representation.BinaryFullLinearRecognition
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MaximalLevi
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.Residuals.GeometricFlags
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Orbits.VectorNormalForm
public import Theory.Representation.SL5ExteriorSquare.MarkedRecognition
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.PointOrbitCardinality
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.LeviStructure.Blocks

/-!
# Point parabolics in binary SL₅ modules

A faithful degree-five action is the full natural linear action in suitable
coordinates. Its nonzero point stabilizer is a maximal line parabolic and has
quotient PSL₄(2) by its intrinsic two-core.

For a ten-dimensional irreducible, the marked classification supplies the
exterior square, possibly after the specified inverse-transpose twist. A point
fixed by a full Sylow two-subgroup cannot belong to the nondecomposable orbit:
that orbit has index 868, which is even. The decomposable stabilizer is the
maximal 2+3 parabolic, with actual two-core quotient SL₂(2) × SL₃(2).
The stabilizer equivalences use the given actions and transport both groups
and vectors; dimension alone is not substituted for an action marking.

Source: Aschbacher--Smith, I.1.6(7), 10.2.9 (printed pp.752--753), and
12.5.5 (printed p.819), combined manuscript of 1 March 2004.
-/

@[expose] public noncomputable section
open Subgroup
open BinaryNaturalDual.VectorStabilizers
namespace Representation.BinaryFivePointStabilizers
open BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.FiveFlagGeometry.MaximalOvergroups
open SL5TenDimensional

private def quotientCongr {A B : Type*} [_root_.Group A] [_root_.Group B]
    (e : A ≃* B) : (A ⧸ pCore 2 A) ≃* (B ⧸ pCore 2 B) :=
  QuotientGroup.congr _ _ e (pCore_map_iso 2 e)

/-- A faithful binary representation of SL5 in degree five has the actual
point-stabilizer quotient PSL4, under its given action. -/
theorem natural_structure {A W : Type*} [_root_.Group A] [Finite A]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (hf : Function.Injective ρ)
    (e₀ : A ≃* Group) (hd : Module.finrank (ZMod 2) W = 5)
    (w : W) (hw : w ≠ 0) :
    IsCoatom (representationStabilizer ρ w) ∧
    Nonempty ((representationStabilizer ρ w ⧸ pCore 2 (representationStabilizer ρ w)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) := by
  let : FiniteDimensional (ZMod 2) W := Module.finite_of_finrank_pos (by omega)
  obtain ⟨e,f,he⟩ := BinaryFullLinearRecognition.exists_natural_equiv ρ hf e₀ hd
  let σ : Representation (ZMod 2) (LinearGroup 5) (Space 5) :=
    { toFun := fun g => g.toLinearMap
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let a := e.trans (slEquivLinear 5)
  have ha (g : A) (x : W) : f (ρ g x) = σ (a g) (f x) := he g x
  let c := BinaryNaturalDual.Transport.stabilizerEquiv ρ σ a f ha w
  have hwf : f w ≠ 0 := fun h => hw (f.map_eq_zero_iff.mp h)
  have hs : representationStabilizer σ (f w) =
      BinaryLinear.parabolic (Submodule.span (ZMod 2) {f w}) :=
    (pointParabolic_eq_stabilizer hwf).symm
  obtain ⟨b,hb⟩ := GeometricFlags.exists_flagSpace (Submodule.span (ZMod 2) {f w}) (0 : Fin 4)
    (finrank_span_singleton hwf)
  have hs' : representationStabilizer σ (f w) = flagStabilizer b {0} := by
    rw [hs,flagStabilizer_singleton,hb]
  constructor
  · have hc : IsCoatom ((representationStabilizer ρ w).map a.toMonoidHom) := by
      rw [BinaryNaturalDual.Transport.stabilizer_map ρ σ a f ha,hs']
      exact singleton_flag_isCoatom b 0
    exact (OrderIso.isCoatom_iff a.mapSubgroup _).mp hc
  · exact ⟨(quotientCongr (c.trans (MulEquiv.subgroupCongr hs'))).trans
      (lineQuotientEquiv b)⟩

private theorem square_conjugate_stabilizer (g : Group) (v : SL5ExteriorSquare.V) :
    (SL5ExteriorSquare.vectorStabilizer v).map (MulAut.conj g).toMonoidHom =
      SL5ExteriorSquare.vectorStabilizer (exteriorAction 2 g v) := by
  have h (a : Group) (x : SL5ExteriorSquare.V) :
      (exteriorAction 2 g) (exteriorAction 2 a x) =
        exteriorAction 2 ((MulAut.conj g) a) (exteriorAction 2 g x) := by
    rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
    simp [MulAut.conj_apply,mul_assoc]
  let f : SL5ExteriorSquare.V ≃ₗ[ZMod 2] SL5ExteriorSquare.V :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _) ((exteriorAction 2).asGroupHom g)
  exact BinaryNaturalDual.Transport.stabilizer_map (exteriorAction 2) (exteriorAction 2)
    (MulAut.conj g) f h v

/-- A nonzero exterior vector fixed by a full Sylow belongs to the
original decomposable orbit: the other orbit has even index 868. -/
theorem square_sylow_fixed_decomposable (S : Sylow 2 Group)
    (v : SL5ExteriorSquare.V) (hv : v ≠ 0)
    (hS : (S : Subgroup Group) ≤ SL5ExteriorSquare.vectorStabilizer v) :
    SL5ExteriorSquare.InExteriorOrbit SL5ExteriorSquare.decomposable v := by
  rcases SL5ExteriorSquare.exterior_orbits_exhaustive v hv with h | ⟨g,rfl⟩
  · exact h
  · exfalso
    have hi : (SL5ExteriorSquare.vectorStabilizer
        (exteriorAction 2 g SL5ExteriorSquare.nondecomposable)).index = 868 := by
      rw [←square_conjugate_stabilizer]
      exact (Subgroup.index_map_equiv (SL5ExteriorSquare.vectorStabilizer _) (MulAut.conj g)).trans
        SL5ExteriorSquare.index_nondecomposableStabilizer
    have hh := Subgroup.index_dvd_of_le hS
    rw [hi] at hh
    exact S.not_dvd_index ((by decide : 2 ∣ 868).trans hh)

private theorem plane_parabolic_isCoatom : IsCoatom (SL5ExteriorSquare.parabolic 2) := by
  let W := SL5ExteriorSquare.naturalFlag 2
  let e := slEquivLinear 5
  have he : (SL5ExteriorSquare.parabolic 2).map e.toMonoidHom = BinaryLinear.parabolic W := by
    ext x
    rw [mem_map_equiv]
    change (∀ v, (e (e.symm x)) v ∈ W ↔ v ∈ W) ↔ (∀ v, x v ∈ W ↔ v ∈ W)
    rw [e.apply_symm_apply]
  obtain ⟨b,hb⟩ := GeometricFlags.exists_flagSpace W (1 : Fin 4)
    (SL5ExteriorSquare.finrank_naturalFlag 2 (by decide))
  apply (OrderIso.isCoatom_iff e.mapSubgroup _).mp
  change IsCoatom ((SL5ExteriorSquare.parabolic 2).map e.toMonoidHom)
  rw [he,←hb,←flagStabilizer_singleton]
  exact singleton_flag_isCoatom b 1

/-- Actual square point stabilizers above a full Sylow have the 2+3 Levi quotient. -/
theorem square_structure (S : Sylow 2 Group)
    (v : SL5ExteriorSquare.V) (hv : v ≠ 0)
    (hS : (S : Subgroup Group) ≤ SL5ExteriorSquare.vectorStabilizer v) :
    IsCoatom (SL5ExteriorSquare.vectorStabilizer v) ∧
    Nonempty ((SL5ExteriorSquare.vectorStabilizer v ⧸
      pCore 2 (SL5ExteriorSquare.vectorStabilizer v)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) ×
        Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  obtain ⟨g,rfl⟩ := square_sylow_fixed_decomposable S v hv hS
  have he : SL5ExteriorSquare.vectorStabilizer SL5ExteriorSquare.decomposable =
      SL5ExteriorSquare.parabolic 2 := by
    rw [SL5ExteriorSquare.vectorStabilizer_eq_exteriorStabilizer_point]
    have hline : Submodule.span (ZMod 2) {SL5ExteriorSquare.decomposable} =
        SL5ExteriorSquare.V₁ := by
      simp [SL5ExteriorSquare.V₁,SL5ExteriorSquare.coordinateSpan,
        SL5ExteriorSquare.decomposable]
    rw [hline,SL5ExteriorSquare.exteriorStabilizer_V₁_eq_parabolic]
  let a := ((SL5ExteriorSquare.vectorStabilizer SL5ExteriorSquare.decomposable).equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr (square_conjugate_stabilizer g _))
  constructor
  · rw [←square_conjugate_stabilizer]
    apply (OrderIso.isCoatom_iff (MulAut.conj g).mapSubgroup _).mpr
    rw [he]
    exact plane_parabolic_isCoatom
  · exact ⟨(quotientCongr (a.symm.trans (MulEquiv.subgroupCongr he))).trans
      SL5ExteriorSquare.parabolicTwoQuotientEquiv⟩

/-- Both ten-dimensional irreducibles give the same genuine point quotient;
the cube is transported by the inverse-transpose automorphism. -/
theorem exterior_structure {A W : Type*} [_root_.Group A] [Finite A]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) [IsIrreducible ρ]
    (e₀ : A ≃* Group) (hd : Module.finrank (ZMod 2) W = 10)
    (S : Sylow 2 A) (w : W) (hw : w ≠ 0)
    (hS : (S : Subgroup A) ≤ representationStabilizer ρ w) :
    IsCoatom (representationStabilizer ρ w) ∧
    Nonempty ((representationStabilizer ρ w ⧸ pCore 2 (representationStabilizer ρ w)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) ×
        Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  obtain ⟨e,f,_,hf⟩ := SL5ExteriorSquare.square_coordinates_of_finrank_ten ρ e₀ hd
  have hs := BinaryNaturalDual.Transport.stabilizer_map ρ (exteriorAction 2) e f hf w
  have hfix : ((S.mapSurjective (f := e.toMonoidHom) e.surjective) : Subgroup Group) ≤
      SL5ExteriorSquare.vectorStabilizer (f w) := by
    change (S : Subgroup A).map e.toMonoidHom ≤ _
    rw [←show (representationStabilizer ρ w).map e.toMonoidHom =
      SL5ExteriorSquare.vectorStabilizer (f w) from hs]
    exact map_mono hS
  obtain ⟨hm,⟨q⟩⟩ := square_structure (S.mapSurjective (f := e.toMonoidHom) e.surjective) (f w)
    (fun h => hw (f.map_eq_zero_iff.mp h)) hfix
  let a := BinaryNaturalDual.Transport.stabilizerEquiv ρ (exteriorAction 2) e f hf w
  constructor
  · apply (OrderIso.isCoatom_iff e.mapSubgroup _).mp
    change IsCoatom ((representationStabilizer ρ w).map e.toMonoidHom)
    rw [hs]
    exact hm
  · exact ⟨(quotientCongr a).trans q⟩

end Representation.BinaryFivePointStabilizers
