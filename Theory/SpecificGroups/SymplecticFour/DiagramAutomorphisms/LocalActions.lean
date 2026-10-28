module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFacts
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary

/-!
# Automorphisms of the actual symplectic local SL₂ quotients

For field order `2 ^ n`, `n > 1`, the local factors are the embedded solvable
residuals of the parabolics. Consequently any automorphism fixing one of the
parabolics fixes its local factor. A parabolic-class-preserving automorphism
can first be corrected by the explicit conjugating element using
`correct_parabolic`.

An automorphism preserving a local factor induces an automorphism on its
characteristic two-core quotient. Transport through the already proved
matrix quotient isomorphisms gives the displayed SL₂ actions. Their
intertwining formulas use the actual middle-block and plane-restriction maps.
Entrywise field automorphisms induce entrywise SL₂ maps. Upper unipotents
detect the field map, and companion-matrix traces show that its contribution
is trivial if it acts inner on either local quotient.

Source: Aschbacher--Smith, F.1.12, printed pp.263--264 of the combined
manuscript of 1 March 2004, `refs/quasithin.pdf`. The classification of all
diagram-preserving automorphisms and the local two-element kernel calculation
are separate from the quotient-action constructions proved here.
-/

@[expose] public section

noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)

omit [CharP F 2] in
private theorem map_embedded_residual (a : MulAut (Sp F)) (P : Subgroup (Sp F))
    (hP : P.map a.toMonoidHom = P) :
    ((Subgroup.solvableResidual P).map P.subtype).map a.toMonoidHom =
      (Subgroup.solvableResidual P).map P.subtype := by
  let r := restrict a P hP
  calc
    _ = ((Subgroup.solvableResidual P).map r.toMonoidHom).map P.subtype := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    _ = _ := by rw [Subgroup.map_solvableResidual_eq r.toMonoidHom r.surjective]

include hcard hn in
/-- Fixing the point parabolic also fixes its actual nonbinary local factor. -/
theorem pointLocal_map (a : MulAut (Sp F))
    (hP : pointParabolic.map a.toMonoidHom = pointParabolic) :
    pointLocal.map a.toMonoidHom = pointLocal := by
  rw [← pointParabolic_solvableResidual_eq hcard hn]
  exact map_embedded_residual a pointParabolic hP

include hcard hn in
/-- Fixing the plane parabolic fixes its actual nonbinary local factor. -/
theorem planeLocal_map (a : MulAut (Sp F))
    (hP : planeParabolic.map a.toMonoidHom = planeParabolic) :
    planeLocal.map a.toMonoidHom = planeLocal := by
  rw [← planeParabolic_solvableResidual_eq hcard hn]
  exact map_embedded_residual a planeParabolic hP

/-- The automorphism induced on the actual point-local SL₂ quotient. -/
def pointSL2Action (a : MulAut (Sp F))
    (hL : pointLocal.map a.toMonoidHom = pointLocal) :
    MulAut (Matrix.SpecialLinearGroup (Fin 2) F) :=
  MulAut.congr (pointLocalCoreQuotientEquiv hcard hn)
    (QuotientGroup.congr _ _ (restrict a pointLocal hL)
      (pCore_map_iso 2 _))

/-- The automorphism induced on the actual plane-local SL₂ quotient. -/
def planeSL2Action (a : MulAut (Sp F))
    (hL : planeLocal.map a.toMonoidHom = planeLocal) :
    MulAut (Matrix.SpecialLinearGroup (Fin 2) F) :=
  MulAut.congr (planeLocalCoreQuotientEquiv hcard hn)
    (QuotientGroup.congr _ _ (restrict a planeLocal hL)
      (pCore_map_iso 2 _))

theorem pointSL2Action_quotient (a : MulAut (Sp F))
    (hL : pointLocal.map a.toMonoidHom = pointLocal) (l : pointLocal (F := F)) :
    pointSL2Action hcard hn a hL (pointQuotient l) =
      pointQuotient (restrict a pointLocal hL l) := by
  unfold pointSL2Action
  change pointLocalCoreQuotientEquiv hcard hn
    ((QuotientGroup.congr _ _ _ (pCore_map_iso 2 _)) ((pointLocalCoreQuotientEquiv hcard hn).symm
      (pointQuotient l))) = _
  rw [← pointLocalCoreQuotientEquiv_mk hcard hn l, MulEquiv.symm_apply_apply]
  exact pointLocalCoreQuotientEquiv_mk hcard hn _

theorem planeSL2Action_quotient (a : MulAut (Sp F))
    (hL : planeLocal.map a.toMonoidHom = planeLocal) (l : planeLocal (F := F)) :
    planeSL2Action hcard hn a hL (Plane.quotientMap l) =
      Plane.quotientMap (restrict a planeLocal hL l) := by
  unfold planeSL2Action
  change planeLocalCoreQuotientEquiv hcard hn
    ((QuotientGroup.congr _ _ _ (pCore_map_iso 2 _)) ((planeLocalCoreQuotientEquiv hcard hn).symm
      (Plane.quotientMap l))) = _
  rw [← planeLocalCoreQuotientEquiv_mk hcard hn l, MulEquiv.symm_apply_apply]
  exact planeLocalCoreQuotientEquiv_mk hcard hn _

theorem pointSL2Action_field (σ : F ≃+* F) (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    pointSL2Action hcard hn (fieldAutomorphism σ) (pointLocal_map hcard hn _ (field_map_pointParabolic σ)) A =
      Matrix.SpecialLinearGroup.map σ.toRingHom A := by
  obtain ⟨l, rfl⟩ := pointQuotient_surjective A
  rw [pointSL2Action_quotient]
  rfl

theorem planeSL2Action_field (σ : F ≃+* F) (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    planeSL2Action hcard hn (fieldAutomorphism σ) (planeLocal_map hcard hn _ (field_map_planeParabolic σ)) A =
      Matrix.SpecialLinearGroup.map σ.toRingHom A := by
  obtain ⟨l, rfl⟩ := Plane.quotientMap_surjective A
  rw [planeSL2Action_quotient]
  rfl

private def upper (t : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1,t;0,1], by simp [Matrix.det_fin_two]⟩

omit [Finite F] [CharP F 2] in
private theorem fieldMap_injective : Function.Injective
    (fun σ : F ≃+* F => Matrix.SpecialLinearGroup.map (n := Fin 2) σ.toRingHom) := by
  intro σ τ h
  apply RingEquiv.ext
  intro t
  have hx := congrArg (fun f : Matrix.SpecialLinearGroup (Fin 2) F →*
      Matrix.SpecialLinearGroup (Fin 2) F => (f (upper t)).val 0 1) h
  exact hx

/-- Field automorphisms are detected on the actual point-local quotient. -/
theorem pointSL2Action_field_injective : Function.Injective
    (fun σ : F ≃+* F => pointSL2Action hcard hn (fieldAutomorphism σ)
      (pointLocal_map hcard hn _ (field_map_pointParabolic σ))) := by
  intro σ τ h
  apply fieldMap_injective
  ext A : 1
  simpa only [pointSL2Action_field] using congrArg
    (fun a : MulAut (Matrix.SpecialLinearGroup (Fin 2) F) => a A) h

/-- Field automorphisms are detected on the actual plane-local quotient. -/
theorem planeSL2Action_field_injective : Function.Injective
    (fun σ : F ≃+* F => planeSL2Action hcard hn (fieldAutomorphism σ)
      (planeLocal_map hcard hn _ (field_map_planeParabolic σ))) := by
  intro σ τ h
  apply fieldMap_injective
  ext A : 1
  simpa only [planeSL2Action_field] using congrArg
    (fun a : MulAut (Matrix.SpecialLinearGroup (Fin 2) F) => a A) h
/-- A field automorphism acting inner on the point quotient is trivial. -/
theorem pointSL2Action_field_eq_inner (σ : F ≃+* F)
    (c : Matrix.SpecialLinearGroup (Fin 2) F)
    (h : pointSL2Action hcard hn (fieldAutomorphism σ)
      (pointLocal_map hcard hn _ (field_map_pointParabolic σ)) = MulAut.conj c) :
    σ = RingEquiv.refl F := by
  apply fieldEquiv_eq_refl_of_SL2_inner σ c
  intro A
  rw [← pointSL2Action_field hcard hn σ A]
  exact congrArg (fun a : MulAut (Matrix.SpecialLinearGroup (Fin 2) F) => a A) h

/-- A field automorphism acting inner on the plane quotient is trivial. -/
theorem planeSL2Action_field_eq_inner (σ : F ≃+* F)
    (c : Matrix.SpecialLinearGroup (Fin 2) F)
    (h : planeSL2Action hcard hn (fieldAutomorphism σ)
      (planeLocal_map hcard hn _ (field_map_planeParabolic σ)) = MulAut.conj c) :
    σ = RingEquiv.refl F := by
  apply fieldEquiv_eq_refl_of_SL2_inner σ c
  intro A
  rw [← planeSL2Action_field hcard hn σ A]
  exact congrArg (fun a : MulAut (Matrix.SpecialLinearGroup (Fin 2) F) => a A) h
end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
