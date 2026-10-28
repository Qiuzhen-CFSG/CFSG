module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.Geometry.Selection.Containment
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.NaturalQuotient.Supplement

/-!
# The literal opposite-point supplement

The point radical sends the opposite coordinate line to every field line
outside the perpendicular three-space. The original quotient map lifts
this actor to L₁. Every point in the M₁-orbit of V₁ʸ is an L-conjugate:
M₁ normalizes L and V₁. Its preservation of V₃ keeps that orbit outside
V₃, so the correcting L₁-element gives M₁=L₁ N_M₁(V₁ʸ).
No abstract point-transitivity premise or replacement orbit is used.
Source: Aschbacher--Smith 11.5.7, printed p.783.
-/

open Subgroup Theory.SpecificGroups.SymplecticFour
set_option backward.isDefEq.respectTransparency false
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
open CFSG.Quasithin.Chapter12.Section02 OppositeGeometry

private theorem pointLocal_opposite_line_transitive {F : Type*} [Field F] [Finite F] [CharP F 2]
    (g : Sp F) (U : Submodule F (Vector F)) (hd : Module.finrank F U = 1)
    (hout : ¬ U ≤ LocalGeometry.Sp4.ModelFlag.movedStage g 3) :
    ∃ l ∈ pointLocal.map (MulAut.conj g).toMonoidHom,
      ((F ∙ (Pi.single (.inr 0) 1 : Vector F)).map (toLinear g).toLinearMap).map
        (toLinear l).toLinearMap = U := by
  obtain ⟨w,hw,hwout⟩ := Set.not_subset.mp hout
  let a := g⁻¹ • w
  have ha : a (.inr 0) ≠ 0 := by
    intro h
    exact hwout ((LocalGeometry.Sp4.ModelFlag.mem_movedStage _ _ _).mpr
      ((LocalGeometry.Sp4.ModelFlag.mem_hyperplane _).mpr h))
  have hw0 : w ≠ 0 := by intro h; subst w; exact hwout (Submodule.zero_mem _)
  let r := pointRadicalElement ((a (.inr 0))⁻¹ * a (.inl 1))
    ((a (.inr 0))⁻¹ * a (.inr 1)) ((a (.inr 0))⁻¹ * a (.inl 0))
  refine ⟨g*r.val*g⁻¹,mem_map_of_mem (MulAut.conj g).toMonoidHom r.property,?_⟩
  have hr : r.val • (Pi.single (.inr 0) 1 : Vector F) = (a (.inr 0))⁻¹ • a := by
    ext i
    rcases i with i | i <;> fin_cases i <;>
      simp [r,pointRadicalElement,pointRadicalMatrix,ha]
  rw [Submodule.map_span,Set.image_singleton,Submodule.map_span,Set.image_singleton]
  change F ∙ ((g*r.val*g⁻¹) • (g • (Pi.single (.inr 0) 1 : Vector F))) = U
  rw [mul_smul,mul_smul,inv_smul_smul,hr]
  change F ∙ (toLinear g ((a (.inr 0))⁻¹ • a)) = U
  rw [map_smul]
  change F ∙ ((a (.inr 0))⁻¹ • (g • (g⁻¹ • w))) = U
  rw [smul_inv_smul,Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero ha))]
  exact (eq_span_singleton_of_mem_of_finrank_eq_one hd hw hw0).symm

private theorem map_conj_mul' {A : Type*} [Group A] (U : Subgroup A) (x y : A) :
    U.map (MulAut.conj (x*y)).toMonoidHom =
      (U.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [map_map]
  congr 1
  ext z
  simp [MulAut.conj_apply,mul_assoc]

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- Every original component-conjugate point outside V₃ is reached from
the selected opposite point by an actual member of L₁. -/
theorem opposite_local_orbit (m : MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hflag : ∀ i : Fin 3, m.flag.space i = LocalGeometry.Sp4.ModelFlag.movedStage g i.succ)
    (y : L) (hy : PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹)
    (z : L) (hout : ¬ E.V₁.map (MulAut.conj (z:G)).toMonoidHom ≤ E.V₃) :
    ∃ l ∈ E.L₁, E.V₁.map (MulAut.conj (z:G)).toMonoidHom =
      (E.V₁.map (MulAut.conj (y:G)).toMonoidHom).map (MulAut.conj l).toMonoidHom := by
  let c := LocalGeometry.Coordinates.sp4 m.action
  let U := (m.flag.space 0).map (toLinear (PointModel.quotientMap m z)).toLinearMap
  have he : E.V₁.map (MulAut.conj (z:G)).toMonoidHom = c.preimage U := by
    rw [m.point_preimage]
    exact (c.preimage_map_action z (m.flag.space 0)).symm
  have hU : ¬ U ≤ LocalGeometry.Sp4.ModelFlag.movedStage g 3 := by
    intro h
    apply hout
    rw [he,m.threeSpace_preimage]
    exact (c.preimage_le_iff _ _).mpr ((hflag 2).symm ▸ h)
  have hd : Module.finrank E.input.field.Carrier U = 1 :=
    ((toLinear (PointModel.quotientMap m z)).finrank_map_eq _).trans (m.flag.dimension 0)
  obtain ⟨a,ha,haU⟩ := pointLocal_opposite_line_transitive g U hd hU
  rw [← PointModel.local_identification m g (hflag 0)] at ha
  obtain ⟨l,hl,hla⟩ := ha
  refine ⟨l,hl,?_⟩
  rw [he,opposition_point_preimage E m g (hflag 0) y hy,← c.preimage_map_action]
  congr 1
  change U = (Submodule.map (toLinear g).toLinearMap _).map (toLinear (PointModel.quotientMap m l)).toLinearMap
  rw [hla]
  exact haU.symm

/-- The supplement uses only the actual M₁ orbit. Normalizing L and V₁
makes each of its points an L-conjugate; the concrete point radical
supplies the correcting L₁-element. -/
theorem marked_point_stabilizer_supplement (m : MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hflag : ∀ i : Fin 3, m.flag.space i = LocalGeometry.Sp4.ModelFlag.movedStage g i.succ)
    (y : L) (hy : PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹)
    (hout : ¬ E.V₁.map (MulAut.conj (y:G)).toMonoidHom ≤ E.V₃)
    (hM3 : E.M₁ ≤ normalizer (E.V₃ : Set G)) :
    E.M₁ = E.L₁ ⊔ oppositePointStabilizer E (y:G) := by
  have hLM : E.L₁ ≤ E.M₁ := le_inf (E.L₁_le.trans L.le_normalizer)
    ((residualIn_le _).trans inf_le_right)
  apply le_antisymm _ (sup_le hLM (inf_le_left.trans le_rfl))
  intro s hs
  let z : L := ⟨s*(y:G)*s⁻¹,(mem_normalizer_iff.mp hs.1 (y:G)).mp y.property⟩
  have hpoints : E.V₁.map (MulAut.conj (z:G)).toMonoidHom =
      (E.V₁.map (MulAut.conj (y:G)).toMonoidHom).map (MulAut.conj s).toMonoidHom := by
    change E.V₁.map (MulAut.conj (s*(y:G)*s⁻¹)).toMonoidHom = _
    rw [map_conj_mul',map_conj_mul']
    have hpEq : E.V₁.map (MulAut.conj s⁻¹).toMonoidHom = E.V₁ :=
      mem_normalizer_iff_map_conj_eq.mp (E.G₁.inv_mem hs.2)
    rw [hpEq]
  have hzout : ¬ E.V₁.map (MulAut.conj (z:G)).toMonoidHom ≤ E.V₃ := by
    intro h
    have hh := map_mono (f := (MulAut.conj s⁻¹).toMonoidHom) h
    rw [hpoints,← map_conj_mul',inv_mul_cancel] at hh
    have hid : (MulAut.conj (1:G)).toMonoidHom = MonoidHom.id G := by ext x; simp
    have h3Eq : E.V₃.map (MulAut.conj s⁻¹).toMonoidHom = E.V₃ :=
      mem_normalizer_iff_map_conj_eq.mp (hM3 (E.M₁.inv_mem hs))
    rw [hid,map_id,h3Eq] at hh
    exact hout hh
  obtain ⟨l,hl,hle⟩ := opposite_local_orbit E m g hflag y hy z hzout
  rw [hpoints] at hle
  have hstab : l⁻¹*s ∈ oppositePointStabilizer E (y:G) := by
    refine ⟨E.M₁.mul_mem (E.M₁.inv_mem (hLM hl)) hs,?_⟩
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (E.V₁.map (MulAut.conj (y:G)).toMonoidHom).map (MulAut.conj (l⁻¹*s)).toMonoidHom = _
    rw [map_conj_mul',hle,← map_conj_mul',inv_mul_cancel]
    have hid : (MulAut.conj (1:G)).toMonoidHom = MonoidHom.id G := by ext x; simp
    rw [hid,map_id]
  change s ∈ E.L₁ ⊔ oppositePointStabilizer E (y:G)
  simpa only [mul_inv_cancel_left] using (E.L₁ ⊔ oppositePointStabilizer E (y:G)).mul_mem
    (mem_sup_left hl) (mem_sup_right hstab)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The earlier literal radical displacement gives M₁-invariance of V₃.
Its producer is the full-cover radical-action branch of
qt-d-1222-natural-closure-sp4. -/
theorem M₁_normalizes_threeSpace_of_radical_displacement (m : MarkedFlag E)
    (hti : ∀ g ∈ E.M, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hthree : ⁅V,E.L₁.pCoreIn 2⁆ = E.V₃) :
    E.M₁ ≤ normalizer (E.V₃ : Set G) := by
  have hn : E.M₁ ≤ normalizer (E.L₁ : Set G) := by
    apply le_trans _ (normalizer_le_normalizer_characteristic_image
      (L ⊓ E.G₁) (solvableResidual (L ⊓ E.G₁ : Subgroup G)))
    exact (le_inf inf_le_left (inf_le_right.trans E.G₁.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hnR := hn.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hnV := M₁_normalizes_seed_of_TI E m hti
  intro s hs
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [← hthree,map_commutator]
  have hVeq : V.map (MulAut.conj s).toMonoidHom = V := mem_normalizer_iff_map_conj_eq.mp (hnV hs)
  have hReq : (E.L₁.pCoreIn 2).map (MulAut.conj s).toMonoidHom = E.L₁.pCoreIn 2 :=
    mem_normalizer_iff_map_conj_eq.mp (hnR hs)
  change ⁅V.map (MulAut.conj s).toMonoidHom,(E.L₁.pCoreIn 2).map (MulAut.conj s).toMonoidHom⁆ = _
  rw [hVeq,hReq]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
