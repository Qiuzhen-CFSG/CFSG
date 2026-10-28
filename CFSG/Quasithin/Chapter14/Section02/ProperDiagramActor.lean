module
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramResidual
public import Theory.GroupTheory.PairNormalizerIndex
public import Theory.GroupTheory.SolvableResidual.Transport

/-!
# Conjugation of the actual marked residual

The normal component gives an action of the source group on its marked
quotient. This action transports parabolic preimages and their perfect
residuals. Elements of the original maximal subgroup preserve the marked
Borel, and any residual outside it generates with the Sylow subgroup by
uniqueness of that maximal overgroup.

Source: Aschbacher–Smith, 14.2.8(3), printed p.983.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]

@[expose] noncomputable def markedParabolicActor (M K : Subgroup H) [K.Normal]
    (e : sourceImage M K ≃* D) : H →* MulAut D :=
  (MulAut.congr e).toMonoidHom.comp
    (by
      let : (sourceImage M K).Normal :=
        (inferInstance : K.Normal).map (QuotientGroup.mk' (sourceKernel M))
          (QuotientGroup.mk'_surjective _)
      exact MulAut.conjNormal.comp (QuotientGroup.mk' (sourceKernel M)))

omit [Finite H] [Finite D] in
theorem markedParabolicActor_apply (M K : Subgroup H) [K.Normal]
    (e : sourceImage M K ≃* D) (g : H) (x : K) :
    markedParabolicActor M K e g (markedParabolicMap M K e x) =
      markedParabolicMap M K e
        ⟨g * (x : H) * g⁻¹,(inferInstance : K.Normal).conj_mem _ x.property g⟩ := by
  let : (sourceImage M K).Normal :=
    (inferInstance : K.Normal).map (QuotientGroup.mk' (sourceKernel M))
      (QuotientGroup.mk'_surjective _)
  change e (MulAut.conjNormal (QuotientGroup.mk' (sourceKernel M) g)
    (e.symm (e _))) = e _
  rw [e.symm_apply_apply]
  apply congrArg e
  apply Subtype.ext
  change (QuotientGroup.mk' (sourceKernel M)) g *
      (QuotientGroup.mk' (sourceKernel M)) (x : H) *
      ((QuotientGroup.mk' (sourceKernel M)) g)⁻¹ =
    (QuotientGroup.mk' (sourceKernel M)) (g * (x : H) * g⁻¹)
  simp only [map_mul, map_inv]

omit [Finite D] in
private theorem markedParabolicResidual_eq_residual_preimage (M K : Subgroup H)
    (e : sourceImage M K ≃* D) (P : Subgroup D) :
    markedParabolicResidual M K e P =
      (solvableResidual ((markedParabolicPreimage M K e P).map K.subtype)).map
        ((markedParabolicPreimage M K e P).map K.subtype).subtype := by
  let R := markedParabolicPreimage M K e P
  have hh := congrArg (fun W => W.map (R.map K.subtype).subtype)
    (map_solvableResidual_eq (K.subtype.subgroupMap R) (K.subtype.subgroupMap_surjective R))
  rw [map_map] at hh
  exact hh

private theorem map_embedded_residual {X : Type*} [Group X] [Finite X]
    (a : MulAut X) (P : Subgroup X) :
    ((solvableResidual P).map P.subtype).map a.toMonoidHom =
      (solvableResidual (P.map a.toMonoidHom)).map (P.map a.toMonoidHom).subtype := by
  let d := P.equivMapOfInjective a.toMonoidHom a.injective
  have hh := congrArg (fun W => W.map (P.map a.toMonoidHom).subtype)
    (map_solvableResidual_eq d.toMonoidHom d.surjective)
  rw [map_map] at hh
  rw [map_map]
  exact hh

omit [Finite D] in
theorem markedParabolicResidual_conj (M K : Subgroup H) [K.Normal]
    (e : sourceImage M K ≃* D) (P Q : Subgroup D) (g : H)
    (he : P.map (markedParabolicActor M K e g).toMonoidHom = Q) :
    (markedParabolicResidual M K e P).map (MulAut.conj g).toMonoidHom =
      markedParabolicResidual M K e Q := by
  let f := markedParabolicMap M K e
  let a := MulAut.conjNormal (H := K) g
  let b := markedParabolicActor M K e g
  have hc (x : K) : f (a x) = b (f x) :=
    (markedParabolicActor_apply M K e g x).symm
  have ha : (P.comap f).map a.toMonoidHom = Q.comap f := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      change f (a x) ∈ Q
      rw [hc,← he]
      exact mem_map_of_mem _ hx
    · intro hy
      have hx : f (a.symm y) ∈ P := by
        change f y ∈ Q at hy
        rw [← he,mem_map_equiv] at hy
        have hh : f (a.symm y) = b.symm (f y) := by
          apply b.injective
          rw [← hc,a.apply_symm_apply,b.apply_symm_apply]
        exact hh.symm ▸ hy
      exact ⟨a.symm y,hx,a.apply_symm_apply y⟩
  have hEq : ((P.comap f).map K.subtype).map (MulAut.conj g).toMonoidHom =
      (Q.comap f).map K.subtype := by
    rw [← ha,map_map,map_map]
    rfl
  rw [markedParabolicResidual_eq_residual_preimage,map_embedded_residual]
  exact (congrArg (fun L : Subgroup H => (solvableResidual L).map L.subtype)
    hEq).trans (markedParabolicResidual_eq_residual_preimage M K e Q).symm


omit [Finite H] [Finite D] in
theorem markedParabolicActor_borel (M K : Subgroup H) [K.Normal]
    (e : sourceImage M K ≃* D) {B : Subgroup D}
    (he : (componentOverlap M K).map e.toMonoidHom = B)
    (g : H) (hg : g ∈ M) : B.map (markedParabolicActor M K e g).toMonoidHom = B := by
  apply le_antisymm
  · rintro _ ⟨b,hb,rfl⟩
    obtain ⟨x,rfl⟩ := markedParabolicMap_surjective M K e b
    change markedParabolicActor M K e g (markedParabolicMap M K e x) ∈ B
    rw [markedParabolicActor_apply,markedParabolicMap_mem_borel M K e he]
    exact M.mul_mem (M.mul_mem hg ((markedParabolicMap_mem_borel M K e he x).mp hb))
      (M.inv_mem hg)
  · intro b hb
    obtain ⟨x,hx⟩ := markedParabolicMap_surjective M K e b
    let y : K := ⟨g⁻¹ * (x:H) * g,(inferInstance : K.Normal).conj_mem _ x.property g⁻¹
      |> (by simpa only [inv_inv] using ·)⟩
    refine ⟨markedParabolicMap M K e y,?_,?_⟩
    · apply (markedParabolicMap_mem_borel M K e he y).mpr
      exact M.mul_mem (M.mul_mem (M.inv_mem hg)
        ((markedParabolicMap_mem_borel M K e he x).mp (hx.symm ▸ hb))) hg
    · change markedParabolicActor M K e g (markedParabolicMap M K e y) = b
      rw [markedParabolicActor_apply]
      convert hx using 1
      congr 1
      apply Subtype.ext
      simp [y,mul_assoc]

omit [Finite D] in
theorem markedParabolicResidual_sup_sylow (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (K : Subgroup H)
    (e : sourceImage (ChapterB.minimalParabolicMax T hP) K ≃* D) (P : Subgroup D)
    (hout : ¬ markedParabolicResidual (ChapterB.minimalParabolicMax T hP) K e P ≤
      ChapterB.minimalParabolicMax T hP) :
    markedParabolicResidual (ChapterB.minimalParabolicMax T hP) K e P ⊔
      (T : Subgroup H) = ⊤ := by
  rcases eq_top_or_exists_le_coatom
      (markedParabolicResidual (ChapterB.minimalParabolicMax T hP) K e P ⊔
        (T : Subgroup H)) with h | ⟨N,hN,hLN⟩
  · exact h
  · have hn := ChapterB.minimalParabolicMax_unique T hP hN (le_sup_right.trans hLN)
    have hle := (show markedParabolicResidual (ChapterB.minimalParabolicMax T hP) K e P ≤
        markedParabolicResidual (ChapterB.minimalParabolicMax T hP) K e P ⊔
          (T : Subgroup H) from le_sup_left).trans hLN
    rw [hn] at hle
    exact (hout hle).elim

end CFSG.Quasithin.Chapter14.Section02
