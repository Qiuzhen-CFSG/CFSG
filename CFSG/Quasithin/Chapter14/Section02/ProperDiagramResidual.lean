module
public import CFSG.Quasithin.Chapter14.Section02.NormalKOne
public import Theory.GroupTheory.PerfectCentralCoverLocalResidual
import all CFSG.Quasithin.Chapter14.Section02.NormalKOne

/-!
# The actual residual in a marked maximal parabolic

The component map to the marked quotient is a perfect central cover. When
its parabolic residual has odd-prime ranks at most one, its perfect residual
preimage embeds in the model. This identifies the source residual with the
literal model residual, including its quotient by the two-core. The source
normal core normalizes the selected residual, and noncontainment in the
model Borel transfers back to the original maximal subgroup.

Source: Aschbacher--Smith, 14.2.8(3), printed p.983; the central-cover
argument uses I.1.2, printed p.407.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02
open ChapterE ChapterE.Structure
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]

@[expose] noncomputable def markedParabolicMap (M K : Subgroup H)
    (e : sourceImage M K ≃* D) : K →* D :=
  e.toMonoidHom.comp ((QuotientGroup.mk' (sourceKernel M)).subgroupMap K)

@[expose] noncomputable def markedParabolicPreimage (M K : Subgroup H)
    (e : sourceImage M K ≃* D) (P : Subgroup D) : Subgroup K :=
  P.comap (markedParabolicMap M K e)

@[expose] noncomputable def markedParabolicResidual (M K : Subgroup H)
    (e : sourceImage M K ≃* D) (P : Subgroup D) : Subgroup H :=
  let R := markedParabolicPreimage M K e P
  (solvableResidual R).map (K.subtype.comp R.subtype)

omit [Finite H] [Finite D] in
theorem markedParabolicMap_surjective (M K : Subgroup H)
    (e : sourceImage M K ≃* D) : Function.Surjective (markedParabolicMap M K e) :=
  e.surjective.comp ((QuotientGroup.mk' (sourceKernel M)).subgroupMap_surjective K)

omit [Finite H] [Finite D] in
theorem markedParabolicResidual_le (M K : Subgroup H)
    (e : sourceImage M K ≃* D) (P : Subgroup D) : markedParabolicResidual M K e P ≤ K := by
  rintro _ ⟨x,_,rfl⟩
  exact x.val.property

omit [Finite D] in
theorem markedParabolicResidual_perfect (M K : Subgroup H)
    (e : sourceImage M K ≃* D) (P : Subgroup D) :
    Group.IsPerfect (markedParabolicResidual M K e P) :=
  Group.IsPerfect.map _

omit [Finite H] [Finite D] in
theorem markedParabolicMap_mem_borel (M K : Subgroup H)
    (e : sourceImage M K ≃* D) {B : Subgroup D}
    (he : (componentOverlap M K).map e.toMonoidHom = B) (x : K) :
    markedParabolicMap M K e x ∈ B ↔ (x : H) ∈ M := by
  rw [← he, mem_map_equiv]
  change e.symm (e _) ∈ componentOverlap M K ↔ _
  rw [e.symm_apply_apply]
  change QuotientGroup.mk' (sourceKernel M) x ∈ sourceImage M (M ⊓ K) ↔ _
  constructor
  · rintro ⟨y,hy,hyx⟩
    have hd := M.normalCore_le (QuotientGroup.eq_iff_div_mem.mp hyx)
    have hh := M.mul_mem (M.inv_mem hd) hy.1
    simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel,
      mul_one] using hh
  · intro hx
    exact ⟨x,⟨hx,x.property⟩,rfl⟩

omit [Finite D] in
theorem sourceKernel_le_normalizer_markedParabolicResidual (M K : Subgroup H) [K.Normal]
    (e : sourceImage M K ≃* D) (P : Subgroup D) :
    sourceKernel M ≤ normalizer (markedParabolicResidual M K e P : Set H) := by
  let R := markedParabolicPreimage M K e P
  let A := R.map K.subtype
  have hA : sourceKernel M ≤ normalizer (A : Set H) := by
    apply le_normalizer_iff.mpr
    intro g hg a ha
    obtain ⟨a,ha,rfl⟩ := ha
    have hak : g * (a : H) * g⁻¹ ∈ K := (inferInstance : K.Normal).conj_mem _ a.property g
    refine ⟨⟨g * (a : H) * g⁻¹,hak⟩,?_,rfl⟩
    change markedParabolicMap M K e _ ∈ P
    have hh : markedParabolicMap M K e ⟨g * (a : H) * g⁻¹,hak⟩ =
        markedParabolicMap M K e a := by
      apply congrArg e
      apply Subtype.ext
      change QuotientGroup.mk' (sourceKernel M) (g * (a : H) * g⁻¹) =
        QuotientGroup.mk' (sourceKernel M) a
      have hgq : QuotientGroup.mk' (sourceKernel M) g = 1 :=
        (QuotientGroup.eq_one_iff g).mpr hg
      simp only [map_mul,map_inv,hgq,one_mul,inv_one,mul_one]
    exact hh.symm ▸ ha
  have hres : markedParabolicResidual M K e P = (solvableResidual A).map A.subtype := by
    have hh := congrArg (fun W : Subgroup A => W.map A.subtype)
      (map_solvableResidual_eq (K.subtype.subgroupMap R) (K.subtype.subgroupMap_surjective R))
    rw [map_map] at hh
    exact hh
  rw [hres]
  exact hA.trans (normalizer_le_normalizer_characteristic_image A (solvableResidual A))

omit [Finite D] in
theorem markedParabolicResidual_not_le (M K : Subgroup H)
    (e : sourceImage M K ≃* D) (P B : Subgroup D)
    (he : (componentOverlap M K).map e.toMonoidHom = B)
    (hout : ¬ (solvableResidual P).map P.subtype ≤ B) :
    ¬ markedParabolicResidual M K e P ≤ M := by
  intro hle
  apply hout
  rintro _ ⟨y,hy,rfl⟩
  let f := (markedParabolicMap M K e).subgroupComap P
  obtain ⟨x,hx⟩ := f.solvableResidualMap_surjective
    ((markedParabolicMap M K e).subgroupComap_surjective_of_surjective P
      (markedParabolicMap_surjective M K e)) ⟨y,hy⟩
  have hm : x.val.val.val ∈ M := hle (mem_map_of_mem _ x.property)
  have hb := (markedParabolicMap_mem_borel M K e he x.val.val).mpr hm
  have hh := congrArg (fun z : solvableResidual P => z.val.val) hx
  change markedParabolicMap M K e x.val.val = (y : D) at hh
  change (y : D) ∈ B
  rw [← hh]
  exact hb

noncomputable def originalParabolicResidualCoreEquiv
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (e : sourceImage (ChapterB.minimalParabolicMax T hP) K ≃* D) (P : Subgroup D)
    (hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p (solvableResidual P) ≤ 1) :
    (markedParabolicResidual (ChapterB.minimalParabolicMax T hP) K e P ⧸
      pCore 2 (markedParabolicResidual (ChapterB.minimalParabolicMax T hP) K e P)) ≃*
    (solvableResidual P ⧸ pCore 2 (solvableResidual P)) := by
  let c := originalComponentStarCover T hP hs K hK hqK hgen
  let d : PerfectCentralCovering.Cover (K ⧸ pCore 2 K) D :=
    { toMonoidHom := e.toMonoidHom.comp c.toMonoidHom
      surjective := e.surjective.comp c.surjective
      isPerfect := c.isPerfect
      ker_le_center := by
        intro x hx
        apply c.ker_le_center
        exact e.injective ((MonoidHom.mem_ker.mp hx).trans (map_one e).symm) }
  let q := QuotientGroup.mk' (pCore 2 K)
  let M := ChapterB.minimalParabolicMax T hP
  let R := markedParabolicPreimage M K e P
  have he : (P.comap d.toMonoidHom).comap q = R := by
    unfold R markedParabolicPreimage markedParabolicMap d c originalComponentStarCover
    rfl
  have hq : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let a := d.residualPreimagePCoreEquiv (pCore_quotient_pCore_eq_bot 2) P hr q
    (QuotientGroup.mk'_surjective _) hq
  let a₀ := (MulEquiv.subgroupCongr he).solvableResidualEquiv
  let a₁ := QuotientGroup.congr _ _ a₀ (pCore_map_iso 2 a₀)
  let b := (solvableResidual R).equivMapOfInjective (K.subtype.comp R.subtype)
    (K.subtype_injective.comp R.subtype_injective)
  exact (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.trans (a₁.symm.trans a)

end CFSG.Quasithin.Chapter14.Section02
