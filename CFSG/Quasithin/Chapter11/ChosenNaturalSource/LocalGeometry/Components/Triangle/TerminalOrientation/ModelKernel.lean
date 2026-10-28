module
public import Theory.SpecificGroups.PSL3.LinearThreeLocalCores
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.PointwiseFixer
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.CubicRootGeometry.Unitriangular
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel

/-!
# The joint local action kernel in PSL₃(4)

The two intrinsic local two-cores intersect in the highest root subgroup.
An automorphism of order dividing three trivial on both local sections
therefore acts trivially on the unipotent group modulo its center. That
center lies in the Frattini subgroup, whose automorphism kernel is a
two-group. The pointwise Sylow-fixer theorem then makes the automorphism
inner by a highest-root element; its order is again a power of two.
Thus the cubic automorphism is trivial on the whole projective group.

ProjectiveKernels transports this calculation through the original full
K/O₂(K) map and applies it to the canonical source triangle. This is the
local action comparison in Aschbacher--Smith, 11.1.2, printed p.764;
the pointwise Sylow-fixer calculation is the one used in E.6.8.
-/

open Subgroup Matrix
open scoped MatrixGroups commutatorElement
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3Even.UnipotentGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation.ModelKernel
public noncomputable section
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem point_core_coordinates (x : PSL(3,F))
    (hx : x ∈ (pointLocal F).pCoreIn 2) :
    ∃ a c : F, x = projective F ⟨a,0,c⟩ := by
  obtain ⟨x,hx,rfl⟩ := hx
  rw [pointLocal_twoCore_eq] at hx
  obtain ⟨g,hg,rfl⟩ := hx
  have hp := (mem_pointLocalSL_iff F g.val).mp g.property
  have hc := (mem_pointRadicalSL_iff F g).mp hg
  refine ⟨g.val.val 0 1,g.val.val 0 2,?_⟩
  change projection F g.val = projection F (specialLinear F _)
  apply congrArg (projection F)
  apply Subtype.ext
  change g.val.val = matrix F _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix,hp.1,hp.2.1,hp.2.2,
    hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]

private theorem line_core_coordinates (x : PSL(3,F))
    (hx : x ∈ (lineLocal F).pCoreIn 2) :
    ∃ b c : F, x = projective F ⟨0,b,c⟩ := by
  obtain ⟨x,hx,rfl⟩ := hx
  rw [lineLocal_twoCore_eq] at hx
  obtain ⟨g,hg,rfl⟩ := hx
  have hp := (mem_lineLocalSL_iff F g.val).mp g.property
  have hc := (mem_lineRadicalSL_iff F g).mp hg
  refine ⟨g.val.val 1 2,g.val.val 0 2,?_⟩
  change projection F g.val = projection F (specialLinear F _)
  apply congrArg (projection F)
  apply Subtype.ext
  change g.val.val = matrix F _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix,hp.1,hp.2.1,hp.2.2,
    hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]

/-- The two literal local two-cores intersect in the highest root. -/
theorem local_core_intersection_le_center :
    (pointLocal F).pCoreIn 2 ⊓ (lineLocal F).pCoreIn 2 ≤ projectiveCenter F := by
  rintro x ⟨hp,hl⟩
  obtain ⟨a,c,hp⟩ := point_core_coordinates x hp
  obtain ⟨b,d,hl⟩ := line_core_coordinates x hl
  have he := projective_injective F (hp.symm.trans hl)
  have ha : a = 0 := congrArg U.x he
  rw [hp,ha]
  exact (mem_projectiveCenter F _).mpr ⟨c,rfl⟩

omit [CharP F 2] in
/-- A cubic coordinate automorphism inducing the identity modulo the
highest root is trivial by the Frattini automorphism-kernel theorem. -/
theorem cubic_coordinates_eq_one (hF : Nat.card F = 4)
    (β : MulAut (U F)) (h3 : β^3 = 1)
    (hd : ∀ u : U F, β u * u⁻¹ ∈ Z F) : β = 1 := by
  have hp : IsPGroup 2 (U F) := IsPGroup.of_card (n := 6) (by rw [card_U,hF]; norm_num)
  let : Fact (IsPGroup 2 (U F)) := ⟨hp⟩
  have hz : Z F ≤ frattini (U F) := CubicRootGeometry.center_le_derived_coordinates.trans
    (commutator_le_frattini_of_isPGroup (p := 2))
  have hk : β ∈ (quotientAut (frattini (U F))).ker := by
    apply MulEquiv.ext
    intro q
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (frattini (U F)) q
    rw [quotientAut_apply_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    exact hz (hd u)
  have hβ := (isPGroup_quotientAut_frattini_kernel hp).exists_orderOf_dvd_pow
    (⟨β,hk⟩ : (quotientAut (frattini (U F))).ker)
  obtain ⟨n,hn⟩ := hβ
  have he : orderOf (⟨β,hk⟩ : (quotientAut (frattini (U F))).ker) = 1 :=
    Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 3 2).pow_right n)
      (orderOf_dvd_of_pow_eq_one (Subtype.ext h3)) hn
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp he)

/-- A cubic automorphism trivial on both literal parabolic sections is
trivial on PSL₃(4). The calculation retains the two different local cores. -/
theorem cubic_eq_one_of_local_kernels (hF : Nat.card F = 4)
    (α : MulAut PSL(3,F)) (h3 : α^3 = 1)
    (hp : ∀ x ∈ pointLocal F, α x * x⁻¹ ∈ (pointLocal F).pCoreIn 2)
    (hl : ∀ x ∈ lineLocal F, α x * x⁻¹ ∈ (lineLocal F).pCoreIn 2) : α = 1 := by
  have hd (u : PSL(3,F)) (hu : u ∈ unipotent F) :
      α u * u⁻¹ ∈ projectiveCenter F :=
    local_core_intersection_le_center ⟨hp u (unipotent_le_pointLocal F hu),
      hl u (unipotent_le_lineLocal F hu)⟩
  have hZU : projectiveCenter F ≤ unipotent F := by
    intro z hz
    obtain ⟨c,rfl⟩ := (mem_projectiveCenter F z).mp hz
    rw [←projective_range]
    exact ⟨⟨0,0,c⟩,rfl⟩
  have hU : (unipotent F).map α.toMonoidHom = unipotent F := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨u,hu,rfl⟩
      have h := (unipotent F).mul_mem (hZU (hd u hu)) hu
      simpa using h
    · exact (card_map_of_injective α.injective).ge
  let a : MulAut (unipotent F) :=
    (α.subgroupMap (unipotent F)).trans (MulEquiv.subgroupCongr hU)
  let e := unipotentEquiv F
  let β := MulAut.congr e.symm a
  have hb (u : U F) : projective F (β u) = α (projective F u) := by
    change (e (e.symm (a (e u))) : PSL(3,F)) = _
    rw [e.apply_symm_apply]
    rfl
  have hb3 : β^3 = 1 := by
    apply MulEquiv.ext
    intro u
    apply projective_injective F
    have ha := DFunLike.congr_fun h3 (projective F u)
    simp only [pow_succ,pow_zero,MulAut.mul_apply,MulAut.one_apply] at ha ⊢
    rw [hb,hb,hb]
    exact ha
  have hbZ (u : U F) : β u * u⁻¹ ∈ Z F := by
    have hh := hd (projective F u) (by rw [←projective_range]; exact ⟨u,rfl⟩)
    rw [←hb,←map_inv,←map_mul] at hh
    obtain ⟨c,hc⟩ := (mem_projectiveCenter F _).mp hh
    have he := projective_injective F hc
    rw [←he]
    exact (mem_Z F _).mpr ⟨rfl,rfl⟩
  have hβ := cubic_coordinates_eq_one hF β hb3 hbZ
  have hfix : ∀ u ∈ unipotent F, α u = u := by
    intro u hu
    rw [←projective_range] at hu
    obtain ⟨v,rfl⟩ := hu
    rw [←hb,hβ]
    rfl
  obtain ⟨z,hz,he⟩ := exists_projectiveCenter_of_fixes_unipotent F (by decide : 0 < 2)
    (by simpa using hF) α hfix
  obtain ⟨c,rfl⟩ := (mem_projectiveCenter F z).mp hz
  have hz2 : projective F (⟨0,0,c⟩ : U F)^2 = 1 := by
    rw [←map_pow,(square_eq_one_iff F _).mpr (Or.inl rfl),map_one]
  have h2 : α^2 = 1 := by rw [he,←map_pow,hz2,map_one]
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 3)
    (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3))

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation.ModelKernel
