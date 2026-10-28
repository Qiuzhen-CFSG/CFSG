module

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Symplectic.PlaneCore
public import Theory.LinearAlgebra.BinaryInvolutionLagrangian

/-!
# Involutions in the original plane core

An involution fixes a binary Lagrangian pointwise. A basis of this
Lagrangian gives three pairwise collinear points, hence an original plane
of the C₃ geometry. Plane transitivity moves it to the base plane.

The pointwise fixer of that plane is elementary abelian and normalized
by its vertex. The retained ambient Sylow subgroup puts this fixer inside
the vertex, hence inside its actual two-core. This proves the precise
representative coverage used by Burnside fusion in Aschbacher–Smith
13.4.9, printed p.906. It does not identify the four individual orbits.
-/

public noncomputable section

namespace Quasithin.I5.C3Recognition.SymplecticMark
open Subgroup Matrix Theory.SpecificGroups.SymplecticSix
open Theory.SpecificGroups.SymplecticSix.TwoLocalCover
variable {G : Type*} [Group G] {S : DSystem .C3 G} (m : SymplecticMark S)

/-- Every binary Lagrangian comes from an original plane of the geometry. -/
theorem exists_plane_space (W : Submodule (ZMod 2) (Vector (ZMod 2)))
    (hW : (form (ZMod 2)).orthogonal W = W) :
    ∃ π : S.Plane, m.planeSpace π = W := by
  have hiso (u) (hu : u ∈ W) (v) (hv : v ∈ W) : form (ZMod 2) u v = 0 := by
    exact (show v ∈ (form (ZMod 2)).orthogonal W from hW.symm ▸ hv) u hu
  have hdim : Module.finrank (ZMod 2) W = 3 := by
    have hh' := LinearMap.BilinForm.finrank_orthogonal form_nondegenerate W
    rw [hW] at hh'
    have htotal : Module.finrank (ZMod 2) (Vector (ZMod 2)) = 6 := by simp [Theory.SpecificGroups.SymplecticSix.Vector]
    have hle := Submodule.finrank_le W
    rw [htotal] at hle hh'
    omega
  let b : Module.Basis (Fin 3) (ZMod 2) W :=
    (Module.finBasis (ZMod 2) W).reindex (finCongr hdim)
  have hb0 (i : Fin 3) : (b i : Vector (ZMod 2)) ≠ 0 := by
    intro hh
    exact b.ne_zero i (Subtype.ext hh)
  choose x hx using fun i => m.point_bijective.surjective ⟨(b i : Vector (ZMod 2)), hb0 i⟩
  have he (i : Fin 3) : m.point (x i) = (b i : Vector (ZMod 2)) := congrArg Subtype.val (hx i)
  have hinj : Function.Injective x := by
    intro i j hij
    apply b.injective
    apply Subtype.ext
    rw [← he i, ← he j, hij]
  have hc (i j : Fin 3) : S.Collinear (x i) (x j) := by
    apply (m.orthogonal _ _).mp
    rw [he i, he j]
    exact hiso _ (b i).property _ (b j).property
  obtain ⟨l, h0l, h1l⟩ := hc 0 1
  obtain ⟨k, h0k, h2k⟩ := hc 0 2
  obtain ⟨π, hlπ, hkπ⟩ := (S.collinear_iff_coplanar_at_middle S.source_local_polar_facts
    (hinj.ne (by decide : (0 : Fin 3) ≠ 1)) (hinj.ne (by decide : (0 : Fin 3) ≠ 2))
    h0l h1l h0k h2k).mp (hc 1 2)
  have hmem (i : Fin 3) : (b i : Vector (ZMod 2)) ∈ m.planeSpace π := by
    rw [← he i]
    apply m.point_mem_planeSpace
    fin_cases i
    · exact S.point_line_plane h0l hlπ
    · exact S.point_line_plane h1l hlπ
    · exact S.point_line_plane h2k hkπ
  have hle : W ≤ m.planeSpace π := by
    intro w hw
    have hsum := b.sum_repr (⟨w, hw⟩ : W)
    have hh := (m.planeSpace π).sum_mem fun i (_ : i ∈ Finset.univ) =>
      (m.planeSpace π).smul_mem (b.repr ⟨w, hw⟩ i) (hmem i)
    have hsum'' : (∑ i, (b.repr ⟨w, hw⟩ i) • (b i : Vector (ZMod 2))) = w := by
      simpa only [map_sum, map_smul, Submodule.subtype_apply] using congrArg W.subtype hsum
    rwa [hsum''] at hh
  exact ⟨π, (Submodule.eq_of_le_of_finrank_eq hle (by rw [hdim, m.planeSpace_finrank])).symm⟩
end Quasithin.I5.C3Recognition.SymplecticMark

namespace Quasithin.I5.C3Recognition
open Subgroup Matrix Theory.SpecificGroups.SymplecticSix
variable {G : Type*} [Group G] {S : DSystem .C3 G}
namespace SymplecticMark
variable (m : SymplecticMark S)

private theorem plane_fixer_elementary (m : SymplecticMark S) :
    IsElementaryAbelian 2 (fixingSubgroup G {x : S.Point | S.Inc x S.basePlane}) := by
  let K := fixingSubgroup G {x : S.Point | S.Inc x S.basePlane}
  let ρ : K →* (Vector (ZMod 2) ≃ₗ[ZMod 2] Vector (ZMod 2)) :=
    toLinear.comp (m.hom.comp K.subtype)
  apply Theory.LinearAlgebra.binary_lagrangian_kernel_isElementaryAbelian
    (form (ZMod 2)) (m.planeSpace S.basePlane) (m.planeSpace_orthogonal _) ρ
  · intro a b hab
    apply Subtype.ext
    apply m.hom_injective
    apply Matrix.PSp4Three.ext_action
    intro v
    exact congrArg (fun f : Vector (ZMod 2) ≃ₗ[ZMod 2] Vector (ZMod 2) => f v) hab
  · intro a x y
    exact preserves_form (m.hom a.val) x y
  · intro a v hv
    rcases (m.mem_planeSpace_iff S.basePlane v).mp hv with rfl | ⟨x, hx, rfl⟩
    · exact map_zero _
    change (m.hom a.val).val *ᵥ m.point x = m.point x
    rw [m.equivariant, (mem_fixingSubgroup_iff G).mp a.property x hx]

private theorem plane_normalizes_fixer :
    S.family 2 ≤ normalizer (fixingSubgroup G {x : S.Point | S.Inc x S.basePlane}) := by
  intro g hg
  have hgπ : g • S.basePlane = S.basePlane := by
    apply MulAction.mem_stabilizer_iff.mp
    rwa [S.stabilizer_basePlane]
  have hgπ' : g⁻¹ • S.basePlane = S.basePlane := by
    simpa only [inv_smul_smul] using (congrArg (g⁻¹ • ·) hgπ).symm
  have hconj {g : G} (hgp : g • S.basePlane = S.basePlane)
      {a : G} (ha : a ∈ fixingSubgroup G {x : S.Point | S.Inc x S.basePlane}) :
      g * a * g⁻¹ ∈ fixingSubgroup G {x : S.Point | S.Inc x S.basePlane} := by
    have hgip : g⁻¹ • S.basePlane = S.basePlane := by
      simpa only [inv_smul_smul] using (congrArg (g⁻¹ • ·) hgp).symm
    rw [mem_fixingSubgroup_iff]
    intro x hx
    have hxi : S.Inc (g⁻¹ • x) S.basePlane := by
      simpa only [hgip] using hx.smul S g⁻¹
    rw [mul_smul, mul_smul, (mem_fixingSubgroup_iff G).mp ha _ hxi, smul_inv_smul]
  rw [mem_normalizer_iff]
  intro a
  constructor
  · exact hconj hgπ
  · intro ha
    have hh := hconj hgπ' ha
    simpa only [inv_inv, inv_mul_cancel_left, mul_inv_cancel_right, mul_assoc, inv_mul_cancel, mul_one] using hh

private theorem plane_fixer_le_core (m : SymplecticMark S) (P : Sylow 2 G) (hP : (P : Subgroup G) = S.T) :
    fixingSubgroup G {x : S.Point | S.Inc x S.basePlane} ≤ S.Q 2 := by
  let K := fixingSubgroup G {x : S.Point | S.Inc x S.basePlane}
  have hK := (m.plane_fixer_elementary).isPGroup 2 K
  have hn : S.family 2 ≤ normalizer K := plane_normalizes_fixer
  have hPK : (P : Subgroup G) ≤ normalizer K := hP ▸ (S.T_le 2).trans hn
  have hsup : K ⊔ (P : Subgroup G) = P :=
    P.is_maximal' (hK.to_sup_of_normal_left' P.isPGroup' hPK) le_sup_right
  have hKT : K ≤ S.T := hP ▸ (hsup ▸ (show K ≤ K ⊔ (P : Subgroup G) from le_sup_left))
  exact le_pCoreIn_of_normalizes hK (hKT.trans (S.T_le 2)) hn

/-- The literal plane core is exactly the pointwise fixer of its seven points.
This also identifies explicit transvection products with elements of that core. -/
theorem plane_fixer_eq_core (m : SymplecticMark S) (P : Sylow 2 G)
    (hP : (P : Subgroup G) = S.T) :
    fixingSubgroup G {x : S.Point | S.Inc x S.basePlane} = S.Q 2 := by
  apply le_antisymm (m.plane_fixer_le_core P hP)
  intro a ha
  rw [mem_fixingSubgroup_iff]
  intro x hx
  exact S.core_fixes_incident_coset 2 0 (by decide) ha
    (CosetGeometry.Incident.symm S.family hx)

/-- Every involution is conjugate into the actual plane core. -/
theorem square_one_representative (m : SymplecticMark S) (P : Sylow 2 G) (hP : (P : Subgroup G) = S.T)
    (a : G) (ha : a ^ 2 = 1) : ∃ c : G, MulAut.conj c a ∈ S.Q 2 := by
  obtain ⟨W, hW, hfix⟩ := Theory.LinearAlgebra.binary_involution_fixed_lagrangian
    (form (ZMod 2)) Theory.SpecificGroups.SymplecticSix.TwoLocalCover.form_alternating
    Theory.SpecificGroups.SymplecticSix.TwoLocalCover.form_nondegenerate
    (toLinear (m.hom a)) (fun x => by
      change m.hom a • (m.hom a • x) = x
      rw [← mul_smul, ← pow_two, ← map_pow, ha, map_one, one_smul])
    (fun x y => preserves_form (m.hom a) x y)
  obtain ⟨π, hπ⟩ := m.exists_plane_space W hW
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G π S.basePlane
  apply Exists.intro c
  apply m.plane_fixer_le_core P hP
  rw [mem_fixingSubgroup_iff]
  intro x hx
  have hxπ : S.Inc (c⁻¹ • x) π := by
    have hh := hx.smul S c⁻¹
    simpa only [← hc, inv_smul_smul] using hh
  have haf : a • (c⁻¹ • x) = c⁻¹ • x := by
    apply m.point_injective
    rw [← m.equivariant]
    exact hfix _ (hπ ▸ m.point_mem_planeSpace hxπ)
  change (c * a * c⁻¹) • x = x
  rw [mul_smul, mul_smul, haf, smul_inv_smul]
end SymplecticMark

/-- The original marked chamber supplies involution representatives in its plane core. -/
theorem square_one_representative (S : DSystem .C3 G) (P : Sylow 2 G)
    (hP : (P : Subgroup G) = S.T) (a : G) (ha : a ^ 2 = 1) :
    ∃ c : G, MulAut.conj c a ∈ S.Q 2 := by
  let d := S.source_local_polar_facts
  obtain ⟨m⟩ := exists_symplecticMark S
    ⟨S.c3_points_card d, S.faithful_points, S.c3_exists_noncollinear,
      fun x y h => S.source_one_or_all_triples d x y h⟩
  exact m.square_one_representative P hP a ha
end Quasithin.I5.C3Recognition
