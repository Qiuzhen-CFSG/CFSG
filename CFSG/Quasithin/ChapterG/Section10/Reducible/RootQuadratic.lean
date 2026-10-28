module
public import CFSG.Quasithin.ChapterG.Section10.Lagrangian
public import Theory.SpecificGroups.BinaryLinear.LineRadical

/-!
# The quadratic root group in the reducible branch of G.10.4

A Sylow subgroup fixing the source point fixes a nonzero vector in the
axis on U. Its full common-center radical lies in that Sylow subgroup.
One source transvection has displacement in the sum of this center and
the marked point; the entire radical fixes that displacement. Conjugacy
inside the point stabilizer then makes the radical quadratic on V.
Source: Aschbacher--Smith G.10.4, printed p.358, case H=G.
-/

public section
open Module Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

/-- The actual full linear marking produces a genuine quadratic root group. -/
theorem exists_quadratic_center_radical (U : Subrepresentation ρ)
    [IsIrreducible U.toRepresentation] (hU0 : U.toSubmodule ≠ ⊥)
    (hUt : U.toSubmodule ≠ ⊤) (hdim : 3 ≤ finrank (ZMod 2) U.toSubmodule) :
    ∃ (e : G ≃* (U.toSubmodule ≃ₗ[ZMod 2] U.toSubmodule)) (a : U.toSubmodule),
      (∀ g u, e g u = U.toRepresentation g u) ∧ a ≠ 0 ∧
      IsQuadratic ρ ((BinaryLinear.radical (Submodule.span (ZMod 2) {a})).comap e.toMonoidHom) := by
  obtain ⟨e, he⟩ := h.exists_full_linear_marking_of_large_irreducible_submodule U hU0 hUt hdim
  obtain ⟨S,hS⟩ := h.exists_sylow_fixes_point
  let f := (B v).comp U.toSubmodule.subtype
  have hf : f ≠ 0 := h.axis_form_ne_zero U hU0
  let A : Subrepresentation (U.toRepresentation.comp (S : Subgroup G).subtype) := {
    toSubmodule := f.ker
    apply_mem_toSubmodule s u hu := by
      have hh := h.preserves (s : G) v u
      rw [hS s] at hh
      exact hh.trans hu }
  let μ := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) A.toSubmodule).toMonoidHom.comp
    A.toRepresentation.asGroupHom
  have hAf : finrank (ZMod 2) A.toSubmodule + 1 = finrank (ZMod 2) U.toSubmodule := by
    change finrank (ZMod 2) f.ker + 1 = finrank (ZMod 2) U.toSubmodule
    have hh := f.finrank_range_add_finrank_ker
    rw [Module.Dual.range_eq_top_of_ne_zero hf,finrank_top,Module.finrank_self] at hh
    omega
  let : Finite A.toSubmodule := Module.finite_of_finite (ZMod 2)
  have hAc : 2 ∣ Nat.card A.toSubmodule := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact dvd_pow_self 2 (by omega)
  have hp : IsPGroup 2 μ.range := S.isPGroup'.of_surjective μ.rangeRestrict μ.rangeRestrict_surjective
  obtain ⟨a,ha,ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (BinaryLinear.fixedSpace_ne_bot hAc hp)
  have hSa (s : S) : U.toRepresentation s (a : U.toSubmodule) = a := by
    exact congrArg Subtype.val (ha (μ s) ⟨s,rfl⟩)
  have haU : (a : U.toSubmodule) ≠ 0 := fun hh => ha0 (Subtype.ext hh)
  let L := Submodule.span (ZMod 2) {(a : U.toSubmodule)}
  let R := BinaryLinear.radical L
  let Y := R.comap e.toMonoidHom
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hRS : R ≤ (S' : Subgroup (U.toSubmodule ≃ₗ[ZMod 2] U.toSubmodule)) := by
    apply BinaryLinear.LineRadical.le_sylow_of_fixes
    intro s hs
    obtain ⟨g,hg,rfl⟩ := hs
    exact (he g a).trans (hSa ⟨g,hg⟩)
  have hYS : Y ≤ S := by
    intro y hy
    obtain ⟨s,hs,hs'⟩ := hRS hy
    exact (e.injective hs') ▸ hs
  have hYa (y : G) (hy : y ∈ Y) : ρ y (a : U.toSubmodule) = (a : U.toSubmodule) := by
    have hh := hy.1 (a : U.toSubmodule) (Submodule.mem_span_singleton_self _)
    change e y a = a at hh
    rw [he] at hh
    exact congrArg Subtype.val hh
  have hYv (y : G) (hy : y ∈ Y) : ρ y v = v := hS ⟨y,hYS hy⟩
  obtain ⟨x,hx⟩ := (h.full_axis_on_submodule U hU0 hUt).2.2 a
  have hex : e (x : G) = BinaryLinear.transvection (a : U.toSubmodule) f a.property := by
    apply LinearEquiv.ext
    intro u
    exact (he x u).trans (hx u)
  have hpartial (y : G) (hy : y ∈ Y) (z : V) : ρ y (ρ (x : G) z-z) = ρ (x : G) z-z := by
    obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp
      ((codisjoint_iff.mp (h.full_axis_on_submodule U hU0 hUt).1.codisjoint).symm ▸
        Submodule.mem_top (x := z))
    have hxu : ρ (x : G) u = u + f ⟨u,hu⟩ • (a : U.toSubmodule) :=
      congrArg Subtype.val (hx ⟨u,hu⟩)
    obtain ⟨k,_,hk⟩ := h.transvections x
    have hxw := hk ⟨w,hw⟩
    have hd : ρ (x : G) (u+w)-(u+w) =
        f ⟨u,hu⟩ • ((a : U.toSubmodule) : V) + k ⟨w,hw⟩ • v := by
      rw [map_add,hxu,hxw]
      abel
    rw [hd,map_add,map_smul,map_smul,hYa y hy,hYv y hy]
  refine ⟨e,a,he,haU,?_⟩
  intro y hy b hb z
  by_cases hb1 : b = 1
  · simp [hb1]
  have heb : e b ≠ 1 := fun hh => hb1 (e.injective (hh.trans e.map_one.symm))
  obtain ⟨c,hca,hc⟩ := BinaryLinear.LineRadical.conjugate_fixing_center
    (a : U.toSubmodule) haU f hf a.property hb heb
  let g := e.symm c
  have hg : e g = c := e.apply_symm_apply c
  have hgb : g * (x : G) * g⁻¹ = b := by
    apply e.injective
    rw [map_mul,map_mul,map_inv,hg,hex]
    exact hc
  have hcP : c ∈ BinaryLinear.parabolic L := by
    intro u
    constructor
    · intro hu
      obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hu
      exact Submodule.mem_span_singleton.mpr ⟨r,c.injective (by rw [map_smul,hca]; exact hr)⟩
    · intro hu
      obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [map_smul,hca]
      exact L.smul_mem _ (Submodule.mem_span_singleton_self _)
  have hcN := BinaryLinear.parabolic_le_normalizer L ((BinaryLinear.parabolic L).inv_mem hcP)
  have hgy : g⁻¹ * y * g ∈ Y := by
    change e (g⁻¹*y*g) ∈ R
    rw [map_mul,map_mul,map_inv,hg]
    simpa only [inv_inv] using (mem_normalizer_iff.mp hcN (e y)).mp (show e y ∈ R from hy)
  have hh := congrArg (ρ g) (hpartial (g⁻¹*y*g) hgy (ρ g⁻¹ z))
  simp only [map_sub,←Module.End.mul_apply,←map_mul] at hh
  have h₁ : g * g⁻¹*y*g * (x : G) * g⁻¹ = y*b := by rw [←hgb]; group
  have h₂ : g * g⁻¹*y*g * g⁻¹ = y := by group
  simp only [←mul_assoc] at hh
  rw [h₁,h₂,hgb,mul_inv_cancel,map_one] at hh
  simpa only [map_mul,Module.End.mul_apply,Module.End.one_apply,map_sub] using hh

end CFSG.Quasithin.ChapterG.Section10.Hypothesis
