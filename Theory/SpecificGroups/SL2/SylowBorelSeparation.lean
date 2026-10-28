module

public import Theory.SpecificGroups.SL2.SylowUniqueMaximal

/-!
# Sylow Borel separation in SL₂ in characteristic two

A nonidentity upper unipotent conjugate belongs to the upper Borel only when
the conjugator belongs to that Borel. The lower-left matrix entry proves this
directly over any field. Sylow conjugacy then supplies the intrinsic statement:
a conjugator carrying a nonidentity Sylow element into its normalizer lies in
that normalizer. Every proper overgroup of the Sylow is contained there.
These facts provide the rank-one separation in Campbell II.5.3–5.4.
-/

public section
open Subgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups Pointwise
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F]

theorem mem_borel_of_conjugate_unipotent_mem_borel (x g : SL(2,F)) (hx : x ∈ upperUnipotent F) (hne : x ≠ 1)
    (hgx : g*x*g⁻¹ ∈ rankOneBorel F) : g ∈ rankOneBorel F := by
  obtain ⟨t,rfl⟩ := (mem_upperUnipotent F x).mp hx
  have ht : t ≠ 0 := by rintro rfl; exact hne (transvection_coeff_zero _)
  apply (mem_rankOneBorel_iff g).mpr
  have he := (mem_rankOneBorel_iff _).mp hgx
  simp [adjugate_fin_two,mul_apply,Fin.sum_univ_two,transvection_coe] at he
  have hz : t*(g.val 1 0*g.val 1 0)=0 := by linear_combination -he
  exact mul_self_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left ht)

variable [Finite F] [CharP F 2]
private theorem sylow_borel_coordinates (S : Sylow 2 SL(2,F)) :
    ∃ a : SL(2,F), (S : Subgroup SL(2,F)).map (MulAut.conj a).toMonoidHom = upperUnipotent F ∧
      (normalizer (S : Set SL(2,F))).map (MulAut.conj a).toMonoidHom = rankOneBorel F := by
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq SL(2,F) S (upperUnipotentSylow F 2)
  let c := (MulAut.conj a).toMonoidHom
  have hS : (S : Subgroup SL(2,F)).map c = upperUnipotent F := by
    change ((a • S : Sylow 2 SL(2,F)) : Subgroup SL(2,F)) = _
    rw [ha]
    rfl
  have hN : (normalizer (S : Set SL(2,F))).map c = rankOneBorel F := by
    calc
      _ = normalizer ((S : Subgroup SL(2,F)).map c : Set SL(2,F)) :=
        map_equiv_normalizer_eq (S : Subgroup SL(2,F)) (MulAut.conj a)
      _ = rankOneBorel F := by rw [hS]
  exact ⟨a,hS,hN⟩

theorem mem_sylow_normalizer_of_conjugate_mem (S : Sylow 2 SL(2,F)) (x g : SL(2,F))
    (hx : x ∈ S) (hne : x ≠ 1) (hgx : g*x*g⁻¹ ∈ normalizer (S : Set SL(2,F))) :
    g ∈ normalizer (S : Set SL(2,F)) := by
  obtain ⟨a,hS,hN⟩ := sylow_borel_coordinates S
  let c := (MulAut.conj a).toMonoidHom
  have hcx : c x ∈ upperUnipotent F := hS ▸ mem_map_of_mem c hx
  have hcgx : c g * c x * (c g)⁻¹ ∈ rankOneBorel F := by
    have hh := hN ▸ mem_map_of_mem c hgx
    simpa only [map_mul,map_inv] using hh
  have hcg := mem_borel_of_conjugate_unipotent_mem_borel (c x) (c g) hcx
    (fun h => hne ((MulAut.conj a).injective (h.trans c.map_one.symm))) hcgx
  rw [←hN] at hcg
  obtain ⟨b,hb,he⟩ := hcg
  exact (MulAut.conj a).injective he ▸ hb

theorem sylow_normalizer_ne_top (S : Sylow 2 SL(2,F)) :
    normalizer (S : Set SL(2,F)) ≠ ⊤ := by
  obtain ⟨a,_,hN⟩ := sylow_borel_coordinates S
  intro he
  rw [he,map_top_of_surjective _ (MulAut.conj a).surjective] at hN
  have hh : transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero (1:F) ∈ rankOneBorel F := hN ▸ mem_top _
  have hz := (mem_rankOneBorel_iff _).mp hh
  simp [transvection_coe] at hz

theorem proper_overgroup_le_sylow_normalizer (S : Sylow 2 SL(2,F)) (M : Subgroup SL(2,F))
    (hSM : (S : Subgroup SL(2,F)) ≤ M) (hM : M ≠ ⊤) :
    M ≤ normalizer (S : Set SL(2,F)) := by
  obtain ⟨a,hS,hN⟩ := sylow_borel_coordinates S
  let c := (MulAut.conj a).toMonoidHom
  have hU : upperUnipotent F ≤ M.map c := hS ▸ map_mono hSM
  have hproper : M.map c ≠ ⊤ := by
    intro hm
    apply hM
    apply top_unique
    intro x _
    have hx : c x ∈ M.map c := hm ▸ mem_top _
    obtain ⟨y,hy,he⟩ := hx
    exact (MulAut.conj a).injective he ▸ hy
  have hle := overgroup_le_rankOneBorel hU hproper
  intro x hx
  have hh : c x ∈ rankOneBorel F := hle (mem_map_of_mem c hx)
  rw [←hN] at hh
  obtain ⟨y,hy,he⟩ := hh
  exact (MulAut.conj a).injective he ▸ hy
end Matrix.SpecialLinearGroup
