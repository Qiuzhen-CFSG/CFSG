module

public import Theory.Representation.GoldschmidtONan.OrbitGeometry.RegularBranches
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Excluding mixed orbit subspaces

If a nonfixed orbit member W meets the moved space D nontrivially but is not
contained in D, its Y-suborbit covers every nonzero moved vector. Any further
suborbit would cover all mixed vectors, contradicting TI, so the whole orbit
consists of the fixed space and that one suborbit. Transport then equates the
dimensions of the spans obtained by omitting either member. Omitting W spans
all of V, while omitting the fixed space lies in the proper space W + D.

Source: GLS, Number 2, Chapter C, Proposition 14.2, last paragraph of Step 1
(`refs/KGroup/GLS2/ChapterC.tex`). All spans are of actual orbit members.
-/

public section
namespace Representation.GoldschmidtONan
open BinaryOffender RegularCyclicNormalClosure
variable {X V : Type*} [Group X] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) X V} {Y : Subgroup X}

/-- The mixed-intersection case in Step 1 contradicts TI after the regular
moved-space orbit is used to cover all nonzero moved vectors. -/
theorem Input.mixed_intersection_contradiction [Finite X] [Finite V] (h : Input ρ Y)
    {W : Submodule (ZMod 2) V} (hW : W ∈ fixedOrbit ρ Y)
    (hne : W ≠ fixedSpace ρ Y) (hnle : ¬ W ≤ displacementSpan ρ Y ⊤)
    (hstab : ∀ y : Y, W.map (ρ y) = W → y = 1)
    (hdis : ¬ Disjoint W (displacementSpan ρ Y ⊤)) : False := by
  let D : Submodule (ZMod 2) V := displacementSpan ρ Y ⊤
  let F : Submodule (ZMod 2) V := fixedSpace ρ Y
  have hz : ∃ z : V, z ∈ W ∧ z ∈ D ∧ z ≠ 0 := by
    rw [Submodule.disjoint_def] at hdis
    push Not at hdis
    exact hdis
  obtain ⟨z, hzW, hzD, hz0⟩ := hz
  have hDcover : D ≤ ⨆ y : Y, W.map (ρ y) := by
    intro d hd
    by_cases hd0 : d = 0
    · simp [hd0]
    obtain ⟨y, hy⟩ := h.transitive z hzD hz0 d hd hd0
    have hmem : d ∈ W.map (ρ y) := ⟨z, hzW, hy⟩
    exact (le_iSup (fun y : Y => W.map (ρ y)) y) hmem
  have hsup_le : (⨆ y : Y, W.map (ρ y)) ≤ W ⊔ D := by
    apply iSup_le
    intro y
    apply Submodule.map_le_iff_le_comap.mpr
    intro w hw
    change ρ y w ∈ W ⊔ D
    have hd : ρ y w - w ∈ D := Submodule.subset_span ⟨y, y.property, w, by trivial, rfl⟩
    have he : ρ y w = w + (ρ y w - w) := by abel
    rw [he]
    exact ((W ⊔ D).add_mem (show w ∈ W ⊔ D from Submodule.mem_sup_left hw)
      (show ρ y w - w ∈ W ⊔ D from Submodule.mem_sup_right hd))
  have hinter : W ⊓ D ≠ ⊥ := by
    intro he
    have : z ∈ (⊥ : Submodule (ZMod 2) V) := he ▸ ⟨hzW, hzD⟩
    exact hz0 (by simpa only [Submodule.mem_bot] using this)
  have hinterpos : 0 < Module.finrank (ZMod 2) (↥(W ⊓ D)) := by
    let : Nontrivial (↥(W ⊓ D)) := Submodule.nontrivial_iff_ne_bot.mpr hinter
    exact Module.finrank_pos
  have hsup_lt : Module.finrank (ZMod 2) (↥(W ⊔ D)) < Module.finrank (ZMod 2) V := by
    have heq := Submodule.finrank_sup_add_finrank_inf_eq W D
    have hsplit := Submodule.finrank_add_eq_of_isCompl h.split
    have hWdim := finrank_eq_fixed_of_mem_fixedOrbit hW
    have hsplit' : Module.finrank (ZMod 2) (↥W) +
        Module.finrank (ZMod 2) (↥D) = Module.finrank (ZMod 2) V := by
      calc
        _ = Module.finrank (ZMod 2) (↥(fixedSpace ρ Y)) +
            Module.finrank (ZMod 2) (↥D) := by rw [hWdim]
        _ = _ := hsplit
    omega
  have hsup_ne : W ⊔ D ≠ ⊤ := by
    intro he
    have := hsup_lt
    rw [he] at this
    exact (Nat.lt_irrefl _ (by simpa only [finrank_top] using this))
  have hWout : ∃ w : V, w ∈ W ∧ w ∉ D := by
    by_contra hh
    apply hnle
    intro w hw
    by_contra hwd
    exact hh ⟨w, hw, hwd⟩
  obtain ⟨w, hwW, hwD⟩ := hWout
  have hw0 : w ≠ 0 := fun hw0 => hwD (hw0 ▸ D.zero_mem)
  have hwF : w ∉ F := by
    intro hwf
    exact hw0 (Submodule.disjoint_def.mp (h.orbit_disjoint_fixed hW hne) w hwW hwf)
  have hOmega : fixedOrbit ρ Y = {F} ∪ Set.range (fun y : Y => W.map (ρ y)) := by
    ext U
    constructor
    · intro hU
      by_cases hUF : U = F
      · exact Set.mem_union_left _ (Set.mem_singleton_iff.mpr hUF)
      by_cases hUY : ∃ y : Y, U = W.map (ρ y)
      · exact Set.mem_union_right _ (Set.mem_range.mpr ⟨Classical.choose hUY,
          (Classical.choose_spec hUY).symm⟩)
      have hUD : Disjoint U D := by
        apply Submodule.disjoint_def.mpr
        intro v hvU hvD
        by_cases hv0 : v = 0
        · exact hv0
        obtain ⟨y, hy⟩ := h.transitive z hzD hz0 v hvD hv0
        have hvW : v ∈ W.map (ρ y) := ⟨z, hzW, hy⟩
        have hneUW : U ≠ W.map (ρ y) := by
          intro he
          apply hUY
          exact ⟨y, he⟩
        exact Submodule.disjoint_def.mp (h.ti U hU _ (map_mem_fixedOrbit hW y) hneUW)
          v hvU hvW
      have hUunion := h.suborbit_of_disjoint_moved hU hUF hUD
      have hwmix : w ∈ {v : V | v ∉ F ∧ v ∉ D} := ⟨hwF, hwD⟩
      have hwunion : w ∈ nonzeroSuborbitUnion ρ Y U := by
        rw [hUunion]
        exact hwmix
      obtain ⟨hv0, y, u, hu, hy⟩ := hwunion
      have hneUW : U.map (ρ y) ≠ W := by
        intro he
        apply hUY
        have he' := congrArg (fun T : Submodule (ZMod 2) V => T.map (ρ (y : X)⁻¹)) he
        have he'' : U = W.map (ρ (y : X)⁻¹) := by
          simpa only [← orbit_map_mul, inv_mul_cancel, orbit_map_one] using he'
        exact ⟨y⁻¹, he''⟩
      exact False.elim (hv0 (Submodule.disjoint_def.mp
        (h.ti (U.map (ρ y)) (map_mem_fixedOrbit hU y) W hW hneUW)
        w ⟨u, hu, hy⟩ hwW))
    · intro hU
      rcases (Set.mem_union U {F} (Set.range (fun y : Y => W.map (ρ y)))).mp hU with hUF | hUY
      · subst U
        exact fixed_mem_fixedOrbit
      · obtain ⟨y, rfl⟩ := Set.mem_range.mp hUY
        exact map_mem_fixedOrbit hW y
  let orbitSup : Submodule (ZMod 2) V → Submodule (ZMod 2) V := fun P =>
    ⨆ (U : Submodule (ZMod 2) V) (_ : U ∈ fixedOrbit ρ Y) (_ : U ≠ P), U
  have hS : (⨆ y : Y, W.map (ρ y)) = orbitSup F := by
    apply le_antisymm
    · apply iSup_le
      intro y
      exact le_iSup_of_le (W.map (ρ y))
        (le_iSup_of_le (map_mem_fixedOrbit hW y)
          (le_iSup_of_le (map_actor_ne_fixed hne y) le_rfl))
    · apply iSup_le
      intro U
      apply iSup_le
      intro hU
      apply iSup_le
      intro hUF
      rcases (Set.mem_union U {F} (Set.range (fun y : Y => W.map (ρ y)))).mp (hOmega ▸ hU) with hF | hY
      · exact False.elim (hUF hF)
      · obtain ⟨y, rfl⟩ := Set.mem_range.mp hY
        exact le_iSup (fun y : Y => W.map (ρ y)) y
  obtain ⟨x, hx⟩ := exists_map_eq_of_mem_fixedOrbit fixed_mem_fixedOrbit hW
  have hxF : F.map (ρ x) = W := by simpa [F] using hx
  have hmapSup : (orbitSup F).map (ρ x) = orbitSup W := by
    apply le_antisymm
    · change Submodule.map (ρ x) (⨆ (U : Submodule (ZMod 2) V)
          (_ : U ∈ fixedOrbit ρ Y) (_ : U ≠ F), U) ≤ orbitSup W
      simp only [Submodule.map_iSup]
      apply iSup_le
      intro U
      apply iSup_le
      intro hU
      apply iSup_le
      intro hUF
      have hUx : U.map (ρ x) ∈ fixedOrbit ρ Y := map_mem_fixedOrbit hU x
      have hUne : U.map (ρ x) ≠ W := by
        intro he
        apply hUF
        apply orbit_map_injective x
        exact he.trans hxF.symm
      exact le_iSup_of_le (U.map (ρ x))
        (le_iSup_of_le hUx (le_iSup_of_le hUne le_rfl))
    · change (⨆ (U : Submodule (ZMod 2) V)
          (_ : U ∈ fixedOrbit ρ Y) (_ : U ≠ W), U) ≤ (orbitSup F).map (ρ x)
      apply iSup_le
      intro U
      apply iSup_le
      intro hU
      apply iSup_le
      intro hUW
      have hUx : U.map (ρ x⁻¹) ∈ fixedOrbit ρ Y := map_mem_fixedOrbit hU x⁻¹
      have hUne : U.map (ρ x⁻¹) ≠ F := by
        intro he
        apply hUW
        apply orbit_map_injective x⁻¹
        have hxFinv : F = W.map (ρ (x⁻¹)) := by
          have hh := congrArg (fun T : Submodule (ZMod 2) V => T.map (ρ (x⁻¹))) hxF
          simpa only [← orbit_map_mul, inv_mul_cancel, orbit_map_one] using hh
        exact he.trans hxFinv
      have hle : U.map (ρ x⁻¹) ≤ orbitSup F := le_iSup_of_le (U.map (ρ x⁻¹))
        (le_iSup_of_le hUx (le_iSup_of_le hUne le_rfl))
      intro v hv
      have hv' : (ρ x⁻¹) v ∈ U.map (ρ x⁻¹) :=
        ⟨v, hv, by simp⟩
      have hv'' := hle hv'
      have hv''' := Submodule.mem_map_of_mem (f := ρ x) hv''
      simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
        map_one, Module.End.one_apply] using hv'''
  have hfinrank : Module.finrank (ZMod 2) (orbitSup F) =
      Module.finrank (ZMod 2) (orbitSup W) := by
    calc
      Module.finrank (ZMod 2) (orbitSup F) =
          Module.finrank (ZMod 2) ((orbitSup F).map (ρ x)) :=
        (Submodule.equivMapOfInjective (ρ x) (action_injective x) _).finrank_eq
      _ = Module.finrank (ZMod 2) (orbitSup W) := by rw [hmapSup]
  have htopW : orbitSup W = ⊤ := by
    apply top_unique
    have hFle : F ≤ orbitSup W := by
      exact le_iSup_of_le F (le_iSup_of_le fixed_mem_fixedOrbit
        (le_iSup_of_le hne.symm le_rfl))
    have hspan : (ZMod 2) ∙ z < D := by
      apply lt_of_le_of_ne
      · apply Submodule.span_le.mpr
        intro u hu
        rcases Set.mem_singleton_iff.mp hu with rfl
        simpa using D.smul_mem 1 hzD
      · intro he
        have hh := finrank_span_singleton (K := ZMod 2) hz0
        have hdgt : 1 < Module.finrank (ZMod 2) (↥D) := by
          simpa [D] using h.moved_dimension_gt_one
        rw [← he] at hdgt
        omega
    obtain ⟨d', hd'D, hd'not⟩ := SetLike.exists_of_lt hspan
    have hd'0 : d' ≠ 0 := by
      intro he
      apply hd'not
      rw [he]
      exact Submodule.zero_mem _
    have hd'z : d' ≠ z := by
      intro he
      apply hd'not
      rw [he]
      exact Submodule.mem_span_singleton.mpr ⟨1, by simp⟩
    have hmem_of_ne_z : ∀ q : V, q ∈ D → q ≠ 0 → q ≠ z → q ∈ orbitSup W := by
      intro q hqD hq0 hqz
      obtain ⟨y, hy⟩ := h.transitive z hzD hz0 q hqD hq0
      have hy1 : y ≠ 1 := by
        intro he
        apply hqz
        have hh : z = q := by simpa [he] using hy
        exact hh.symm
      have hyW : W.map (ρ y) ≠ W := by
        intro he
        exact hy1 (hstab y he)
      have hsub : W.map (ρ y) ≤ orbitSup W := le_iSup_of_le (W.map (ρ y))
        (le_iSup_of_le (map_mem_fixedOrbit hW y)
          (le_iSup_of_le hyW le_rfl))
      exact hsub ⟨z, hzW, hy⟩
    have hDle : D ≤ orbitSup W := by
      intro q hqD
      by_cases hq0 : q = 0
      · simp [hq0]
      by_cases hqz : q = z
      · have heD : z + d' ∈ D := D.add_mem hzD hd'D
        have he0 : z + d' ≠ 0 := by
          intro he
          apply hd'z
          have hneg : (-d' : V) = d' := by
            calc
              -d' = (-1 : ZMod 2) • d' := (neg_one_smul (ZMod 2) d').symm
              _ = (1 : ZMod 2) • d' := by simp
              _ = d' := one_smul _ _
          rw [add_eq_zero_iff_eq_neg] at he
          exact (hneg ▸ he).symm
        have hez : z + d' ≠ z := by
          intro he
          have hh : z + d' = z + 0 := by simpa using he
          exact hd'0 (add_left_cancel hh)
        have hq' := hmem_of_ne_z d' hd'D hd'0 hd'z
        have he' := hmem_of_ne_z (z + d') heD he0 hez
        subst q
        have hadd : d' + d' = 0 := by
          rw [← two_smul (ZMod 2) d', show (2 : ZMod 2) = 0 by decide, zero_smul]
        simpa [add_assoc, add_comm, add_left_comm, hadd] using
          (orbitSup W).add_mem hq' he'
      · exact hmem_of_ne_z q hqD hq0 hqz
    have htop : F ⊔ D ≤ orbitSup W := sup_le hFle hDle
    rw [h.split.sup_eq_top] at htop
    exact htop
  have htopF : orbitSup F = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [htopW] at hfinrank
    simpa only [finrank_top] using hfinrank
  apply hsup_ne
  apply top_unique
  rw [← htopF]
  exact hS ▸ hsup_le

end Representation.GoldschmidtONan
