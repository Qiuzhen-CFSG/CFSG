module
public import Theory.Representation.BinaryOffender.ComponentSum
public import Theory.Representation.NormalComponentConstituents
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormSylow
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Complementary moved spaces of a crossed component pair

An index-two component normalizer makes the product with an exchanged
conjugate normal. In a faithful irreducible module that product moves the
whole space and has no fixed vectors. If each factor fixes the other's
moved space, the two moved spaces are complementary and the ambient group
permutes them. Perfectness gives degree greater than two on either side.
Conversely, the invariant intersection of the two moved spaces is either zero
or the whole irreducible module, giving crossed support or full movement by
both factors.

Source: Aschbacher--Smith D.3.6--9, printed pp.197--201.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]


/-- An exchanged component pair in a faithful irreducible module either has
crossed supports or each component moves the whole module. -/
theorem component_pair_crossed_or_full
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (J : Subgroup G) (hJ : IsComponent G J)
    (hindex : (normalizer (J : Set G)).index = 2)
    (a : G) (han : a ∉ normalizer (J : Set G)) :
    subspaceCommutator ρ ⊤ J ≤ fixedSpace ρ (J.map (MulAut.conj a).toMonoidHom) ∨
      (subspaceCommutator ρ ⊤ J = ⊤ ∧
        subspaceCommutator ρ ⊤ (J.map (MulAut.conj a).toMonoidHom) = ⊤) := by
  let J' := J.map (MulAut.conj a).toMonoidHom
  let X := J ⊔ J'
  let : X.Normal := sup_conjugate_normal_of_normalizer_index_two J hindex a han
  have hJn : J ≠ ⊥ := by
    intro hz
    have ho : componentOrbit J ⊤ = ⊥ := by simp [hz,componentOrbit]
    exact hJ.componentOrbit_top_ne_bot ho
  have hXn : X ≠ ⊥ := fun hz => hJn (bot_unique (le_sup_left.trans hz.le))
  let U := subspaceCommutator ρ ⊤ J
  let U' := subspaceCommutator ρ ⊤ J'
  have hmap : U.map (ρ a) = U' := moved_map_conjugate ρ J a
  have hsum : U ⊔ U' = ⊤ := by
    have hh := subspaceCommutator_iSup_family ρ (fun b : Bool => if b then J else J')
    have he : subspaceCommutator ρ ⊤ X = U ⊔ U' := by
      simpa only [iSup_bool_eq,Bool.false_eq_true,if_false,if_true] using hh
    exact he.symm.trans (subspaceCommutator_top_eq_top_of_normal_faithful_irreducible ρ hf hi X hXn)
  by_cases hU : U = ⊤
  · right
    refine ⟨hU,?_⟩
    change U' = ⊤
    rw [←hmap,hU,Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (ρ.apply_bijective a).surjective
  have hne : U ≠ U' := by
    intro he
    rw [←he,sup_idem] at hsum
    exact hU hsum
  have hm : J' ≠ J := fun he => han (mem_normalizer_iff_map_conj_eq.mpr he)
  have hperm (b : G) : U.map (ρ b) = U ∨ U.map (ρ b) = U' := by
    rcases NormPair.conjugate_eq_or_eq_of_normalizer_index_two hindex hm b with he | he
    · left; rw [moved_map_conjugate,he]
    · right; rw [moved_map_conjugate,he]
  have hperm' (b : G) : U'.map (ρ b) = U ∨ U'.map (ρ b) = U' := by
    have he : U'.map (ρ b) = U.map (ρ (b*a)) := by
      rw [←hmap,←Submodule.map_comp,map_mul]
      rfl
    rw [he]
    exact hperm (b*a)
  have hinf (b : G) : (U ⊓ U').map (ρ b) = U ⊓ U' := by
    rw [Submodule.map_inf _ (ρ.apply_bijective b).injective]
    have hiMap := Submodule.map_injective_of_injective (ρ.apply_bijective b).injective
    rcases hperm b with h | h <;> rcases hperm' b with h' | h'
    · exact (hne (hiMap (h.trans h'.symm))).elim
    · rw [h,h']
    · rw [h,h',inf_comm]
    · exact (hne (hiMap (h.trans h'.symm))).elim
  let R : Subrepresentation ρ := {
    toSubmodule := U ⊓ U'
    apply_mem_toSubmodule b v hv := hinf b ▸ Submodule.mem_map_of_mem (f := ρ b) hv }
  have hbot : U ⊓ U' = ⊥ := by
    rcases hi.eq_bot_or_eq_top R with hb | ht
    · exact congrArg Subrepresentation.toSubmodule hb
    · have he : U ⊓ U' = ⊤ := congrArg Subrepresentation.toSubmodule ht
      exact (hU (top_unique (he.ge.trans inf_le_left))).elim
  have hnorm : J' ≤ normalizer (J : Set G) :=
    (commutator_eq_bot_iff_le_centralizer.mp ((hJ.map_conj a).commutator_eq_bot_of_ne hJ hm)).trans
      (centralizer_le_normalizer (J : Set G))
  have hstable : J' ≤ subspaceStabilizer ρ U := subspaceCommutator_invariant_normalizer ρ
    (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) hnorm
  left
  intro v hv j
  change ρ (j : G) v = v
  apply sub_eq_zero.mp
  apply hbot.le
  refine ⟨U.sub_mem ((hstable j.property v).2 hv) hv,?_⟩
  exact Submodule.subset_span ⟨j,j.property,v,Submodule.mem_top,rfl⟩

variable [FiniteDimensional (ZMod 2) V]

/-- Cross-centralizing moved spaces of an exchanged component pair are literal
complementary summands of a faithful irreducible module. -/
theorem crossed_component_pair_complement
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (J : Subgroup G) (hJ : IsComponent G J)
    (hindex : (normalizer (J : Set G)).index = 2)
    (a : G) (han : a ∉ normalizer (J : Set G)) (ha2 : a * a = 1)
    (hcross : subspaceCommutator ρ ⊤ J ≤
      fixedSpace ρ (J.map (MulAut.conj a).toMonoidHom)) :
    IsCompl (subspaceCommutator ρ ⊤ J) ((subspaceCommutator ρ ⊤ J).map (ρ a)) ∧
    2 < Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ J) ∧
    ∀ b : G, (subspaceCommutator ρ ⊤ J).map (ρ b) = subspaceCommutator ρ ⊤ J ∨
      (subspaceCommutator ρ ⊤ J).map (ρ b) = (subspaceCommutator ρ ⊤ J).map (ρ a) := by
  let J' := J.map (MulAut.conj a).toMonoidHom
  let X := J ⊔ J'
  let : X.Normal := sup_conjugate_normal_of_normalizer_index_two J hindex a han
  let := hJ.2
  have hJn : J ≠ ⊥ := by
    intro hz
    have ho : componentOrbit J ⊤ = ⊥ := by simp [hz,componentOrbit]
    exact hJ.componentOrbit_top_ne_bot ho
  have hXn : X ≠ ⊥ := fun hz => hJn (bot_unique (le_sup_left.trans hz.le))
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf hi X hXn
  have hfull := subspaceCommutator_top_eq_top_of_normal_faithful_irreducible ρ hf hi X hXn
  let U := subspaceCommutator ρ ⊤ J
  let U' := subspaceCommutator ρ ⊤ J'
  have hmap : U.map (ρ a) = U' := moved_map_conjugate ρ J a
  have hrev : U' ≤ fixedSpace ρ J := by
    rw [←hmap]
    rintro _ ⟨v,hv,rfl⟩ j
    have hj : a * (j : G) * a⁻¹ ∈ J' := mem_map_of_mem _ j.property
    have hh := hcross hv ⟨_,hj⟩
    change ρ (a * (j : G) * a⁻¹) v = v at hh
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha2
    have he := congrArg (ρ a⁻¹) hh
    have he' : ρ (j : G) (ρ a⁻¹ v) = ρ a⁻¹ v := by
      simpa only [map_mul,Module.End.mul_apply,ρ.inv_self_apply] using he
    change ρ (j : G) (ρ a v) = ρ a v
    simpa only [hai] using he'
  have hdis : Disjoint U U' := by
    apply disjoint_iff_inf_le.mpr
    intro v hv
    have hh : v ∈ fixedSpace ρ X := by
      rw [show fixedSpace ρ X = fixedSpace ρ J ⊓ fixedSpace ρ J' from ρ.invariants_comp_sup J J']
      exact ⟨hrev hv.2,hcross hv.1⟩
    exact hfix.le hh
  have hsum : U ⊔ U' = ⊤ := by
    have hh := subspaceCommutator_iSup_family ρ (fun b : Bool => if b then J else J')
    have he : subspaceCommutator ρ ⊤ X = U ⊔ U' := by
      simpa only [iSup_bool_eq,Bool.false_eq_true,if_false,if_true] using hh
    exact he.symm.trans hfull
  have hd : 2 < Module.finrank (ZMod 2) U := by
    obtain ⟨I,hI⟩ := exists_isIrrPlus_of_faithful ρ hf J hJn
    apply (hI.finrank_gt_two ρ J).trans_le
    apply Submodule.finrank_mono
    exact hI.choose_spec.1.ge.trans (subspaceCommutator_mono_left ρ le_top J)
  refine ⟨hmap.symm ▸ (show IsCompl U U' from ⟨hdis,codisjoint_iff.mpr hsum⟩),hd,?_⟩
  intro b
  have hm : J' ≠ J := fun he => han (mem_normalizer_iff_map_conj_eq.mpr he)
  rcases NormPair.conjugate_eq_or_eq_of_normalizer_index_two hindex hm b with he | he
  · left
    rw [moved_map_conjugate,he]
  · right
    rw [moved_map_conjugate,moved_map_conjugate,he]
end Representation.BinaryOffender
