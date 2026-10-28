module
public import Theory.SpecificGroups.PSL3Three.EightGeometry
public import Theory.SpecificGroups.PSL3Three.GraphWitnesses.Conjugacy
/-!
# Transport of the elementary-eight geometry of Aut(PSL₃(3))

An actual equivalence transports elementary-eight conjugacy, outer-involution
conjugacy, the pointwise fixer of each inner four, and its exact normalizer
two-core. The chosen outer involution has fixed group equal to the four's
normalizer inside the inner subgroup, which is S₄. All statements use the
literal preimage of the inner automorphism subgroup and actual centralizers.

Source: Aschbacher--Smith, Lemma 2.5.15, printed pp.558--559, outer case.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace Matrix.PSL3Three.EightGeometry
variable {A : Type*} [Group A]

private theorem map_centralizer {D H : Type*} [Group D] [Group H]
    (e : D ≃* H) (s : Set D) :
    (centralizer s).map e.toMonoidHom = centralizer (e '' s) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    exact (e.map_mul _ _).symm.trans ((congrArg e (hy z hz)).trans (e.map_mul _ _))
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro z hz
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e z) ⟨z, hz, rfl⟩

private theorem map_embedded_core {D H : Type*} [Group D] [Group H]
    (e : D ≃* H) (N : Subgroup D) :
    ((pCore 2 N).map N.subtype).map e.toMonoidHom =
      (pCore 2 (N.map e.toMonoidHom)).map (N.map e.toMonoidHom).subtype := by
  let d := e.subgroupMap N
  have he : e.toMonoidHom.comp N.subtype =
      (N.map e.toMonoidHom).subtype.comp d.toMonoidHom := rfl
  rw [Subgroup.map_map, he, ← Subgroup.map_map, pCore_map_iso]

/-- Conjugacy of elementary eights on any actual carrier of Aut(PSL₃(3)). -/
theorem eight_conjugate_of_equiv (e : A ≃* MulAut PSL) (B C : Subgroup A)
    (hB : IsElementaryAbelian 2 B) (hBc : Nat.card B = 8)
    (hC : IsElementaryAbelian 2 C) (hCc : Nat.card C = 8) :
    ∃ a : A, B.map (MulAut.conj a).toMonoidHom = C := by
  let : IsElementaryAbelian 2 B := hB
  let : IsElementaryAbelian 2 C := hC
  obtain ⟨g, hg⟩ := eight_conjugate (B.map e.toMonoidHom) (C.map e.toMonoidHom)
    (IsElementaryAbelian.map _) (by rw [card_map_of_injective e.injective, hBc])
    (IsElementaryAbelian.map _) (by rw [card_map_of_injective e.injective, hCc])
  refine ⟨e.symm g, ?_⟩
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_map, ← hg, Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro a
  simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    MulAut.conj_apply, map_mul, map_inv, e.apply_symm_apply]

/-- Outer involutions are conjugate on the same actual automorphism carrier. -/
theorem outer_involutions_conjugate_of_equiv (e : A ≃* MulAut PSL)
    (f g : A) (hf : orderOf f = 2) (hg : orderOf g = 2)
    (hfo : e f ∉ MulAut.innerSubgroup PSL) (hgo : e g ∉ MulAut.innerSubgroup PSL) :
    IsConj f g := by
  obtain ⟨u, hu⟩ := GraphWitnesses.outer_involution_graph_conjugate (e f)
    ((e.orderOf_eq f).trans hf) hfo
  obtain ⟨v, hv⟩ := GraphWitnesses.outer_involution_graph_conjugate (e g)
    ((e.orderOf_eq g).trans hg) hgo
  refine isConj_iff.mpr ⟨e.symm (v * u⁻¹), ?_⟩
  apply e.injective
  rw [map_mul, map_mul, map_inv, e.apply_symm_apply, hu, hv]
  group

/-- The elementary-eight fixer, its exact normalizer two-core and its graph
marking on any actual carrier of the full automorphism group. -/
theorem inner_four_structure_of_equiv (e : A ≃* MulAut PSL) (E : Subgroup A)
    (hEI : E ≤ (MulAut.innerSubgroup PSL).comap e.toMonoidHom)
    (hE : IsElementaryAbelian 2 E) (hc : Nat.card E = 4) :
    let K := (MulAut.innerSubgroup PSL).comap e.toMonoidHom
    let F := centralizer (E : Set A)
    IsElementaryAbelian 2 F ∧ Nat.card F = 8 ∧
    (pCore 2 (normalizer (E : Set A))).map (normalizer (E : Set A)).subtype = F ∧
    ∃ f : A, orderOf f = 2 ∧ f ∉ K ∧
      K ⊓ centralizer ({f} : Set A) = K ⊓ normalizer (E : Set A) ∧
      Nonempty ((K ⊓ normalizer (E : Set A) : Subgroup A) ≃* Equiv.Perm (Fin 4)) ∧
      F = E ⊔ zpowers f := by
  let : IsElementaryAbelian 2 E := hE
  let K := (MulAut.innerSubgroup PSL).comap e.toMonoidHom
  let F := centralizer (E : Set A)
  let D := E.map e.toMonoidHom
  let U := D.comap (MulAut.conj : PSL →* MulAut PSL)
  have hi := MulAut.conj_injective_of_center_eq_bot GraphWitnesses.EightCentralizers.psl_center_eq_bot
  have hDI : D ≤ MulAut.innerSubgroup PSL := by
    rintro _ ⟨x, hx, rfl⟩
    exact hEI hx
  have hUD : innerFour U = D := Subgroup.map_comap_eq_self hDI
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map e.toMonoidHom
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.comap_of_injective MulAut.conj hi D
  have hUc : Nat.card U = 4 := by
    rw [← card_map_of_injective (K := U) hi]
    change Nat.card (innerFour U) = 4
    rw [hUD, card_map_of_injective e.injective, hc]
  have hFmap : F.map e.toMonoidHom = fullFixer U := by
    rw [map_centralizer]
    change centralizer (D : Set (MulAut PSL)) = fullFixer U
    rw [← hUD, centralizer_innerFour]
  let dF := (e.subgroupMap F).trans (MulEquiv.subgroupCongr hFmap)
  let : IsElementaryAbelian 2 (fullFixer U) := four_fixer_elementary U inferInstance hUc
  have hFel : IsElementaryAbelian 2 F := IsElementaryAbelian.of_injective dF.toMonoidHom dF.injective
  have hFc : Nat.card F = 8 :=
    (Nat.card_congr dF.toEquiv).trans (card_four_fixer U inferInstance hUc)
  refine ⟨hFel, hFc, ?_, ?_⟩
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [map_embedded_core, map_equiv_normalizer_eq, hFmap]
    change (pCore 2 (normalizer (D : Set (MulAut PSL)))).map
      (normalizer (D : Set (MulAut PSL))).subtype = fullFixer U
    rw [← hUD]
    exact four_normalizer_twoCore U inferInstance hUc
  · obtain ⟨f, hf, hfo, hcent, ⟨d⟩, hgen⟩ := four_graph_inner_marking U inferInstance hUc
    have hKmap : K.map e.toMonoidHom = MulAut.innerSubgroup PSL :=
      map_comap_eq_self (by rw [e.toMonoidHom.range_eq_top_of_surjective e.surjective]; exact le_top)
    have hNmap : (K ⊓ normalizer (E : Set A) : Subgroup A).map e.toMonoidHom =
        MulAut.innerSubgroup PSL ⊓ normalizer (innerFour U : Set (MulAut PSL)) := by
      rw [Subgroup.map_inf _ _ _ e.injective, hKmap, map_equiv_normalizer_eq, hUD]
    refine ⟨e.symm f, (e.symm.orderOf_eq f).trans hf, ?_, ?_, ?_, ?_⟩
    · intro hm
      apply hfo
      change e (e.symm f) ∈ MulAut.innerSubgroup PSL at hm
      simpa only [e.apply_symm_apply] using hm
    · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [hNmap, Subgroup.map_inf _ _ _ e.injective, hKmap, map_centralizer,
        Set.image_singleton, e.apply_symm_apply]
      exact hcent
    · exact ⟨((e.subgroupMap _).trans (MulEquiv.subgroupCongr hNmap)).trans d⟩
    · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [hFmap, Subgroup.map_sup, MonoidHom.map_zpowers]
      change fullFixer U = D ⊔ zpowers (e (e.symm f))
      rw [e.apply_symm_apply, ← hUD, hgen]

end Matrix.PSL3Three.EightGeometry
