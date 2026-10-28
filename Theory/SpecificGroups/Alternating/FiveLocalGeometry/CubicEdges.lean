module

public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicEdges.Model
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Ordered edges and two triangles in A₅

The finite marked-pair calculation is transported through actual group
isomorphisms. Conjugation gives ordered-edge transitivity, a trivial
pointwise fixer, and an embedded cyclic setwise stabilizer with its
specified reversing generator. The two triangle witnesses retain their
conjugating elements and their distinct A₄ and A₅ joins.

Source: Aschbacher, *Sporadic Groups* (1994), 47.6 and 47.10,
pp.264, 266–267.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace alternatingGroup.FiveLocalGeometry.CubicEdges

variable {H : Type*} [Group H]

theorem conj_map_mul (g h : H) (P : Subgroup H) :
    P.map (MulAut.conj (g * h)).toMonoidHom =
      (P.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  change MulAut.conj (g * h) • P = MulAut.conj g • MulAut.conj h • P
  rw [map_mul, mul_smul]

theorem map_conj_equiv {H' : Type*} [Group H'] (e : H ≃* H')
    (g : H) (P : Subgroup H) :
    (P.map (MulAut.conj g).toMonoidHom).map e.toMonoidHom =
      (P.map e.toMonoidHom).map (MulAut.conj (e g)).toMonoidHom := by
  rw [map_map, map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem marking_model (P Q : Subgroup A5) (hP : Nat.card P = 3)
    (hQ : Nat.card Q = 3) (hJ : Nat.card (P ⊔ Q : Subgroup A5) = 12) :
    ∃ g : A5, P.map (MulAut.conj g).toMonoidHom = C 0 ∧
      Q.map (MulAut.conj g).toMonoidHom = C 1 := by
  obtain ⟨a, ha⟩ := cubic_conjugate (MulEquiv.refl A5) P (C 0) hP (card_C 0)
  obtain ⟨i, hi⟩ := cubic_representative (Q.map (MulAut.conj a).toMonoidHom)
    (by rw [card_map_of_injective (MulAut.conj a).injective, hQ])
  have hp : P.map (MulAut.conj (adjustment i * a)).toMonoidHom = C 0 := by
    rw [conj_map_mul, ha, (adjustment_maps i).1]
  have hq : Q.map (MulAut.conj (adjustment i * a)).toMonoidHom = C (representative i) := by
    rw [conj_map_mul, hi, (adjustment_maps i).2]
  have hc : Nat.card (C 0 ⊔ C (representative i) : Subgroup A5) = 12 := by
    rw [← hp, ← hq, ← Subgroup.map_sup, card_map_of_injective (MulAut.conj _).injective, hJ]
  have cases : representative i = 0 ∨ representative i = 1 ∨ representative i = 5 := by
    have h : ∀ i, representative i = 0 ∨ representative i = 1 ∨ representative i = 5 := by
      decide +kernel
    exact h i
  rcases cases with h | h | h
  · rw [h, sup_idem, card_C] at hc
    omega
  · exact ⟨adjustment i * a, hp, h ▸ hq⟩
  · rw [h, nonedge_join, card_top, card] at hc
    omega


/-- Mark an actual A₄ edge in any carrier isomorphic to A₅. -/
theorem exists_marking (e : H ≃* A5) (P Q : Subgroup H)
    (hP : Nat.card P = 3) (hQ : Nat.card Q = 3)
    (eJ : ↥(P ⊔ Q) ≃* alternatingGroup (Fin 4)) :
    ∃ a : H ≃* A5, P.map a.toMonoidHom = C 0 ∧ Q.map a.toMonoidHom = C 1 := by
  obtain ⟨g, hp, hq⟩ := marking_model (P.map e.toMonoidHom) (Q.map e.toMonoidHom)
    (by rw [card_map_of_injective e.injective, hP])
    (by rw [card_map_of_injective e.injective, hQ]) (by
      rw [← Subgroup.map_sup, card_map_of_injective e.injective, Nat.card_congr eJ.toEquiv,
        nat_card_alternatingGroup]
      norm_num [Nat.factorial])
  exact ⟨e.trans (MulAut.conj g), by rw [map_map] at hp; exact hp,
    by rw [map_map] at hq; exact hq⟩

/-- The literal intersection of the two intrinsic normalizers is trivial. -/
theorem normalizer_inf_eq_bot (e : H ≃* A5) (P Q : Subgroup H)
    (hP : Nat.card P = 3) (hQ : Nat.card Q = 3)
    (eJ : ↥(P ⊔ Q) ≃* alternatingGroup (Fin 4)) :
    normalizer (P : Set H) ⊓ normalizer (Q : Set H) = ⊥ := by
  obtain ⟨a, hp, hq⟩ := exists_marking e P Q hP hQ eJ
  apply (map_injective (f := a.toMonoidHom) a.injective)
  rw [map_inf _ _ _ a.injective, map_equiv_normalizer_eq, map_equiv_normalizer_eq,
    hp, hq, normalizer_inf_model, Subgroup.map_bot]

/-- Transitivity is witnessed by an element of the actual carrier. -/
theorem ordered_edge_transitive (e : H ≃* A5) (P Q R S : Subgroup H)
    (hP : Nat.card P = 3) (hQ : Nat.card Q = 3)
    (hR : Nat.card R = 3) (hS : Nat.card S = 3)
    (ePQ : ↥(P ⊔ Q) ≃* alternatingGroup (Fin 4))
    (eRS : ↥(R ⊔ S) ≃* alternatingGroup (Fin 4)) :
    ∃ g : H, P.map (MulAut.conj g).toMonoidHom = R ∧
      Q.map (MulAut.conj g).toMonoidHom = S := by
  have cardJ (U V : Subgroup H) (d : ↥(U ⊔ V) ≃* alternatingGroup (Fin 4)) :
      Nat.card (U.map e.toMonoidHom ⊔ V.map e.toMonoidHom : Subgroup A5) = 12 := by
    rw [← Subgroup.map_sup, card_map_of_injective e.injective, Nat.card_congr d.toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  obtain ⟨a, haP, haQ⟩ := marking_model (P.map e.toMonoidHom) (Q.map e.toMonoidHom)
    (by rw [card_map_of_injective e.injective, hP])
    (by rw [card_map_of_injective e.injective, hQ]) (cardJ P Q ePQ)
  obtain ⟨b, hbR, hbS⟩ := marking_model (R.map e.toMonoidHom) (S.map e.toMonoidHom)
    (by rw [card_map_of_injective e.injective, hR])
    (by rw [card_map_of_injective e.injective, hS]) (cardJ R S eRS)
  have go (U V : Subgroup H) (i : Fin 10)
      (hu : (U.map e.toMonoidHom).map (MulAut.conj a).toMonoidHom = C i)
      (hv : (V.map e.toMonoidHom).map (MulAut.conj b).toMonoidHom = C i) :
      U.map (MulAut.conj (e.symm (b⁻¹ * a))).toMonoidHom = V := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_conj_equiv, e.apply_symm_apply]
    apply map_injective (f := (MulAut.conj b).toMonoidHom) (MulAut.conj b).injective
    rw [← conj_map_mul, mul_inv_cancel_left, hu, hv]
  exact ⟨e.symm (b⁻¹ * a), go P R 0 haP hbR, go Q S 1 haQ hbS⟩

theorem exists_reversal (e : H ≃* A5) (P Q : Subgroup H)
    (hP : Nat.card P = 3) (hQ : Nat.card Q = 3)
    (eJ : ↥(P ⊔ Q) ≃* alternatingGroup (Fin 4)) :
    ∃ t : H, orderOf t = 2 ∧ P.map (MulAut.conj t).toMonoidHom = Q ∧
      Q.map (MulAut.conj t).toMonoidHom = P := by
  obtain ⟨a, hp, hq⟩ := exists_marking e P Q hP hQ eJ
  refine ⟨a.symm reversal, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, reversal_order]
  · apply map_injective (f := a.toMonoidHom) a.injective
    rw [map_conj_equiv, a.apply_symm_apply, hp, hq, reversal_maps.1]
  · apply map_injective (f := a.toMonoidHom) a.injective
    rw [map_conj_equiv, a.apply_symm_apply, hp, hq, reversal_maps.2]

theorem conj_map_inv_of_eq (g : H) {P Q : Subgroup H}
    (h : P.map (MulAut.conj g).toMonoidHom = Q) :
    Q.map (MulAut.conj g⁻¹).toMonoidHom = P := by
  rw [← h, ← conj_map_mul, inv_mul_cancel, map_one]
  exact Subgroup.map_id P

/-- The setwise stabilizer, as a literal subgroup of the given carrier. -/
def pairStabilizer (P Q : Subgroup H) : Subgroup H where
  carrier := {g | (P.map (MulAut.conj g).toMonoidHom = P ∧
      Q.map (MulAut.conj g).toMonoidHom = Q) ∨
    (P.map (MulAut.conj g).toMonoidHom = Q ∧ Q.map (MulAut.conj g).toMonoidHom = P)}
  one_mem' := by
    change (MulAut.conj (1 : H) • P = P ∧ MulAut.conj (1 : H) • Q = Q) ∨ _
    exact Or.inl ⟨by rw [map_one, one_smul], by rw [map_one, one_smul]⟩
  mul_mem' := by
    rintro a b (⟨ha, ha'⟩ | ⟨ha, ha'⟩) (⟨hb, hb'⟩ | ⟨hb, hb'⟩) <;>
      simp only [Set.mem_ofPred_eq, conj_map_mul, ha, ha', hb, hb'] <;> tauto
  inv_mem' := by
    rintro g (⟨hp, hq⟩ | ⟨hp, hq⟩)
    · exact Or.inl ⟨conj_map_inv_of_eq g hp, conj_map_inv_of_eq g hq⟩
    · exact Or.inr ⟨conj_map_inv_of_eq g hq, conj_map_inv_of_eq g hp⟩

theorem pairStabilizer_eq_zpowers_of_reversal (P Q : Subgroup H)
    (hfix : normalizer (P : Set H) ⊓ normalizer (Q : Set H) = ⊥)
    (t : H) (htP : P.map (MulAut.conj t).toMonoidHom = Q)
    (htQ : Q.map (MulAut.conj t).toMonoidHom = P) :
    pairStabilizer P Q = zpowers t := by
  have fixed (g : H) (hp : P.map (MulAut.conj g).toMonoidHom = P)
      (hq : Q.map (MulAut.conj g).toMonoidHom = Q) : g = 1 := by
    have hg : g ∈ normalizer (P : Set H) ⊓ normalizer (Q : Set H) :=
      ⟨mem_normalizer_iff_map_conj_eq.mpr hp, mem_normalizer_iff_map_conj_eq.mpr hq⟩
    simpa only [hfix, mem_bot] using hg
  apply le_antisymm
  · intro g hg
    rcases hg with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · rw [fixed g hp hq]
      exact one_mem _
    · have he : g * t⁻¹ = 1 := fixed (g * t⁻¹)
        (by rw [conj_map_mul, conj_map_inv_of_eq t htQ, hq])
        (by rw [conj_map_mul, conj_map_inv_of_eq t htP, hp])
      have heq : g = t := mul_inv_eq_one.mp he
      rw [heq]
      exact mem_zpowers _
  · exact zpowers_le.mpr (Or.inr ⟨htP, htQ⟩)

/-- The cyclic equivalence remembers the specified generating involution. -/
noncomputable def involutionZpowersEquiv (t : H) (ht : orderOf t = 2) :
    Multiplicative (ZMod 2) ≃* zpowers t :=
  zmodMulEquivOfGenerator (g := ⟨t, mem_zpowers t⟩) (by
    rintro ⟨x, hx⟩
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, Subtype.ext hn⟩) (by rw [Nat.card_zpowers, ht])

theorem involutionZpowersEquiv_generator (t : H) (ht : orderOf t = 2) :
    (involutionZpowersEquiv t ht (Multiplicative.ofAdd 1) : H) = t := by
  exact congrArg Subtype.val (zmodMulEquivOfGenerator_apply_ofAdd_one _ _)

/-- The setwise stabilizer is C₂, with its embedding and a generating reversal. -/
theorem exists_pairStabilizer_equiv (e : H ≃* A5) (P Q : Subgroup H)
    (hP : Nat.card P = 3) (hQ : Nat.card Q = 3)
    (eJ : ↥(P ⊔ Q) ≃* alternatingGroup (Fin 4)) :
    ∃ t : H, ∃ d : Multiplicative (ZMod 2) ≃* pairStabilizer P Q,
      (d (Multiplicative.ofAdd 1) : H) = t ∧ orderOf t = 2 ∧
      P.map (MulAut.conj t).toMonoidHom = Q ∧ Q.map (MulAut.conj t).toMonoidHom = P ∧
      pairStabilizer P Q = zpowers t := by
  obtain ⟨t, ht, hp, hq⟩ := exists_reversal e P Q hP hQ eJ
  have he := pairStabilizer_eq_zpowers_of_reversal P Q
    (normalizer_inf_eq_bot e P Q hP hQ eJ) t hp hq
  refine ⟨t, (involutionZpowersEquiv t ht).trans (MulEquiv.subgroupCongr he.symm),
    involutionZpowersEquiv_generator t ht, ht, hp, hq, he⟩

/-- Both remaining edges carry actual ordered conjugating witnesses. -/
def TriangleEdges (P Q T : Subgroup H) : Prop :=
  (∃ g : H, P.map (MulAut.conj g).toMonoidHom = Q ∧
    Q.map (MulAut.conj g).toMonoidHom = T) ∧
  (∃ g : H, P.map (MulAut.conj g).toMonoidHom = T ∧
    Q.map (MulAut.conj g).toMonoidHom = P)

/-- The two source triangle types, with their third subgroups and all edge witnesses. -/
theorem exists_two_triangles (e : H ≃* A5) (P Q : Subgroup H)
    (hP : Nat.card P = 3) (hQ : Nat.card Q = 3)
    (eJ : ↥(P ⊔ Q) ≃* alternatingGroup (Fin 4)) :
    ∃ T₁ T₂ : Subgroup H, Nat.card T₁ = 3 ∧ Nat.card T₂ = 3 ∧
      TriangleEdges P Q T₁ ∧ TriangleEdges P Q T₂ ∧
      (P ⊔ Q) ⊔ T₁ = P ⊔ Q ∧ (P ⊔ Q) ⊔ T₂ = ⊤ ∧ T₁ ≠ T₂ := by
  obtain ⟨a, hp, hq⟩ := exists_marking e P Q hP hQ eJ
  let T₁ := (C 3).map a.symm.toMonoidHom
  let T₂ := (C 2).map a.symm.toMonoidHom
  have ht₁ : T₁.map a.toMonoidHom = C 3 := by simp [T₁, map_map]
  have ht₂ : T₂.map a.toMonoidHom = C 2 := by simp [T₂, map_map]
  have move (i : Fin 4) (U V : Subgroup H)
      (hu : U.map a.toMonoidHom = C (![1,3,1,2] i))
      (hv : V.map a.toMonoidHom = C (![3,0,2,0] i)) :
      ∃ g : H, P.map (MulAut.conj g).toMonoidHom = U ∧
        Q.map (MulAut.conj g).toMonoidHom = V := by
    refine ⟨a.symm (triangleMover i), ?_, ?_⟩
    · apply map_injective (f := a.toMonoidHom) a.injective
      rw [map_conj_equiv, a.apply_symm_apply, hp, hu, (triangleMover_maps i).1]
    · apply map_injective (f := a.toMonoidHom) a.injective
      rw [map_conj_equiv, a.apply_symm_apply, hq, hv, (triangleMover_maps i).2]
  have hs : (P ⊔ Q) ⊔ T₁ = P ⊔ Q := by
    apply map_injective (f := a.toMonoidHom) a.injective
    simp only [Subgroup.map_sup, hp, hq, ht₁, triangle_small_join]
  have hl : (P ⊔ Q) ⊔ T₂ = ⊤ := by
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [Subgroup.map_sup, Subgroup.map_sup, hp, hq, ht₂, triangle_large_join,
      map_top_of_surjective _ a.surjective]
  refine ⟨T₁, T₂, ?_, ?_, ⟨move 0 Q T₁ hq ht₁, move 1 T₁ P ht₁ hp⟩,
    ⟨move 2 Q T₂ hq ht₂, move 3 T₂ P ht₂ hp⟩, hs, hl, ?_⟩
  · rw [card_map_of_injective a.symm.injective, card_C]
  · rw [card_map_of_injective a.symm.injective, card_C]
  · intro he
    rw [← he, hs] at hl
    have hc := congrArg (fun U : Subgroup H => Nat.card (U.map a.toMonoidHom)) hl
    rw [Subgroup.map_sup, hp, hq, model_card, map_top_of_surjective _ a.surjective,
      card_top, card] at hc
    omega

end alternatingGroup.FiveLocalGeometry.CubicEdges
