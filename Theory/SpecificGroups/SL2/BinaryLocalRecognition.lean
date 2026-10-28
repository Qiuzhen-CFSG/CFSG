module

public import Theory.SpecificGroups.SL2.TwoConjugateWitness.Recognition
public import Theory.SpecificGroups.SL2.TwoSubgroupExponent
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# Binary rank-one subgroups containing noncommuting involutions

A subgroup of SL₂ over a finite field of characteristic two that contains
noncommuting involutions has trivial intrinsic two-core. It is either an
odd dihedral group or SL₂ over a binary subfield degree greater than one.
The subgroup and its marked elements remain the original ones throughout.

A nontrivial two-core would contain both involutions; every two-subgroup of
binary SL₂ is abelian. For a Sylow subgroup of order at least four, the
existing Dickson recognition applies. A Sylow subgroup of order two has its
normalizer in an involution centralizer, which is a two-group. It is therefore
self-normalizing, and Huppert II.8.23 gives the odd dihedral alternative.

Source: Aschbacher--Smith, G.4.9(a), printed p.341, citing Dickson's theorem.
The field with two elements is included and falls in the dihedral alternative.
-/

public section

open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A noncommuting involution pair forces the actual subgroup's two-core to vanish. -/
theorem binary_subgroup_twoCore_eq_bot_of_noncommuting_involutions (H : Subgroup SL(2,F)) (a b : H)
    (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : ¬ Commute a b) : pCore 2 H = ⊥ := by
  by_contra hn
  have hmem (x : H) (hx : orderOf x = 2) : x ∈ pCore 2 H := by
    apply isPGroup_le_twoCore_of_ne_bot H hn (zpowers x) _ (mem_zpowers x)
    apply IsPGroup.of_card_dvd_pow (n := 1)
    simp only [Nat.card_zpowers, hx, pow_one, dvd_refl]
  let K := (pCore 2 H).map H.subtype
  have hK : IsPGroup 2 K := (pCore_isPGroup (p := 2) (G := H)).map H.subtype
  have hpow (x : pCore 2 H) : x ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : K => (z : SL(2,F))) (twoSubgroup_pow_two K hK
      ⟨x.val.val, mem_map_of_mem H.subtype x.property⟩)
  have hc := Commute.of_orderOf_dvd_two
    (fun x : pCore 2 H => orderOf_dvd_of_pow_eq_one (hpow x))
    ⟨a, hmem a ha⟩ ⟨b, hmem b hb⟩
  exact hab (hc.map (pCore 2 H).subtype)

private theorem psl_small_sylow_normalizer (H : Subgroup PSL(2,F))
    (P : Sylow 2 H) (hP : Nat.card P = 2) :
    normalizer (P : Set H) = (P : Subgroup H) := by
  obtain ⟨x, hx, _⟩ := (Nat.card_eq_two_iff' (1 : P)).mp hP
  have hox : orderOf x = 2 := by
    have hd := orderOf_dvd_natCard x
    change orderOf x ∣ Nat.card (P : Subgroup H) at hd
    rw [hP] at hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
    · exact (hx (orderOf_eq_one_iff.mp he)).elim
    · exact he
  have hoxH : orderOf (x : H) = 2 :=
    (orderOf_injective (P : Subgroup H).subtype Subtype.coe_injective x).trans hox
  have hoxF : orderOf ((x : H) : PSL(2,F)) = 2 :=
    (orderOf_injective H.subtype Subtype.coe_injective (x : H)).trans hoxH
  obtain ⟨_, _, _, _, _, hC⟩ := Theory.PSL2.involution_root_geometry
    ((x : H) : PSL(2,F)) hoxF
  have hN : IsPGroup 2 (normalizer (P : Set H)) := by
    apply (hC.comap_of_injective H.subtype Subtype.coe_injective).to_le
    intro g hg
    apply mem_centralizer_singleton_iff.mpr
    have hc := normalizer_le_centralizer_of_card_two (P : Subgroup H) hP hg
    exact congrArg Subtype.val (hc (x : H) x.property).symm
  exact P.is_maximal' hN (P : Subgroup H).le_normalizer

/-- Dickson recognition for the actual binary SL₂ subgroup containing the marked pair. -/
theorem binary_subgroup_recognition_of_noncommuting_involutions {n : ℕ} (hF : Nat.card F = 2^n)
    (H : Subgroup SL(2,F)) (a b : H)
    (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : ¬ Commute a b) :
    (∃ m : ℕ, Odd m ∧ 1 < m ∧ Nonempty (H ≃* DihedralGroup m)) ∨
    (∃ k : ℕ, 1 < k ∧ k ∣ n ∧ Nonempty (H ≃* SL(2,GaloisField 2 k))) := by
  classical
  have hc := binary_subgroup_twoCore_eq_bot_of_noncommuting_involutions H a b ha hb hab
  let P : Sylow 2 H := default
  by_cases hP : 4 ≤ Nat.card (P : Subgroup H)
  · exact Or.inr (TwoConjugateWitness.sl_subgroup_recognition hF H hc P hP)
  have hPc : Nat.card (P : Subgroup H) = 2 := by
    have h2H : 2 ∣ Nat.card H := by simpa only [ha] using orderOf_dvd_natCard a
    have h2P := P.dvd_card_of_dvd_card h2H
    have hpos := Nat.card_pos (α := (P : Subgroup H))
    obtain ⟨j, hj⟩ := h2P
    omega
  let f := TwoConjugateWitness.slEquivPSL F
  let I := H.map f.toMonoidHom
  let e : H ≃* I := H.equivMapOfInjective f.toMonoidHom f.injective
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQc : Nat.card (Q : Subgroup I) = 2 := by
    have he := Nat.card_congr (Subgroup.equivMapOfInjective
      (P : Subgroup H) e.toMonoidHom e.injective).toEquiv
    exact he.symm.trans hPc
  have hnoncomm : ¬ Commute (e a) (e b) := by
    intro h
    apply hab
    apply e.injective
    simpa only [map_mul] using h.eq
  rcases Glauberman.Dickson.huppert_II_8_23_dickson_case_p_part_normalizer_self
      hF I Q (m := 1) hQc (by decide) (psl_small_sylow_normalizer I Q hQc) with h | h | h
  · let := h.2
    exact (hnoncomm (by exact mul_comm' (e a) (e b))).elim
  · obtain ⟨_, m, hm, _, hcard, ⟨d⟩⟩ := h
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hm (dvd_zero 2)
    have hm1 : m ≠ 1 := by
      intro he
      have hI2 : Nat.card I = 2 := by simpa [he] using hcard
      let := isCyclic_of_prime_card hI2
      exact hnoncomm (by exact mul_comm' (e a) (e b))
    exact Or.inl ⟨m, Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hm),
      by omega, ⟨e.trans d⟩⟩
  · norm_num at h

end Matrix.SpecialLinearGroup
