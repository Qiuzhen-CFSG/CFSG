module

public import Theory.SpecificGroups.PSL3Three.SylowFixers.MatrixRigidity
public import Theory.GroupAction.AutomorphismFixerCardinality.Transport

/-!
# Pointwise Sylow fixers of the actual PSL₃(3) model

The explicit matrices a and b lie in a two-subgroup by their semidihedral
relation. Together with r they generate SL₃(3), as a short word recovers the
standard transvection. The matrix rigidity calculation therefore identifies
any automorphism fixing a and b with the identity or conjugation by a⁴.

Place their two-subgroup in a Sylow subgroup and use Sylow conjugacy to bound
any pointwise Sylow fixer by two. Finally transport through the canonical
SL₃(3) ≃ PSL₃(3). The bound applies to every subgroup of automorphisms, hence
in particular to the elementary abelian image used in E.6.8.

Source: Aschbacher–Smith, E.6.8(5), printed p.248, and 1.1.5(3)(e), p.502.
-/

namespace Matrix.PSL3Three.SylowFixers
open Subgroup

private theorem generators_closure : closure ({a, b, r} : Set SL) = ⊤ := by
  apply eq_top_of_ambientGenerators_mem
  let H := closure ({a, b, r} : Set SL)
  have ha : a ∈ H := subset_closure (by simp)
  have hb : b ∈ H := subset_closure (by simp)
  have hr : r ∈ H := subset_closure (by simp)
  have h0 : ambientGenerators 0 = r := by decide
  have h1 : ambientGenerators 1 = b * a * r * a * r := by decide
  have hg0 : ambientGenerators 0 ∈ H := h0 ▸ hr
  have hg1 : ambientGenerators 1 ∈ H := h1 ▸ H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hb ha) hr) ha) hr
  intro i
  fin_cases i
  · exact hg0
  · exact hg1
  · have he : ambientGenerators 2 = (ambientGenerators 0)⁻¹ := by decide
    exact he ▸ H.inv_mem hg0
  · have he : ambientGenerators 3 = (ambientGenerators 1)⁻¹ := by decide
    exact he ▸ H.inv_mem hg1

private theorem aut_ext (α β : MulAut SL) (ha : α a = β a)
    (hb : α b = β b) (hr : α r = β r) : α = β := by
  apply MulEquiv.toMonoidHom_injective
  apply MonoidHom.eq_of_eqOn_dense generators_closure
  intro x hx
  rcases hx with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hr

private theorem quadratic_of_relations (y : SL) (hy : y ^ 3 = 1)
    (hw : (a * y ^ 2 * b) ^ 2 = 1) : y ^ 2 = d * y * d := by
  have hbi : b⁻¹ = b := by decide
  have hyi : y⁻¹ = y ^ 2 := inv_eq_of_mul_eq_one_right (by
    rw [← pow_succ', hy])
  have hi : a * y ^ 2 * b = b * y * a⁻¹ := by
    have hh : (a * y ^ 2 * b)⁻¹ = a * y ^ 2 * b :=
      inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hw)
    simpa only [mul_inv_rev, hbi, ← hyi, inv_inv, mul_assoc] using hh.symm
  have hd : a⁻¹ * b = d := by decide
  calc
    y ^ 2 = a⁻¹ * (a * y ^ 2 * b) * b⁻¹ := by group
    _ = a⁻¹ * (b * y * a⁻¹) * b := by rw [hi, hbi]
    _ = (a⁻¹ * b) * y * (a⁻¹ * b) := by group
    _ = d * y * d := by rw [hd]

private theorem aut_fixes_generators (α : MulAut SL) (ha : α a = a) (hb : α b = b) :
    α = 1 ∨ α = MulAut.conj (a ^ 4) := by
  have h1 : r ^ 3 = 1 := by decide
  have h2 : (a * r ^ 2 * b) ^ 2 = 1 := by decide
  have h3 : (a ^ 2 * r * b * r) ^ 3 = 1 := by decide
  have hy1 : (α r) ^ 3 = 1 := by rw [← map_pow, h1, map_one]
  have hy2 : (a * (α r) ^ 2 * b) ^ 2 = 1 := by
    simpa only [map_pow, map_mul, map_one, ha, hb] using congrArg α h2
  have hy3 : (a ^ 2 * α r * b * α r) ^ 3 = 1 := by
    simpa only [map_pow, map_mul, map_one, ha, hb] using congrArg α h3
  rcases matrix_rigidity (α r).val
    (congrArg Subtype.val (quadratic_of_relations (α r) hy1 hy2))
    (congrArg Subtype.val hy1) (congrArg Subtype.val hy3) with hr | hr
  · exact Or.inl (aut_ext α 1 ha hb (Subtype.ext hr))
  · apply Or.inr
    apply aut_ext
    · exact ha.trans (show a = MulAut.conj (a ^ 4) a by decide)
    · exact hb.trans (show b = MulAut.conj (a ^ 4) b by decide)
    · exact (Subtype.ext hr).trans (show r' = MulAut.conj (a ^ 4) r by decide)

private theorem exists_sylow_generators : ∃ S : Sylow 2 SL, a ∈ S ∧ b ∈ S := by
  have ha : a ^ 8 = 1 := by decide
  have hb : b ^ 2 = 1 := by decide
  have hconj : b * a * b⁻¹ = a ^ 3 := by decide
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hb)
  have hforward : ∀ x ∈ zpowers a, b * x * b⁻¹ ∈ zpowers a := by
    have hm : (zpowers a).map (MulAut.conj b).toMonoidHom ≤ zpowers a := by
      rw [MonoidHom.map_zpowers]
      apply zpowers_le.mpr
      change b * a * b⁻¹ ∈ zpowers a
      rw [hconj]
      exact (zpowers a).pow_mem (mem_zpowers a) _
    exact fun x hx => hm (mem_map_of_mem _ hx)
  have hn : b ∈ normalizer (zpowers a : Set SL) := by
    apply mem_normalizer_iff.mpr
    intro x
    refine ⟨hforward x, fun hx => ?_⟩
    have hh := hforward _ hx
    have he : b * (b * x * b⁻¹) * b⁻¹ = x := by
      rw [hbi]
      calc
        b * (b * x * b) * b = (b * b) * x * (b * b) := by group
        _ = x := by rw [← pow_two, hb]; simp
    rwa [he] at hh
  have hA : IsPGroup 2 (zpowers a) := IsPGroup.of_card_dvd_pow (n := 3) (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one ha)
  have hB : IsPGroup 2 (zpowers b) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hb)
  obtain ⟨S, hS⟩ := (hA.to_sup_of_normal_left' hB (zpowers_le.mpr hn)).exists_le_sylow
  exact ⟨S, hS ((show zpowers a ≤ zpowers a ⊔ zpowers b from le_sup_left) (mem_zpowers a)), hS ((show zpowers b ≤ zpowers a ⊔ zpowers b from le_sup_right) (mem_zpowers b))⟩

private theorem fixed_generators_card_le_two (A : Subgroup (MulAut SL))
    (hA : ∀ α ∈ A, α a = a ∧ α b = b) : Nat.card A ≤ 2 := by
  classical
  let f : A → Bool := fun α => decide (α = 1)
  have hf : Function.Injective f := by
    intro α β he
    by_cases ha : α = 1
    · have hb : β = 1 := by simpa [f, ha] using he.symm
      exact ha.trans hb.symm
    by_cases hb : β = 1
    · have ha' : α = 1 := by simpa [f, hb] using he
      exact (ha ha').elim
    apply Subtype.ext
    have hα := aut_fixes_generators α (hA α α.property).1 (hA α α.property).2
    have hβ := aut_fixes_generators β (hA β β.property).1 (hA β β.property).2
    exact (hα.resolve_left (fun h => ha (Subtype.ext h))).trans
      (hβ.resolve_left (fun h => hb (Subtype.ext h))).symm
  exact (Nat.card_le_card_of_injective f hf).trans (by simp)

/-- Every automorphism subgroup fixing a Sylow two-subgroup of SL₃(3) has order at most two. -/
public theorem sylow_fixer_card_le_two_SL (P : Sylow 2 SL)
    (A : Subgroup (MulAut SL)) (hfix : ∀ α ∈ A, ∀ x ∈ P, α x = x) :
    Nat.card A ≤ 2 := by
  obtain ⟨S, ha, hb⟩ := exists_sylow_generators
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL P S
  let e := MulAut.conj g
  have he : (P : Subgroup SL).map e.toMonoidHom = (S : Subgroup SL) := by
    have hh := congrArg (fun Q : Sylow 2 SL => (Q : Subgroup SL)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hh
    exact hh
  exact Theory.GroupAction.automorphism_fixer_card_le_of_equiv e (P : Subgroup SL)
    (S : Subgroup SL) he 2
    (fun B hf => fixed_generators_card_le_two B (fun α hα => ⟨hf α hα a ha, hf α hα b hb⟩))
    A hfix

/-- Every automorphism subgroup fixing a Sylow two-subgroup of PSL₃(3) has order at most two. -/
public theorem sylow_fixer_card_le_two (P : Sylow 2 PSL)
    (A : Subgroup (MulAut PSL)) (hfix : ∀ α ∈ A, ∀ x ∈ P, α x = x) :
    Nat.card A ≤ 2 := by
  let e := equiv.symm
  let S := P.mapSurjective (f := e.toMonoidHom) e.surjective
  exact Theory.GroupAction.automorphism_fixer_card_le_of_equiv e (P : Subgroup PSL)
    (S : Subgroup SL) rfl 2 (sylow_fixer_card_le_two_SL S) A hfix

end Matrix.PSL3Three.SylowFixers
