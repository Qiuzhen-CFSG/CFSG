module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.LinearGeometry.Torus
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear

/-!
# The marked outer involution in the linear model

Preserving the actual Borel preserves its square-one elements, the upper root
group. Once the chosen outside involution has been put at the Weyl matrix,
the proved root-coordinate reconstruction makes every such automorphism an
entrywise field automorphism. A nontrivial binary field involution is Frobenius
for its fixed field: that field has order 2ᵐ and the full field has order 2²ᵐ.
Consequently its action on the actual two-point torus is the power 2ᵐ.

The determinant-one Hilbert–90 theorem also trivializes every cocycle for an
arbitrary outer involution. In particular a fixed involution s has a witness
g⁻¹ a(g) = s in the original group. This is the literal conjugation convention
needed for the external involutions in an ambient extension.

Source: GLS IV, Chapter 4, Lemma 3.4(a,c), and Chapter 2, Proposition 16.5,
especially the torus action and conjugacy arguments at lines 2947–2953 of
`refs/KGroup/GLS4/Chapter2.tex`. No chosen-field-automorphism premise is used.
-/

public section

open Subgroup BenderSuzuki.Converse BenderSuzuki.MatrixGroups
open BenderSuzuki.PFAppendixIII BenderSuzuki.PFchapter1section1
namespace BenderSuzuki.ZD.RankOneModelGeometry.LinearGeometry
variable {G : Type*} [Group G] [Finite G] {n : ℕ}
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

/-- Every square-one cocycle for an outer involution is an actual coboundary. -/
theorem outer_cocycle (a : MulAut (PSL2MatrixGroup K)) (ha : a ^ 2 = 1)
    (houter : ¬ ∃ b, a = MulAut.conj b)
    (s : PSL2MatrixGroup K) (hs : s * a s = 1) :
    ∃ x, x⁻¹ * a x = s := by
  obtain ⟨g, σ, hσ⟩ := Linear.semilinear_coverage a
  have ha' : (MulAut.conj g * Linear.fieldAut σ) ^ 2 = 1 := hσ ▸ ha
  obtain ⟨hσ2, hg⟩ := Linear.semilinear_involution_data σ g ha'
  have hσne : σ ≠ RingEquiv.refl K := by
    intro he
    apply houter
    exact ⟨g, by rw [hσ, he, Linear.fieldAut_refl, mul_one]⟩
  have hsg : (s * g) * Linear.fieldAut σ (s * g) = 1 := by
    have hsg' : s * (g * Linear.fieldAut σ s * g⁻¹) = 1 := by
      simpa only [hσ, MulAut.mul_apply, MulAut.conj_apply] using hs
    calc
      (s * g) * Linear.fieldAut σ (s * g) =
          (s * (g * Linear.fieldAut σ s * g⁻¹)) * (g * Linear.fieldAut σ g) := by
            simp [map_mul, mul_assoc]
      _ = 1 := by rw [hsg', hg, one_mul]
  obtain ⟨c, hc⟩ := Linear.semilinear_coboundary σ hσ2 hσne g hg
  obtain ⟨d, hd⟩ := Linear.semilinear_coboundary σ hσ2 hσne (s * g) hsg
  refine ⟨c * d⁻¹, ?_⟩
  have hs' : s = d * (Linear.fieldAut σ d)⁻¹ * g⁻¹ := by
    rw [← hd, mul_inv_cancel_right]
  rw [hσ]
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  rw [hs', hc]
  simp [map_mul, map_inv, mul_assoc]

omit [Finite G] in
/-- The source conjugacy statement supplies a conjugating element in the actual group. -/
theorem outer_fixed_involution_coboundary (e : G ≃* PSL2BinaryMatrixGroup n)
    (a : MulAut G) (ha : a ^ 2 = 1) (houter : ¬ ∃ b, a = MulAut.conj b)
    (s : G) (hs : IsInvolution s) (has : a s = s) : ∃ g : G, g⁻¹ * a g = s := by
  let b := MulAut.congr e a
  have hb : b ^ 2 = 1 := by rw [← map_pow, ha, map_one]
  have hbo : ¬ ∃ x, b = MulAut.conj x := fun h => houter ((MulAut.congr_inner_iff e a).mp h)
  have hes : e s * b (e s) = 1 := by
    change e s * e (a (e.symm (e s))) = 1
    rw [e.symm_apply_apply, has, ← map_mul]
    simpa only [pow_two, map_one] using congrArg e hs.sq_eq_one
  obtain ⟨x, hx⟩ := outer_cocycle b hb hbo (e s) hes
  refine ⟨e.symm x, e.injective ?_⟩
  change x⁻¹ * e (a (e.symm x)) = e s at hx
  simpa only [map_mul, map_inv, e.apply_symm_apply] using hx

/-- A nontrivial involution of GF(2ⁿ) is the square-root Frobenius. -/
theorem field_involution_power (hn : 0 < n)
    (σ : BinaryGaloisField n ≃+* BinaryGaloisField n)
    (hs : Function.Involutive σ) (hne : σ ≠ RingEquiv.refl _) :
    ∃ m : ℕ, 0 < m ∧ n = 2 * m ∧ ∀ x, σ x = x ^ (2 ^ m) := by
  let K := BinaryGaloisField n
  let H := Subgroup.zpowers σ
  let F := FixedPoints.subfield H K
  have ho : orderOf σ = 2 := orderOf_eq_prime (by ext x; exact hs x) hne
  have : Finite H := Finite.of_injective
    (fun g : H => (g.val : K → K)) (fun a b h => Subtype.ext (DFunLike.coe_injective h))
  let : Fintype H := Fintype.ofFinite H
  let : Fintype F := Fintype.ofFinite F
  let : Fintype K := Fintype.ofFinite K
  have hd : Module.finrank F K = 2 := by
    rw [FixedPoints.finrank_eq_card, Fintype.card_eq_nat_card, Nat.card_zpowers, ho]
  have hF : F = FixedBy.subfield K σ := by
    ext x
    change (∀ g : H, g • x = x) ↔ σ x = x
    constructor
    · intro hx
      exact hx ⟨σ, Subgroup.mem_zpowers σ⟩
    · intro hx g
      exact smul_eq_self_of_mem_zpowers g.property hx
  obtain ⟨m, hm, hnm, ⟨f⟩⟩ := Linear.binary_fixedField_model hn σ hs hne
  have hc : Fintype.card F = 2 ^ m := by
    rw [Fintype.card_eq_nat_card, hF, Nat.card_congr f.toEquiv]
    exact GaloisField.card 2 m hm.ne'
  let τ : K ≃ₐ[F] K := { σ with commutes' := fun r => r.property ⟨σ, mem_zpowers σ⟩ }
  obtain ⟨k, hk⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F K).surjective τ
  have hklt : (k : ℕ) < 2 := by simpa only [hd] using k.isLt
  have hpow : ∀ x : K, σ x = x ^ Fintype.card F := by
    intro x
    have hh := DFunLike.congr_fun hk x
    change (FiniteField.frobeniusAlgEquivOfAlgebraic F K ^ (k : ℕ)) x = σ x at hh
    interval_cases h : (k : ℕ)
    · have ht : σ = RingEquiv.refl K := by
        ext y
        have he := DFunLike.congr_fun hk y
        change (FiniteField.frobeniusAlgEquivOfAlgebraic F K ^ (k : ℕ)) y = σ y at he
        change σ y = y
        simpa only [h, pow_zero, AlgEquiv.one_apply] using he.symm
      exact (hne ht).elim
    · simpa only [h, pow_one, FiniteField.coe_frobeniusAlgEquivOfAlgebraic] using hh.symm
  exact ⟨m, hm, hnm, fun x => by rw [hpow, hc]⟩

variable {F : Type*} [Field F] [CharP F 2]

theorem unip_sq {x : SL2 F} (hx : x ∈ Unip F) : x ^ 2 = 1 := by
  obtain ⟨a, rfl⟩ := (mem_Unip_iff _).mp hx
  rw [pow_two, uni_mul_uni, CharTwo.add_self_eq_zero, uni_zero]

theorem borel_sq_mem_unip {x : SL2 F} (hx : x ∈ Borel F) (h2 : x ^ 2 = 1) :
    x ∈ Unip F := by
  have h10 := (mem_Borel_iff _).mp hx
  have h00 : x.val 0 0 = 1 := by
    have hh := congrArg (fun a : SL2 F => a.val 0 0) h2
    have hs : x.val 0 0 ^ 2 = 1 := by
      simpa [pow_two, Matrix.mul_apply, Fin.sum_univ_two, h10] using hh
    rcases sq_eq_one_iff.mp hs with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  have h11 : x.val 1 1 = 1 := by rw [Borel_lower_right hx, h00, inv_one]
  apply (mem_Unip_iff _).mpr
  refine ⟨x.val 0 1, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]


/-- The upper root group is intrinsically the square-one elements of the Borel. -/
theorem preserves_unip_of_borel (a : MulAut (SL2 F))
    (hB : (Borel F).map a.toMonoidHom = Borel F) :
    (Unip F).map a.toMonoidHom = Unip F := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    apply borel_sq_mem_unip
    · rw [← hB]
      exact Subgroup.mem_map_of_mem _ (Unip_le_Borel hx)
    · rw [← map_pow, unip_sq hx, map_one]
  · intro x hx
    have haB : a.symm x ∈ Borel F := by
      apply mem_map_equiv.mp
      rw [hB]
      exact Unip_le_Borel hx
    refine ⟨a.symm x, borel_sq_mem_unip haB ?_, a.apply_symm_apply x⟩
    rw [← map_pow, unip_sq hx, map_one]

/-- An automorphism preserving the marked Borel and Weyl element is a field action. -/
theorem field_of_borel_weyl [Finite F] (a : MulAut (SL2 F))
    (hB : (Borel F).map a.toMonoidHom = Borel F) (hw : a (weyl F) = weyl F) :
    ∃ σ : F ≃+* F, a = Linear.sl2FieldAut σ :=
  Linear.eq_sl2FieldAut_of_preserves_root_weyl a (preserves_unip_of_borel a hB) hw

omit [CharP F 2] in
/-- Entrywise field powers act by the same power on the actual diagonal torus. -/
theorem torus_field_power (σ : F ≃+* F) (k : ℕ) (hσ : ∀ x, σ x = x ^ k)
    {d : SL2 F} (hd : d ∈ Torus F) : Linear.sl2FieldAut σ d = d ^ k := by
  rw [Torus_eq_range] at hd
  obtain ⟨u, rfl⟩ := hd
  rw [← (torHom F).map_pow u k]
  change Linear.sl2FieldAut σ (tor u) = tor (u ^ k)
  have hu : σ (u : F) = (u : F) ^ k := hσ _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Linear.sl2FieldAut, hu]

/-- The source field involution acts on the marked two-point subgroup by square-root Frobenius.
No choice of a preassigned field automorphism is assumed. -/
theorem outer_marked_torus_power (hn : 0 < n) (e : G ≃* PSL2BinaryMatrixGroup n)
    (P : Sylow 2 G) {t : G} (ht : IsInvolution t)
    (htB : t ∉ normalizer ((P : Subgroup G) : Set G))
    (a : MulAut G) (ha : a ^ 2 = 1) (houter : ¬ ∃ g, a = MulAut.conj g)
    (haB : (normalizer ((P : Subgroup G) : Set G)).map a.toMonoidHom =
      normalizer ((P : Subgroup G) : Set G)) (hat : a t = t) :
    ∃ m : ℕ, 0 < m ∧ n = 2 * m ∧
      ∀ x ∈ twoPoint (normalizer ((P : Subgroup G) : Set G)) t, a x = x ^ (2 ^ m) := by
  obtain ⟨f, _, hfB, hft⟩ := exists_marked_coordinates e P ht htB
  let b := MulAut.congr f a
  have hb : b ^ 2 = 1 := by rw [← map_pow, ha, map_one]
  have hbo : ¬ ∃ g, b = MulAut.conj g := fun h => houter ((MulAut.congr_inner_iff f a).mp h)
  have hcomp : b.toMonoidHom.comp f.toMonoidHom = f.toMonoidHom.comp a.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change f (a (f.symm (f x))) = f (a x)
    rw [f.symm_apply_apply]
  have hbB : (Borel (BinaryGaloisField n)).map b.toMonoidHom = Borel (BinaryGaloisField n) := by
    rw [← hfB, Subgroup.map_map, hcomp, ← Subgroup.map_map, haB]
  have hbw : b (weyl (BinaryGaloisField n)) = weyl (BinaryGaloisField n) := by
    rw [← hft]
    change f (a (f.symm (f t))) = f t
    rw [f.symm_apply_apply, hat]
  obtain ⟨σ, hbσ⟩ := field_of_borel_weyl b hbB hbw
  have hσ2 : Function.Involutive σ := by
    intro x
    have hh := congrArg (fun c : MulAut (SL2 (BinaryGaloisField n)) =>
      (c (uni x)).val 0 1) hb
    rw [hbσ] at hh
    simp only [pow_two, MulAut.mul_apply, Linear.sl2FieldAut_uni] at hh
    exact hh

  have hσne : σ ≠ RingEquiv.refl _ := by
    intro hσ
    have hb1 : b = 1 := by
      rw [hbσ, hσ]
      ext g i j
      rfl
    exact hbo ⟨1, by simpa using hb1⟩
  obtain ⟨m, hm, hnm, hp⟩ := field_involution_power hn σ hσ2 hσne
  refine ⟨m, hm, hnm, ?_⟩
  intro x hx
  have hfx : f x ∈ Torus (BinaryGaloisField n) := by
    rw [← twoPoint_coordinates _ t f hfB hft]
    exact Subgroup.mem_map_of_mem _ hx
  have hh := torus_field_power σ (2 ^ m) hp hfx
  rw [← hbσ] at hh
  change f (a (f.symm (f x))) = (f x) ^ (2 ^ m) at hh
  apply f.injective
  simpa only [f.symm_apply_apply, map_pow] using hh

end BenderSuzuki.ZD.RankOneModelGeometry.LinearGeometry
