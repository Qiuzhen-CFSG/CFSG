module

public import Theory.SpecificGroups.PSL3.CartanActions.ThreeAlignment
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The actual split Borel quotients in degree three

Upper triangular determinant-one matrices factor into a unitriangular matrix
and `diag(a,(ab)⁻¹,b)`. This gives the SL₃ torus quotient. In PSL₃, the
parameter kernel consists precisely of `(a,a)` with `a³=1`; it is retained
in the quotient equivalence. In binary characteristic the unitriangular
subgroup is the two-core, since it is normal and the torus has odd order.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954. The factorization
extends the calculation in `CartanActions.ThreeAlignment` to a public quotient
interface. Automorphism coverage and residual centralizers are separate results.
-/

@[expose] public section

open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3.LinearThree
namespace Matrix.PSL3.CartanActions.BorelQuotient
variable (F : Type*) [Field F]

/-- The only scalar ambiguity in the two diagonal parameters. -/
def cubicScalars : Subgroup (Fˣ × Fˣ) where
  carrier := {d | d.1 = d.2 ∧ d.1 ^ 3 = 1}
  one_mem' := by simp
  mul_mem' := by
    rintro a b ⟨ha, ha3⟩ ⟨hb, hb3⟩
    exact ⟨congrArg₂ (· * ·) ha hb, by simp only [Prod.fst_mul, mul_pow, ha3, hb3, one_mul]⟩
  inv_mem' := by
    rintro a ⟨ha, ha3⟩
    exact ⟨congrArg Inv.inv ha, by simp only [Prod.fst_inv, inv_pow, ha3, inv_one]⟩

/-- The special linear diagonal parametrization is faithful. -/
theorem torusSL_injective : Function.Injective (torusSL F) := by
  intro d e h
  exact Prod.ext
    (Units.ext (congrArg (fun g : SL(3,F) => g.val 0 0) h))
    (Units.ext (congrArg (fun g : SL(3,F) => g.val 2 2) h))

noncomputable def torusSLEquiv : (Fˣ × Fˣ) ≃* (torusSL F).range :=
  MonoidHom.ofInjective (torusSL_injective F)

/-- Projectivizing kills exactly the cubic diagonal scalars. -/
theorem torusMap_eq_one_iff (d : Fˣ × Fˣ) :
    torusMap F d = 1 ↔ d.1 = d.2 ∧ d.1 ^ 3 = 1 := by
  change projection F (torusSL F d) = 1 ↔ _
  rw [← MonoidHom.mem_ker, projection_ker, SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, he⟩
    have h0 := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 0 0) he
    have h2 := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 2 2) he
    simp only [torusSL_val, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_two] at h0 h2
    refine ⟨Units.ext (h0.symm.trans h2), Units.ext ?_⟩
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, ← h0, Fintype.card_fin] using hr
  · rintro ⟨hab, ha⟩
    have hi : (d.1 * d.1)⁻¹ = d.1 :=
      inv_eq_of_mul_eq_one_left (by simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using ha)
    refine ⟨(d.1 : F), ?_, ?_⟩
    · simpa using congrArg Units.val ha
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [torusSL_val, ← hab, hi]

theorem torusMap_ker : (torusMap F).ker = cubicScalars F := by
  ext d
  exact torusMap_eq_one_iff F d

/-- The quotient by cube roots is essential, including over F₄ and F₆₄. -/
noncomputable def torusEquiv : ((Fˣ × Fˣ) ⧸ cubicScalars F) ≃* torus F :=
  (QuotientGroup.quotientMulEquivOfEq (torusMap_ker F).symm).trans
    (QuotientGroup.quotientKerEquivRange (torusMap F))

@[simp] theorem torusEquiv_mk (d : Fˣ × Fˣ) :
    (torusEquiv F (QuotientGroup.mk d) : PSL(3,F)) = torusMap F d := rfl

/-- Identify the parameter kernel with the actual group of cube roots. -/
def cubicScalarsEquiv : cubicScalars F ≃* (powMonoidHom 3 : Fˣ →* Fˣ).ker where
  toFun d := ⟨d.val.1, d.property.2⟩
  invFun a := ⟨(a.val, a.val), rfl, a.property⟩
  left_inv d := Subtype.ext (Prod.ext rfl d.property.1)
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable [Finite F]

theorem card_cubicScalars : Nat.card (cubicScalars F) = Nat.gcd 3 (Nat.card F - 1) := by
  rw [Nat.card_congr (cubicScalarsEquiv F).toEquiv,
    IsCyclic.card_powMonoidHom_ker, Nat.card_units, Nat.gcd_comm]

theorem card_torus_mul_scalar :
    Nat.card (torus F) * Nat.gcd 3 (Nat.card F - 1) = (Nat.card F - 1) ^ 2 := by
  rw [← card_cubicScalars F, ← torusMap_ker F, torus, ← index_ker, mul_comm,
    Subgroup.card_mul_index, Nat.card_prod, Nat.card_units, pow_two]

theorem torusSL_mem_borel (d : Fˣ × Fˣ) : torusSL F d ∈ borelSL F := by
  rw [mem_borelSL_iff, torusSL_val]
  simp

theorem torusSL_le_borel : (torusSL F).range ≤ borelSL F := by
  rintro _ ⟨d, rfl⟩
  exact torusSL_mem_borel F d

/-- A literal factorization, with no cardinality or quotient assumption. -/
theorem borelSL_factorization (g : SL(3,F)) (hg : g ∈ borelSL F) :
    ∃ d : Fˣ × Fˣ, ∃ u ∈ unipotentSL F, g = u * torusSL F d := by
  obtain ⟨h10,h20,h21⟩ := (mem_borelSL_iff F g).mp hg
  have hd : g.val 0 0 * g.val 1 1 * g.val 2 2 = 1 := by
    have h := g.property
    rw [Matrix.det_fin_three, h10,h20,h21] at h
    simpa only [zero_mul, mul_zero, add_zero, sub_zero] using h
  have h00 : g.val 0 0 ≠ 0 := by intro h; simp [h] at hd
  have h22 : g.val 2 2 ≠ 0 := by intro h; simp [h] at hd
  let d : Fˣ × Fˣ := (Units.mk0 _ h00, Units.mk0 _ h22)
  refine ⟨d, g * torusSL F d⁻¹, ?_, ?_⟩
  · rw [unipotentSL, mem_inf, mem_pointLocalSL_iff, mem_lineLocalSL_iff]
    simp [torusSL_val, Matrix.mul_diagonal, d, h00,h22,h10,h20,h21]
  · simp only [map_inv, mul_assoc, inv_mul_cancel, mul_one]

/-- The factorization descends through the actual projective map. -/
theorem borel_factorization (g : PSL(3,F)) (hg : g ∈ borel F) :
    ∃ d : Fˣ × Fˣ, ∃ u ∈ unipotent F, g = u * torusMap F d := by
  obtain ⟨x,hx,rfl⟩ := hg
  obtain ⟨d,u,hu,rfl⟩ := borelSL_factorization F x hx
  exact ⟨d,projection F u,mem_map_of_mem _ hu,map_mul _ _ _⟩

instance unipotentSL_normal : ((unipotentSL F).subgroupOf (borelSL F)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (unipotentSL_le_borelSL F)).mpr
    (borelSL_le_normalizer_unipotentSL F)

instance unipotent_normal : ((unipotent F).subgroupOf (borel F)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (unipotent_le_borel F)).mpr
    (borel_le_normalizer_unipotent F)

/-- The unitriangular subgroup and diagonal torus complement one another. -/
theorem borelSL_complement :
    ((unipotentSL F).subgroupOf (borelSL F)).IsComplement'
      ((torusSL F).range.subgroupOf (borelSL F)) := by
  refine ⟨Subgroup.mul_injective_of_disjoint ?_, ?_⟩
  · rw [Subgroup.disjoint_def]
    rintro x hx ⟨d,hd⟩
    change torusSL F d = x.val at hd
    have h00 := ((mem_pointLocalSL_iff F _).mp hx.1).1
    have h22 := ((mem_lineLocalSL_iff F _).mp hx.2).2.2
    change x.val.val 0 0 = 1 at h00
    change x.val.val 2 2 = 1 at h22
    rw [← hd] at h00 h22
    have he : d = 1 := Prod.ext (Units.ext h00) (Units.ext h22)
    apply Subtype.ext
    rw [← hd, he, map_one]
    rfl
  · intro g
    obtain ⟨d,u,hu,hg⟩ := borelSL_factorization F g.val g.property
    exact ⟨(⟨⟨u,unipotentSL_le_borelSL F hu⟩,hu⟩,
      ⟨⟨torusSL F d,torusSL_mem_borel F d⟩,⟨d,rfl⟩⟩), Subtype.ext hg.symm⟩

theorem units_odd {n : ℕ} (hF : Nat.card F = 2 ^ n) : Odd (Nat.card Fˣ) := by
  have hn : n ≠ 0 := by
    intro h
    have := Finite.one_lt_card (α := F)
    simp [hF, h] at this
  rw [Nat.card_units, hF, Nat.odd_iff]
  have hp : 0 < (2:ℕ)^n := pow_pos (by decide) _
  have hd := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 hn)
  omega

/-- In the projective group, odd torus order also proves disjointness from U. -/
theorem borel_complement {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    ((unipotent F).subgroupOf (borel F)).IsComplement'
      ((torus F).subgroupOf (borel F)) := by
  have ht : Odd (Nat.card (torus F)) := by
    apply Odd.of_dvd_nat _ (Subgroup.card_range_dvd (torusMap F))
    rw [Nat.card_prod]
    exact (units_odd F hF).mul (units_odd F hF)
  have hc : Nat.Coprime (Nat.card (unipotent F)) (Nat.card (torus F)) := by
    rw [card_unipotent, hF, ← pow_mul]
    exact ht.coprime_two_left.pow_left _
  refine ⟨Subgroup.mul_injective_of_disjoint ?_, ?_⟩
  · apply Subgroup.disjoint_of_coprime_natCard
    rwa [Nat.card_congr (subgroupOfEquivOfLe (unipotent_le_borel F)).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe (torus_le_borel F)).toEquiv]
  · intro g
    obtain ⟨d,u,hu,hg⟩ := borel_factorization F g.val g.property
    exact ⟨(⟨⟨u,unipotent_le_borel F hu⟩,hu⟩,
      ⟨⟨torusMap F d,torus_le_borel F ⟨d,rfl⟩⟩,⟨d,rfl⟩⟩), Subtype.ext hg.symm⟩

/-- The special linear Borel two-core is the actual upper unipotent subgroup. -/
theorem twoCoreSL_eq {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    pCore 2 (borelSL F) = (unipotentSL F).subgroupOf (borelSL F) := by
  have hu : IsPGroup 2 ((unipotentSL F).subgroupOf (borelSL F)) := by
    apply IsPGroup.of_card (n := n * 3)
    rw [Nat.card_congr (subgroupOfEquivOfLe (unipotentSL_le_borelSL F)).toEquiv,
      card_unipotentSL, hF, pow_mul]
  have hi : ¬ 2 ∣ ((unipotentSL F).subgroupOf (borelSL F)).index := by
    rw [(borelSL_complement F).symm.index_eq_card,
      Nat.card_congr (subgroupOfEquivOfLe (torusSL_le_borel F)).toEquiv,
      ← Nat.card_congr (torusSLEquiv F).toEquiv, Nat.card_prod]
    exact ((units_odd F hF).mul (units_odd F hF)).not_two_dvd_nat
  exact le_antisymm (pCore_isPGroup.le_sylow_of_normal (hu.toSylow hi))
    (le_sSup ⟨inferInstance, hu⟩)

/-- The projective two-core keeps the literal embedding of U. -/
theorem twoCore_eq {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    pCore 2 (borel F) = (unipotent F).subgroupOf (borel F) := by
  have hu : IsPGroup 2 ((unipotent F).subgroupOf (borel F)) := by
    apply IsPGroup.of_card (n := n * 3)
    rw [Nat.card_congr (subgroupOfEquivOfLe (unipotent_le_borel F)).toEquiv,
      card_unipotent, hF, pow_mul]
  have hi : ¬ 2 ∣ ((unipotent F).subgroupOf (borel F)).index := by
    rw [(borel_complement F hF).symm.index_eq_card,
      Nat.card_congr (subgroupOfEquivOfLe (torus_le_borel F)).toEquiv]
    have ht : Odd (Nat.card (torus F)) := by
      apply Odd.of_dvd_nat _ (Subgroup.card_range_dvd (torusMap F))
      rw [Nat.card_prod]
      exact (units_odd F hF).mul (units_odd F hF)
    exact ht.not_two_dvd_nat
  exact le_antisymm (pCore_isPGroup.le_sylow_of_normal (hu.toSylow hi))
    (le_sSup ⟨inferInstance, hu⟩)

/-- The SL₃ quotient is the full two-parameter diagonal torus. -/
noncomputable def quotientSLTorusEquiv {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    borelSL F ⧸ pCore 2 (borelSL F) ≃* (Fˣ × Fˣ) :=
  (QuotientGroup.quotientMulEquivOfEq (twoCoreSL_eq F hF)).trans
    ((borelSL_complement F).symm.QuotientMulEquiv.trans
      ((subgroupOfEquivOfLe (torusSL_le_borel F)).trans (torusSLEquiv F).symm))

/-- The PSL₃ quotient is the two-parameter torus modulo its cubic scalars. -/
noncomputable def quotientTorusEquiv {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    borel F ⧸ pCore 2 (borel F) ≃* ((Fˣ × Fˣ) ⧸ cubicScalars F) :=
  (QuotientGroup.quotientMulEquivOfEq (twoCore_eq F hF)).trans
    ((borel_complement F hF).symm.QuotientMulEquiv.trans
      ((subgroupOfEquivOfLe (torus_le_borel F)).trans (torusEquiv F).symm))

end Matrix.PSL3.CartanActions.BorelQuotient

namespace Matrix.PSL3.CartanActions.BorelQuotient
variable (F : Type*) [Field F] [Finite F]

/-- Passing from PSL₃ back to SL₃ multiplies the unipotent index by the
actual scalar kernel, which has odd order. -/
theorem index_unipotentSL : (unipotentSL F).index =
    Nat.gcd 3 (Nat.card F - 1) * (unipotent F).index := by
  have hcard : Nat.card SL(3,F) =
      Nat.gcd 3 (Nat.card F - 1) * Nat.card PSL(3,F) := by
    rw [← (projection F).ker.card_mul_index, card_projectionKernel, index_ker,
      MonoidHom.range_eq_top.mpr (projection_surjective F), card_top]
  apply Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card F ^ 3 from pow_pos Nat.card_pos _)
  calc
    _ = Nat.card SL(3,F) := by
      rw [← card_unipotentSL F]
      exact (unipotentSL F).card_mul_index
    _ = Nat.gcd 3 (Nat.card F - 1) * (Nat.card F ^ 3 * (unipotent F).index) := by
      rw [hcard, ← (unipotent F).card_mul_index, card_unipotent]
    _ = _ := by ring

/-- The literal upper unitriangular subgroup is Sylow also in SL₃. -/
noncomputable def unipotentSLSylow {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n) :
    Sylow 2 SL(3,F) := by
  have hu : IsPGroup 2 (unipotentSL F) := by
    apply IsPGroup.of_card (n := n * 3)
    rw [card_unipotentSL, hF, pow_mul]
  apply hu.toSylow
  rw [index_unipotentSL]
  exact Nat.prime_two.not_dvd_mul
    ((Odd.of_dvd_nat (by decide : Odd 3) (Nat.gcd_dvd_left 3 (Nat.card F - 1))).not_two_dvd_nat)
    (odd_index_unipotent F hn hF)

@[simp] theorem coe_unipotentSLSylow {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n) :
    (unipotentSLSylow F hn hF : Subgroup SL(3,F)) = unipotentSL F := rfl

/-- Simultaneously align the specified SL₃ Sylow and its full normalizer. -/
theorem sylowSL_normalizer_conjugate {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (S : Sylow 2 SL(3,F)) : ∃ g : SL(3,F),
      (unipotentSL F).map (MulAut.conj g).toMonoidHom = (S : Subgroup SL(3,F)) ∧
      (borelSL F).map (MulAut.conj g).toMonoidHom = normalizer (S : Set SL(3,F)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(3,F) (unipotentSLSylow F hn hF) S
  have he : (unipotentSL F).map (MulAut.conj g).toMonoidHom = (S : Subgroup SL(3,F)) :=
    congrArg Sylow.toSubgroup hg
  refine ⟨g,he,?_⟩
  rw [← normalizer_unipotentSL, map_equiv_normalizer_eq, he]
  rfl

/-- Simultaneously align the specified PSL₃ Sylow and its full normalizer. -/
theorem sylow_normalizer_conjugate {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (S : Sylow 2 PSL(3,F)) : ∃ g : PSL(3,F),
      (unipotent F).map (MulAut.conj g).toMonoidHom = (S : Subgroup PSL(3,F)) ∧
      (borel F).map (MulAut.conj g).toMonoidHom = normalizer (S : Set PSL(3,F)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) (unipotentSylow F hn hF) S
  have he : (unipotent F).map (MulAut.conj g).toMonoidHom = (S : Subgroup PSL(3,F)) :=
    congrArg Sylow.toSubgroup hg
  refine ⟨g,he,?_⟩
  rw [← normalizer_unipotent F hn hF, map_equiv_normalizer_eq, he]
  rfl

noncomputable def sylowSLNormalizerEquiv {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (S : Sylow 2 SL(3,F)) : normalizer (S : Set SL(3,F)) ≃* borelSL F := by
  classical
  let g := Classical.choose (sylowSL_normalizer_conjugate F hn hF S)
  have hg := (Classical.choose_spec (sylowSL_normalizer_conjugate F hn hF S)).2
  exact ((equivMapOfInjective (borelSL F) (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hg)).symm

noncomputable def sylowNormalizerEquiv {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (S : Sylow 2 PSL(3,F)) : normalizer (S : Set PSL(3,F)) ≃* borel F := by
  classical
  let g := Classical.choose (sylow_normalizer_conjugate F hn hF S)
  have hg := (Classical.choose_spec (sylow_normalizer_conjugate F hn hF S)).2
  exact ((equivMapOfInjective (borel F) (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hg)).symm

/-- The SL₃ normalizer at any specified Sylow has the full two-parameter quotient. -/
noncomputable def sylowSLNormalizerQuotientEquiv {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) (S : Sylow 2 SL(3,F)) :
    normalizer (S : Set SL(3,F)) ⧸ pCore 2 (normalizer (S : Set SL(3,F))) ≃* (Fˣ × Fˣ) :=
  (QuotientGroup.congr _ _ (sylowSLNormalizerEquiv F hn hF S)
    (pCore_map_iso 2 (sylowSLNormalizerEquiv F hn hF S))).trans (quotientSLTorusEquiv F hF)

/-- The PSL₃ normalizer quotient retains its cubic scalar kernel. -/
noncomputable def sylowNormalizerQuotientEquiv {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) (S : Sylow 2 PSL(3,F)) :
    normalizer (S : Set PSL(3,F)) ⧸ pCore 2 (normalizer (S : Set PSL(3,F))) ≃*
      ((Fˣ × Fˣ) ⧸ cubicScalars F) :=
  (QuotientGroup.congr _ _ (sylowNormalizerEquiv F hn hF S)
    (pCore_map_iso 2 (sylowNormalizerEquiv F hn hF S))).trans (quotientTorusEquiv F hF)

end Matrix.PSL3.CartanActions.BorelQuotient

namespace Matrix.PSL3.CartanActions.BorelQuotient
variable (F : Type*) [Field F] [Finite F]

/-- The inverse equivalence is represented by the literal diagonal matrix. -/
@[simp] theorem quotientSLTorusEquiv_symm_apply {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (d : Fˣ × Fˣ) :
    (quotientSLTorusEquiv F hF).symm d =
      QuotientGroup.mk (⟨torusSL F d,torusSL_mem_borel F d⟩ : borelSL F) := by
  rfl

/-- The inverse projective equivalence uses the actual torus image. -/
@[simp] theorem quotientTorusEquiv_symm_mk {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (d : Fˣ × Fˣ) :
    (quotientTorusEquiv F hF).symm (QuotientGroup.mk d) =
      QuotientGroup.mk (⟨torusMap F d,torus_le_borel F ⟨d,rfl⟩⟩ : borel F) := by
  rfl

theorem quotientSLTorusEquiv_mk_torus {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (d : Fˣ × Fˣ) :
    quotientSLTorusEquiv F hF
      (QuotientGroup.mk (⟨torusSL F d,torusSL_mem_borel F d⟩ : borelSL F)) = d := by
  rw [← quotientSLTorusEquiv_symm_apply F hF d, MulEquiv.apply_symm_apply]

theorem quotientTorusEquiv_mk_torus {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (d : Fˣ × Fˣ) :
    quotientTorusEquiv F hF
      (QuotientGroup.mk (⟨torusMap F d,torus_le_borel F ⟨d,rfl⟩⟩ : borel F)) =
        QuotientGroup.mk d := by
  rw [← quotientTorusEquiv_symm_mk F hF d, MulEquiv.apply_symm_apply]

theorem card_quotientSL {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Nat.card (borelSL F ⧸ pCore 2 (borelSL F)) = (2 ^ n - 1) ^ 2 := by
  rw [Nat.card_congr (quotientSLTorusEquiv F hF).toEquiv, Nat.card_prod,
    Nat.card_units, hF, pow_two]

theorem card_quotient_mul_scalar {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Nat.card (borel F ⧸ pCore 2 (borel F)) * Nat.gcd 3 (2 ^ n - 1) = (2 ^ n - 1) ^ 2 := by
  rw [Nat.card_congr ((quotientTorusEquiv F hF).trans (torusEquiv F)).toEquiv,
    ← hF, card_torus_mul_scalar]

end Matrix.PSL3.CartanActions.BorelQuotient
