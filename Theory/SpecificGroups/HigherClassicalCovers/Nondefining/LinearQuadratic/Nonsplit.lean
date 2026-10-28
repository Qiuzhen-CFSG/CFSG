module

public import Theory.SpecificGroups.GL2.FiniteQuadraticTorus
public import Theory.GroupTheory.CentralExtensionSwap
public import Theory.GroupTheory.PerfectCentralCoverAbelianSylow
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support


/-!
# Nonsplit quadratic-torus primes in PSL₄ covering kernels

Let |F| = p and let r be an odd prime dividing p+1. A Sylow r-subgroup U
of the units of the actual quadratic extension is cyclic. Its regular
representation has determinant one, since r does not divide p−1. Two copies
of this representation give a determinant-one block torus in SL₄. Its map
into the literal quotient by the center is injective: a scalar in the kernel
has fourth power one, whereas U has odd order.

The order formula shows that this rank-two torus is Sylow, including r=3.
Indeed, writing |U|m = p²−1, its index times the scalar-center factor is
m²p⁶(p²+1)(p³−1), all of whose factors are prime to r. The determinant-one
permutation exchanging the two blocks swaps the two cyclic generators.
The swapping-lifts lemma makes the full torus preimage abelian in every
central extension. Central Sylow transfer then excludes r from the kernel
of any finite perfect central cover.

This proves the nonsplit-prime part of the degree-four linear covering
calculation used in Aschbacher–Smith, *The Classification of Quasithin
Groups*, A.2.17, printed p.39. Covering and transfer conventions are those
of I.1.1–I.1.2, printed p.407. The order formula is the attributed ATLAS
port in `Theory.AtlasPort.ExceptionalIsomorphisms.Support`.
-/

open Matrix Subgroup
open scoped MatrixGroups IsMulCommutative
noncomputable section
namespace Theory.SpecificGroups.HigherClassicalCovers.Nondefining.Nonsplit

variable {F : Type*} [Field F]

def blocks (A B : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  !![A 0 0,A 0 1,0,0; A 1 0,A 1 1,0,0;
     0,0,B 0 0,B 0 1; 0,0,B 1 0,B 1 1]

private theorem det_blocks (A B : Matrix (Fin 2) (Fin 2) F) :
    (blocks A B).det = A.det * B.det := by
  simp [blocks, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix, Fin.succAbove]
  ring

def blocksHom : (SL(2,F) × SL(2,F)) →* SL(4,F) where
  toFun a := ⟨blocks a.1.val a.2.val, by rw [det_blocks, a.1.property, a.2.property, mul_one]⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blocks]
  map_mul' a b := by
    apply Subtype.ext
    change blocks (a.1.val * b.1.val) (a.2.val * b.2.val) =
      blocks a.1.val a.2.val * blocks b.1.val b.2.val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blocks, Matrix.mul_apply, Fin.sum_univ_succ]

theorem blocksHom_injective : Function.Injective (blocksHom (F := F)) := by
  intro a b h
  apply Prod.ext
  · apply Subtype.ext
    ext i j
    have he := congrArg (fun A : SL(4,F) => A.val (i.castAdd 2) (j.castAdd 2)) h
    change blocks a.1.val a.2.val _ _ = blocks b.1.val b.2.val _ _ at he
    fin_cases i <;> fin_cases j <;> simpa [blocks] using he
  · apply Subtype.ext
    ext i j
    have he := congrArg (fun A : SL(4,F) => A.val (i.natAdd 2) (j.natAdd 2)) h
    change blocks a.1.val a.2.val _ _ = blocks b.1.val b.2.val _ _ at he
    fin_cases i <;> fin_cases j <;> simpa [blocks] using he

def swapSL : SL(4,F) :=
  ⟨!![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0], by
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
      Matrix.submatrix, Fin.succAbove]⟩

theorem swap_blocks (a b : SL(2,F)) :
    swapSL * blocksHom (a,b) * swapSL⁻¹ = blocksHom (b,a) := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  change swapSL.val * blocks a.val b.val = blocks b.val a.val * swapSL.val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapSL, blocks, Matrix.mul_apply, Fin.sum_univ_succ]

variable {U : Type*} [Group U]

def torusSL (σ : U →* SL(2,F)) : (U × U) →* SL(4,F) :=
  blocksHom.comp (σ.prodMap σ)

def torusHom (σ : U →* SL(2,F)) : (U × U) →* PSL(4,F) :=
  (QuotientGroup.mk' _).comp (torusSL σ)

def swap : PSL(4,F) := QuotientGroup.mk' _ (swapSL (F := F))

theorem swap_torus (σ : U →* SL(2,F)) (a b : U) :
    swap * torusHom σ (a,b) * swap⁻¹ = torusHom σ (b,a) := by
  change QuotientGroup.mk' _ swapSL * QuotientGroup.mk' _ (blocksHom (σ a, σ b)) *
    (QuotientGroup.mk' _ swapSL)⁻¹ = QuotientGroup.mk' _ (blocksHom (σ b, σ a))
  rw [← map_inv, ← map_mul, ← map_mul, swap_blocks]

theorem torusSL_injective (σ : U →* SL(2,F)) (hσ : Function.Injective σ) :
    Function.Injective (torusSL σ) := by
  intro a b h
  have he := blocksHom_injective h
  exact Prod.ext (hσ (congrArg Prod.fst he)) (hσ (congrArg Prod.snd he))

theorem torusHom_injective [Finite U] (σ : U →* SL(2,F))
    (hσ : Function.Injective σ) (ho : (Nat.card U).Coprime 2) :
    Function.Injective (torusHom σ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  have hh : QuotientGroup.mk' _ (torusSL σ a) = 1 := ha
  obtain ⟨v,hv,he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp
    (show torusSL σ a ∈ center SL(4,F) from (QuotientGroup.eq_one_iff _).mp hh)
  have hfour : torusSL σ a ^ 4 = 1 := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, ← he]
    rw [← map_pow]
    simpa only [Fintype.card_fin, map_one] using congrArg (Matrix.scalar (Fin 4)) hv
  have hfour' : a ^ 4 = 1 := torusSL_injective σ hσ (by rw [map_pow, hfour, map_one])
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (show (Nat.card (U × U)).Coprime 4 by
      rw [Nat.card_prod]; exact (ho.mul_left ho).pow_right 2)
    (orderOf_dvd_natCard a) (orderOf_dvd_of_pow_eq_one hfour'))

theorem torus_generated [IsCyclic U] (σ : U →* SL(2,F))
    (u : U) (hu : ∀ v : U, v ∈ zpowers u) :
    closure ({torusHom σ (u,1), torusHom σ (1,u)} : Set PSL(4,F)) =
      (torusHom σ).range := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨(u,1),rfl⟩
    · rw [Set.mem_singleton_iff] at hx
      subst x
      exact ⟨(1,u),rfl⟩
  · rintro x ⟨⟨v,w⟩,rfl⟩
    obtain ⟨i,hi⟩ := hu v
    obtain ⟨j,hj⟩ := hu w
    have he : torusHom σ (v,w) =
        torusHom σ (u,1) ^ i * torusHom σ (1,u) ^ j := by
      rw [← map_zpow, ← map_zpow, ← map_mul]
      congr 1
      ext <;> simp [hi,hj]
    rw [he]
    exact mul_mem (zpow_mem (subset_closure (by simp)) _)
      (zpow_mem (subset_closure (by simp)) _)

theorem abelian_preimage [Finite U] [IsCyclic U]
    (σ : U →* SL(2,F)) (ho : (Nat.card U).Coprime 2)
    {E : Type*} [Group E] (f : E →* PSL(4,F))
    (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    IsMulCommutative ((torusHom σ).range.comap f) := by
  obtain ⟨u,hu⟩ := IsCyclic.exists_generator (α := U)
  let x := torusHom σ (u,1)
  let y := torusHom σ (1,u)
  obtain ⟨a,ha⟩ := hf x
  obtain ⟨b,hb⟩ := hf y
  have hx : x ^ Nat.card U = 1 := by
    dsimp only [x]
    rw [← map_pow]
    have he : ((u,1) : U × U) ^ Nat.card U = 1 := by
      ext <;> simp [pow_card_eq_one']
    rw [he, map_one]
  have hxy : Commute x y := (Commute.all (u,1) (1,u)).map (torusHom σ)
  have hab : Commute a b := CentralExtension.commute_lifts_of_swap f hf hk
    x y swap ho hx hxy (swap_torus σ u 1) (swap_torus σ 1 u) a b ha hb
  apply CentralExtension.isMulCommutative_comap_of_pair_lifts f hk _ a b hab
  rw [ha,hb]
  exact torus_generated σ u hu

theorem prime_to_factors {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hr2 : r ≠ 2) (hplus : r ∣ p + 1) :
    ¬ r ∣ p - 1 ∧ ¬ r ∣ p ^ 2 + 1 ∧ ¬ r ∣ p ^ 3 - 1 := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp3 : 1 ≤ p^3 := Nat.one_le_pow _ _ (by omega)
  have hpm : (p : ZMod r) = -1 := by
    have hz := (ZMod.natCast_eq_zero_iff (p+1) r).mpr hplus
    push_cast at hz
    exact eq_neg_of_add_eq_zero_left hz
  have htwo : (2 : ZMod r) ≠ 0 := by
    intro hz
    exact hr2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime) Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 r).mp hz))
  refine ⟨?_, ?_, ?_⟩
  · intro hd
    have hz := (ZMod.natCast_eq_zero_iff (p-1) r).mpr hd
    rw [Nat.cast_sub (by omega), Nat.cast_one, hpm] at hz
    exact htwo (by linear_combination -hz)
  · intro hd
    have hz := (ZMod.natCast_eq_zero_iff (p^2+1) r).mpr hd
    norm_num [hpm] at hz
    exact htwo hz
  · intro hd
    have hz := (ZMod.natCast_eq_zero_iff (p^3-1) r).mpr hd
    rw [Nat.cast_sub hp3, Nat.cast_pow, Nat.cast_one, hpm] at hz
    exact htwo (by linear_combination -hz)

theorem not_dvd_index_of_card {F : Type*} [Field F] [Finite F]
    {p r n m : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hF : Nat.card F = p) (hr2 : r ≠ 2) (hrp : r ≠ p)
    (hplus : r ∣ p+1) (hn : 0 < n) (hnm : n*m = p^2-1)
    (hm : ¬ r ∣ m) (C : Subgroup PSL(4,F)) (hC : Nat.card C = n^2) :
    ¬ r ∣ C.index := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hr : r.Prime := Fact.out
  have h41 : p^4-p = p*(p^3-1) := by rw [Nat.mul_sub]; ring_nf
  have h42 : p^4-p^2 = p^2*(p^2-1) := by rw [Nat.mul_sub]; ring_nf
  have h43 : p^4-p^3 = p^3*(p-1) := by rw [Nat.mul_sub]; ring_nf
  have h4 : p^4-1 = (p^2-1)*(p^2+1) := by
    calc
      p^4-1 = (p^2)^2-1^2 := by ring_nf
      _ = _ := by rw [Nat.sq_sub_sq]; ac_rfl
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
  norm_num [hF, Fin.prod_univ_succ] at hc
  rw [h41,h42,h43,h4, ← hnm, ← C.card_mul_index, hC] at hc
  have he : C.index * Nat.gcd 4 (p-1) * (p-1) =
      m^2 * p^6 * (p^2+1) * (p^3-1) * (p-1) := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hn 2)
    calc
      _ = n^2*C.index*Nat.gcd 4 (p-1)*(p-1) := by ring
      _ = _ := hc
      _ = _ := by ring
  obtain ⟨h1,h2,h3⟩ := prime_to_factors hr2 hplus
  have hnp : ¬ r ∣ p^6 := fun hd => hrp
    ((Nat.prime_dvd_prime_iff_eq hr (Fact.out : p.Prime)).mp (hr.dvd_of_dvd_pow hd))
  have hnm2 : ¬ r ∣ m^2 := fun hd => hm (hr.dvd_of_dvd_pow hd)
  intro hi
  exact (hr.not_dvd_mul (hr.not_dvd_mul (hr.not_dvd_mul
    (hr.not_dvd_mul hnm2 hnp) h2) h3) h1)
    (he ▸ dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hi _) _)

end Theory.SpecificGroups.HigherClassicalCovers.Nondefining.Nonsplit

namespace Theory.SpecificGroups.HigherClassicalCovers.Nondefining

/-- Nonsplit quadratic-torus primes do not divide the kernel of a finite
perfect central cover of the literal projective special linear group. -/
public theorem linear_not_dvd_kernel_of_dvd_add_one {F : Type*} [Field F] [Finite F]
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hF : Nat.card F = p)
    (_hp2 : p ≠ 2) (hr2 : r ≠ 2) (hrp : r ≠ p) (hplus : r ∣ p+1)
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E PSL(4,F)) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  classical
  let := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime (by rwa [← Nat.card_eq_fintype_card])
  let K := FiniteField.Extension F p 2
  let U : Sylow r Kˣ := default
  obtain ⟨ρ, _, hρ, _⟩ := Matrix.GeneralLinearGroup.exists_finite_quadratic_torus F p
  let ρU : U →* GL (Fin 2) F := ρ.comp (U : Subgroup Kˣ).subtype
  obtain ⟨k,hk⟩ := U.isPGroup'.exists_card_eq
  have hr : r.Prime := Fact.out
  have hr2cop : r.Coprime 2 := hr.coprime_iff_not_dvd.mpr
    (fun hd => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hd))
  have ho : (Nat.card U).Coprime 2 := by rw [hk]; exact hr2cop.pow_left k
  have hminus : ¬ r ∣ p-1 := (Nonsplit.prime_to_factors hr2 hplus).1
  have hcop : (Nat.card U).Coprime (Nat.card Fˣ) := by
    rw [Nat.card_units, hF, hk]
    exact (hr.coprime_iff_not_dvd.mpr hminus).pow_left k
  have hd (u : U) : Matrix.GeneralLinearGroup.det (ρU u) = 1 := by
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes hcop
      ((orderOf_map_dvd (Matrix.GeneralLinearGroup.det.comp ρU) u).trans
        (orderOf_dvd_natCard u)) (orderOf_dvd_natCard _)
  let σ : U →* SL(2,F) := {
    toFun := fun u => ⟨(ρU u).val, congrArg Units.val (hd u)⟩
    map_one' := by apply Subtype.ext; exact congrArg Units.val ρU.map_one
    map_mul' := fun u v => by apply Subtype.ext; exact congrArg Units.val (ρU.map_mul u v) }
  have hσ : Function.Injective σ := by
    intro u v huv
    apply Subtype.ext
    apply hρ
    apply Units.ext
    exact congrArg Subtype.val huv
  let T := (Nonsplit.torusHom σ).range
  have hTcard : Nat.card T = Nat.card U ^ 2 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective
      (Nonsplit.torusHom_injective σ hσ ho)).toEquiv, Nat.card_prod, pow_two]
  have hTp : IsPGroup r T := IsPGroup.of_card (n := 2*k) (by
    rw [hTcard,hk,← pow_mul,Nat.mul_comm])
  have hindex : ¬ r ∣ T.index := by
    apply Nonsplit.not_dvd_index_of_card hF hr2 hrp hplus Nat.card_pos
      (m := U.index) ?_ U.not_dvd_index T hTcard
    rw [(U : Subgroup Kˣ).card_mul_index, Nat.card_units,
      FiniteField.natCard_extension, hF]
  let Q : Sylow r PSL(4,F) := hTp.toSylow hindex
  let := f.isPerfect
  exact PerfectCentralCovering.not_dvd_card_kernel_of_abelian_sylow_preimage
    f.toMonoidHom f.surjective f.ker_le_center Q
    (Nonsplit.abelian_preimage σ ho f.toMonoidHom f.surjective f.ker_le_center)

end Theory.SpecificGroups.HigherClassicalCovers.Nondefining
