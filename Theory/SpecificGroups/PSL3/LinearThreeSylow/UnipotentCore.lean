module
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.ScalarGeneration
public import Theory.SpecificGroups.PSL3.CartanActions.ThreeAlignment
public import Theory.GroupTheory.PCoreFromTwoNormalizers
public import Theory.GroupTheory.SylowNormalizerOvergroup
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.SolvableOvergroups
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.SylowKernelCore

/-!
# Recovering the full unipotent core from a noncyclic odd actor

In the split torus of PSL₃, the kernel of either simple-root character is
cyclic. A noncyclic torus subgroup therefore moves each simple root.
If the unipotent group normalizes X and the torus subgroup lies in X,
scalar commutators put both simple roots, and hence their commutator root,
inside X. Odd-primary Borel subgroups align with the torus by Sylow
conjugacy, retaining the cubic scalar quotient.

For an arbitrary specified Sylow subgroup, solvability places its product
with X in the Borel. The root calculation then identifies O₂(X) with that
full Sylow subgroup and constructs compatible projective coordinates.
No equality with the full unipotent subgroup is assumed.

Source: Aschbacher–Smith, proof of 13.1.12, final paragraph, printed p.875.
-/

public noncomputable section
open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.LinearThree.UnipotentCore
variable (F : Type*) [Field F] [Finite F]

private def firstScalar (d : Fˣ × Fˣ) : Fˣ := d.1 * (d.1 * d.2)
private def secondScalar (d : Fˣ × Fˣ) : Fˣ := (d.1 * d.2)⁻¹ * d.2⁻¹

private def firstKernel : Fˣ →* PSL(3,F) := (torusMap F).comp {
  toFun a := (a,(a*a)⁻¹)
  map_one' := by simp
  map_mul' a b := by simp [mul_comm,mul_left_comm,mul_assoc] }
private def secondKernel : Fˣ →* PSL(3,F) := (torusMap F).comp {
  toFun a := ((a*a)⁻¹,a)
  map_one' := by simp
  map_mul' a b := by simp [mul_comm,mul_left_comm,mul_assoc] }

private theorem first_move (P : Subgroup PSL(3,F)) (hPT : P ≤ torus F)
    (hnc : ¬ IsCyclic P) : ∃ d : Fˣ × Fˣ, torusMap F d ∈ P ∧ firstScalar F d ≠ 1 := by
  by_contra! h
  let : IsCyclic (firstKernel F).range := isCyclic_of_surjective
    (firstKernel F).rangeRestrict (firstKernel F).rangeRestrict_surjective
  apply hnc
  apply isCyclic_of_injective (inclusion (show P ≤ (firstKernel F).range from ?_))
    (inclusion_injective _)
  intro x hx
  obtain ⟨d,rfl⟩ := hPT hx
  have hd : d.2 = (d.1*d.1)⁻¹ := by
    have he := h d hx
    change d.1 * (d.1 * d.2) = 1 at he
    exact eq_inv_of_mul_eq_one_left (by simpa only [mul_assoc,mul_comm,mul_left_comm] using he)
  exact ⟨d.1,by change torusMap F (d.1,(d.1*d.1)⁻¹) = torusMap F d; rw [← hd]⟩

private theorem second_move (P : Subgroup PSL(3,F)) (hPT : P ≤ torus F)
    (hnc : ¬ IsCyclic P) : ∃ d : Fˣ × Fˣ, torusMap F d ∈ P ∧ secondScalar F d ≠ 1 := by
  by_contra! h
  let : IsCyclic (secondKernel F).range := isCyclic_of_surjective
    (secondKernel F).rangeRestrict (secondKernel F).rangeRestrict_surjective
  apply hnc
  apply isCyclic_of_injective (inclusion (show P ≤ (secondKernel F).range from ?_))
    (inclusion_injective _)
  intro x hx
  obtain ⟨d,rfl⟩ := hPT hx
  have hd : d.1 = (d.2*d.2)⁻¹ := by
    have he := congrArg Inv.inv (h d hx)
    have he' : (d.2*d.2)*d.1 = 1 := by
      simpa [secondScalar,mul_comm,mul_left_comm,mul_assoc] using he
    exact eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using he')
  exact ⟨d.2,by change torusMap F ((d.2*d.2)⁻¹,d.2) = torusMap F d; rw [← hd]⟩

omit [Finite F] in
private theorem torus_conj (d : Fˣ × Fˣ) (u : U F) :
    torusMap F d * projective F u * (torusMap F d)⁻¹ =
      projective F ⟨firstScalar F d * u.x, secondScalar F d * u.y,
        (d.1*d.2⁻¹ : Fˣ) * u.c⟩ := by
  change projection F (torusSL F d) * projection F (specialLinear F u) *
    (projection F (torusSL F d))⁻¹ = projection F (specialLinear F _)
  rw [← map_inv,← map_mul,← map_mul]
  apply congrArg (projection F)
  rw [← map_inv]
  apply Subtype.ext
  change (torusSL F d).val * matrix F u * (torusSL F d⁻¹).val = matrix F _
  rw [torusSL_val,torusSL_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix,firstScalar,secondScalar,Matrix.diagonal_mul,Matrix.mul_diagonal,
      mul_assoc,mul_left_comm,mul_comm]
  all_goals field_simp

omit [Finite F] in
private theorem scalar_root_le_of_normalizes {D : Type*} [Group D]
    (N : Subgroup D) (f : Multiplicative F →* D)
    (hn : f.range ≤ normalizer (N : Set D))
    (t : D) (ht : t ∈ N) (a : F) (ha : a ≠ 1)
    (hact : ∀ x : F, t * f (Multiplicative.ofAdd x) * t⁻¹ =
      f (Multiplicative.ofAdd (a * x))) : f.range ≤ N := by
  rintro _ ⟨x,rfl⟩
  let y : F := x.toAdd / (a - 1)
  have hmem : t * f (Multiplicative.ofAdd y) * t⁻¹ *
      (f (Multiplicative.ofAdd y))⁻¹ ∈ N := by
    have hh := (mem_normalizer_iff.mp (hn ⟨Multiplicative.ofAdd y,rfl⟩) (t⁻¹)).mp (N.inv_mem ht)
    convert N.mul_mem ht hh using 1
    group
  have he : t * f (Multiplicative.ofAdd y) * t⁻¹ *
      (f (Multiplicative.ofAdd y))⁻¹ = f x := by
    rw [hact,← map_inv,← map_mul]
    congr 1
    change a*y + -y = x.toAdd
    dsimp [y]
    field_simp [sub_ne_zero.mpr ha]
    ring
  rwa [he] at hmem

/-- A noncyclic torus subgroup inside an invariant subgroup generates the full
unipotent group by commutators with its two simple roots. -/
theorem unipotent_le_of_noncyclic_torus
    (X P : Subgroup PSL(3,F)) (hPX : P ≤ X) (hPT : P ≤ torus F)
    (hnc : ¬ IsCyclic P) (hn : unipotent F ≤ normalizer (X : Set PSL(3,F))) :
    unipotent F ≤ X := by
  rw [← projective_range F]
  apply range_le_of_roots F (projective F)
  · obtain ⟨d,hd,hm⟩ := first_move F P hPT hnc
    apply scalar_root_le_of_normalizes F X ((projective F).comp (firstRoot F))
      (by rintro _ ⟨a,rfl⟩; exact hn ((projective_range F).le ⟨_,rfl⟩))
      (torusMap F d) (hPX hd) (firstScalar F d) (fun h => hm (Units.ext h))
    intro x
    simpa [firstRoot] using
      torus_conj F d (firstRoot F (Multiplicative.ofAdd x))
  · obtain ⟨d,hd,hm⟩ := second_move F P hPT hnc
    apply scalar_root_le_of_normalizes F X ((projective F).comp (secondRoot F))
      (by rintro _ ⟨a,rfl⟩; exact hn ((projective_range F).le ⟨_,rfl⟩))
      (torusMap F d) (hPX hd) (secondScalar F d) (fun h => hm (Units.ext h))
    intro x
    simpa [secondRoot] using
      torus_conj F d (secondRoot F (Multiplicative.ofAdd x))

/-- Every odd-primary Borel subgroup can be aligned with the split torus. -/
theorem conjugate_borel_pSubgroup_into_torus {n p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = 2^n) (ho : Odd p)
    (P : Subgroup PSL(3,F)) (hP : IsPGroup p P) (hPB : P ≤ borel F) :
    ∃ g ∈ borel F, P.map (MulAut.conj g).toMonoidHom ≤ torus F := by
  have hp : p.Prime := Fact.out
  have hind : ¬ p ∣ ((torus F).subgroupOf (borel F)).index := by
    intro h
    have hd := h.trans (ThreeAlignment.torus_index_dvd F)
    rw [hF] at hd
    have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow hd)
    have he : p = 2 := (Nat.dvd_prime Nat.prime_two).mp hp2 |>.resolve_left hp.ne_one
    exact ho.not_two_dvd_nat (by rw [he])
  obtain ⟨g,hg⟩ := exists_conj_overgroup_of_index_primeTo
    (P.subgroupOf (borel F)) ((torus F).subgroupOf (borel F))
    hP.comap_subtype hind
  refine ⟨g,g.property,?_⟩
  rintro _ ⟨x,hx,rfl⟩
  exact hg (show (⟨x,hPB hx⟩ : borel F) ∈ P.subgroupOf (borel F) from hx)


/-- A Borel subgroup normalized by the full Sylow group and containing a
noncyclic odd-primary subgroup contains the entire unipotent radical. -/
theorem unipotent_le_of_noncyclic_odd_actor {n p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = 2^n) (ho : Odd p)
    (X P : Subgroup PSL(3,F)) (hXB : X ≤ borel F) (hPX : P ≤ X)
    (hP : IsPGroup p P) (hnc : ¬ IsCyclic P)
    (hn : unipotent F ≤ normalizer (X : Set PSL(3,F))) : unipotent F ≤ X := by
  obtain ⟨g,hg,hgP⟩ := conjugate_borel_pSubgroup_into_torus F hF ho P hP (hPX.trans hXB)
  let c := MulAut.conj g
  have hU : (unipotent F).map c.toMonoidHom = unipotent F :=
    mem_normalizer_iff_map_conj_eq.mp (borel_le_normalizer_unipotent F hg)
  have hn' : unipotent F ≤ normalizer (X.map c.toMonoidHom : Set PSL(3,F)) := by
    rw [← hU,← map_equiv_normalizer_eq X c]
    exact map_mono hn
  have hc : ¬ IsCyclic (P.map c.toMonoidHom) :=
    fun hc => hnc ((P.equivMapOfInjective c.toMonoidHom c.injective).isCyclic.mpr hc)
  have hle := unipotent_le_of_noncyclic_torus F (X.map c.toMonoidHom)
    (P.map c.toMonoidHom) (map_mono hPX) hgP hc hn'
  rw [← hU] at hle
  exact (map_le_map_iff_of_injective c.injective).mp hle

/-- The actual two-core equals the full unipotent group in this configuration. -/
theorem twoCore_eq_unipotent {n p : ℕ} [Fact p.Prime]
    (hnF : 0 < n) (hF : Nat.card F = 2^n) (ho : Odd p)
    (X P : Subgroup PSL(3,F)) (hXB : X ≤ borel F) (hPX : P ≤ X)
    (hP : IsPGroup p P) (hnc : ¬ IsCyclic P)
    (hn : unipotent F ≤ normalizer (X : Set PSL(3,F))) : X.pCoreIn 2 = unipotent F := by
  have hUX := unipotent_le_of_noncyclic_odd_actor F hF ho X P hXB hPX hP hnc hn
  apply le_antisymm
  · exact (isPGroup_pCoreIn 2 X).le_sylow_of_normalized (unipotentSylow F hnF hF)
      (hn.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
  · exact le_pCoreIn_of_normalizes (unipotentSylow F hnF hF).isPGroup'
      hUX (hXB.trans (borel_le_normalizer_unipotent F))

/-- A solvable subgroup normalized by a Sylow two-subgroup and containing
a noncyclic odd-primary subgroup has the full marked unipotent two-core. -/
theorem exists_unipotent_marking {J : Type*} [Group J] [Finite J]
    {n p : ℕ} [Fact p.Prime] (hnF : 2 ≤ n) (hF : Nat.card F = 2^n) (ho : Odd p)
    (e : J ≃* PSL(3,F)) (S : Sylow 2 J)
    (X P : Subgroup J) [Group.IsSolvable X] (hPX : P ≤ X)
    (hP : IsPGroup p P) (hnc : ¬ IsCyclic P)
    (hn : (S : Subgroup J) ≤ normalizer (X : Set J)) :
    ∃ f : J ≃* PSL(3,F), (X.pCoreIn 2).map f.toMonoidHom = unipotent F := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let Se := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) Se (unipotentSylow F (by omega) hF)
  let f := e.trans (MulAut.conj g)
  have hS : (S : Subgroup J).map f.toMonoidHom = unipotent F := by
    have h := congrArg Sylow.toSubgroup hg
    change ((S : Subgroup J).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = unipotent F at h
    change (S : Subgroup J).map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
    rw [← Subgroup.map_map]
    exact h
  let Y := X.map f.toMonoidHom
  let Q := P.map f.toMonoidHom
  let U := unipotent F
  have hUY : U ≤ normalizer (Y : Set PSL(3,F)) := by
    change unipotent F ≤ normalizer (X.map f.toMonoidHom : Set PSL(3,F))
    rw [← hS,← map_equiv_normalizer_eq X f]
    exact map_mono hn
  let : Group.IsSolvable Y := Group.isSolvable_of_surjective
    (f.toMonoidHom.subgroupMap_surjective X)
  let : Group.IsNilpotent U := (unipotentSylow F (by omega) hF).isPGroup'.isNilpotent
  let : Group.IsSolvable (Y ⊔ U : Subgroup PSL(3,F)) :=
    Group.isSolvable_sup_of_normalizes Y U hUY
  have hYB : Y ≤ borel F := le_sup_left.trans
    (SolvableOvergroups.solvable_le_borel F (by
      rw [hF]; exact Nat.pow_le_pow_right (n := 2) (by decide : 0 < 2) hnF) (Y ⊔ U) le_sup_right)
  have hQcyc : ¬ IsCyclic Q :=
    fun h => hnc ((P.equivMapOfInjective f.toMonoidHom f.injective).isCyclic.mpr h)
  refine ⟨f,?_⟩
  rw [map_pCoreIn_of_injective 2 X f.toMonoidHom f.injective]
  exact twoCore_eq_unipotent F (by omega) hF ho Y Q hYB (map_mono hPX)
    (hP.map f.toMonoidHom) hQcyc hUY

end Matrix.PSL3.LinearThree.UnipotentCore
