module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Elementary.Nontrivial.Position.Model
public import Theory.SpecificGroups.GL2.NoncommutativeCentralizer
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Mathlib.LinearAlgebra.Determinant


/-!
# Involution placement for reducible elementary PSL₃ pairs

Maschke supplies an invariant complement to a proper nonzero subspace of the
full SL₃ inverse image. In dimension three this gives an invariant plane and
line. Acting as minus one on the plane and as one on the line produces a
nonidentity determinant-one involution centralizing the whole inverse image.

To control the entire intrinsic Sylow center, restrict an ambient SL₃ Sylow
subgroup to this involution centralizer and identify the latter with GL₂.
Every genuine Sylow two-subgroup of GL₂ is noncommutative: the explicit
rotation and reflection matrices generate a noncommutative two-subgroup.
The GL₂ centralizer theorem therefore makes every element of its centralizer
scalar. In particular the intrinsic Sylow center commutes with the whole
involution centralizer. The odd central kernel preserves the involution and
identifies the Sylow subgroups, so the entire containment descends to PSL₃.

This proves the reducible geometric contract for the elementary branch of
Aschbacher–Smith, Proposition 1.3.4, printed p.511 (PDF p.528 of
`refs/quasithin.pdf`). The subspace alternative is GLS3, Theorem 6.5.3(a)
and its proof, `refs/KGroup/GLS3/chapter6.tex`. The invariant complement and
Sylow-center arguments supply the additional placement needed by this branch.
-/

public section

open Subgroup Matrix Module
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.ElementaryNontrivial

private theorem invariant_two_one {F : Type*} [Field F]
    (H : Subgroup SL(3,F))
    (hs : Representation.IsSemisimpleRepresentation
      ((Representation.specialLinearNatural (k := F) 3).comp H.subtype))
    (hr : ∃ W : Submodule F (Fin 3 → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ g ∈ H, ∀ v ∈ W, g • v ∈ W) :
    ∃ P Q : Submodule F (Fin 3 → F), IsCompl P Q ∧ finrank F P = 2 ∧
      finrank F Q = 1 ∧
      (∀ g ∈ H, ∀ v ∈ P, g • v ∈ P) ∧
      (∀ g ∈ H, ∀ v ∈ Q, g • v ∈ Q) := by
  let ρ := (Representation.specialLinearNatural (k := F) 3).comp H.subtype
  let _ : Representation.IsSemisimpleRepresentation ρ := hs
  obtain ⟨W, hW0, hW1, hW⟩ := hr
  let A : Subrepresentation ρ := ⟨W, fun g _ hv => hW g g.property _ hv⟩
  obtain ⟨B, hAB⟩ := exists_isCompl A
  have hc : IsCompl W B.toSubmodule := by
    constructor
    · exact disjoint_iff.mpr (congrArg Subrepresentation.toSubmodule hAB.inf_eq_bot)
    · exact codisjoint_iff.mpr (congrArg Subrepresentation.toSubmodule hAB.sup_eq_top)
  have hd : finrank F W + finrank F B.toSubmodule = 3 := by
    simpa using Submodule.finrank_add_eq_of_isCompl hc
  have hdim0 : finrank F W ≠ 0 := fun he => hW0 (Submodule.finrank_eq_zero.mp he)
  have hdim1 : finrank F W < 3 := by simpa using Submodule.finrank_lt hW1
  have hB : ∀ g ∈ H, ∀ v ∈ B.toSubmodule, g • v ∈ B.toSubmodule :=
    fun g hg _ hv => B.apply_mem_toSubmodule ⟨g, hg⟩ hv
  by_cases hdim : finrank F W = 2
  · exact ⟨W, B.toSubmodule, hc, hdim, by omega, hW, hB⟩
  · exact ⟨B.toSubmodule, W, hc.symm, by omega, by omega, hB, hW⟩

private theorem involution_of_invariant_two_one {F : Type*} [Field F]
    (h2 : (2 : F) ≠ 0) (H : Subgroup SL(3,F))
    (P Q : Submodule F (Fin 3 → F)) (hc : IsCompl P Q)
    (hd : finrank F P = 2)
    (hP : ∀ g ∈ H, ∀ v ∈ P, g • v ∈ P)
    (hQ : ∀ g ∈ H, ∀ v ∈ Q, g • v ∈ Q) :
    ∃ z : SL(3,F), orderOf z = 2 ∧ H ≤ centralizer ({z} : Set SL(3,F)) := by
  classical
  let e := P.prodEquivOfIsCompl Q hc
  let d : Module.End F (P × Q) := LinearMap.prodMap ((-1 : F) • (1 : Module.End F P)) 1
  let f : Module.End F (Fin 3 → F) := e.toLinearMap ∘ₗ d ∘ₗ e.symm.toLinearMap
  have hf (v : P × Q) : f (e v) = e (-v.1, v.2) := by simp [f, d]
  have hf2 : f * f = 1 := by
    apply LinearMap.ext
    intro v
    obtain ⟨v, rfl⟩ := e.surjective v
    simp only [Module.End.mul_apply, hf]
    simp
  have hdet : f.det = 1 := by
    rw [LinearMap.det_conj]
    simp [d, LinearMap.det_prodMap, LinearMap.det_smul, hd]
  let z : SL(3,F) := ⟨LinearMap.toMatrix' f, by rwa [LinearMap.det_toMatrix']⟩
  have hz2 : z ^ 2 = 1 := by
    rw [pow_two]
    apply Subtype.ext
    change LinearMap.toMatrix' f * LinearMap.toMatrix' f = 1
    rw [← LinearMap.toMatrix'_mul, hf2]
    simp
  have hz1 : z ≠ 1 := by
    intro hz
    have hf1 : f = 1 := by
      apply LinearMap.toMatrix'.injective
      simpa using congrArg Subtype.val hz
    have hP0 : P = ⊥ := by
      apply eq_bot_iff.mpr
      intro v hv
      change v = 0
      have heq := hf (⟨v, hv⟩, 0)
      rw [hf1] at heq
      have heq' : v = -v := by simpa [e] using heq
      have hv2 : (2 : F) • v = 0 := by
        simpa [two_smul] using eq_neg_iff_add_eq_zero.mp heq'
      exact (smul_eq_zero.mp hv2).resolve_left h2
    have := Submodule.finrank_eq_zero.mpr hP0
    omega
  refine ⟨z, orderOf_eq_prime hz2 hz1, ?_⟩
  intro g hg
  apply mem_centralizer_singleton_iff.mpr
  apply Subtype.ext
  apply Matrix.toLin'.injective
  change Matrix.toLin' (g.val * LinearMap.toMatrix' f) =
    Matrix.toLin' (LinearMap.toMatrix' f * g.val)
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro v
  obtain ⟨v, rfl⟩ := e.surjective v
  let gv : P × Q := (⟨g • (v.1 : Fin 3 → F), hP g hg _ v.1.property⟩,
    ⟨g • (v.2 : Fin 3 → F), hQ g hg _ v.2.property⟩)
  have hge : Matrix.toLin' g.val (e v) = e gv := by
    change g • ((v.1 : Fin 3 → F) + v.2) = g • (v.1 : Fin 3 → F) + g • (v.2 : Fin 3 → F)
    exact smul_add _ _ _
  simp only [LinearMap.comp_apply, hf, hge]
  change g • (-(v.1 : Fin 3 → F) + v.2) =
    -(g • (v.1 : Fin 3 → F)) + g • (v.2 : Fin 3 → F)
  simp


private theorem gl2_sylow_noncommutative {F : Type*} [Field F] [Finite F]
    (h2 : (2 : F) ≠ 0) (P : Sylow 2 (GL (Fin 2) F)) : ¬ IsMulCommutative P := by
  classical
  let r : GL (Fin 2) F := GeneralLinearGroup.mkOfDetNeZero !![0, -1; 1, 0]
    (by simp [Matrix.det_fin_two])
  let s : GL (Fin 2) F := GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, -1]
    (by simp [Matrix.det_fin_two])
  have hr4 : r ^ 4 = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [r, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  have hs2 : s ^ 2 = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [s, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hs2)
  have hconj : s * r * s⁻¹ = r⁻¹ := by
    rw [hsi]
    apply eq_inv_iff_mul_eq_one.mpr
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [r, s, Matrix.mul_apply, Fin.sum_univ_two]
  have hn : zpowers s ≤ normalizer (zpowers r : Set (GL (Fin 2) F)) := by
    rw [zpowers_le, mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change zpowers (s * r * s⁻¹) = zpowers r
    rw [hconj, zpowers_inv]
  have hrP : IsPGroup 2 (zpowers r) := IsPGroup.of_card_dvd_pow (n := 2) (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hr4)
  have hsP : IsPGroup 2 (zpowers s) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hs2)
  let D := zpowers s ⊔ zpowers r
  obtain ⟨P₀, hDP⟩ := (hsP.to_sup_of_normal_right' hrP hn).exists_le_sylow
  let f : D →* P := (P₀.equiv P).toMonoidHom.comp (inclusion hDP)
  have hfi : Function.Injective f := (P₀.equiv P).injective.comp (inclusion_injective hDP)
  let rD : D := ⟨r, (le_sup_right : zpowers r ≤ D) (mem_zpowers r)⟩
  let sD : D := ⟨s, (le_sup_left : zpowers s ≤ D) (mem_zpowers s)⟩
  intro hcomm
  let _ : IsMulCommutative P := hcomm
  have hrs : r * s = s * r := congrArg Subtype.val (hfi (show f (rD * sD) = f (sD * rD) by
    rw [map_mul, map_mul, mul_comm]))
  have heq := congrArg (fun x : GL (Fin 2) F => x 0 1) hrs
  have heq' : (1 : F) = -1 := by simpa [r, s, Matrix.mul_apply, Fin.sum_univ_two] using heq
  apply h2
  linear_combination heq'

private theorem sl3_centralizer_le_center_centralizer {F : Type*} [Field F] [Finite F]
    (h2 : (2 : F) ≠ 0) (S : Sylow 2 SL(3,F))
    (z : SL(3,F)) (hz : orderOf z = 2)
    (hS : (S : Subgroup _) ≤ centralizer ({z} : Set SL(3,F))) :
    centralizer ({z} : Set SL(3,F)) ≤
      centralizer ((center (S : Subgroup SL(3,F))).map (S : Subgroup SL(3,F)).subtype : Set SL(3,F)) := by
  let C := centralizer ({z} : Set SL(3,F))
  let e := SL3.involutionCentralizerEquiv F z hz h2
  let SC : Sylow 2 C := S.comapOfInjective C.subtype C.subtype_injective
    (by rwa [C.range_subtype])
  let P : Sylow 2 (GL (Fin 2) F) := SC.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP : ¬ IsMulCommutative P := gl2_sylow_noncommutative h2 P
  intro x hx y hy
  obtain ⟨y, hyZ, rfl⟩ := hy
  let yC : C := ⟨y, hS y.property⟩
  have hycentral : e yC ∈ centralizer (P : Set (GL (Fin 2) F)) := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := hu
    change e v * e yC = e yC * e v
    rw [← e.map_mul, ← e.map_mul]
    apply congrArg e
    apply Subtype.ext
    change (v : SL(3,F)) * (y : SL(3,F)) = y * v
    exact congrArg (fun a : S => (a : SL(3,F))) (mem_center_iff.mp hyZ ⟨v, hv⟩)
  obtain ⟨a, ha⟩ := GeneralLinearGroup.centralizer_le_scalar_of_noncommutative
    (P : Subgroup (GL (Fin 2) F)) hP hycentral
  have heq : e yC * e ⟨x, hx⟩ = e ⟨x, hx⟩ * e yC := by
    rw [← ha]
    exact GeneralLinearGroup.scalar_commute a (e ⟨x, hx⟩)
  have heqC : yC * (⟨x, hx⟩ : C) = (⟨x, hx⟩ : C) * yC :=
    e.injective (by simpa only [map_mul] using heq)
  exact congrArg Subtype.val heqC

private theorem projective_involution_order {F : Type*} [Field F] [Finite F]
    (z : SL(3,F)) (hz : orderOf z = 2) : orderOf (PSL3.projection F z) = 2 := by
  apply orderOf_eq_prime
  · rw [← map_pow, show z ^ 2 = 1 from hz ▸ pow_orderOf_eq_one z, map_one]
  · intro he
    have hc : z ∈ center SL(3,F) := by
      rw [← PSL3.projection_ker]
      exact he
    have hd := ((center SL(3,F)).orderOf_dvd_natCard hc).trans (SL3.card_center_dvd_three F)
    rw [hz] at hd
    norm_num at hd

private theorem psl3_centralizer_le_center_centralizer {F : Type*} [Field F] [Finite F]
    (h2 : (2 : F) ≠ 0) (T : Sylow 2 PSL(3,F))
    (z : SL(3,F)) (hz : orderOf z = 2)
    (hT : (T : Subgroup _) ≤ centralizer ({PSL3.projection F z} : Set PSL(3,F))) :
    centralizer ({PSL3.projection F z} : Set PSL(3,F)) ≤
      centralizer ((center (T : Subgroup PSL(3,F))).map (T : Subgroup PSL(3,F)).subtype : Set PSL(3,F)) := by
  let q := PSL3.projection F
  obtain ⟨S, hmap⟩ := Sylow.mapSurjective_surjective (PSL3.projection_surjective F) 2 T
  have hST : (S : Subgroup _).map q = (T : Subgroup _) :=
    congrArg Sylow.toSubgroup hmap
  have hqC : (centralizer ({q z} : Set PSL(3,F))).comap q =
      centralizer ({z} : Set SL(3,F)) :=
    InvariantLarge.OddCartan.sl3_comap_projective_involution_centralizer F z hz
  have hS : (S : Subgroup _) ≤ centralizer ({z} : Set SL(3,F)) := by
    rw [← hqC]
    exact map_le_iff_le_comap.mp (hST ▸ hT)
  have hC := sl3_centralizer_le_center_centralizer h2 S z hz hS
  have hker : Nat.Coprime 2 (Nat.card q.ker) := by
    rw [PSL3.projection_ker]
    exact (SL3.odd_card_center F).coprime_two_left
  have hi := injective_comp_subtype_of_coprime_ker q hker (S : Subgroup _) S.isPGroup'
  intro x hx y hy
  obtain ⟨y, hyZ, rfl⟩ := hy
  have hyT : (y : PSL(3,F)) ∈ (S : Subgroup _).map q := hST.symm ▸ y.property
  obtain ⟨s, hs, hsy⟩ := hyT
  let sS : S := ⟨s, hs⟩
  have hsZ : sS ∈ center (S : Subgroup _) := by
    apply mem_center_iff.mpr
    intro v
    apply hi
    have hvT : q v ∈ (T : Subgroup _) := hST ▸ mem_map_of_mem q v.property
    have he : q (v : SL(3,F)) * (y : PSL(3,F)) = y * q v :=
      congrArg Subtype.val (mem_center_iff.mp hyZ ⟨q v, hvT⟩)
    change q ((v : SL(3,F)) * s) = q (s * (v : SL(3,F)))
    simpa only [map_mul, hsy] using he
  obtain ⟨a, ha⟩ := PSL3.projection_surjective F x
  change q a = x at ha
  have haC : a ∈ centralizer ({z} : Set SL(3,F)) := by
    rw [← hqC]
    change q a ∈ centralizer ({q z} : Set PSL(3,F))
    rwa [ha]
  have he := congrArg q (hC haC s ⟨sS, hsZ, rfl⟩)
  change (y : PSL(3,F)) * x = x * y
  simpa only [map_mul, hsy, ha] using he

/-- Reducibility of the actual inverse image places U in an involution
centralizer that centralizes the whole mapped intrinsic center of T. -/
theorem involutionPosition_of_reducible
    {F : Type} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (_hodd : Odd p) (hlarge : 3 < p) (_hsplit : p % 3 = 1)
    (hF : Nat.card F = p) (T : Sylow 2 PSL(3,F)) (U : Subgroup PSL(3,F))
    (h : ModelInput T U) (hred : ReduciblePreimage (U ⊔ (T : Subgroup _))) :
    InvolutionPosition (T : Subgroup _) U := by
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Fintype F := Fintype.ofFinite F
  let _ : CharP F p := charP_of_card_eq_prime
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have h2 : (2 : F) ≠ 0 := by
    exact CharP.cast_ne_zero_of_ne_of_prime F (p := p) (q := 2) Nat.prime_two
      (by omega)
  obtain ⟨P, Q, hc, hd, _, hP, hQ⟩ := invariant_two_one _
    (h.preimage_semisimple hp hlarge hF) hred
  obtain ⟨z, hz, hC⟩ := involution_of_invariant_two_one h2 _ P Q hc hd hP hQ
  have hprod : U ⊔ (T : Subgroup _) ≤
      centralizer ({PSL3.projection F z} : Set PSL(3,F)) := by
    intro x hx
    obtain ⟨g, rfl⟩ := PSL3.projection_surjective F x
    have hg : g ∈ SL3.SplitMonomial.projectivePreimage (U ⊔ (T : Subgroup _)) := hx
    exact mem_centralizer_singleton_iff.mpr (by
      simpa only [map_mul] using congrArg (PSL3.projection F)
        (mem_centralizer_singleton_iff.mp (hC hg)))
  exact ⟨PSL3.projection F z, projective_involution_order z hz,
    le_trans le_sup_left hprod,
    psl3_centralizer_le_center_centralizer h2 T z hz (le_trans le_sup_right hprod)⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.ElementaryNontrivial
