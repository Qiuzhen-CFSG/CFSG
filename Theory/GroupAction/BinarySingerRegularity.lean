module

public import Theory.Representation.CompleteReducibility
public import Theory.Representation.ElementaryAbelianAction
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Regularity of faithful binary Singer actions

A faithful odd-order cyclic group acting on a finite elementary abelian
2-group has a free orbit. When the actor has order one less than the vector
space, this orbit exhausts the nonidentity elements and the action is regular.

Maschke's theorem decomposes the representation into simple modules over the
commutative group algebra. Choose a nonzero vector in every simple summand.
A scalar annihilating their tuple annihilates every summand, since each chosen
vector generates its summand. Consequently an actor fixing this tuple acts
trivially everywhere. Faithfulness and counting finish the argument; no
irreducibility or transitivity hypothesis is needed.

Application: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.6.11, printed p.250, the cyclic torus action on the nonidentity elements of
[V,X]. The proof uses the Maschke development in `Theory.Representation`.
-/

namespace Theory.GroupAction

private theorem exists_annihilator_vector {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Finite M] [IsSemisimpleModule R M] :
    ∃ v : M, ∀ r : R, r • v = 0 → ∀ w : M, r • w = 0 := by
  classical
  obtain ⟨n, V, e, hS⟩ :=
    IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp R M
  let := hS
  let d := e.trans (DFinsupp.linearEquivFunOnFintype (R := R))
  have hnon (i : Fin n) : Nontrivial (V i) := IsSimpleModule.nontrivial R (V i)
  choose v hv using fun i => @exists_ne (V i) (hnon i) 0
  refine ⟨d.symm v, ?_⟩
  intro r hr w
  have hr' : r • v = 0 := by simpa using congrArg d hr
  apply d.injective
  simp only [map_smul, map_zero]
  funext i
  obtain ⟨s, hs⟩ := IsSimpleModule.toSpanSingleton_surjective R (hv i) (d w i)
  change s • v i = d w i at hs
  change r • d w i = 0
  rw [← hs, smul_comm r s]
  have hri : r • v i = 0 := congrFun hr' i
  rw [hri, smul_zero]

private theorem exists_separating_vector {F A V : Type*} [Field F] [CommGroup A]
    [AddCommGroup V] [Module F V] [Finite V]
    (ρ : Representation F A V) (hρ : ρ.IsCompletelyReducible) :
    ∃ v : V, ∀ a b : A, ρ a v = ρ b v → ρ a = ρ b := by
  let : Finite ρ.asModule := Finite.of_injective ρ.asModuleEquiv ρ.asModuleEquiv.injective
  let : IsSemisimpleModule (MonoidAlgebra F A) ρ.asModule := hρ
  obtain ⟨v, hv⟩ := exists_annihilator_vector (R := MonoidAlgebra F A) (M := ρ.asModule)
  refine ⟨ρ.asModuleEquiv v, ?_⟩
  intro a b hab
  have hzero : (MonoidAlgebra.of F A a - MonoidAlgebra.of F A b) • v = 0 := by
    apply ρ.asModuleEquiv.injective
    simpa only [sub_smul, map_sub, Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_of, map_zero, sub_eq_zero] using hab
  ext w
  have hw := hv _ hzero (ρ.asModuleEquiv.symm w)
  have hw' := congrArg ρ.asModuleEquiv hw
  simpa only [sub_smul, map_sub, Representation.asModuleEquiv_map_smul,
    Representation.asAlgebraHom_of, map_zero, LinearEquiv.apply_symm_apply,
    sub_eq_zero] using hw'

open scoped IsMulCommutative

/-- A faithful odd-order cyclic action on a finite binary vector space has a free orbit. -/
public theorem faithful_cyclic_odd_binary_exists_free_orbit {A W : Type*} [Group A] [Finite A] [IsCyclic A]
    [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (ρ : A →* MulAut W) (hρ : Function.Injective ρ) (hodd : Odd (Nat.card A)) :
    ∃ w : W, Function.Injective (fun a : A => ρ a w) := by
  let : MulDistribMulAction A W := MulDistribMulAction.compHom W ρ
  let σ := Representation.ofElementaryAbelianAction (A := A) (G := W) (p := 2)
  have hs : σ.IsCompletelyReducible :=
    σ.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime
      (Or.inr (by
        rw [ringChar.eq (ZMod 2) 2]
        exact ⟨Nat.prime_two, hodd.coprime_two_left⟩))
  obtain ⟨v, hv⟩ := exists_separating_vector σ hs
  refine ⟨Additive.toMul v, ?_⟩
  intro a b hab
  apply hρ
  ext w
  have hσ : σ a = σ b := hv a b (Additive.toMul.injective hab)
  exact congrArg Additive.toMul (LinearMap.congr_fun hσ (Additive.ofMul w))

/-- A faithful cyclic action of order `2 ^ n - 1` on an elementary abelian group
of order `2 ^ n`, with `n > 1`, is regular on its nonidentity elements. -/
public theorem faithful_cyclic_binary_singer_regular {A W : Type*} [Group A] [Finite A] [IsCyclic A]
    [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (ρ : A →* MulAut W) (hρ : Function.Injective ρ)
    {n : ℕ} (hn : 1 < n) (hA : Nat.card A = 2 ^ n - 1) (hW : Nat.card W = 2 ^ n)
    (x y : W) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃! a : A, ρ a x = y := by
  classical
  have hpow : 2 < 2 ^ n := lt_of_le_of_lt hn (Nat.lt_two_pow_self (n := n))
  have hodd : Odd (Nat.card A) := by
    rw [hA]
    exact Nat.Even.sub_odd (by omega) (even_two.pow_of_ne_zero (by omega)) odd_one
  obtain ⟨w, hw⟩ := faithful_cyclic_odd_binary_exists_free_orbit ρ hρ hodd
  have hw1 : w ≠ 1 := by
    intro he
    have hsub : Subsingleton A := ⟨fun a b => hw (by simp [he])⟩
    have := Nat.card_eq_one_iff_unique.mpr ⟨hsub, inferInstance⟩
    omega
  let f : A → {v : W // v ≠ 1} := fun a => ⟨ρ a w, fun h => hw1 ((ρ a).injective
    (h.trans (map_one (ρ a)).symm))⟩
  have hf : Function.Bijective f := by
    apply (Nat.bijective_iff_injective_and_card f).mpr
    refine ⟨fun a b h => hw (congrArg Subtype.val h), ?_⟩
    let : Fintype W := Fintype.ofFinite W
    rw [Nat.card_eq_fintype_card (α := {v : W // v ≠ 1}),
      Fintype.card_subtype_compl,
      show Fintype.card {v : W // v = 1} = 1 from Fintype.card_unique,
      ← Nat.card_eq_fintype_card, hW, hA]
  obtain ⟨a, ha⟩ := hf.surjective ⟨x, hx⟩
  obtain ⟨b, hb⟩ := hf.surjective ⟨y, hy⟩
  have ha' : ρ a w = x := congrArg Subtype.val ha
  have hb' : ρ b w = y := congrArg Subtype.val hb
  refine ⟨b * a⁻¹, ?_, ?_⟩
  · change ρ (b * a⁻¹) x = y
    rw [map_mul, map_inv]
    change ρ b ((ρ a).symm x) = y
    rw [← ha', MulEquiv.symm_apply_apply, hb']
  · intro c hc
    apply (eq_mul_inv_iff_mul_eq).mpr
    apply hw
    change ρ (c * a) w = ρ b w
    rw [map_mul]
    change ρ c (ρ a w) = ρ b w
    rw [ha', hb', hc]

end Theory.GroupAction
