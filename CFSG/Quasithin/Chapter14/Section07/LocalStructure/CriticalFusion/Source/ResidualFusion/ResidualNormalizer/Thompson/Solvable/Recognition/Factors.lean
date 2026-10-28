module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Application.Source
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.NormalSymmetricThreePairRank.Inner
public import Theory.GroupTheory.SymmetricThreeTwoCore

/-!
# One marked exceptional factor at three-rank one

The noncentral B.2.16 alternative supplies a nonempty family of actual
PSL₂(2) factors. Two coordinates give an embedding S₃ × S₃, which violates
three-rank at most one. The unique marked factor therefore identifies the
Thompson image with S₃. A separate elementary extension lemma shows that
a two-reduced two-extension of a normal S₃ is itself S₃: all automorphisms
of S₃ are inner, and the complementary centralizer is a normal two-group.

These facts are applied to the literal centralizer quotient in Recognition.
Source: Aschbacher–Smith, B.2.16, printed p.79, as used in 14.7.67(4),
printed p.1070, combined manuscript of 1 March 2004.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.ResidualThompsonRecognition
open Chapter1.RadicalNormalizers.ThompsonSource Theory.GroupTheory
universe u
variable {A : Type u} [Group A] [Finite A] {S : Sylow 2 A}
  [IsElementaryAbelian 2 (closure S)]
local notation "S3" => Equiv.Perm (Fin 3)

/-- The actual PSL₂(2) marking, followed by the SL₂(2) and S₃ comparisons. -/
noncomputable def factorEquiv (ex : Exceptional S) (i : Fin ex.count) : ex.factor i ≃* S3 :=
  (ex.factorModel i).trans (Matrix.SpecialLinearGroup.sl2TwoEquivPSL2Two.symm.trans
    (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three))

private theorem three_rank_S3_pos : 0 < primeRank 3 S3 := by
  have hc : Nat.card S3 = 6 := by rw [Nat.card_perm, Nat.card_fin]; decide
  have hn : primeRank 3 S3 ≠ 0 := by
    intro h
    have hd := PrimeRank.eq_zero_iff_not_dvd_card.mp h
    rw [hc] at hd
    exact hd (by decide)
  omega

/-- Nonemptiness and the three-rank bound leave exactly one factor. -/
theorem exceptional_count_eq_one (ex : Exceptional S)
    (hr : primeRank 3 (CentralQuotient (closure S)) ≤ 1) : ex.count = 1 := by
  classical
  have hpos : 0 < ex.count := by
    obtain ⟨i⟩ := ex.nonempty_factors
    exact Nat.zero_lt_of_lt i.isLt
  by_contra hn
  have htwo : 2 ≤ ex.count := by omega
  let f : S3 × S3 →* ((i : Fin ex.count) → ex.factor i) := {
    toFun := fun x i => if i.val = 0 then (factorEquiv ex i).symm x.1
      else if i.val = 1 then (factorEquiv ex i).symm x.2 else 1
    map_one' := by funext i; split_ifs <;> simp
    map_mul' := by intro x y; funext i; split_ifs <;> simp_all }
  have hf : Function.Injective f := by
    intro x y h
    apply Prod.ext
    · have he := congrArg (fun z => factorEquiv ex ⟨0, by omega⟩ (z ⟨0, by omega⟩)) h
      simpa [f] using he
    · have he := congrArg (fun z => factorEquiv ex ⟨1, by omega⟩ (z ⟨1, by omega⟩)) h
      simpa [f] using he
  let g := (Subgroup.subtype _).comp (ex.groupProduct.toMonoidHom.comp f)
  have hg : Function.Injective g := Subtype.val_injective.comp (ex.groupProduct.injective.comp hf)
  have h := (Theory.GroupTheory.primeRank_le_of_injective 3 g hg).trans hr
  rw [primeRank_prod_eq_add] at h
  have hp := three_rank_S3_pos
  omega

/-- The marked single factor gives an actual symmetric-three equivalence. -/
noncomputable def exceptionalThompsonEquiv (ex : Exceptional S)
    (hr : primeRank 3 (CentralQuotient (closure S)) ≤ 1) :
    ((Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup A)).map (starMap (closure S))) ≃* S3 := by
  let : Unique (Fin ex.count) := by rw [exceptional_count_eq_one ex hr]; infer_instance
  exact ex.groupProduct.symm.trans ((MulEquiv.piUnique (fun i => ex.factor i)).trans
    (factorEquiv ex default))


omit [Finite A] [IsElementaryAbelian 2 (closure S)] in
/-- A reduced two-extension of a normal S₃ is already that S₃. -/
theorem normal_symmetricThree_eq_top (N : Subgroup A) [N.Normal]
    (e : N ≃* S3) (hp : IsPGroup 2 (A ⧸ N)) (hcore : pCore 2 A = ⊥) : N = ⊤ := by
  let C := centralizer (N : Set A)
  have hNC : ∀ x : A, x ∈ N → x ∈ C → x = 1 := by
    intro x hx hc
    have he : e ⟨x, hx⟩ = 1 := by
      apply NormalSymmetricThreePairRank.symmetricThree_center_trivial
      intro y
      obtain ⟨n, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext (hc n n.property))
    exact congrArg Subtype.val (e.injective (he.trans e.map_one.symm))
  let f := (QuotientGroup.mk' N).comp C.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    have hxN : x.val ∈ N := (QuotientGroup.eq_one_iff _).mp hx
    exact Subtype.ext (hNC x hxN x.property)
  have hC : C ≤ pCore 2 A := le_sSup ⟨inferInstance,
    hp.of_injective f hf⟩
  rw [hcore] at hC
  apply top_unique
  intro a _
  let α : MulAut S3 := e.symm.trans ((MulAut.conjNormal a).trans e)
  obtain ⟨k, hk⟩ := NormalSymmetricThreePairRank.symmetricThree_aut_inner α
  let n := e.symm k
  have ha : ∀ x : N, a * x * a⁻¹ = (n * x * n⁻¹ : N) := by
    intro x
    change ((MulAut.conjNormal a x : N) : A) = _
    apply congrArg (fun z : N => (z : A))
    apply e.injective
    have hx := DFunLike.congr_fun hk (e x)
    simpa [α, n, MulAut.conj_apply] using hx
  have hac : (n : A)⁻¹ * a ∈ C := by
    intro x hx
    have hh := congrArg (fun z : A => (n : A)⁻¹ * z * a) (ha ⟨x, hx⟩)
    simpa [mul_assoc] using hh.symm
  have he : (n : A)⁻¹ * a = 1 := hC hac
  have han : a = n := by simpa using (inv_mul_eq_one.mp he).symm
  exact han.symm ▸ n.property

end CFSG.Quasithin.Chapter14.Section07.ResidualThompsonRecognition
