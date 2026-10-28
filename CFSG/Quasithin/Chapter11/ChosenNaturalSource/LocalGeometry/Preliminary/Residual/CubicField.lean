module
public import Theory.Representation.SL3OddNaturalNormalizer
public import Theory.Representation.FiniteFieldSemilinearDisplacement.Descent
public import Theory.SpecificGroups.PSL3.SplitPrimeRank
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# Cubic field actors on a natural SL₃ constituent

A cubic coefficient action has a fixed basis by finite semilinear descent.
In those coordinates, the SL₃ group over the fixed field centralizes the
original cubic. Its three-rank is at least two, since the fixed-field unit
order is divisible by three. The independent cubic then forces rank three.
This works with the entire special linear group and its scalar center.

Source: the natural-module argument of Aschbacher--Smith A.3.19, printed
pp.54--55, used for 11.0.4, printed p.760. The consumer is CubicNatural.
-/

public noncomputable section
open Subgroup Matrix Theory.GroupTheory Module
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.CubicNatural
variable {F H : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
    [Group H] [Finite H]
open Representation.SL3OddNaturalNormalizer

omit [Algebra (ZMod 2) F] in
private theorem fixed_units_three_dvd (σ : F ≃+* F) (hσ : orderOf σ = 3)
    (hd : 3 ∣ Nat.card F - 1) :
    3 ∣ Nat.card (FixedPoints.subfield (zpowers σ) F) - 1 := by
  have hP : IsPGroup 3 (zpowers σ) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hσ, pow_one])
  have hc := hP.card_modEq_card_fixedPoints F
  change Nat.card F ≡ Nat.card (FixedPoints.subfield (zpowers σ) F) [MOD 3] at hc
  exact Nat.modEq_zero_iff_dvd.mp ((Nat.ModEq.sub_right
    (Nat.card_pos (α := F)) (Nat.card_pos (α := FixedPoints.subfield (zpowers σ) F))
    hc).symm.trans hd.modEq_zero_nat)

omit [Finite F] [Algebra (ZMod 2) F] in
private theorem cyclic_field_injective (φ : H →* (F ≃+* F)) (x : H)
    (hx : orderOf x = 3) (hφ : orderOf (φ x) = 3) :
    Function.Injective (φ.comp (zpowers x).subtype) := by
  classical
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro a ha
  obtain ⟨k,hk,he⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp a.property)
  have hk' : k < orderOf x := Finset.mem_range.mp hk
  have hmap : (φ x)^k = 1 := by rw [← map_pow, he]; exact ha
  have hdiv := orderOf_dvd_of_pow_eq_one hmap
  rw [hφ] at hdiv
  have hk0 : k = 0 := by rw [hx] at hk'; omega
  apply Subtype.ext
  change (a : H) = 1
  rw [← he,hk0,pow_zero]

/-- A cubic with nontrivial coefficient action in a faithful natural overgroup
forces cubic rank at least three, retaining the full SL₃ scalar center. -/
theorem three_le_rank_of_cubic_field
    (L : Subgroup H) [L.Normal] (e : L ≃* SL(3,F))
    (ρ : Representation (ZMod 2) H (Fin 3 → F)) (hf : Function.Injective ρ)
    (hnat : ∀ (g : L) (v : Fin 3 → F), ρ (g : H) v = (e g).val.mulVec v)
    (hd : 3 ∣ Nat.card F - 1) (x : H) (hx : orderOf x = 3)
    (hfield : fieldAction ρ (normalizer_semilinear L e ρ hnat) x ≠ 1) :
    3 ≤ primeRank 3 H := by
  classical
  let hsemi := normalizer_semilinear L e ρ hnat
  let φ := fieldAction ρ hsemi
  let σ := φ x
  have hσ : orderOf σ = 3 := orderOf_eq_prime (by
    change φ x ^ 3 = 1
    rw [← map_pow, show x ^ 3 = 1 from hx ▸ pow_orderOf_eq_one x, map_one]) hfield
  let P := zpowers x
  let : Fintype P := Fintype.ofFinite P
  obtain ⟨s,b,hb⟩ := Representation.FiniteFieldSemilinearDisplacement.Descent.exists_fixed_basis
    (ρ.comp P.subtype) (φ.comp P.subtype) (cyclic_field_injective φ x hx hσ)
    (fun g a v => fieldAction_smul ρ hsemi g a v)
  let : Finite s := Module.Finite.finite_basis b
  let : Fintype s := Fintype.ofFinite s
  have hs : Fintype.card s = Fintype.card (Fin 3) := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_pi]
  let b' := b.reindex (Fintype.equivOfCardEq hs)
  let c : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F) := b'.equivFun.symm
  have hcoord (v : Fin 3 → F) : ρ x (c v) = c (fun i => σ (v i)) := by
    simp only [c, Basis.equivFun_symm_apply, map_sum]
    congr 1
    funext i
    rw [fieldAction_smul ρ hsemi]
    rw [show ρ x (b' i) = b' i by
      simpa only [b',Basis.reindex_apply,MonoidHom.comp_apply,Subgroup.subtype_apply] using
        hb ((Fintype.equivOfCardEq hs).symm i) ⟨x,mem_zpowers x⟩]
  let C : GL (Fin 3) F := GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv c)
  have hC (v : Fin 3 → F) : C.val.mulVec v = c v := by
    change (GeneralLinearGroup.toLin C : Module.End F (Fin 3 → F)) v = _
    rw [GeneralLinearGroup.toLin.apply_symm_apply]
    rfl
  let E := FixedPoints.subfield (zpowers σ) F
  let f : SL(3,E) →* H := L.subtype.comp (e.symm.toMonoidHom.comp
    ((Matrix.PSL3.OuterSolvable.linearConjSL F C).toMonoidHom.comp
      (SpecialLinearGroup.map E.subtype)))
  have hf0 : Function.Injective (SpecialLinearGroup.map E.subtype (n := Fin 3)) := by
    intro a b hab
    apply Subtype.ext
    ext i j
    exact congrArg (fun g : SL(3,F) => g.val i j) hab
  have hfi : Function.Injective f := L.subtype_injective.comp
    (e.symm.injective.comp ((Matrix.PSL3.OuterSolvable.linearConjSL F C).injective.comp hf0))
  have hfact (a : SL(3,E)) (v : Fin 3 → F) :
      ρ (f a) (c v) = c ((a.val.map E.subtype).mulVec v) := by
    rw [show f a = (e.symm (Matrix.PSL3.OuterSolvable.linearConjSL F C
      (SpecialLinearGroup.map E.subtype a)) : L) from rfl, hnat,e.apply_symm_apply]
    rw [← hC,← hC,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec]
    congr 1
    have hh := congrArg (fun A : GL (Fin 3) F => (A * C).val)
      (Matrix.PSL3.OuterSolvable.linearConjSL_toGL F C (SpecialLinearGroup.map E.subtype a))
    simp only [mul_assoc,inv_mul_cancel,mul_one,GeneralLinearGroup.coe_mul,
      SpecialLinearGroup.coe_GL_coe_matrix] at hh
    convert hh using 1
    congr 1
  have hfix (a : SL(3,E)) : Commute (f a) x := by
    apply hf
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := c.surjective w
    simp only [map_mul,Module.End.mul_apply]
    rw [hcoord,hfact,hfact,hcoord]
    congr 1
    ext i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun t : F => t * σ (v j))
      ((a.val i j).property ⟨σ,mem_zpowers σ⟩).symm
  have hL : L ≤ φ.ker := by
    intro g hg
    apply (fieldAction_eq_one_iff ρ hsemi g).mpr
    intro a v
    change ρ (⟨g,hg⟩ : L) (a • v) = a • ρ (⟨g,hg⟩ : L) v
    rw [hnat,hnat,Matrix.mulVec_smul]
  have hxL : x ∉ L := fun hxL => hfield (hL hxL)
  have hdj : Disjoint f.range (zpowers x) :=
    f.range.disjoint_zpowers_of_prime_order_not_mem x hx (by
      rintro ⟨a,ha⟩
      exact hxL (ha ▸ (e.symm _).property))
  have hr : 2 ≤ primeRank 3 f.range := by
    rw [← primeRank_equiv 3 (MonoidHom.ofInjective hfi)]
    exact Matrix.PSL3.SplitPrimeRank.special_rank E (fixed_units_three_dvd σ hσ hd)
  have hc : f.range ≤ centralizer (zpowers x : Set H) := by
    rintro _ ⟨a,rfl⟩
    have hm : zpowers x ≤ centralizer ({f a} : Set H) :=
      zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hfix a).eq.symm)
    intro y hy
    exact mem_centralizer_singleton_iff.mp (hm hy)
  have hsum := primeRank_sup_eq_add_of_disjoint_commuting f.range (zpowers x) hdj hc 3
  have hbound := Theory.GroupTheory.primeRank_le_of_injective 3 (f.range ⊔ zpowers x : Subgroup H).subtype
    (f.range ⊔ zpowers x : Subgroup H).subtype_injective
  have hxp : 1 ≤ primeRank 3 (zpowers x) := by
    by_contra hn
    have hz : primeRank 3 (zpowers x) = 0 := by omega
    exact PrimeRank.eq_zero_iff_not_dvd_card.mp hz (by rw [Nat.card_zpowers,hx])
  omega

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.CubicNatural
