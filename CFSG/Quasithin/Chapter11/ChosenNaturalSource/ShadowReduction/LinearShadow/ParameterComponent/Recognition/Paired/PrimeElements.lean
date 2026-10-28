module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.FieldPower

/-!
# Prime-element form of the paired Cartan obstruction

The original odd Hall subgroup need not be assumed abelian for this local
calculation. Its intersection with L embeds in the literal L/O₂(L). Apply
11.0.4 to each cyclic prime-order subgroup to place its generator in L.
Compatible diagonal coordinates and a triangular semilinear intertwiner
then give one common field power on these elements.

A common power preserves every cyclic subgroup. A nonidentity Cauchy
element therefore cannot be carried into a disjoint conjugate factor.
This is an alternative to the mixed fixed-point calculation, avoiding its
extra square-centralizer premise. It does not construct the compatible
coordinates or assert that an arbitrary elementary-plane action is scalar.

Source: Aschbacher--Smith, 11.0.4 and 11.3.5(2), printed pp.760,771--772.
The literal source application is in PrimeExclusion; recognition and
coordinate construction stay with the parameter-component owner.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Matrix
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired
variable {G : Type*} [Group G] [Finite G]

/-- An odd subgroup meets the two-core trivially, so the literal quotient
is faithful on its intersection with L. No abelianness is needed. -/
theorem odd_intersection_quotient_injective (A L : Subgroup G)
    (hodd : Odd (Nat.card A)) :
    Function.Injective ((QuotientGroup.mk' (pCore 2 L)).comp
      (inclusion (show A ⊓ L ≤ L from inf_le_right))) := by
  have hd : Disjoint A (L.pCoreIn 2) := by
    obtain ⟨n,hn⟩ := (isPGroup_pCoreIn 2 L).exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hn]
    exact (Nat.coprime_two_right.mpr hodd).pow_right n
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro a ha
  apply mem_bot.mpr
  apply Subtype.ext
  have hx : inclusion (show A ⊓ L ≤ L from inf_le_right) a ∈ pCore 2 L :=
    (QuotientGroup.eq_one_iff _).mp ha
  exact disjoint_def.mp hd a.property.1 (mem_map_of_mem L.subtype hx)

/-- Apply the genuine preceding residual clauses to the cyclic subgroup
of a prime-order element. This does not assume that its odd overgroup is
abelian or that its p-core contains every element of order p. -/
theorem source_prime_order_mem
    {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (A : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (p : ℕ) (hp : p.Prime) (hd : p ∣ 2 ^ S.field.degree - 1)
    (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree))
    (hres : ∀ r : ℕ, r.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          r ∣ 2 ^ S.field.degree - 1 ∧ 3 < r) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          r ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual r (normalizer (L : Set G)) =
        L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    (x : G) (hx : x ∈ A) (ho : orderOf x = p) : x ∈ L := by
  let : Fact p.Prime := ⟨hp⟩
  have hC : zpowers x ≤ A := zpowers_le.mpr hx
  apply source_primeTorsion_le S (zpowers x) (hC.trans hA) p hp hd halt hres hcubic
  exact (mem_primeTorsion_iff (zpowers x) p x).mpr
    ⟨mem_zpowers x, ho ▸ pow_orderOf_eq_one x⟩

private theorem field_power {F : Type*} [Field F] [Finite F] [CharP F 2]
    (σ : F ≃+* F) : ∃ j : ℕ, ∀ x : F, σ x = x ^ (2 ^ j) := by
  let : Fintype F := Fintype.ofFinite F
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let σ' : F ≃ₐ[ZMod 2] F := AlgEquiv.ofRingEquiv (f := σ) (by
    intro x
    have h : σ.toRingHom.comp (algebraMap (ZMod 2) F) = algebraMap (ZMod 2) F :=
      RingHom.ext_zmod _ _
    exact DFunLike.congr_fun h x)
  obtain ⟨j,hj⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
    (ZMod 2) F).surjective σ'
  refine ⟨j,fun x => ?_⟩
  have hx := DFunLike.congr_fun hj x
  change (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F ^ (j : ℕ)) x = σ x at hx
  simpa only [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
    pow_iterate, ZMod.card] using hx.symm

/-- The same triangular semilinear marking gives one common field power
on all prime-order elements in the odd subgroup. Both sides are lifted
through the same injective map (A ∩ L) → L/O₂(L). -/
theorem prime_order_power_of_triangular
    {F ι : Type*} [Field F] [Finite F] [CharP F 2]
    [Fintype ι] [LinearOrder ι] [DecidableEq ι]
    (A L : Subgroup G) (hodd : Odd (Nat.card A)) (p : ℕ)
    (hL : ∀ x ∈ A, orderOf x = p → x ∈ L)
    (t : G) (htA : t ∈ normalizer (A : Set G)) (htL : t ∈ normalizer (L : Set G))
    (ρ : (L ⧸ pCore 2 L) →* Matrix ι ι F) (hρ : Function.Injective ρ)
    (σ : F ≃+* F) (g : Matrix ι ι F) (hg : g.IsUpperTriangular) (hdet : g.det ≠ 0)
    (hdiag : ∀ x : L, (x : G) ∈ A → orderOf (x : G) = p →
      ∃ d : ι → F, ρ (QuotientGroup.mk' (pCore 2 L) x) = diagonal d)
    (hint : ∀ x : L, (x : G) ∈ A → orderOf (x : G) = p →
      g * (ρ (QuotientGroup.mk' (pCore 2 L) x)).map σ =
        ρ (quotientConjugation L t htL (QuotientGroup.mk' (pCore 2 L) x)) * g) :
    ∃ j : ℕ, ∀ x ∈ A, orderOf x = p → t*x*t⁻¹ = x ^ (2 ^ j) := by
  obtain ⟨j,hj⟩ := field_power σ
  have hn : ∀ i, g i i ≠ 0 := by
    rw [det_of_isUpperTriangular hg, Finset.prod_ne_zero_iff] at hdet
    exact fun i => hdet i (Finset.mem_univ i)
  refine ⟨j, fun x hx ho => ?_⟩
  let a : L := ⟨x,hL x hx ho⟩
  let y : G := t*x*t⁻¹
  have hyA : y ∈ A := (htA x).mp hx
  have hyL : y ∈ L := (htL x).mp a.property
  have hyorder : orderOf y = p := ((MulAut.conj t).orderOf_eq x).trans ho
  let b : L := ⟨y,hyL⟩
  obtain ⟨d,hd⟩ := hdiag a hx ho
  obtain ⟨e,he⟩ := hdiag b hyA hyorder
  have he' : ρ (quotientConjugation L t htL (QuotientGroup.mk' (pCore 2 L) a)) =
      diagonal e := he
  have hi := hint a hx ho
  rw [hd,he',diagonal_map (map_zero σ)] at hi
  have hed : e = fun i => σ (d i) := by
    funext i
    apply mul_right_cancel₀ (hn i)
    have hii := congrArg (fun z : Matrix ι ι F => z i i) hi
    simp only [mul_diagonal,diagonal_mul] at hii
    exact hii.symm.trans (mul_comm _ _)
  have hquot : QuotientGroup.mk' (pCore 2 L) b =
      (QuotientGroup.mk' (pCore 2 L) a) ^ (2 ^ j) := by
    apply hρ
    rw [map_pow,he,hd,diagonal_pow,hed]
    congr 1
    funext i
    exact hj (d i)
  have heq : (⟨y,hyA,hyL⟩ : (A ⊓ L : Subgroup G)) = (⟨x,hx,a.property⟩ : (A ⊓ L : Subgroup G)) ^ (2 ^ j) :=
    odd_intersection_quotient_injective A L hodd (by
      change QuotientGroup.mk' (pCore 2 L) b = QuotientGroup.mk' (pCore 2 L) (a ^ (2 ^ j))
      rw [map_pow]
      exact hquot)
  exact congrArg Subtype.val heq

/-- A power action preserves the cyclic subgroup of a Cauchy element.
It cannot send that element to a disjoint conjugate factor. This argument
does not need a fixed point, abelianness of A, or an assertion about t². -/
theorem no_disjoint_factor_of_prime_order_power
    (A B : Subgroup G) (hBA : B ≤ A) (p : ℕ) (hp : p.Prime)
    (hpB : p ∣ Nat.card B) (t : G)
    (hd : Disjoint B (B.map (MulAut.conj t).toMonoidHom))
    (k : ℕ) (ha : ∀ x ∈ A, orderOf x = p → t*x*t⁻¹ = x ^ k) : False := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a,ho⟩ := exists_prime_orderOf_dvd_card' (G := B) p hpB
  have hoG : orderOf (a : G) = p := (orderOf_coe a).trans ho
  have hyB : t*(a : G)*t⁻¹ ∈ B := by
    rw [ha a (hBA a.property) hoG]
    exact B.pow_mem a.property k
  have hyC : t*(a : G)*t⁻¹ ∈ B.map (MulAut.conj t).toMonoidHom :=
    mem_map_of_mem _ a.property
  have he : t*(a : G)*t⁻¹ = 1 := disjoint_def.mp hd hyB hyC
  have ha1 : (a : G) = 1 := (MulAut.conj t).injective (he.trans (map_one _).symm)
  have hop : p = 1 := hoG.symm.trans (ha1 ▸ orderOf_one)
  exact hp.ne_one hop

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired
