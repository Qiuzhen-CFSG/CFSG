module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourNilpotent
public import Theory.ElementaryAbelian.AutomorphismLinearModel
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The extraspecial radical at the Hermitian four-space

An equivariant image of a Xi radical is trivial or has order divisible by
p². Indeed, irreducibility puts its kernel inside the preimage of the
Frattini subgroup unless that kernel covers the Frattini quotient. In the
latter case Frattini nongeneration and two-perfectness kill the whole image.
Both elementary and extraspecial Xi quotients have Frattini quotient of
order p². Since p² does not divide |GL₄(2)| for p > 3, every such radical
normalizing the canonical four-space centralizes it.

This proves the centralization step needed for the extraspecial case of
8.2.7 with the full two-core retained. The Chapter 12 consumer applies it to
the original containing component on both tensor branches and constructs
the actual cyclic center of each escaping odd Sylow supplement. Placement
of that center in the original normalizer, and the final odd-normalizer
contradiction, remain to be established.

Source: Aschbacher--Smith, 1.3.1--3 and the extraspecial paragraph of 8.2.7,
printed pp.508--509,718, refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open Chapter1 Chapter1.Section02
variable {G : Type*} [Group G] [Finite G]

private theorem odd_frattini_card {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} [Fact p.Prime] (hq : XiOddQuotient p Q) :
    Nat.card (Q ⧸ frattini Q) = p^2 := by
  rcases hq with ⟨he,hc⟩ | ⟨he,hc,_⟩
  · let := he
    let : Fact (IsPGroup p Q) := ⟨he.isPGroup⟩
    exact (Nat.card_congr (frattiniQuotientEquivOfIsElementaryAbelian (p := p)).toEquiv).trans hc
  · let := he
    rw [IsExtraspecial.frattini_eq_center (p := p)]
    have hh := card_eq_card_quotient_mul_card_subgroup (center Q)
    rw [hc,IsExtraspecial.center_order_p p Q] at hh
    have hp := (Fact.out : p.Prime).pos
    nlinarith [pow_succ p 2]

/-- An equivariant image of a Xi radical is trivial or has order divisible by p². -/
theorem xi_image_card_dichotomy
    {T X J : Subgroup G} (hX : XiMember T X) (hXJ : X ≤ J) (hTJ : T ≤ J)
    {p : ℕ} [Fact p.Prime] (hq : XiOddQuotient p (XiQuotient X))
    {D : Type*} [Group D] [Finite D] (f : J →* D) :
    X.subgroupOf J ≤ f.ker ∨ p^2 ∣ Nat.card D := by
  let k := f.comp (inclusion hXJ)
  let q := QuotientGroup.mk' (pCore 2 X)
  let r := QuotientGroup.mk' (frattini (XiQuotient X))
  let A := (k.ker.map q).map r
  have hstable : ∀ t : T, ∀ a ∈ A, xiFrattiniAction T X hX.invariant t a ∈ A := by
    rintro t a ⟨b,⟨x,hx,rfl⟩,rfl⟩
    let z : X := ⟨(t : G)*x*(t : G)⁻¹,
      (mem_normalizer_iff.mp (hX.invariant t.property) x).mp x.property⟩
    have hz : z ∈ k.ker := by
      change f ((⟨t,hTJ t.property⟩ : J) * inclusion hXJ x * (⟨t,hTJ t.property⟩ : J)⁻¹) = 1
      have hx' : f (inclusion hXJ x) = 1 := hx
      simp only [map_mul,map_inv,hx',mul_one,mul_inv_cancel]
    refine ⟨q z,⟨z,hz,rfl⟩,?_⟩
    simp only [r,q,xiFrattiniAction,MonoidHom.comp_apply,quotientAut_apply_mk]
    rfl
  rcases hX.irreducible A hstable with hb | ht
  · right
    have hk : k.ker ≤ (r.comp q).ker := by
      intro x hx
      exact mem_bot.mp (hb ▸ mem_map_of_mem r (mem_map_of_mem q hx))
    have hs : Function.Surjective (r.comp q) :=
      (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
    have hc : (r.comp q).ker.index = p^2 := by
      rw [index_ker,MonoidHom.range_eq_top.mpr hs]
      exact (Nat.card_congr topEquiv.toEquiv).trans (odd_frattini_card hq)
    rw [←hc]
    exact (index_dvd_of_le hk).trans ((index_ker k) ▸ card_subgroup_dvd_card k.range)
  · left
    have hI : k.ker.map q = ⊤ := by
      apply frattini_nongenerating
      have hh := congrArg (comap r) ht
      simpa only [A,comap_map_eq,r,QuotientGroup.ker_mk',comap_top] using hh
    have hgen : k.ker ⊔ pCore 2 X = ⊤ := by
      have hh := congrArg (comap q) hI
      simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using hh
    have htwo : IsPGroup 2 (X ⧸ k.ker) :=
      isPGroup_quotient_of_sup_eq_top _ _ pCore_isPGroup hgen
    have hk : k.ker = ⊤ := hX.perfect _ inferInstance htwo
    intro x hx
    exact show (⟨x,hx⟩ : X) ∈ k.ker from hk ▸ mem_top _

private theorem prime_sq_not_dvd_GL_four {p : ℕ} [Fact p.Prime] (hp : 3 < p) :
    ¬ p^2 ∣ 20160 := by
  have hprime : p.Prime := Fact.out
  intro hd
  have hd' : p ∣ 20160 := dvd_trans (dvd_pow_self p (by decide : 2 ≠ 0)) hd
  have hp' : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    have hf : 20160 = 2^6*3^2*5*7 := by norm_num
    rw [hf] at hd'
    rcases hprime.dvd_mul.mp hd' with hd' | hd'
    · rcases hprime.dvd_mul.mp hd' with hd' | hd'
      · rcases hprime.dvd_mul.mp hd' with hd' | hd'
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp (hprime.dvd_of_dvd_pow hd'))
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_three).mp (hprime.dvd_of_dvd_pow hd')))
      · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hprime (by norm_num)).mp hd')))
    · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hprime (by norm_num)).mp hd')))
  rcases hp' with rfl | rfl | rfl | rfl <;> norm_num at hd <;> omega

/-- Both kinds of odd Xi radical centralize any normalized binary four-space. -/
theorem xi_radical_centralizes_four_space
    {T X U : Subgroup G} [IsElementaryAbelian 2 U]
    (hX : XiMember T X) (hTU : T ≤ normalizer (U : Set G))
    (hXU : X ≤ normalizer (U : Set G)) (hU : rank U = 4)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hq : XiOddQuotient p (XiQuotient X)) :
    X ≤ centralizer (U : Set G) := by
  let J := normalizer (U : Set G)
  let f : J →* MulAut U := normalizerMonoidHom U
  have hcard : Nat.card U = 2^4 := by
    obtain ⟨a,ha⟩ := (IsElementaryAbelian.isPGroup 2 U).exists_card_eq
    rw [rank,ha,Nat.log_pow Nat.one_lt_two] at hU
    simpa only [hU] using ha
  let e := IsElementaryAbelian.mulAutLinearEquivOfCard U hcard
  have haut : Nat.card (MulAut U) = 20160 := by
    rw [Nat.card_congr e.toEquiv,Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ]
  have hk : X.subgroupOf J ≤ f.ker :=
    (xi_image_card_dichotomy hX hXU hTU hq f).resolve_right
      (by rw [haut]; exact prime_sq_not_dvd_GL_four hp)
  intro x hx
  apply mem_centralizer_iff.mpr
  intro u hu
  have hkx : (⟨x,hXU hx⟩ : J) ∈ f.ker := hk hx
  have hh := congrArg (fun a : MulAut U => (a ⟨u,hu⟩ : G)) hkx
  change x*u*x⁻¹=u at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

omit [Finite G] in
/-- The actual center of an escaping extraspecial supplement is a nontrivial
cyclic odd subgroup in C_G(U), with a normalizer escaping N_G(L). This does
not assume that the center has already been placed in N_G(L) or C_G(V). -/
theorem extraspecial_supplement_center_escape
    {U Y M : Subgroup G} {p : ℕ} [Fact p.Prime] [IsExtraspecial p Y]
    (hYU : Y ≤ centralizer (U : Set G)) (hout : ¬ Y ≤ M) :
    let Z := (center Y).map Y.subtype
    Nat.card Z = p ∧ IsCyclic Z ∧ Z ≠ ⊥ ∧ Z ≤ centralizer (U : Set G) ∧
      Y ≤ normalizer (Z : Set G) ∧ ¬ normalizer (Z : Set G) ≤ M := by
  let Z := (center Y).map Y.subtype
  have hc : Nat.card Z = p :=
    (Nat.card_congr ((center Y).equivMapOfInjective Y.subtype Y.subtype_injective).toEquiv).symm.trans
      (IsExtraspecial.center_order_p p Y)
  have hne : Z ≠ ⊥ := by
    intro hz
    have hone : Nat.card Z = 1 := (eq_bot_iff_card Z).mp hz
    exact (Fact.out : p.Prime).ne_one (hc.symm.trans hone)
  have hn : Y ≤ normalizer (Z : Set G) :=
    Y.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Y (center Y))
  exact ⟨hc,isCyclic_of_prime_card hc,hne,(map_subtype_le _).trans hYU,hn,
    fun h => hout (hn.trans h)⟩

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
