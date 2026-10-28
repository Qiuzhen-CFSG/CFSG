module
public import Theory.Representation.SmallBinaryPrimeNormalizer.SupportedInvolution

/-!
# Cubic centralization by involutions on a quintic four-space

In a faithful binary action on sixteen elements, the product of two
involutions lies in a normal subgroup of order five. Conjugating one
involution by a normal cubic puts the same product in that cubic, so the
involution centralizes it.

For a larger module, restrict to the literal four-dimensional five-support.
Coprime decomposition makes the five-action faithful there. A fixed-free
normal cubic is also faithful on this nonzero support. Pass to the actual
image, apply the sixteen-point result, and lift through its exact kernel.
The fixed complement of the five-action is retained throughout.

Source: Aschbacher–Smith, 14.7.6, printed p.1045, using the small binary
normalizer calculation D.2.23–24, pp.189–190; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace SmallBinaryPrimeNormalizer
variable {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
  [IsElementaryAbelian 2 V] [MulDistribMulAction G V] [FaithfulSMul G V]

/-- A square-one element centralizes a normal cubic in a faithful sixteen-point
binary action with a normal five-subgroup. -/
theorem square_one_centralizes_normal_three
    (P B : Subgroup G) [P.Normal] [B.Normal]
    (hP : Nat.card P = 5) (hB : Nat.card B = 3) (hV : Nat.card V = 16)
    (t : G) (ht : t ^ 2 = 1) : t ∈ centralizer (B : Set G) := by
  by_cases ht1 : t = 1
  · simp [ht1]
  have hti : IsInvolution t := ⟨ht1,ht⟩
  have hdis : Disjoint P B := disjoint_of_coprime_natCard (by rw [hP,hB]; decide)
  intro b hb
  have hbi : IsInvolution (b * t * b⁻¹) := by
    constructor
    · intro he
      apply ht1
      simpa [mul_assoc] using
        congrArg (fun x => b⁻¹ * x * b) he
    · rw [conj_pow,ht]
      simp
  have hp : b * t * b⁻¹ * t ∈ P :=
    involution_mul_mem_five (V := V) P hP hV (b * t * b⁻¹) t hbi hti
  have hb' : b * t * b⁻¹ * t ∈ B := by
    have hconj := (inferInstance : B.Normal).conj_mem b⁻¹ (B.inv_mem hb) t
    have he : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ht)
    simpa only [mul_assoc,he] using B.mul_mem hb hconj
  have he : b * t * b⁻¹ * t = 1 := hdis.le_bot ⟨hp,hb'⟩
  have he' : b * t * b⁻¹ = t := by
    have hh := congrArg (fun x => x * t) he
    simpa only [mul_assoc,←pow_two,ht,mul_one,one_mul] using hh
  exact mul_inv_eq_iff_eq_mul.mp he'

/-- The same assertion on a normal five-support, retaining the full ambient
module and its fixed complement. -/
theorem square_one_centralizes_cubic_on_five_support
    (P B : Subgroup G) [P.Normal] [B.Normal]
    (hP : Nat.card P = 5) (hB : Nat.card B = 3)
    (hU : Nat.card (commutatorAction P V) = 16)
    (hfixed : FixedPoints.subgroup B V = ⊥)
    (t : G) (ht : t ^ 2 = 1) : t ∈ centralizer (B : Set G) := by
  let U := commutatorAction P V
  let invTop : IsInvariant (⊤ : Subgroup G) V U :=
    commutatorAction_isInvariant_of_normalizing_actor ⊤ P (by rw [normalizer_eq_top])
  let : IsInvariant G V U := ⟨fun g v =>
    invTop.invariant (⟨g,mem_top g⟩ : (⊤ : Subgroup G)) v⟩
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective U.subtype U.subtype_injective
  let φ : G →* MulAut U := MulDistribMulAction.toMulAut G U
  let q := φ.rangeRestrict
  have hcop : Nat.Coprime (Nat.card P) (Nat.card V) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hP,hn]
    exact (by decide : Nat.Coprime 5 2).pow_right n
  have hinjP : Function.Injective (q.comp P.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro p hp
    apply Subtype.ext
    apply ActionSupport.eq_one_of_fixes_support P hcop p
    intro v hv
    have hh : φ p = 1 := congrArg Subtype.val hp
    exact congrArg Subtype.val (congrArg (fun f : MulAut U => f ⟨v,hv⟩) hh)
  have hinjB : Function.Injective (q.comp B.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro b hb
    by_contra hne
    have hz : U = ⊥ := by
      apply bot_unique
      intro v hv
      apply hfixed.le
      intro c
      obtain ⟨n,hn⟩ := mem_zpowers_iff.mp
        (show c ∈ zpowers b from mem_zpowers_of_prime_card hB hne)
      have hbφ : φ b = 1 := congrArg Subtype.val hb
      have hcφ : φ c = 1 := by
        rw [←hn]
        change φ ((b : G) ^ n) = 1
        rw [map_zpow,hbφ,one_zpow]
      exact congrArg Subtype.val (congrArg (fun f : MulAut U => f ⟨v,hv⟩) hcφ)
    have hcard : Nat.card U = 16 := hU
    rw [hz,card_bot] at hcard
    omega
  have hPmap : Nat.card (P.map q) = 5 := by
    simpa only [MonoidHom.range_comp,range_subtype] using
      (Nat.card_congr (MonoidHom.ofInjective hinjP).toEquiv).symm.trans hP
  have hBmap : Nat.card (B.map q) = 3 := by
    simpa only [MonoidHom.range_comp,range_subtype] using
      (Nat.card_congr (MonoidHom.ofInjective hinjB).toEquiv).symm.trans hB
  let : (P.map q).Normal := Normal.map inferInstance q φ.rangeRestrict_surjective
  let : (B.map q).Normal := Normal.map inferInstance q φ.rangeRestrict_surjective
  have hc := square_one_centralizes_normal_three (V := U)
    (P.map q) (B.map q) hPmap hBmap hU (q t) (by rw [←map_pow,ht,map_one])
  intro b hb
  have hconj : t * b * t⁻¹ ∈ B := (inferInstance : B.Normal).conj_mem b hb t
  have he : q (t * b * t⁻¹) = q b := by
    rw [map_mul,map_mul,map_inv]
    exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp hc) _ (mem_map_of_mem q hb)).symm
  have hb' : (⟨t * b * t⁻¹,hconj⟩ : B) = ⟨b,hb⟩ := hinjB he
  exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hb')).symm

end SmallBinaryPrimeNormalizer
