module
public import Theory.SpecificGroups.Janko4.Model.SevenNormalizers
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient
public import Theory.GroupTheory.CoprimeSubgroupCentralizer
import Mathlib.Tactic

/-!
# A proved lower bound and the remaining upper bound for J4 seven-centralizers

The literal max4 subgroup maps onto S5 × SL3(2) with two-group kernel.
Lift a cyclic seven-subgroup of the second factor. Coprime centralizer
lifting covers S5 × C7, so 840 divides its centralizer order upstairs.
The native J4 order has only one factor of seven; Sylow conjugacy therefore
transfers this divisibility to every element of order seven.

Consequently an ambient centralizer bound below 3360 suffices for
nonreality: its order is 840, 1680 or 2520, and the Sylow normalizer
congruence modulo 49 forces the conjugation image to have odd order.
The full binary point automizers contain real sevens, so cannot occur as
two-core quotients of subgroups once this bound is supplied.

The upper bound is NOT proved here. The actual centralizer is expected
to have order 840; the source application only needs the weaker strict
bound. No local-to-ambient centralizer identification is assumed.
Source: ATLAS J4 classes 7A--7B and the literal max4 subgroup program,
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/J4/ (20 October 2026);
Aschbacher--Smith 12.1.1, printed p.788.
-/

public noncomputable section
open Subgroup
namespace Janko4.SevenCentralizerBounds
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
open Janko4.LocalStructure.SymmetricLinear

private theorem exists_local_seven : ∃ x : max4Subgroup, orderOf x = 7 ∧
    840 ∣ Nat.card (centralizer (zpowers x : Set max4Subgroup)) := by
  obtain ⟨y,hy⟩ := exists_prime_orderOf_dvd_card'
    (G := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) 7
    (by rw [Atlas.Comparisons.Exceptional.sl3Two_card]; decide)
  let z : QuotientModel := (1,y)
  have hz : orderOf z = 7 := by
    apply orderOf_eq_prime
    · apply Prod.ext
      · simp [z]
      · exact hy ▸ pow_orderOf_eq_one y
    · intro he
      have hy1 : y = 1 := congrArg Prod.snd he
      simp [hy1] at hy
  let D := zpowers z
  let : IsElementaryAbelian 7 D := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := by
      rw [←hz,←Nat.card_zpowers]
      exact Group.exponent_dvd_nat_card }
  have hk : Nat.Coprime 7 (Nat.card max4Projection.ker) := by
    obtain ⟨m,hm⟩ := max4Projection_kernel_isTwoGroup.exists_card_eq
    rw [hm]
    exact (by decide : Nat.Coprime 7 2).pow_right m
  obtain ⟨A,hA,hm,hc⟩ := exists_elementaryAbelian_map_eq_of_surjective_coprime
    max4Projection max4Projection_surjective hk D
  let := hA
  have hcA : Nat.card A = 7 := by rw [hc,Nat.card_zpowers,hz]
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := A) 7 (by rw [hcA])
  have hx' : orderOf (x : max4Subgroup) = 7 := by rw [Subgroup.orderOf_coe]; exact hx
  have hAC : centralizer (A : Set max4Subgroup) ≤
      centralizer (zpowers (x : max4Subgroup) : Set max4Subgroup) :=
    centralizer_le (zpowers_le.mpr x.property)
  have hB : (⊤ : Subgroup (Equiv.Perm (Fin 5))).prod (zpowers y) ≤
      centralizer (D : Set QuotientModel) := by
    rintro ⟨s,t⟩ ⟨_,ht⟩ a ⟨k,rfl⟩
    obtain ⟨j,rfl⟩ := ht
    change (1,y)^k * (s,y^j) = (s,y^j) * (1,y)^k
    ext <;> simp [zpow_mul_comm]
  have hcB : Nat.card ((⊤ : Subgroup (Equiv.Perm (Fin 5))).prod (zpowers y)) = 840 := by
    rw [Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod,card_top,Nat.card_zpowers,hy]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hd : 840 ∣ Nat.card (centralizer (D : Set QuotientModel)) :=
    hcB ▸ card_dvd_of_le hB
  have he := map_centralizer_eq_of_isPGroup_of_surjective_coprime 7 A (IsElementaryAbelian.isPGroup 7 A)
    max4Projection max4Projection_surjective hk
  rw [hm] at he
  have hd' : Nat.card (centralizer (D : Set QuotientModel)) ∣
      Nat.card (centralizer (A : Set max4Subgroup)) := by
    rw [←he]
    exact card_map_dvd _ _
  exact ⟨x,hx',hd.trans (hd'.trans (card_dvd_of_le hAC))⟩

/-- All cyclic seven-subgroups are Sylow, so their centralizers have equal order. -/
theorem centralizer_card_eq (x y : Janko4.Model)
    (hx : orderOf x = 7) (hy : orderOf y = 7) :
    Nat.card (centralizer (zpowers x : Set Janko4.Model)) =
      Nat.card (centralizer (zpowers y : Set Janko4.Model)) := by
  have hs : ¬7^2 ∣ Nat.card Janko4.Model := by rw [Janko4.Cardinality.model_card]; norm_num
  obtain ⟨k,g,he⟩ := Janko4.Simplicity.exists_conjugate_pow_of_prime_sq_not_dvd
    (by decide : Nat.Prime 7) hs hx hy
  have hle : zpowers y ≤ (zpowers x).map (MulAut.conj g).toMonoidHom := by
    apply zpowers_le.mpr
    exact ⟨x^k,pow_mem (mem_zpowers x) k,he.symm⟩
  have heq : zpowers y = (zpowers x).map (MulAut.conj g).toMonoidHom :=
    eq_of_le_of_card_ge hle (by
      rw [card_map_of_injective (MulAut.conj g).injective,Nat.card_zpowers,Nat.card_zpowers,hx,hy])
  have hmap : centralizer (zpowers y : Set Janko4.Model) =
      (centralizer (zpowers x : Set Janko4.Model)).map (MulAut.conj g).toMonoidHom := by
    rw [heq]
    apply le_antisymm
    · intro t ht
      refine ⟨(MulAut.conj g).symm t,?_,(MulAut.conj g).apply_symm_apply t⟩
      intro q hq
      apply (MulAut.conj g).injective
      simpa only [map_mul, MulEquiv.apply_symm_apply] using
        ht (MulAut.conj g q) (mem_map_of_mem _ hq)
    · exact map_centralizer_le_centralizer_image _ _
  rw [hmap,card_map_of_injective (MulAut.conj g).injective]

/-- The certified S5 × SL3(2) quotient forces 840 to divide every native
seven-centralizer order. No ambient centralizer upper bound is assumed. -/
theorem seven_centralizer_divisible (x : Janko4.Model) (hx : orderOf x = 7) :
    840 ∣ Nat.card (centralizer (zpowers x : Set Janko4.Model)) := by
  obtain ⟨y,hy,hc⟩ := exists_local_seven
  have hle : (centralizer (zpowers y : Set max4Subgroup)).map max4Subgroup.subtype ≤
      centralizer (zpowers (y : Janko4.Model) : Set Janko4.Model) := by
    have hh := map_centralizer_le_centralizer_image
      (zpowers y : Set max4Subgroup) max4Subgroup.subtype
    change _ ≤ centralizer ((zpowers y).map max4Subgroup.subtype : Set Janko4.Model) at hh
    simpa only [MonoidHom.map_zpowers,Subgroup.subtype_apply] using hh
  have hd := card_dvd_of_le hle
  rw [card_map_of_injective max4Subgroup.subtype_injective] at hd
  have hy' : orderOf (y : Janko4.Model) = 7 := by rw [Subgroup.orderOf_coe]; exact hy
  rw [←centralizer_card_eq (y : Janko4.Model) x hy' hx]
  exact hc.trans hd

/-- Below 3360, the normalizer's conjugation image has order one or three. -/
theorem normalizer_image_card_of_centralizer_lt
    (x : Janko4.Model) (hx : orderOf x = 7)
    (hc : Nat.card (centralizer (zpowers x : Set Janko4.Model)) < 3360) :
    Nat.card (zpowers x).normalizerMonoidHom.range = 1 ∨
      Nat.card (zpowers x).normalizerMonoidHom.range = 3 := by
  let P := zpowers x
  have hk : Nat.card P.normalizerMonoidHom.ker =
      Nat.card (centralizer (zpowers x : Set Janko4.Model)) := by
    rw [normalizerMonoidHom_ker,
      Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (P : Set Janko4.Model))).toEquiv]
  have hd : Nat.card P.normalizerMonoidHom.range ∣ 6 := by
    have h := P.normalizerMonoidHom.range.card_subgroup_dvd_card
    rwa [IsCyclic.card_mulAut,Nat.card_zpowers,hx,show Nat.totient 7 = 6 from by decide] at h
  have hm := P.normalizerMonoidHom.ker.card_mul_index
  rw [index_ker,hk] at hm
  have hn := Sylow.card_normalizer_modEq_card (p := 7) (n := 1)
    (H := P) (by rw [Nat.card_zpowers,hx,pow_one])
  rw [←hm,Janko4.Cardinality.model_card] at hn
  obtain ⟨m,hmc⟩ := seven_centralizer_divisible x hx
  rw [hmc] at hn hc
  have hmb : m < 4 := by omega
  have hb := Nat.le_of_dvd (by decide : 0 < 6) hd
  change Nat.card P.normalizerMonoidHom.range = 1 ∨
    Nat.card P.normalizerMonoidHom.range = 3
  generalize Nat.card P.normalizerMonoidHom.range = k at *
  interval_cases m <;> interval_cases k <;> norm_num [Nat.ModEq] at *

/-- The proved divisibility turns a strict upper bound into nonreality. -/
theorem not_real_of_centralizer_lt
    (x : Janko4.Model) (hx : orderOf x = 7)
    (hc : Nat.card (centralizer (zpowers x : Set Janko4.Model)) < 3360) :
    ¬ IsConj x x⁻¹ := by
  intro hr
  obtain ⟨a,ha⟩ := isConj_iff.mp hr
  let P := zpowers x
  have haN : a ∈ normalizer (P : Set Janko4.Model) := by
    rw [mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
    change zpowers (a*x*a⁻¹) = zpowers x
    rw [ha,zpowers_inv]
  let α := P.normalizerMonoidHom ⟨a,haN⟩
  have he (z : P) : α z = z⁻¹ := by
    apply Subtype.ext
    obtain ⟨k,hk⟩ := z.property
    change a * (z : Janko4.Model) * a⁻¹ = (z : Janko4.Model)⁻¹
    rw [←hk]
    change MulAut.conj a (x ^ k) = (x ^ k)⁻¹
    rw [map_zpow]
    change (a*x*a⁻¹)^k = (x^k)⁻¹
    rw [ha,inv_zpow]
  have hs : α^2 = 1 := by
    rw [pow_two]
    ext z
    rw [MulAut.mul_apply,he,he,inv_inv]
    rfl
  have hne : α ≠ 1 := by
    intro h
    have hh := congrArg Subtype.val (he (⟨x,mem_zpowers x⟩ : P))
    rw [h] at hh
    change x = x⁻¹ at hh
    have h2 : x^2 = 1 := by
      calc
        x^2 = x * x := pow_two x
        _ = x * x⁻¹ := congrArg (x * ·) hh
        _ = 1 := mul_inv_cancel x
    have hd := orderOf_dvd_of_pow_eq_one h2
    rw [hx] at hd
    norm_num at hd
  let β : P.normalizerMonoidHom.range := ⟨α,⟨⟨a,haN⟩,rfl⟩⟩
  have ho : orderOf β = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime hs hne
  have hd := orderOf_dvd_natCard β
  rcases normalizer_image_card_of_centralizer_lt x hx hc with hh | hh <;>
    rw [ho,hh] at hd <;> norm_num at hd

/-- It suffices to bound the centralizer of the already certified matrix word. -/
theorem not_real_of_representative_centralizer_lt
    (hc : Nat.card (centralizer (zpowers Janko4.SevenNormalizers.representative :
      Set Janko4.Model)) < 3360)
    (x : Janko4.Model) (hx : orderOf x = 7) : ¬ IsConj x x⁻¹ := by
  apply not_real_of_centralizer_lt x hx
  rwa [centralizer_card_eq x Janko4.SevenNormalizers.representative hx
    Janko4.SevenNormalizers.representative_order]

/-- The remaining ambient bound excludes either full point-automizer section
by lifting its real seven through its two-core quotient. -/
theorem no_binary_automizer_section_of_representative_centralizer_lt
    (hc : Nat.card (centralizer (zpowers Janko4.SevenNormalizers.representative :
      Set Janko4.Model)) < 3360)
    (n : ℕ) (hn : n = 3 ∨ n = 4) (H : Subgroup Janko4.Model)
    (e : (H ⧸ pCore 2 H) ≃*
      MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) : False := by
  obtain ⟨y,hy,hr⟩ := BinaryLinear.OuterCyclic.aut_binary_real_seven n hn
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : Nat.Coprime 7 (Nat.card f.ker) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    obtain ⟨m,hm⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
    rw [hm]
    exact (by decide : Nat.Coprime 7 2).pow_right m
  obtain ⟨x,hx,_,hreal⟩ := f.exists_real_prime_lift hf hk y hy hr
  apply not_real_of_representative_centralizer_lt hc (x : Janko4.Model)
    (by rw [Subgroup.orderOf_coe]; exact hx)
  obtain ⟨a,ha⟩ := isConj_iff.mp hreal
  exact isConj_iff.mpr ⟨(a : Janko4.Model),congrArg Subtype.val ha⟩
end Janko4.SevenCentralizerBounds
