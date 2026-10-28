module
public import Theory.Representation.Suzuki.ComponentPairDegree
public import Theory.Representation.Suzuki.BinaryDegree
public import Theory.SpecificGroups.Suzuki.SchurCoverReduction
public import Theory.Representation.BinaryPrimeDisplacement
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.QuadraticSection

public import Theory.Representation.BinaryOffender.Basic
public import Theory.ElementaryAbelian.Injective
public import Theory.ElementaryAbelian.Quotient
public import Theory.SpecificGroups.Suzuki.TwoRank
public import Theory.GroupTheory.ComponentLocalOrbitCore
public import Theory.GroupTheory.Commutator.ConjugateGeneration
public import Mathlib.GroupTheory.IndexNormal

/-!
# Displacement of an actor exchanging a Suzuki component

A primitive prime of binary order `4*(2*r+1)` occurs in the Suzuki component.
An element of that order and its conjugate lie in distinct commuting
components, so their commutator retains the same prime order. Its binary
displacement is at most twice that of the exchanger.

When a normal overgroup of the component acts as two identical summands,
faithfulness passes to either summand. The primitive-prime displacement on
one summand doubles on the original space, giving exchanger displacement
at least `4*(2*r+1)`. No irreducible constituent is required to be invariant
under the exchanger, and the exchanger need not be an involution.

The elementary actor rank is also at most the rank of its literal orbit
centralizer plus `2*r+2`: its index-two component stabilizer maps into the
Suzuki automorphism group, whose two-rank is `2*r+1`. A nonidentity
centralizing actor has a nonzero pair-invariant displacement submodule,
so its displacement is at least the checked pair degree `8*(2*r+1)`.

Source: Aschbacher--Smith D.3.7--9, printed pp.197--201. The prime-order
argument replaces the tensor-coordinate calculation for this lower bound;
the original natural-centralizer consumer is in Chapter 10 SeedAnalysis.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.Suzuki
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

omit [Finite G] in
private theorem exchanged_prime_commutator
    (J : Subgroup G) (hJ : IsComponent G J) (hZ : center J = ⊥)
    (a : G) (han : a ∉ normalizer (J : Set G))
    {p : ℕ} (hp : p.Prime) (x : J) (hx : orderOf x = p) :
    orderOf (a * (x : G) * a⁻¹ * (x : G)⁻¹) = p := by
  let K := J.map (MulAut.conj a).toMonoidHom
  have hne : K ≠ J := fun he => han (mem_normalizer_iff_map_conj_eq.mpr he)
  have hc : K ≤ centralizer (J : Set G) := commutator_eq_bot_iff_le_centralizer.mp
    ((hJ.map_conj a).commutator_eq_bot_of_ne hJ hne)
  have hy : a * (x : G) * a⁻¹ ∈ K := mem_map_of_mem _ x.property
  have hxp : (x : G) ^ p = 1 := by
    exact congrArg Subtype.val (hx ▸ pow_orderOf_eq_one x)
  have hyp : (a * (x : G) * a⁻¹) ^ p = 1 := by
    have h := congrArg (MulAut.conj a) hxp
    simpa only [map_pow, map_one, MulAut.conj_apply] using h
  have hcomm : Commute (a * (x : G) * a⁻¹) (x : G)⁻¹ :=
    (hc hy _ (J.inv_mem x.property)).symm
  have hpow : (a * (x : G) * a⁻¹ * (x : G)⁻¹) ^ p = 1 := by
    rw [hcomm.mul_pow, hyp, inv_pow, hxp, inv_one, mul_one]
  have hn : a * (x : G) * a⁻¹ * (x : G)⁻¹ ≠ 1 := by
    intro he
    have hyx := mul_inv_eq_one.mp he
    have hxC : (x : G) ∈ centralizer (J : Set G) := hyx ▸ hc hy
    have hz : x ∈ center J := mem_center_iff.mpr fun j =>
      Subtype.ext (hxC j j.property)
    have hx1 : x = 1 := mem_bot.mp (hZ ▸ hz)
    rw [hx1, orderOf_one] at hx
    exact hp.ne_one hx.symm
  let : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime hpow hn

/-- If a normal overgroup of the component acts as two identical summands,
the exchanger displaces at least the full minimum Suzuki binary degree. -/
theorem exchanged_component_displacement_of_double
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (J : Subgroup G) (hJ : IsComponent G J)
    (a : G) (han : a ∉ normalizer (J : Set G))
    (r : ℕ) (hr : 0 < r) (e : J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r)
    (K : Subgroup G) [K.Normal] (hJK : J ≤ K)
    (U : Subrepresentation (ρ.comp K.subtype))
    (E : Representation.Equiv (ρ.comp K.subtype) (U.toRepresentation.prod U.toRepresentation)) :
    4 * (2*r+1) ≤ fixedCodim ρ (zpowers a) := by
  let τ := ρ.comp K.subtype
  have hfτ : Function.Injective τ := hf.comp K.subtype_injective
  have hfU : Function.Injective U.toRepresentation := by
    intro b c he
    apply hfτ
    ext v
    apply E.toLinearEquiv.injective
    have hb := LinearMap.congr_fun (E.isIntertwining' b) v
    have hc := LinearMap.congr_fun (E.isIntertwining' c) v
    exact hb.trans ((Prod.ext (LinearMap.congr_fun he _)
      (LinearMap.congr_fun he _)).trans hc.symm)
  obtain ⟨p,hp,ho⟩ := Theory.NumberTheory.exists_prime_orderOf_two_four_mul_odd
    (n := 2*r+1) ⟨r,rfl⟩ (by omega)
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [show (2 : ZMod 2) = 0 by decide,orderOf_zero] at ho
    omega
  let : Fact p.Prime := ⟨hp⟩
  have hpJ : p ∣ Nat.card J := by
    rw [Nat.card_congr e.toEquiv]
    exact prime_dvd_card_of_orderOf_two (by omega) hp ho
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := J) p hpJ
  let : Fact (0 < r) := ⟨hr⟩
  let : IsSimpleGroup J := e.isSimpleGroup
  let : IsQuasisimple J := hJ.2
  have hZ : center J = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative J (center_eq_top_iff.mp h))
  let y : K := ⟨a * (x : G) * a⁻¹ * (x : G)⁻¹,
    K.mul_mem ((inferInstance : K.Normal).conj_mem _ (hJK x.property) a)
      (K.inv_mem (hJK x.property))⟩
  have hy : orderOf y = p := by
    rw [← Subgroup.orderOf_coe]
    exact exchanged_prime_commutator J hJ hZ a han hp x hx
  have hlo := prime_order_le_fixedCodim U.toRepresentation hfU hp hp2 y hy
  rw [ho] at hlo
  have he := fixedCodim_map_equivariant τ (U.toRepresentation.prod U.toRepresentation)
    (MonoidHom.id K) E.toLinearEquiv
    (fun b v => LinearMap.congr_fun (E.isIntertwining' b) v) (zpowers y)
  rw [Subgroup.map_id,fixedCodim_prod] at he
  have htrans : fixedCodim τ (zpowers y) = fixedCodim ρ (zpowers (y : G)) := by
    simp only [fixedCodim_zpowers_eq_displacement_rank]
    rfl
  have hhi := fixedCodim_commutator_le_twice ρ a x
  change fixedCodim ρ (zpowers (y : G)) ≤ 2 * fixedCodim ρ (zpowers a) at hhi
  omega

private theorem elementary_card (A : Subgroup G) [IsElementaryAbelian 2 A] :
    Nat.card A = 2 ^ rank A := by
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  rw [rank,hn,Nat.log_pow Nat.one_lt_two]

/-- The literal elementary actor can spend at most the Suzuki field degree
plus one rank outside the pointwise centralizer of its component orbit. -/
theorem exchanged_actor_rank_le
    (J A : Subgroup G) [IsElementaryAbelian 2 A]
    (hindex : (normalizer (J : Set G)).index = 2)
    (r : ℕ) (hr : 0 < r) (e : J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) :
    rank A ≤ rank (A ⊓ centralizer (componentOrbit J A : Set G)) + (2*r+1) + 1 := by
  let N := normalizer (J : Set G)
  let P := A ⊓ N
  let C := A ⊓ centralizer (J : Set G)
  let : N.Normal := normal_of_index_eq_two hindex
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.of_injective
    (inclusion (show P ≤ A from inf_le_left)) (inclusion_injective _)
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_injective
    (inclusion (show C ≤ A from inf_le_left)) (inclusion_injective _)
  have hCP : C ≤ P := le_inf inf_le_left
    (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  let f : P →* MulAut J := J.normalizerMonoidHom.comp (inclusion (show P ≤ N from inf_le_right))
  have hker : f.ker = C.subgroupOf P := by
    ext x
    change inclusion (show P ≤ N from inf_le_right) x ∈ J.normalizerMonoidHom.ker ↔
      (x : G) ∈ C
    rw [normalizerMonoidHom_ker]
    change (x : G) ∈ centralizer (J : Set G) ↔ (x : G) ∈ A ∧
      (x : G) ∈ centralizer (J : Set G)
    exact ⟨fun h => ⟨x.property.1,h⟩,fun h => h.2⟩
  have hcardker : Nat.card f.ker = Nat.card C := by
    rw [hker,Nat.card_congr (subgroupOfEquivOfLe hCP).toEquiv]
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have haut : primeRank 2 (MulAut J) ≤ 2*r+1 := by
    rw [primeRank_equiv 2 (MulAut.congr e)]
    exact BenderSuzuki.MatrixGroups.suzuki_automorphism_two_rank r hr
  have hR : Nat.card f.range ≤ 2^(2*r+1) :=
    (primeRank_le_iff_elementary_card_le _).mp haut f.range inferInstance
  have hP : Nat.card P = Nat.card C * Nat.card f.range := by
    rw [←f.ker.card_mul_index,index_ker,hcardker]
  have hindexP : P.relIndex A ≤ 2 := by
    have hd := N.relIndex_dvd_index_of_normal A
    rw [hindex,←inf_relIndex_left A N] at hd
    exact Nat.le_of_dvd (by decide) hd
  have hcard : Nat.card A = Nat.card P * P.relIndex A := by
    simpa only [relIndex_bot_left] using
      (relIndex_mul_relIndex (⊥ : Subgroup G) P A bot_le inf_le_left).symm
  have hb : Nat.card A ≤ 2 ^ (rank C + (2*r+1) + 1) := by
    rw [hcard,hP,pow_add,pow_add,pow_one,←elementary_card C]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hR) hindexP
  rw [elementary_card A] at hb
  have hrank := (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp hb
  have hAC : A ≤ centralizer (C : Set G) := by
    intro a ha c hc
    exact congrArg Subtype.val (mul_comm (⟨c,hc.1⟩ : A) (⟨a,ha⟩ : A))
  have horbit : componentOrbit J A ≤ centralizer (C : Set G) :=
    iSup_conjugates_le_of_le_normalizer J A (centralizer (C : Set G))
      (le_centralizer_iff.mp (show C ≤ centralizer (J : Set G) from inf_le_right))
      (hAC.trans (centralizer (C : Set G)).le_normalizer)
  have heC : C = A ⊓ centralizer (componentOrbit J A : Set G) := by
    apply le_antisymm
    · exact le_inf inf_le_left (le_centralizer_iff.mp horbit)
    · exact le_inf inf_le_left
        (inf_le_right.trans (centralizer_le (show (J : Set G) ⊆ componentOrbit J A from le_componentOrbit J A)))
  rwa [heC] at hrank

omit [Finite G] in
/-- A nonidentity actor centralizing the fully moving Suzuki pair has an
invariant nonzero displacement submodule, hence moves at least `8*(2*r+1)`
dimensions. The exchanger need not preserve an individual constituent. -/
theorem pair_centralizer_displacement
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (J : Subgroup G) (hJ : IsComponent G J)
    (hindex : (normalizer (J : Set G)).index = 2)
    (a : G) (han : a ∉ normalizer (J : Set G))
    (hm : subspaceCommutator ρ ⊤ J = ⊤)
    (r : ℕ) (hr : 0 < r) (e : J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r)
    (c : G) (hc : c ∈ centralizer ((J ⊔ J.map (MulAut.conj a).toMonoidHom : Subgroup G) : Set G))
    (hc1 : c ≠ 1) : 8 * (2*r+1) ≤ fixedCodim ρ (zpowers c) := by
  let X := J ⊔ J.map (MulAut.conj a).toMonoidHom
  let U : Subrepresentation (ρ.comp X.subtype) := {
    toSubmodule := LinearMap.range (ρ c - LinearMap.id)
    apply_mem_toSubmodule x v hv := by
      obtain ⟨w,rfl⟩ := hv
      refine ⟨ρ x w,?_⟩
      change ρ c (ρ x w) - ρ x w = ρ x (ρ c w - w)
      rw [map_sub]
      congr 1
      rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
      exact LinearMap.congr_fun (congrArg ρ (hc x x.property).symm) w }
  have hU : U ≠ ⊥ := by
    intro he
    apply hc1
    apply hf
    rw [map_one]
    ext v
    have hv : ρ c v - v ∈ U.toSubmodule := ⟨v,rfl⟩
    have he' : U.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule he
    rw [he',Submodule.mem_bot] at hv
    exact sub_eq_zero.mp hv
  have hb := exchanged_pair_subrepresentation_finrank_ge ρ hi J hJ hindex a han hm r hr e U hU
  rw [fixedCodim_zpowers_eq_displacement_rank]
  exact hb
end Representation.Suzuki
