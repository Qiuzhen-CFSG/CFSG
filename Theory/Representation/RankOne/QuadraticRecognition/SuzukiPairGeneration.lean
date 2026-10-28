module
public import Theory.Representation.RankOne.QuadraticRecognition.SuzukiElementBounds
public import Theory.Representation.RankOne.QuadraticRecognition.QuadraticPairs
public import Theory.Representation.RankOne.QuadraticRecognition.SL2Sylow
public import Theory.SpecificGroups.Suzuki.ElementarySylowSubgroups.NormalComplements
public import BenderSuzuki.External.Huppert.XI.SubgroupNonsolvable

/-!
# Defining-field generation and quadratic fixed spaces in Suzuki groups

Choose a prime whose binary multiplicative order is four times the Suzuki
field degree. An odd torus supplies a prime-order element and an inverting
involution. Involution fusion puts their product in a conjugate of the
specified elementary actor. The resulting subgroup cannot be solvable:
the prime excludes Borel and split normalizers, and an elementary four
excludes the cyclic odd-kernel quotients of nonsplit normalizers.

Suzuki subgroup recognition and order divisibility identify its field
degree with the full ambient degree. The actual pair therefore generates
G. Perfectness and vector generation from C_V(A) give C_V(A)=C_V(t).
The Sz(2) endpoint has cyclic Sylows, excluding an elementary actor of
order at least four. No dihedral group is added to the source catalogue.

Source: DGS85, *Groups and Graphs*, (5.3), (5.10)(c), printed pp.106,
110–111; Huppert–Blackburn III, XI.3.3 and XI.3.12(e). The literal
critical-quotient application is ModuleApplications.CriticalFixedSpaces.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace Representation.RankOne.QuadraticRecognition

private theorem binary_order_le_of_dvd_minus {p d : ℕ} (hd : 0<d)
    (h : p∣2^d-1) : orderOf (2 : ZMod p) ≤ d := by
  have he : (2 : ZMod p)^d=1 := by
    have hh := (ZMod.natCast_eq_zero_iff (2^d-1) p).mpr h
    rw [Nat.cast_sub (Nat.one_le_two_pow),Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] at hh
    exact sub_eq_zero.mp hh
  exact orderOf_le_of_pow_eq_one hd he

private theorem binary_order_le_of_dvd_plus {p d : ℕ} (hd : 0<d)
    (h : p∣2^d+1) : orderOf (2 : ZMod p) ≤ 2*d := by
  have he : (2 : ZMod p)^d = -1 := by
    have hh := (ZMod.natCast_eq_zero_iff (2^d+1) p).mpr h
    rw [Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] at hh
    exact eq_neg_of_add_eq_zero_left hh
  apply orderOf_le_of_pow_eq_one (by omega : 0<2*d)
  rw [Nat.mul_comm 2 d,pow_mul,he,neg_one_sq]

private theorem primitive_prime_not_dvd_borel {m p : ℕ} (hm : 0<m)
    (hp : p.Prime) (hp2 : p≠2) (hdeg : orderOf (2 : ZMod p)=4*(2*m+1)) :
    ¬ p∣Nat.card (SuzukiBorelSubgroup m) := by
  rw [suzukiBorelSubgroup_card m hm]
  intro hd
  rcases hp.dvd_mul.mp hd with h | h
  · have he := hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow h)
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp he |>.resolve_left hp.ne_one)
  · have hh := binary_order_le_of_dvd_minus (by omega : 0<2*m+1) h
    omega

private theorem primitive_prime_degree_le_of_dvd_suzuki {m k p : ℕ}
    (hk : 0<k) (hp : p.Prime) (hp2 : p≠2)
    (hdeg : orderOf (2 : ZMod p)=4*(2*m+1))
    (hd : p∣Nat.card (SuzukiMatrixGroup k)) : m≤k := by
  rw [suzukiMatrixGroup_card k hk] at hd
  rcases hp.dvd_mul.mp hd with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · rw [←pow_mul] at h
      have hh := binary_order_le_of_dvd_plus (by omega : 0<(2*k+1)*2) h
      omega
    · have he := hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow h)
      exact (hp2 ((Nat.dvd_prime Nat.prime_two).mp he |>.resolve_left hp.ne_one)).elim
  · have hh := binary_order_le_of_dvd_minus (by omega : 0<2*k+1) h
    omega

private theorem elementary_card_le_two_in_odd_cyclic_quotient
    {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (ho : Odd (Nat.card N)) [IsCyclic (G ⧸ N)]
    (A : Subgroup G) [IsElementaryAbelian 2 A] : Nat.card A≤2 := by
  let f := (QuotientGroup.mk' N).comp A.subtype
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro x hx
    have hxN : (x : G)∈N := (QuotientGroup.eq_one_iff _).mp hx
    have hd : orderOf x∣Nat.card N := by
      rw [←orderOf_coe]
      exact N.orderOf_dvd_natCard hxN
    have hd2 : orderOf x∣2 := orderOf_dvd_of_pow_eq_one
      (Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (x : G) x.property))
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes ho.coprime_two_left hd2 hd)
  let : IsCyclic A := isCyclic_of_injective f hf
  apply Nat.le_of_dvd (by decide : 0<2)
  rw [←IsCyclic.exponent_eq_card]
  exact IsElementaryAbelian.exponent_dvd_p 2 A

private theorem elementary_nonsplit_bound {m : ℕ} (hm : 0<m)
    (U : Subgroup (SuzukiMatrixGroup m)) (hU : IsSuzukiMaximalNonsplit m U)
    (A : Subgroup (SuzukiMatrixGroup m)) [IsElementaryAbelian 2 A]
    (hAN : A≤normalizer (U : Set (SuzukiMatrixGroup m))) : Nat.card A≤2 := by
  let N := normalizer (U : Set (SuzukiMatrixGroup m))
  let T := U.subgroupOf N
  let B := A.subgroupOf N
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hAN
  let : IsCyclic (N ⧸ T) := (hU.normalizer_quotient hm).1
  have ho : Odd (Nat.card T) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe U.le_normalizer).toEquiv]
    exact Odd.of_dvd_nat ((even_two.pow_of_ne_zero (by omega : 2*m+1≠0)).pow_of_ne_zero
      (by decide : 2≠0) |>.add_odd odd_one) hU.card_dvd
  have hb := elementary_card_le_two_in_odd_cyclic_quotient T ho B
  rwa [Nat.card_congr (subgroupOfEquivOfLe hAN).toEquiv] at hb

private theorem suzuki_subgroup_not_solvable {m p : ℕ} (hm : 0<m)
    (hp : p.Prime) (hp2 : p≠2) (hdeg : orderOf (2 : ZMod p)=4*(2*m+1))
    (H A : Subgroup (SuzukiMatrixGroup m)) [IsElementaryAbelian 2 A]
    (hAH : A≤H) (hAc : 4≤Nat.card A) (hdiv : p∣Nat.card H) : ¬Group.IsSolvable H := by
  intro hsol
  let := hsol
  obtain ⟨T⟩ := exists_suzukiNonsplitTorusPair m hm
  obtain ⟨g,hB|hS|hP|hM⟩ := suzukiStandardContainment_of_isSolvable hm T H
  · apply primitive_prime_not_dvd_borel hm hp hp2 hdeg
    have hd := (card_dvd_of_le hB)
    rw [card_map_of_injective (MulAut.conj g).injective] at hd
    exact hdiv.trans hd
  · have hd := card_dvd_of_le hS
    rw [card_map_of_injective (MulAut.conj g).injective,
      suzukiSplitTorus_normalizer_card m hm] at hd
    have hpq := (hp.dvd_mul.mp (hdiv.trans hd)).resolve_left
      (fun h => hp2 ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one))
    have hh := binary_order_le_of_dvd_minus (by omega : 0<2*m+1) hpq
    omega
  · let : IsElementaryAbelian 2 (A.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
    have hh := elementary_nonsplit_bound hm T.plus T.plus_maximal
      (A.map (MulAut.conj g).toMonoidHom) ((map_mono hAH).trans hP)
    rw [card_map_of_injective (MulAut.conj g).injective] at hh
    omega
  · let : IsElementaryAbelian 2 (A.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
    have hh := elementary_nonsplit_bound hm T.minus T.minus_maximal
      (A.map (MulAut.conj g).toMonoidHom) ((map_mono hAH).trans hM)
    rw [card_map_of_injective (MulAut.conj g).injective] at hh
    omega

/-- Any elementary actor of order at least four pairs with a suitable
conjugate of a prescribed involution to generate the actual Suzuki group. -/
theorem suzuki_exists_quadratic_pair {m : ℕ} (hm : 0<m)
    (A : Subgroup (SuzukiMatrixGroup m)) [IsElementaryAbelian 2 A]
    (hAc : 4≤Nat.card A) (t : SuzukiMatrixGroup m) (htA : t∈A) (ht1 : t≠1) :
    ∃ g : SuzukiMatrixGroup m, zpowers t ⊔ A.map (MulAut.conj g).toMonoidHom=⊤ := by
  have ht2 : t^2=1 := elemPow_eq_one_of_isElementaryAbelian t htA
  have hto : orderOf t=2 := orderOf_eq_prime ht2 ht1
  obtain ⟨p,hp,hdeg⟩ := Theory.NumberTheory.exists_prime_orderOf_two_four_mul_odd
    (n := 2*m+1) ⟨m,rfl⟩ (by omega)
  have hp2 : p≠2 := by
    rintro rfl
    rw [show (2 : ZMod 2)=0 from rfl,orderOf_zero] at hdeg
    omega
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨y,hy⟩ := exists_prime_orderOf_dvd_card' (G := SuzukiMatrixGroup m) p
    (Representation.Suzuki.prime_dvd_card_of_orderOf_two hm hp hdeg)
  obtain ⟨U,hyU,hU⟩ := suzukiOddSubgroup_exists_torus hm (zpowers y)
    (by simpa only [Nat.card_zpowers,hy] using hp.odd_of_ne_two hp2)
  obtain ⟨w,hw,hi⟩ := suzuki_torus_inverting_involution hm U hU
  obtain ⟨c,hc⟩ := isConj_iff.mp (suzuki_involutions_isConj m hm w t hw hto)
  let x := MulAut.conj c y
  have hx : orderOf x=p := ((MulAut.conj c).orderOf_eq y).trans hy
  have hxi : t*x*t⁻¹=x⁻¹ := by
    rw [←hc]
    change (c*w*c⁻¹)*(c*y*c⁻¹)*(c*w*c⁻¹)⁻¹=(c*y*c⁻¹)⁻¹
    calc
      _ = c*(w*y*w⁻¹)*c⁻¹ := by group
      _ = c*y⁻¹*c⁻¹ := by rw [hi y (hyU (mem_zpowers y))]
      _ = _ := by group
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ht2)
  have hu2 : (t*x)^2=1 := by
    calc
      _ = (t*x*t⁻¹)*x := by rw [hti,pow_two]; group
      _ = 1 := by rw [hxi,inv_mul_cancel]
  have hu1 : t*x≠1 := by
    intro h
    have hxt : x=t := by calc
      x = t*(t*x) := by rw [←mul_assoc,←pow_two,ht2,one_mul]
      _ = t := by rw [h,mul_one]
    exact hp2 (hx.symm.trans (hxt ▸ hto))
  obtain ⟨g,hg⟩ := isConj_iff.mp (suzuki_involutions_isConj m hm t (t*x) hto
    (orderOf_eq_prime hu2 hu1))
  let B := A.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  let H := zpowers t ⊔ B
  have htH : t∈H := (show zpowers t≤H from le_sup_left) (mem_zpowers t)
  have huH : t*x∈H := (show B≤H from le_sup_right)
    (hg ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom htA)
  have hxH : x∈H := by
    have hh := H.mul_mem htH huH
    simpa only [←mul_assoc,←pow_two,ht2,one_mul] using hh
  have hd : p∣Nat.card H := hx ▸ H.orderOf_dvd_natCard hxH
  have hBc : 4≤Nat.card B := by rw [card_map_of_injective (MulAut.conj g).injective]; exact hAc
  have hsol := suzuki_subgroup_not_solvable hm hp hp2 hdeg H B le_sup_right hBc hd
  obtain ⟨k,hk,⟨e⟩⟩ := BenderSuzuki.External.suzukiSubgroup_exists_mulEquiv_of_not_isSolvable hm H hsol
  have hkm : 2*k+1≤2*m+1 := Nat.le_of_dvd (by omega)
    (suzukiMatrixGroup_degree_dvd_of_card_dvd hk hm (by
      rw [←Nat.card_congr e.toEquiv]; exact H.card_subgroup_dvd_card))
  have hmk := primitive_prime_degree_le_of_dvd_suzuki hk hp hp2 hdeg
    (by rw [←Nat.card_congr e.toEquiv]; exact hd)
  have he : k=m := by omega
  subst k
  exact ⟨g,H.eq_top_of_card_eq (Nat.card_congr e.toEquiv)⟩
open Representation.BinaryOffender

/-- DGS (5.10)(c), Suzuki branch. The pair-generation premise is discharged
for the original actor; no whole-Sylow quadraticity is imposed. -/
private theorem suzuki_quadratic_fixedSpace_eq_of_pos {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] {m : ℕ} (hm : 0<m)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V) (hf : Function.Injective ρ)
    (A : Subgroup (SuzukiMatrixGroup m)) (hAc : 4≤Nat.card A)
    (hq : IsQuadratic ρ A) (hspan : GeneratedByFixedSpace ρ A)
    (t : SuzukiMatrixGroup m) (htA : t∈A) (ht1 : t≠1) :
    fixedSpace ρ A=fixedSpace ρ (zpowers t) := by
  let : IsElementaryAbelian 2 A := elementary_of_faithful_quadratic ρ hf A hq
  let : IsSimpleGroup (SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  let : Group.IsPerfect (SuzukiMatrixGroup m) := by
    constructor
    rcases (inferInstance : (commutator (SuzukiMatrixGroup m)).Normal).eq_bot_or_eq_top with h|h
    · exact False.elim (BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm
        ⟨⟨1,(derivedSeries_one _).trans h⟩⟩)
    · exact h
  obtain ⟨g,hg⟩ := suzuki_exists_quadratic_pair hm A hAc t htA ht1
  exact fixedSpace_eq_of_perfect_quadratic_pair ρ A _ t htA hq
    (SL2SylowFixedRecognition.quadratic_conjugate ρ hq g) hg hspan
private theorem small_suzuki_elementary_card_le_two
    (A : Subgroup (SuzukiMatrixGroup 0)) [IsElementaryAbelian 2 A] : Nat.card A≤2 := by
  let P : Sylow 2 (SuzukiMatrixGroup 0) := Sylow.ofCard (zpowers suzukiZeroRootGenerator) (by
    rw [Nat.card_zpowers,suzukiZeroRootGenerator_order,suzukiZero_card]
    rw [show (20 : ℕ) = 2^2 * 5 from rfl,
      Nat.factorization_mul (by decide) (by decide),Nat.factorization_pow]
    norm_num [Nat.Prime.factorization Nat.prime_two,
      Nat.Prime.factorization (by decide : Nat.Prime 5)])
  let : IsCyclic P := inferInstanceAs (IsCyclic (zpowers suzukiZeroRootGenerator))
  obtain ⟨S,hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  let : IsCyclic S := (Sylow.equiv P S).isCyclic.mp inferInstance
  let : IsCyclic A := Subgroup.isCyclic_of_le hAS
  apply Nat.le_of_dvd (by decide : 0<2)
  rw [←IsCyclic.exponent_eq_card]
  exact IsElementaryAbelian.exponent_dvd_p 2 A

/-- The complete Suzuki clause of DGS (5.10)(c), including the source
small parameter. Its quadratic actor cannot have order at least four in Sz(2). -/
theorem suzuki_quadratic_fixedSpace_eq {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] (m : ℕ)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V) (hf : Function.Injective ρ)
    (A : Subgroup (SuzukiMatrixGroup m)) (hAc : 4≤Nat.card A)
    (hq : IsQuadratic ρ A) (hspan : GeneratedByFixedSpace ρ A)
    (t : SuzukiMatrixGroup m) (htA : t∈A) (ht1 : t≠1) :
    fixedSpace ρ A=fixedSpace ρ (zpowers t) := by
  rcases Nat.eq_zero_or_pos m with rfl|hm
  · let : IsElementaryAbelian 2 A := elementary_of_faithful_quadratic ρ hf A hq
    have hh := small_suzuki_elementary_card_le_two A
    omega
  · exact suzuki_quadratic_fixedSpace_eq_of_pos hm ρ hf A hAc hq hspan t htA ht1
end Representation.RankOne.QuadraticRecognition
