module
public import Theory.Representation.RankOne.QuadraticRecognition.QuadraticPairs
public import Theory.Representation.RankOne.QuadraticRecognition.SL2Sylow
public import Theory.SpecificGroups.SL2.BinaryLocalRecognition
public import Theory.SpecificGroups.PSL2.LargeOddInverter
public import BenderSuzuki.External.Huppert.II.theorem_6_14

/-!
# Defining-field generation and quadratic fixed spaces in binary SL₂

An involution inverts a generator of a nonsplit torus of order 2ⁿ+1.
A suitable conjugate of the original actor therefore generates a subgroup
containing both that torus generator and a two-subgroup of order at least
four. Its two-core is trivial. Dickson recognition makes it SL₂(2ᵏ),
where k divides n; torus-order divisibility forces n<2k, hence k=n.

The perfect-group quadratic-pair argument then identifies C_V(A) with
C_V(t), retaining the source generation V=⟨C_V(A)ᴳ⟩. This works for every
binary defining field, including the small field where the actor-size
premise is impossible, and needs no strict size inequality.

Source: DGS85, *Groups and Graphs*, (5.2), (5.10)(c), printed pp.106,
110–111; Huppert II.8.4 and Dickson's subgroup theorem. The literal
critical-quotient application is ModuleApplications.CriticalFixedSpaces.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Representation.RankOne.QuadraticRecognition
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem sl2_involutions_conjugate (a b : SL(2,F))
    (ha : orderOf a=2) (hb : orderOf b=2) : IsConj a b := by
  let e := Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL F
  obtain ⟨g,hg⟩ := isConj_iff.mp (Theory.PSL2.involutions_isConj (e a) (e b)
    ((e.orderOf_eq a).trans ha) ((e.orderOf_eq b).trans hb))
  apply isConj_iff.mpr
  refine ⟨e.symm g,?_⟩
  apply e.injective
  simpa only [map_mul,map_inv,e.apply_symm_apply] using hg

private theorem sl2_inverts_nonsplit_generator {n : ℕ} (hn : 0<n)
    (hF : Nat.card F=2^n) (t : SL(2,F)) (ht : orderOf t=2) :
    ∃ x : SL(2,F), orderOf x=2^n+1 ∧ t*x*t⁻¹=x⁻¹ := by
  let e := Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL F
  obtain ⟨U,w,hU,hcard,_,hw,hw2,hi,_,_⟩ :=
    BenderSuzuki.External.huppert_II_8_4_nonsplit_torus_reflection_data hF
  have ho : Odd (2^n-1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (even_two.pow_of_ne_zero (by omega)) odd_one
  rw [hF,ho.coprime_two_right.gcd_eq_one,Nat.div_one] at hcard
  let := hU
  obtain ⟨x,hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := U)
  have hwo : orderOf w=2 := orderOf_eq_prime (by simpa only [pow_two] using hw2)
    (fun he => hw (he ▸ U.one_mem))
  obtain ⟨g,hg⟩ := isConj_iff.mp (Theory.PSL2.involutions_isConj w (e t) hwo
    ((e.orderOf_eq t).trans ht))
  refine ⟨e.symm (MulAut.conj g (x : _)),?_,?_⟩
  · rw [MulEquiv.orderOf_eq,MulEquiv.orderOf_eq,Subgroup.orderOf_coe,hx,hcard]
  · apply e.injective
    simp only [map_mul,map_inv,e.apply_symm_apply]
    rw [←hg]
    change (g*w*g⁻¹)*(g*(x:_)*g⁻¹)*(g*w*g⁻¹)⁻¹=(g*(x:_)*g⁻¹)⁻¹
    calc
      _ = g*(w*(x:_)*w⁻¹)*g⁻¹ := by group
      _ = g*(x : PSL(2,F))⁻¹*g⁻¹ := by rw [hi x x.property]
      _ = _ := by group

omit [CharP F 2] in
private theorem sl2_subfield_eq_top_of_nonsplit_order {n : ℕ} (hn : 0<n)
    (hF : Nat.card F=2^n) (H : Subgroup SL(2,F))
    {k : ℕ} (hk : 1<k) (hkn : k∣n) (e : H ≃* SL(2,GaloisField 2 k))
    (x : H) (hx : orderOf x=2^n+1) : H=⊤ := by
  have hcard : Nat.card H=2^k*((2^k)^2-1) := by
    rw [Nat.card_congr e.toEquiv,BenderSuzuki.External.huppert614_card_specialLinearGroup,
      GaloisField.card 2 k (by omega)]
  have hd := orderOf_dvd_natCard x
  rw [hx,hcard] at hd
  have ho : Odd (2^n+1) := (even_two.pow_of_ne_zero (by omega : n≠0)).add_odd odd_one
  have hd' : 2^n+1 ∣ (2^k)^2-1 :=
    (ho.coprime_two_right.pow_right k).dvd_of_dvd_mul_left hd
  have hle : 2^n+1 ≤ (2^k)^2-1 := Nat.le_of_dvd (by
    have hh : 1 < (2:ℕ)^k := one_lt_pow₀ (by decide) (by omega)
    have hh2 : 1 < ((2:ℕ)^k)^2 := one_lt_pow₀ hh (by decide)
    omega) hd'
  have hnk : n<2*k := by
    by_contra! hh
    have hp := Nat.pow_le_pow_right (n := 2) (by decide) hh
    rw [Nat.mul_comm 2 k,pow_mul] at hp
    omega
  have hkeq : k=n := by
    obtain ⟨r,hr⟩ := hkn
    have hrpos : 0<r := by nlinarith
    have hrone : r=1 := by nlinarith
    simpa only [hrone,mul_one] using hr.symm
  subst k
  apply H.eq_top_of_card_eq
  rw [hcard,BenderSuzuki.External.huppert614_card_specialLinearGroup,hF]

/-- A noncyclic binary root actor and a suitable conjugate of any of its
involutions generate the entire defining-field SL₂, with no subfield premise. -/
theorem sl2_exists_quadratic_pair {n : ℕ} (hn : 0<n) (hF : Nat.card F=2^n)
    (S : Sylow 2 SL(2,F)) (A : Subgroup SL(2,F)) (hAS : A≤S)
    (hAc : 4≤Nat.card A) (t : SL(2,F)) (htA : t∈A) (ht1 : t≠1) :
    ∃ g : SL(2,F), zpowers t ⊔ A.map (MulAut.conj g).toMonoidHom=⊤ := by
  have ht2 : t^2=1 := by
    exact congrArg Subtype.val (Matrix.SpecialLinearGroup.twoSubgroup_pow_two
      (S : Subgroup SL(2,F)) S.isPGroup' ⟨t,hAS htA⟩)
  have hto : orderOf t=2 := orderOf_eq_prime ht2 ht1
  obtain ⟨x,hxo,hxi⟩ := sl2_inverts_nonsplit_generator hn hF t hto
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
    have hp : 1 < (2:ℕ)^n := one_lt_pow₀ (by decide) (by omega)
    rw [hxt,hto] at hxo
    omega
  obtain ⟨g,hg⟩ := isConj_iff.mp (sl2_involutions_conjugate t (t*x) hto
    (orderOf_eq_prime hu2 hu1))
  let B := A.map (MulAut.conj g).toMonoidHom
  let H := zpowers t ⊔ B
  have htH : t∈H := (show zpowers t≤H from le_sup_left) (mem_zpowers t)
  have huH : t*x∈H := (show B≤H from le_sup_right)
    (hg ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom htA)
  have hxH : x∈H := by
    have hh := H.mul_mem htH huH
    simpa only [←mul_assoc,←pow_two,ht2,one_mul] using hh
  let a : H := ⟨t,htH⟩
  let b : H := ⟨t*x,huH⟩
  have ha : orderOf a=2 := (orderOf_coe a).symm.trans hto
  have hb : orderOf b=2 := (orderOf_coe b).symm.trans (orderOf_eq_prime hu2 hu1)
  have hab : ¬Commute a b := by
    intro hc
    have hp := hc.mul_pow 2
    rw [show a^2=1 from pow_orderOf_eq_one a ▸ (by rw [ha]),
      show b^2=1 from pow_orderOf_eq_one b ▸ (by rw [hb]),one_mul] at hp
    have hxp : x^2=1 := by
      have hh := congrArg Subtype.val hp
      simpa only [a,b,coe_mul,coe_pow,coe_one,←mul_assoc,←pow_two,ht2,one_mul] using hh
    have hd := orderOf_dvd_of_pow_eq_one hxp
    rw [hxo] at hd
    have hh := Nat.le_of_dvd (by decide : 0<2) hd
    have hpow : 1 < (2:ℕ)^n := one_lt_pow₀ (by decide) (by omega)
    omega
  have hcore := Matrix.SpecialLinearGroup.binary_subgroup_twoCore_eq_bot_of_noncommuting_involutions H a b ha hb hab
  have hBtwo : IsPGroup 2 B := (S.isPGroup'.to_le hAS).map _
  have hBH : B≤H := le_sup_right
  obtain ⟨P,hP⟩ := hBtwo.of_equiv (subgroupOfEquivOfLe hBH).symm |>.exists_le_sylow
  have hPc : 4≤Nat.card P := by
    have hBcard : Nat.card (B.subgroupOf H)=Nat.card A := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hBH).toEquiv,card_map_of_injective (MulAut.conj g).injective]
    rw [←hBcard] at hAc
    exact hAc.trans (Nat.card_le_card_of_injective _ (inclusion_injective hP))
  obtain ⟨k,hk,hkn,⟨e⟩⟩ := Matrix.SpecialLinearGroup.TwoConjugateWitness.sl_subgroup_recognition
    hF H hcore P hPc
  exact ⟨g,sl2_subfield_eq_top_of_nonsplit_order hn hF H hk hkn e ⟨x,hxH⟩
    ((orderOf_coe _).symm.trans hxo)⟩
open Representation.BinaryOffender

/-- DGS (5.10)(c) for all binary defining fields. The group pair is
constructed here; vector generation is precisely from the actor fixed space. -/
theorem sl2_quadratic_fixedSpace_eq {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) SL(2,F) V)
    {n : ℕ} (hn : 0<n) (hF : Nat.card F=2^n)
    (S : Sylow 2 SL(2,F)) (A : Subgroup SL(2,F)) (hAS : A≤S)
    (hAc : 4≤Nat.card A) (hq : IsQuadratic ρ A) (hspan : GeneratedByFixedSpace ρ A)
    (t : SL(2,F)) (htA : t∈A) (ht1 : t≠1) :
    fixedSpace ρ A=fixedSpace ρ (zpowers t) := by
  have hSc : Nat.card S=Nat.card F := Nat.card_congr
    (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 S).symm.toEquiv
  have hF4 : 4≤Nat.card F := by
    rw [←hSc]
    exact hAc.trans (Nat.card_le_card_of_injective _ (inclusion_injective hAS))
  let : Group.IsPerfect SL(2,F) := SL2SylowFixedRecognition.perfect hF4
  obtain ⟨g,hg⟩ := sl2_exists_quadratic_pair hn hF S A hAS hAc t htA ht1
  exact fixedSpace_eq_of_perfect_quadratic_pair ρ A _ t htA hq
    (SL2SylowFixedRecognition.quadratic_conjugate ρ hq g) hg hspan
end Representation.RankOne.QuadraticRecognition
