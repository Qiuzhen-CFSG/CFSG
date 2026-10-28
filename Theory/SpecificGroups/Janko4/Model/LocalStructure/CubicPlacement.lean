module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.CubicResidual
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.GroupTheory.CoprimePrimeFusion

/-!
# Placing a cubic Mathieu cover at a specified element of J₄

The checked native order-three fusion sends powers of any two cubics to a
common representative. Coprime-kernel fusion lifts the resulting conjugacy
through the specified full central cover. Transporting the native simultaneous
centralizer residual therefore gives a quasisimple M₂₂ cover in the centralizer
of any prescribed cubic, with its actual subgroup inclusion retained.

The exterior pushing-up consumer prescribes a cubic in its original intersection
residual which fixes sixteen module vectors. This removes the arbitrary-element
choice from the cubic construction. Identifying this subgroup with the full
cubic-centralizer residual and proving ambient normality are separate steps.

Source: Aschbacher--Smith, 4.2.13, printed p.612. Native matrix and fusion
certificates retain their ATLAS attribution in the imported modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure
attribute [local irreducible] modelGroup matrixA matrixB

private theorem image_cubic_order {U Y : Type*} [Group U] [Finite U] [Group Y]
    (f : U →* Y) (hk : Nat.Coprime 3 (Nat.card f.ker))
    (x : U) (hx : orderOf x = 3) : orderOf (f x) = 3 := by
  have hp : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := 1)
    (by simpa only [Nat.card_zpowers,pow_one] using hx)
  have hi := injective_comp_subtype_of_coprime_ker f hk (zpowers x) hp
  exact (orderOf_injective (f.comp (zpowers x).subtype) hi ⟨x,mem_zpowers x⟩).trans
    ((orderOf_coe _).symm.trans hx)

private theorem cubic_powers_conjugate (x y : Model)
    (hx : orderOf x = 3) (hy : orderOf y = 3) :
    ∃ k l : ℕ, orderOf (x ^ k) = 3 ∧ orderOf (y ^ l) = 3 ∧
      IsConj (x ^ k) (y ^ l) := by
  obtain ⟨k,g,hg⟩ := Simplicity.three_explicit_coverage matrixA_mul_self matrixB_pow_four
    Cardinality.model_card x hx
  obtain ⟨l,h,hh⟩ := Simplicity.three_explicit_coverage matrixA_mul_self matrixB_pow_four
    Cardinality.model_card y hy
  have ho := Simplicity.orderOf_primeRepresentative_two matrixA_mul_self matrixB_pow_four
  have hk : orderOf (x ^ k) = 3 := by
    have he := (MulAut.conj g).orderOf_eq (x ^ k)
    change orderOf (g * x ^ k * g⁻¹) = _ at he
    rw [←hg,ho] at he
    exact he.symm
  have hl : orderOf (y ^ l) = 3 := by
    have he := (MulAut.conj h).orderOf_eq (y ^ l)
    change orderOf (h * y ^ l * h⁻¹) = _ at he
    rw [←hh,ho] at he
    exact he.symm
  exact ⟨k,l,hk,hl,(isConj_iff.mpr ⟨g,hg.symm⟩).trans
    (isConj_iff.mpr ⟨h,hh.symm⟩).symm⟩

private theorem centralizer_cubic_power {U : Type*} [Group U] [Finite U]
    (x : U) (hx : orderOf x = 3) (n : ℕ) (hn : orderOf (x ^ n) = 3) :
    centralizer ({x ^ n} : Set U) = centralizer ({x} : Set U) := by
  have he : zpowers (x ^ n) = zpowers x := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr (pow_mem (mem_zpowers x) n))
    rw [Nat.card_zpowers,Nat.card_zpowers,hx,hn]
  rw [←centralizer_closure,←zpowers_eq_closure,he,zpowers_eq_closure,centralizer_closure]

/-- Every specified cubic in the full three-free central cover has a literal
quasisimple M₂₂ subgroup in its centralizer. The subgroup is transported from
the native simultaneous-centralizer residual, not from a family label. -/
theorem cubic_centralizer_contains_mathieu_cover {U : Type*} [Group U] [Finite U]
    (f : U →* Model) (hf : Function.Surjective f) (hk : f.ker ≤ center U)
    (hthree : Nat.Coprime 3 (Nat.card f.ker)) (x : U) (hx : orderOf x = 3) :
    ∃ B : Subgroup U, IsQuasisimple B ∧ B ≤ centralizer ({x} : Set U) ∧
      Nonempty ((B ⧸ center B) ≃* Sporadic.Mathieu.M22) := by
  obtain ⟨t,ht,htf,hQ,⟨eQ⟩⟩ :=
    InvolutionCentralizers.First.CubicResidual.exists_cubic_residual_of_central_cover
      f hf hk hthree
  let R := InvolutionCentralizers.First.centralizer.comap f
  let C := centralizer ({t} : Set R)
  let Q := solvableResidual C
  let i : C →* U := R.subtype.comp C.subtype
  have hi : Function.Injective i := R.subtype_injective.comp C.subtype_injective
  obtain ⟨k,l,hk3,hl3,hconj⟩ := cubic_powers_conjugate (f (t : U)) (f x) htf
    (image_cubic_order f hthree x hx)
  have htk : orderOf ((t : U) ^ k) = 3 := by
    apply Nat.dvd_antisymm
    · exact (orderOf_pow_dvd k).trans (by rw [orderOf_coe t,ht])
    · have he : orderOf (f ((t : U) ^ k)) = 3 := by rw [map_pow]; exact hk3
      exact he ▸ orderOf_map_dvd f ((t : U) ^ k)
  have hxl : orderOf (x ^ l) = 3 := by
    apply Nat.dvd_antisymm
    · exact (orderOf_pow_dvd l).trans (by rw [hx])
    · have he : orderOf (f (x ^ l)) = 3 := by rw [map_pow]; exact hl3
      exact he ▸ orderOf_map_dvd f (x ^ l)
  have hc := f.isConj_of_map_isConj_of_prime_order_of_coprime_ker hf hthree htk hxl
    (by simpa only [map_pow] using hconj)
  obtain ⟨g,hg⟩ := isConj_iff.mp hc
  let j := (MulAut.conj g).toMonoidHom.comp i
  let B := Q.map j
  let e : Q ≃* B := Q.equivMapOfInjective j ((MulAut.conj g).injective.comp hi)
  let := hQ
  have hZ : (center B).map e.symm.toMonoidHom = center Q := by
    apply le_antisymm
    · rintro _ ⟨b,hb,rfl⟩
      exact (centerCongr e.symm ⟨b,hb⟩).property
    · intro q hq
      exact ⟨e q,(centerCongr e ⟨q,hq⟩).property,e.symm_apply_apply q⟩
  refine ⟨B,IsQuasisimple.of_mulEquiv e,?_,
    ⟨(QuotientGroup.congr _ _ e.symm hZ).trans eQ⟩⟩
  rw [←centralizer_cubic_power x hx l hxl]
  rintro b ⟨c,hc,rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  have hct : Commute (i c) (t : U) := by
    exact congrArg R.subtype (mem_centralizer_singleton_iff.mp c.property)
  have hm := (hct.pow_right k).map (MulAut.conj g).toMonoidHom
  change g * (i c) * g⁻¹ * (g * (t : U) ^ k * g⁻¹) =
    (g * (t : U) ^ k * g⁻¹) * (g * (i c) * g⁻¹) at hm
  change (g * i c * g⁻¹) * x ^ l = x ^ l * (g * i c * g⁻¹)
  simpa only [hg] using hm

/-- The same M₂₂ covering subgroup lies in the literal full cubic-centralizer
residual. No identification of that whole residual is assumed. -/
theorem cubic_residual_contains_mathieu_cover {U : Type*} [Group U] [Finite U]
    (f : U →* Model) (hf : Function.Surjective f) (hk : f.ker ≤ center U)
    (hthree : Nat.Coprime 3 (Nat.card f.ker)) (x : U) (hx : orderOf x = 3) :
    ∃ B : Subgroup U, IsQuasisimple B ∧
      B ≤ (solvableResidual (centralizer ({x} : Set U))).map
        (centralizer ({x} : Set U)).subtype ∧
      Nonempty ((B ⧸ center B) ≃* Sporadic.Mathieu.M22) := by
  obtain ⟨B,hB,hBC,he⟩ := cubic_centralizer_contains_mathieu_cover f hf hk hthree x hx
  let C := centralizer ({x} : Set U)
  let E := B.subgroupOf C
  let := hB
  let e : E ≃* B := subgroupOfEquivOfLe hBC
  let : Group.IsPerfect E := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have hh := map_mono (f := C.subtype) (le_solvableResidual_of_isPerfect E)
  rw [map_subgroupOf_eq_of_le hBC] at hh
  exact ⟨B,hB,hh,he⟩

end Janko4.LocalStructure
