module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer.Index
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer.Seed
public import Theory.Representation.SL3DoubledNaturalOffenders.NormalizerIndex

/-!
# The full doubled automizer bound and the source bounds of 11.2.1

Bijective coordinates on the original V_M give a faithful binary action of
Aut_M(V_M), with its relative layer identified with the same full SL₃.
The doubled normalizer index divides (q−1)|GL₂(q)|n. A genuine Cartan
witness normalizes the layer Sylow, whose odd exponent divides q−1.
Removing the two-part and applying the primitive-divisor bound gives
n′ ≤ 2n. Together with the proved seed bound, this constructs both
AutomizerBounds clauses without a further model or numerical hypothesis.

The generation application still needs the separately owned exact
OddKernelNormalizer contract; SourceConsumers records that application.
Source: Aschbacher–Smith, 11.2.1, printed pp.766–767, using A.3.15
and E.3.36–38. Full covering centers and literal conjugation are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterE.Section06.FixedPointBounds
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer
variable {X : Type*} [Group X] [Finite X]

/-- Two-primary factors in a layer index do not change the Cartan bound. -/
theorem nPrime_le_of_two_power_layer_index (K : Subgroup X) [K.Normal]
    (hK : SolvableSylowControl 2 K) {n k t : ℕ} (hn : 0 < n)
    (hindex : K.index ∣ 2^t * (n * (2^n-1)^k))
    (hexp : ∀ (Q : Sylow 2 K) (b : K), b ∈ normalizer (Q : Set K) →
      Odd (orderOf b) → b^(2^n-1) = 1) : nPrime X ≤ n := by
  apply nPrime_le_iff.mpr
  intro c w
  let := w.cyclic
  obtain ⟨a,ha⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp
    (inferInstance : IsCyclic w.cyclicGroup)
  have ho : Odd (orderOf (a : X)) := by
    rw [Subgroup.orderOf_coe,ha]
    exact w.odd.of_dvd_nat (card_dvd_of_le w.cyclic_le)
  have hmem : (a : X) ∈ normalizer ((w.sylow : Subgroup X) ⊓ K : Set X) :=
    witness_normalizes_layer_sylow K hK w (mem_sup_left (w.cyclic_le a.property))
  have hd := orderOf_dvd_of_pow_eq_one
    (normalizer_pow_eq_one_of_layer_index K hexp w.sylow a hmem ho)
  rw [Subgroup.orderOf_coe,ha,w.card] at hd
  apply Theory.NumberTheory.binary_mersenne_exponent_le_of_torus_power_dvd hn (k := k+1)
  have ho' : Odd (2^c-1) := by rwa [Subgroup.orderOf_coe,ha,w.card] at ho
  apply (ho'.coprime_two_right.pow_right t).dvd_of_dvd_mul_left
  have h := hd.trans (Nat.mul_dvd_mul hindex (dvd_refl (2^n-1)))
  simpa only [pow_succ,mul_assoc] using h

private theorem gl_two_card (F : Type*) [Field F] [Finite F] :
    Nat.card (GL (Fin 2) F) = Nat.card F * (Nat.card F-1) * (Nat.card F^2-1) := by
  let := Fintype.ofFinite F
  rw [Matrix.card_GL_field,←Nat.card_eq_fintype_card]
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  have he : Nat.card F^2 - Nat.card F = Nat.card F * (Nat.card F-1) := by
    rw [Nat.mul_sub_left_distrib,pow_two,mul_one]
  rw [he]
  exact Nat.mul_comm _ _

private theorem doubled_index_arithmetic {n : ℕ} (F : Type*) [Field F]
    [Finite F] (hc : Nat.card F = 2^n) :
    ((2^n-1) * Nat.card (GL (Fin 2) F))*n ∣
      2^n * ((2*n) * (2^(2*n)-1)^3) := by
  have hd : 2^n-1 ∣ 2^(2*n)-1 := Nat.pow_sub_one_dvd_pow_sub_one 2 (dvd_mul_left n 2)
  rw [gl_two_card F,hc,←pow_mul,show n*2=2*n by omega]
  have h := Nat.mul_dvd_mul (Nat.mul_dvd_mul hd hd) (dvd_refl (2^(2*n)-1))
  have he : (2^n-1)*((2^n-1)*(2^(2*n)-1)) ∣ (2^(2*n)-1)^3 := by
    simpa only [pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using h
  have hh := Nat.mul_dvd_mul (dvd_refl (2^n))
    (Nat.mul_dvd_mul (dvd_mul_left n 2) he)
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hh
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterE.Section06 CFSG.Quasithin.ChapterE.Section06.FixedPointBounds
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The original doubled coordinates faithfully realize the ambient automizer
and identify its relative layer with the same full SL₃ marking. -/
theorem doubled_action_data (h : DoubledNatural D S) :
    let U := Source.conjugateSpan (normalizer (L : Set G)) V
    let J := inducedAutomizer U (normalizer (L : Set G))
    let K := (inducedAutomizer U L).subgroupOf J
    ∃ e : K ≃* Matrix.SpecialLinearGroup (Fin 3) S.field.Carrier,
      ∃ ρ : Representation (ZMod 2) J (Fin 2 → Fin 3 → S.field.Carrier),
        Function.Injective ρ ∧ ∀ (g : K) v,
          ρ g v = SL3DoubledNaturalOffenders.representation S.field.Carrier (e g) v := by
  obtain ⟨m,⟨d⟩⟩ := h
  let U := Source.conjugateSpan (normalizer (L : Set G)) V
  let M := normalizer (L : Set G)
  let J := inducedAutomizer U M
  let K := (inducedAutomizer U L).subgroupOf J
  have hMU : M ≤ normalizer (U : Set G) := le_normalizer_componentOrbit V M
  have hLU : L ≤ normalizer (U : Set G) := L.le_normalizer.trans hMU
  have hLJ : inducedAutomizer U L ≤ J := map_mono (comap_mono L.le_normalizer)
  let η : L →* K := (subgroupOfEquivOfLe hLJ).symm.toMonoidHom.comp (localAction U L hLU)
  have hη : Function.Surjective η :=
    (subgroupOfEquivOfLe hLJ).symm.surjective.comp (localAction_surjective U L hLU)
  let q := m.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := m.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  have hi : Function.Injective d.coordinates := by
    apply d.coordinates.ker_eq_bot_iff.mp
    rw [d.kernel_eq,bot_subgroupOf]
  let : IsElementaryAbelian 2 U := Preliminary.fullModule_elementary D S
  let E : Additive U ≃ₗ[ZMod 2] (Fin 2 → Fin 3 → S.field.Carrier) :=
    LinearEquiv.ofBijective (d.coordinates.toAdditiveLeft.toZModLinearMap 2) ⟨hi,d.onto⟩
  let τ : Representation (ZMod 2) J (Additive U) := (automizerRepresentation U).comp J.subtype
  let ρ : Representation (ZMod 2) J (Fin 2 → Fin 3 → S.field.Carrier) :=
    E.conjRingEquiv.toMonoidHom.comp τ
  have hρ : Function.Injective ρ :=
    E.conjRingEquiv.injective.comp ((automizerRepresentation_injective U).comp Subtype.val_injective)
  have heq (l : L) (v : Fin 2 → Fin 3 → S.field.Carrier) :
      ρ (η l) v = SL3DoubledNaturalOffenders.representation S.field.Carrier (q l) v := by
    obtain ⟨a,ha⟩ := d.onto (Multiplicative.ofAdd v)
    have he : E (Additive.ofMul a) = v := congrArg Multiplicative.toAdd ha
    rw [←he]
    change E (automizerRepresentation U (η l).val.val (E.symm (E (Additive.ofMul a)))) = _
    rw [E.symm_apply_apply]
    exact (d.equivariant l a).trans rfl
  have hker : η.ker = q.ker := by
    ext l
    change η l = 1 ↔ q l = 1
    constructor
    · intro hl
      apply SL3DoubledNaturalOffenders.representation_injective
      rw [map_one]
      apply LinearMap.ext
      intro v
      rw [←heq,hl,Subgroup.coe_one,map_one]
    · intro hl
      apply Subtype.ext
      apply hρ
      apply LinearMap.ext
      intro v
      rw [heq,hl,map_one,Subgroup.coe_one,map_one]
  let e : K ≃* Matrix.SpecialLinearGroup (Fin 3) S.field.Carrier :=
    (QuotientGroup.quotientKerEquivOfSurjective η hη).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective q hq))
  have he (l : L) : e (η l) = q l := by
    change e ((QuotientGroup.quotientKerEquivOfSurjective η hη) (QuotientGroup.mk' _ l)) = _
    simp only [e,MulEquiv.trans_apply,MulEquiv.symm_apply_apply]
    rfl
  refine ⟨e,ρ,hρ,?_⟩
  intro g v
  obtain ⟨l,rfl⟩ := hη g
  rw [he]
  exact heq l v
/-- The complete automizer bound on the original doubled full module. -/
theorem doubled_nPrime_le (h : DoubledNatural D S) :
    nPrime (inducedAutomizer
      (Source.conjugateSpan (normalizer (L : Set G)) V)
      (normalizer (L : Set G))) ≤ 2 * S.field.degree := by
  let U := Source.conjugateSpan (normalizer (L : Set G)) V
  let M := normalizer (L : Set G)
  let J := inducedAutomizer U M
  let K := (inducedAutomizer U L).subgroupOf J
  have hMU : M ≤ normalizer (U : Set G) := le_normalizer_componentOrbit V M
  let hLN : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : K.Normal := inducedAutomizer_normal_in L.le_normalizer hMU hLN
  obtain ⟨e,ρ,hρ,he⟩ := doubled_action_data D S h
  have hi := SL3DoubledNaturalOffenders.doubled_layer_index_dvd S.field.Carrier
    S.field.card_eq K e ρ hρ he
  have hn : 0 < S.field.degree := by have := S.nonbinary; omega
  apply nPrime_le_of_two_power_layer_index K
    (relative_layer_solvable_sylow_control D S (le_componentOrbit V M) L.le_normalizer hMU)
    (n := 2 * S.field.degree) (k := 3) (t := S.field.degree) (by omega)
    (hi.trans (doubled_index_arithmetic S.field.Carrier S.field.card_eq))
  intro Q b hb ho
  let P := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hb' : e b ∈ normalizer (P : Set (Matrix.SpecialLinearGroup (Fin 3) S.field.Carrier)) :=
    (Q : Subgroup K).le_normalizer_map e.toMonoidHom (mem_map_of_mem _ hb)
  have hp := odd_pow_eq_one_of_split_torus_quotient
    (Matrix.PSL3.CartanActions.BorelQuotient.sylowSLNormalizerQuotientEquiv
      S.field.Carrier hn S.field.card_eq P) ⟨e b,hb'⟩
    (by simpa only [Subgroup.orderOf_mk,e.orderOf_eq] using ho)
  have hp' : b^(2^S.field.degree-1) = 1 := by
    apply e.injective
    rw [map_pow,map_one]
    simpa only [Subgroup.coe_pow,Subgroup.coe_one,S.field.card_eq] using congrArg Subtype.val hp
  obtain ⟨k,hk⟩ := (Nat.pow_sub_one_dvd_pow_sub_one (x := 2)
    (dvd_mul_left S.field.degree 2))
  rw [hk,pow_mul,hp',one_pow]

/-- Both original automizer bounds of 11.2.1, with no remaining model premise. -/
theorem automizerBounds : AutomizerBounds D S :=
  ⟨seed_nPrime_le D S,doubled_nPrime_le D S⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer
