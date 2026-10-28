module

public import Theory.ElementaryAbelian.Extraspecial
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Abelian size bounds in extraspecial groups at any prime

The central commutator pairing embeds an abelian subgroup modulo the center
into the dual of its ambient quotient, giving |A|² ≤ p|D|. Adjoining the
center removes a center-containment premise. Equality makes A self-centralizing.
Only the central quotient must be elementary; the whole group need not
have exponent p. This is the pairing used in Aschbacher45.8,p246.
-/

open scoped IsMulCommutative commutatorElement
open Subgroup

private theorem prime_hom_card_le
    {p : ℕ} [Fact p.Prime] {X Z : Type*} [Group X] [Finite X] [IsElementaryAbelian p X]
    [Group Z] [Finite Z] [IsElementaryAbelian p Z] (hZ : Nat.card Z = p) :
    Nat.card (X →* Z) ≤ Nat.card X := by
  classical
  let b := Module.Basis.ofVectorSpace (ZMod p) (Additive X)
  let I := Module.Basis.ofVectorSpaceIndex (ZMod p) (Additive X)
  let evaluation : (X →* Z) → (I → Z) := fun f i => f (b i).toMul
  have hinj : Function.Injective evaluation := by
    intro f g heq
    apply MonoidHom.toAdditive.injective
    apply (AddMonoidHom.toZModLinearMap_injective p)
    apply b.ext
    intro i
    exact congrArg Additive.ofMul (congrFun heq i)
  have hcard := Nat.card_le_card_of_injective evaluation hinj
  have hX : Nat.card X = p ^ Nat.card I := by
    let _ : Fintype X := Fintype.ofFinite X
    let _ : Fintype I := Fintype.ofFinite I
    simpa only [Nat.card_eq_fintype_card, Fintype.card_additive, ZMod.card] using
      Module.card_fintype b
  simpa only [Nat.card_fun, hZ, ← hX] using hcard

private theorem extraspecial_commutator_mem_center
    {p : ℕ} [Fact p.Prime] {Y : Type*} [Group Y] [IsExtraspecial p Y] (x y : Y) :
    ⁅x,y⁆ ∈ center Y := by
  let _ := IsExtraspecial.quotient_elementary_abelian p Y
  apply (QuotientGroup.eq_one_iff _).mp
  change (QuotientGroup.mk' (center Y)) ⁅x,y⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

private def centralCommutatorHom
    {p : ℕ} [Fact p.Prime] {Y : Type*} [Group Y] [IsExtraspecial p Y] (x : Y) : Y →* center Y where
  toFun y := ⟨⁅x,y⁆, extraspecial_commutator_mem_center (p := p) x y⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by
    apply Subtype.ext
    change ⁅x,a*b⁆ = ⁅x,a⁆ * ⁅x,b⁆
    rw [commutatorElement_mul_right_eq_mul_conj,
      mul_assoc ⁅x,a⁆ a ⁅x,b⁆,
      mem_center_iff.mp (extraspecial_commutator_mem_center (p := p) x b) a]
    simp only [← mul_assoc, mul_inv_cancel_right]

/-- The square of the order of a center-containing abelian subgroup is
at most p times the order of the extraspecial ambient p-group. -/
public theorem extraspecial_prime_abelian_card_sq_le
    {p : ℕ} [Fact p.Prime] {Y : Type*} [Group Y] [Finite Y] [IsExtraspecial p Y]
    (E : Subgroup Y) [IsMulCommutative E]
    (hZE : center Y ≤ E) : (Nat.card E)^2 ≤ p * Nat.card Y := by
  classical
  let _ := IsExtraspecial.quotient_elementary_abelian p Y
  let _ : E.Normal := ⟨fun x hx g => by
    have heq : g*x*g⁻¹ = ⁅g,x⁆*x := by simp [commutatorElement_def, mul_assoc]
    rw [heq]
    exact E.mul_mem (hZE (extraspecial_commutator_mem_center (p := p) g x)) hx⟩
  let _ : IsElementaryAbelian p (center Y) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun z => by
      simpa only [IsExtraspecial.center_order_p p Y] using (pow_card_eq_one' (x := z)) }
  let _ : IsElementaryAbelian p (Y ⧸ E) := {
    toIsMulCommutative := ⟨⟨fun x y => by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective E x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective E y
      apply commutatorElement_eq_one_iff_mul_comm.mp
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr
        (hZE (extraspecial_commutator_mem_center (p := p) a b))⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective E x
      rw [← map_pow]
      apply (QuotientGroup.eq_one_iff _).mpr
      apply hZE
      apply (QuotientGroup.eq_one_iff _).mp
      change (QuotientGroup.mk' (center Y)) (a^p) = 1
      rw [map_pow]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p (Y ⧸ center Y)) _ }
  have hkill (e : E) : E ≤ (centralCommutatorHom (p := p) (e : Y)).ker := by
    intro x hx
    change (⟨⁅(e : Y),x⁆, _⟩ : center Y) = 1
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (congrArg Subtype.val (mul_comm e (⟨x,hx⟩ : E)))
  let pairing : E →* ((Y ⧸ E) →* center Y) := {
    toFun e := QuotientGroup.lift E (centralCommutatorHom (p := p) (e : Y)) (hkill e)
    map_one' := by
      apply MonoidHom.ext
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective E q
      apply Subtype.ext
      change ⁅(1 : Y),y⁆ = 1
      simp
    map_mul' e f := by
      apply MonoidHom.ext
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective E q
      apply Subtype.ext
      change ⁅(e : Y)*(f : Y),y⁆ = ⁅(e : Y),y⁆ * ⁅(f : Y),y⁆
      rw [commutatorElement_mul_left_eq_conj_mul,
        mem_center_iff.mp (extraspecial_commutator_mem_center (p := p) (f : Y) y) (e : Y)]
      simp only [mul_inv_cancel_right]
      exact (mem_center_iff.mp (extraspecial_commutator_mem_center (p := p) (f : Y) y) ⁅(e : Y),y⁆).symm }
  have hker : pairing.ker = (center Y).subgroupOf E := by
    ext e
    change pairing e = 1 ↔ (e : Y) ∈ center Y
    constructor
    · intro heq
      rw [mem_center_iff]
      intro y
      have heval := congrArg (fun f : (Y ⧸ E) →* center Y => (f (QuotientGroup.mk' E y) : Y)) heq
      change ⁅(e : Y),y⁆ = 1 at heval
      exact (commutatorElement_eq_one_iff_mul_comm.mp heval).symm
    · intro he
      apply MonoidHom.ext
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective E q
      apply Subtype.ext
      change ⁅(e : Y),y⁆ = 1
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp he y).symm
  have hkerCard : Nat.card pairing.ker = p := by
    rw [hker, Nat.card_congr (subgroupOfEquivOfLe hZE).toEquiv]
    exact IsExtraspecial.center_order_p p Y
  let _ : Finite ((Y ⧸ E) →* center Y) :=
    Finite.of_injective (fun f : (Y ⧸ E) →* center Y => (f : (Y ⧸ E) → center Y))
      DFunLike.coe_injective
  have hrange : Nat.card pairing.range ≤ Nat.card (Y ⧸ E) :=
    (Nat.card_le_card_of_injective pairing.range.subtype pairing.range.subtype_injective).trans
      (prime_hom_card_le (IsExtraspecial.center_order_p p Y))
  have hpair := pairing.ker.card_mul_index
  rw [Subgroup.index_ker, hkerCard] at hpair
  have hquot := E.card_mul_index
  rw [Subgroup.index_eq_card] at hquot
  calc
    (Nat.card E)^2 = Nat.card E * (p * Nat.card pairing.range) := by rw [hpair,pow_two]
    _ ≤ Nat.card E * (p * Nat.card (Y ⧸ E)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left p hrange)
    _ = p * Nat.card Y := by rw [←hquot]; ring

/-- An abelian subgroup attaining the extraspecial bound is self-centralizing. -/
public theorem extraspecial_prime_centralizer_eq_of_card_sq
    {p : ℕ} [Fact p.Prime] {Y : Type*} [Group Y] [Finite Y] [IsExtraspecial p Y]
    (E : Subgroup Y) [IsMulCommutative E] (hZE : center Y ≤ E)
    (hcard : (Nat.card E)^2 = p * Nat.card Y) :
    centralizer (E : Set Y) = E := by
  apply le_antisymm
  · intro x hx
    have hxE : zpowers x ≤ centralizer (E : Set Y) := zpowers_le.mpr hx
    let : IsMulCommutative (E ⊔ zpowers x : Subgroup Y) := by
      apply le_centralizer_iff_isMulCommutative.mp
      exact sup_le
        (le_centralizer_iff.mpr (sup_le E.le_centralizer hxE))
        (le_centralizer_iff.mpr
          (sup_le (le_centralizer_iff.mp hxE) (zpowers x).le_centralizer))
    have hsq := extraspecial_prime_abelian_card_sq_le (p := p) (E ⊔ zpowers x)
      (hZE.trans le_sup_left)
    have he : E = E ⊔ zpowers x := eq_of_le_of_card_ge le_sup_left (by nlinarith)
    exact he ▸ (mem_sup_right (mem_zpowers x))
  · exact E.le_centralizer

/-- The abelian subgroup bound does not require the subgroup to contain the center. -/
public theorem extraspecial_prime_abelian_card_sq_le_any
    {p : ℕ} [Fact p.Prime] {Y : Type*} [Group Y] [Finite Y] [IsExtraspecial p Y]
    (E : Subgroup Y) [IsMulCommutative E] : (Nat.card E)^2 ≤ p * Nat.card Y := by
  let F := E ⊔ center Y
  have hZE : center Y ≤ centralizer (E:Set Y) :=
    fun z hz e _ => mem_center_iff.mp hz e
  let : IsMulCommutative F := le_centralizer_iff_isMulCommutative.mp
    (sup_le (le_centralizer_iff.mpr (sup_le E.le_centralizer hZE))
      (le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp hZE) (center Y).le_centralizer)))
  have hh := extraspecial_prime_abelian_card_sq_le (p:=p) F le_sup_right
  have hm := Subgroup.card_le_of_le (show E≤F from le_sup_left)
  nlinarith

/-- Equality in the abelian size bound forces self-centralization, even before
center containment has been supplied. -/
public theorem extraspecial_prime_selfcentralizing_of_card_sq
    {p : ℕ} [Fact p.Prime] {Y : Type*} [Group Y] [Finite Y] [IsExtraspecial p Y]
    (E : Subgroup Y) [IsMulCommutative E]
    (hcard : (Nat.card E)^2 = p * Nat.card Y) : centralizer (E:Set Y)=E := by
  apply le_antisymm
  · intro x hx
    have hxE : zpowers x ≤ centralizer (E:Set Y) := zpowers_le.mpr hx
    let : IsMulCommutative (E⊔zpowers x:Subgroup Y) :=
      le_centralizer_iff_isMulCommutative.mp
        (sup_le (le_centralizer_iff.mpr (sup_le E.le_centralizer hxE))
          (le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp hxE) (zpowers x).le_centralizer)))
    have hh := extraspecial_prime_abelian_card_sq_le_any (p:=p) (E⊔zpowers x)
    have he : E=E⊔zpowers x := eq_of_le_of_card_ge le_sup_left (by nlinarith)
    exact he ▸ mem_sup_right (mem_zpowers x)
  · exact E.le_centralizer
