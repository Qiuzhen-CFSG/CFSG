module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.LinearUnitaryPrime
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicSeparation
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.AffineExclusion
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.UnitaryLayers

/-!
# The larger linear degrees in a linear–unitary octagon

A separating prime in the linear Cartan fixes every unitary root. Its
cyclic group is normalized by both reflections, so it fixes no nonidentity
point of any linear root. Unique root coordinates give its fixed radical
order 2^(9b). The crossed unitary root and its nontrivial square are moved
by the unitary reflection. Thus the fixed radical and its Frattini subgroup
both have a nontrivial unitary action, giving two binary layers of order
at least 2^(6b), a contradiction.

Source: Fong--Seitz I (6F), printed p.46, the cases a=4b and a=6b.
The original-factor and Chapter 12 applications retain both endpoint
orientations and the special/projective scalar conventions.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative MatrixGroups Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

include split in
private theorem cyclic_normalized_of_simple_lifts
    (i j : Fin 2) (hij : i ≠ j) (a b : Q.tits.N)
    (ha : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) a = Q.simple i)
    (hb : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) b = Q.simple j)
    {t : X ⧸ Q.D} (ht : t ∈ Q.tits.B ⊓ Q.tits.N)
    (hat : (a : X ⧸ Q.D)*t*(a : X ⧸ Q.D)⁻¹ = t⁻¹)
    (hbt : Commute (b : X ⧸ Q.D) t) :
    Q.tits.N ≤ normalizer (zpowers t : Set (X ⧸ Q.D)) := by
  classical
  let := split.abelian
  let A := normalizer (zpowers t : Set (X ⧸ Q.D))
  have hH : Q.tits.B ⊓ Q.tits.N ≤ A :=
    ((Subgroup.le_centralizer (Q.tits.B ⊓ Q.tits.N)).trans
      (centralizer_le (zpowers_le.mpr ht))).trans (_root_.centralizer_le_normalizer (zpowers t))
  have haA : (a : X ⧸ Q.D) ∈ A := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    change zpowers ((a : X ⧸ Q.D)*t*(a : X ⧸ Q.D)⁻¹) = zpowers t
    rw [hat,zpowers_inv]
  have hbA : (b : X ⧸ Q.D) ∈ A := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    change zpowers ((b : X ⧸ Q.D)*t*(b : X ⧸ Q.D)⁻¹) = zpowers t
    rw [hbt.eq,mul_inv_cancel_right]
  let s (k : Fin 2) := if k = i then a else b
  have hs (k : Fin 2) : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) (s k) = Q.simple k := by
    by_cases hk : k = i
    · simpa [s,hk] using ha
    · have hkj : k = j := by omega
      simpa [s,hkj,hij.symm] using hb
  have hsA (k : Fin 2) : (s k : X ⧸ Q.D) ∈ A := by
    dsimp only [s]
    split_ifs <;> assumption
  intro g hg
  let q := QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N)
  let gN : Q.tits.N := ⟨g,hg⟩
  obtain ⟨k,hk,hqk⟩ := UnitarySource.exists_weyl_lift_in Q s hs A hsA (q gN)
  have hdiff : gN*k⁻¹ ∈ (Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (gN*k⁻¹) = 1
    rw [map_mul,map_inv,hqk,mul_inv_cancel]
  have hz := A.mul_mem (hH hdiff) hk
  change (g*(k : X ⧸ Q.D)⁻¹)*(k : X ⧸ Q.D) ∈ A at hz
  simpa only [inv_mul_cancel_right] using hz

private theorem linear_cyclic_fixedFree_conjugates
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (i : Fin 2) (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (μi : localGroup Q split i ≃* PSL(2,E)) (si : HexagonStructure.RootReflection Q split i)
    {t : X ⧸ Q.D} (htH : t ∈ Q.tits.B ⊓ Q.tits.N)
    (htR : t ∈ rankOne Q split i) (htne : t ≠ 1)
    (hTN : Q.tits.N ≤ normalizer (zpowers t : Set (X ⧸ Q.D))) (w : Weyl Q) :
    rootAt Q split i w ⊓ centralizer (zpowers t : Set (X ⧸ Q.D)) = ⊥ := by
  have hf : simpleRoot Q split i ⊓ centralizer (zpowers t : Set (X ⧸ Q.D)) = ⊥ := by
    apply bot_unique
    apply le_trans (inf_le_inf_left _ (centralizer_le ?_))
      (le_of_eq (rankOne_cartan_root_fixedFree Q split i hKi μi si htH htR htne))
    exact Set.singleton_subset_iff.mpr (mem_zpowers t)
  let n := representative w
  have hh := congrArg (fun A => rightConjugate A (n : X ⧸ Q.D)) hf
  rw [rightConjugate_inf,rightConjugate_eq_self _
    (normalizer_le_normalizer_centralizer (zpowers t) (hTN n.property))] at hh
  have hb : rightConjugate (⊥ : Subgroup (X ⧸ Q.D)) (n : X ⧸ Q.D) = ⊥ := by
    ext x
    change (n : X ⧸ Q.D)*x*(n : X ⧸ Q.D)⁻¹ = 1 ↔ x = 1
    exact (MulAut.conj (n : X ⧸ Q.D)).map_eq_one_iff
  exact hh.trans hb


/-- A nonidentity linear Cartan element fixing the other root family is
fixed-point-free on every conjugate of the linear root. -/
theorem linear_cartan_separated_roots
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (μi : localGroup Q split i ≃* PSL(2,E))
    {t : X ⧸ Q.D} (htH : t ∈ Q.tits.B ⊓ Q.tits.N)
    (htR : t ∈ rankOne Q split i) (htne : t ≠ 1)
    (hfix : ∀ w, t ∈ centralizer (rootAt Q split j w : Set (X ⧸ Q.D))) :
    ∀ w, rootAt Q split i w ⊓ centralizer ({t} : Set (X ⧸ Q.D)) = ⊥ := by
  let si := UnitarySource.actorReflection Q split i
  let sj := UnitarySource.actorReflection Q split j
  have hR := separated_rankOne_centralized Q split j t hfix
  have hsj : Commute (sj.val : X ⧸ Q.D) t :=
    mem_centralizer_singleton_iff.mp (hR sj.mem_rankOne)
  have hsi : (si.val : X ⧸ Q.D)*t*(si.val : X ⧸ Q.D)⁻¹ = t⁻¹ := by
    obtain ⟨u,hu⟩ := exists_alignedTorus_of_mem Q split i hKi μi si htH htR
    rw [←hu,reflection_alignedTorus]
    exact (alignedTorusHom Q split i hKi μi si).map_inv u
  have hTN : Q.tits.N ≤ normalizer (zpowers t : Set (X ⧸ Q.D)) :=
    cyclic_normalized_of_simple_lifts Q split i j hij si.val sj.val si.class_eq sj.class_eq
      htH hsi hsj
  intro w
  have hh := linear_cyclic_fixedFree_conjugates Q split i hKi μi si htH htR htne hTN w
  simpa only [zpowers_eq_closure,centralizer_closure] using hh

private theorem cross_root_moves_section (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) (s : HexagonStructure.RootReflection Q split j)
    (d : RootSection Q split j) (hd : d.denominator = ⊥)
    (a : X ⧸ Q.D) (ha : a ∈ rootAt Q split j (Q.simple i))
    (hax : a ∈ d.numerator) (hne : a ≠ 1) : d.action ≠ 1 := by
  let x : d.numerator := ⟨a,hax⟩
  let r : rankOne Q split j := ⟨s.val,s.mem_rankOne⟩
  intro he
  have hei : d.action r⁻¹ = 1 := by rw [he]; rfl
  have hx : d.numeratorAction r⁻¹ x = x := by
    have hh := congrArg (fun z : MulAut d.Carrier => z (QuotientGroup.mk x)) hei
    rw [d.action_mk] at hh
    have hh' := QuotientGroup.eq_iff_div_mem.mp hh
    rw [hd,mem_bot] at hh'
    exact div_eq_one.mp hh'
  have hxa : (s.val : X ⧸ Q.D)⁻¹*a*s.val = a := by
    have hh := congrArg Subtype.val hx
    rw [d.numeratorAction_apply] at hh
    simpa only [r,x,coe_inv,inv_inv] using hh
  have hconj : a ∈ rootAt Q split j (Q.simple i*Q.simple j) := by
    rw [←rootAt_right Q split j (Q.simple i) (Q.simple j) s.val s.class_eq,←hxa]
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)⁻¹*a*s.val)*
      (s.val : X ⧸ Q.D)⁻¹ ∈ rootAt Q split j (Q.simple i)
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using ha
  obtain ⟨_,hB,hdis⟩ := cross_root_separation Q split hm i j hij
  exact hne (disjoint_def.mp hdis ha (hB hconj))

/-- The actual fixed radical cannot consist of three unitary roots:
its two nontrivial Frattini layers already require four root orders. -/
theorem separated_unitary_radical_false
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {b : ℕ} (hb : 2 ≤ b) (hcard : Nat.card F = (2^b)^2)
    (hconj : ∀ x, J.conj x=x^(2^b))
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    (hroot : Nat.card (simpleRoot Q split j) = (2^b)^3)
    (hsquare : ∃ a : simpleRoot Q split j, a^2 ≠ 1)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)))
    (hc : ∀ w : Weyl Q,
      (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split j w : Set (X ⧸ Q.D)) ∧
      rootAt Q split i w ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥) : False := by
  let d : RootSection Q split j := {
    numerator := simpleRemainder Q split j ⊓ centralizer ({(c : X ⧸ Q.D)} : Set _)
    le_radical := inf_le_left
    normalized := separated_radical_centralizer_normalized Q split j hKj c (fun w => (hc w).1)
    denominator := ⊥
    invariant _ := map_bot _ }
  let f := frattiniSection Q split j d
  let A := rootAt Q split j (Q.simple i)
  have hAd : A ≤ d.numerator := by
    change A ≤ simpleRemainder Q split j ⊓ centralizer ({(c : X ⧸ Q.D)} : Set _)
    rw [←separated_radical_centralizer_sup Q split hm j i hij.symm c hc]
    exact le_sup_left.trans le_sup_left
  obtain ⟨a,ha⟩ : ∃ a : A, a^2 ≠ 1 := by
    obtain ⟨u,hu⟩ := hsquare
    let e : A ≃* simpleRoot Q split j :=
      RootAction.conjugateEquiv (simpleRoot Q split j) (representative (Q.simple i))
    refine ⟨e.symm u,?_⟩
    intro he
    apply hu
    simpa only [map_pow,map_one,e.apply_symm_apply] using congrArg e he
  have hane : (a : X ⧸ Q.D) ≠ 1 := by
    intro he
    exact ha (by rw [show a=1 from Subtype.ext he,one_pow])
  have hmove : d.action ≠ 1 := cross_root_moves_section Q split hm i j hij
    (UnitarySource.actorReflection Q split j) d rfl a a.property (hAd a.property) hane
  let v : d.numerator := inclusion hAd a
  let : Fact (IsPGroup 2 d.numerator) := ⟨d.isTwo⟩
  have hmovePhi : f.action ≠ 1 := by
    apply cross_root_moves_section Q split hm i j hij
      (UnitarySource.actorReflection Q split j) f rfl ((a : X ⧸ Q.D)^2) (pow_mem a.property 2)
    · exact ⟨v^2,pth_power_mem_frattini_of_isPGroup (p:=2) v,rfl⟩
    · intro he
      exact ha (Subtype.ext he)
  have h1 := unitary_section_card_bound Q split j J hb hcard hconj σ hσ d hmove
  have h2 := unitary_section_card_bound Q split j J hb hcard hconj σ hσ f hmovePhi
  have hden : d.effectiveDenominator = frattini d.numerator := by
    rw [d.effectiveDenominator_eq]
    exact sup_bot_eq _
  have h1' : 2^(6*b) ≤ Nat.card (d.numerator ⧸ frattini d.numerator) := by
    change 2^(6*b) ≤ d.effectiveDenominator.index at h1
    rw [hden] at h1
    exact h1
  have h2' : 2^(6*b) ≤ Nat.card (frattini d.numerator) := by
    have hh := h2.trans (Nat.card_le_card_of_surjective _
      (QuotientGroup.mk'_surjective f.effectiveDenominator))
    exact hh.trans_eq (Nat.card_congr
      ((frattini d.numerator).equivMapOfInjective d.numerator.subtype
        d.numerator.subtype_injective).symm.toEquiv)
  have hlo : 2^(12*b) ≤ Nat.card d.numerator := by
    calc
      _ = 2^(6*b)*2^(6*b) := by rw [←pow_add]; congr 1; omega
      _ ≤ Nat.card (d.numerator ⧸ frattini d.numerator)*Nat.card (frattini d.numerator) :=
        Nat.mul_le_mul h1' h2'
      _ = _ := (frattini d.numerator).index_mul_card
  have hsize : Nat.card d.numerator = 2^(9*b) := by
    have hh := (octagon_separated_root_centralizer_orders Q split hm j i hij.symm c hc).1
    rw [hroot,←pow_mul,←pow_mul] at hh
    simpa only [Nat.mul_comm,Nat.mul_assoc] using hh
  rw [hsize] at hlo
  have hexp := (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).mp hlo
  omega

/-- The ratios four and six are impossible for a nonbinary unitary
endpoint. The separating actor and its two layer contradiction are constructed. -/
theorem octagon_mixed_unitary_no_larger_linear_field
    {E F : Type*} [Field E] [Finite E] [CharP E 2] [Field F] [Finite F]
    (J : HermitianForm 3 F) {b : ℕ} (hb : 2 ≤ b)
    (hcard : Nat.card F = (2^b)^2) (hconj : ∀ x, J.conj x=x^(2^b))
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    (hroot : Nat.card (simpleRoot Q split j) = (2^b)^3)
    (hsquare : ∃ a : simpleRoot Q split j, a^2 ≠ 1)
    {a : ℕ} (hE : Nat.card E = 2^a) (ha : 2*b < a) : False := by
  obtain ⟨r,t,hr,_,_,ht,ho,hfix⟩ := octagon_separating_prime_unitary_fixed
    Q split hm i j hij hKi hKj J μi μj hb hE hcard hconj ha
      (UnitarySource.actorReflection Q split i)
  have hne : t ≠ 1 := by
    intro he
    rw [he,orderOf_one] at ho
    exact hr.ne_one ho.symm
  have hfree := linear_cartan_separated_roots Q split i j hij hKi μi ht.1 ht.2 hne hfix
  exact separated_unitary_radical_false Q split J hb hcard hconj hm i j hij hKj σ hσ
    hroot hsquare ⟨t,ht.1⟩ (fun w => ⟨hfix w,hfree w⟩)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
