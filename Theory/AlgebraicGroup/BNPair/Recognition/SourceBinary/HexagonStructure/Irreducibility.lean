module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.MixedCommutators
public import Mathlib.GroupTheory.FixedPointFree
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderFormulas
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Irreducibility of the actual unequal-linear radical quotient

Both mixed commutators and the separating Cartan actor prove [R_j,V_j]=V_j.
The center calculation gives Z(V_j)=V_j'=C, and R_j centralizes C. The three
subgroups lemma now shows that any subgroup of V_j fixed modulo C lies in C.
Thus the actual quotient V_j/C has neither fixed subgroups nor trivial
quotients under R_j.

For an R_j-invariant C ≤ W ≤ V_j, the literal sections W/C and V_j/W
have orders whose product is |V_j/C|=2^(2a+2b)<2^(4b). One section has
order below the binary SL2 degree bound, so the earlier small-section
theorem makes its actual action trivial. The preceding two obstructions
force W=C or W=V_j. Pulling back each subrepresentation along the actual
abelianization map proves irreducibility of radicalRepresentation. Its
binary scalar structure and dimension 2a+2b are derived on this same carrier.

This proves the irreducibility assertion in the unequal linear branch of
Fong--Seitz I (6E)(b), printed pp.43--45, with a direct degree-budget proof
in place of the source's intermediate Cartan-module and Clifford argument.
The only earlier inputs are the actual local linear models, their kernel
inclusions and the chosen root reflections. There is no perfectness or
simplicity assumption on an unknown original group. The binary opposite
root, acting field four and primitive-divisor exponent six are included.
The companion CubicRatio proves the field ratio; nonlinear/solvable source
branches remain unproved.
The CFSG companion applies these results to the original/geometric marking
and the actual triality structural consumer.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups commutatorElement
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates GTwoSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem fixedFree_le_commutator {G : Type*} [Group G]
    (R A : Subgroup G) [Finite A] (t : G) (htR : t ∈ R)
    (htA : t ∈ normalizer (A : Set G)) (hfree : A ⊓ centralizer ({t} : Set G) = ⊥) :
    A ≤ ⁅R,A⁆ := by
  let f : MulAut A := A.normalizerMonoidHom ⟨t,htA⟩
  have hf : MonoidHom.FixedPointFree f := by
    intro a ha
    have he : t*(a : G)*t⁻¹ = a := congrArg Subtype.val ha
    apply Subtype.ext
    exact mem_bot.mp (hfree ▸ ⟨a.property,mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp he).symm⟩)
  intro a ha
  obtain ⟨b,hb⟩ := hf.commutatorMap_surjective ⟨a,ha⟩
  have he : (b : G)/(t*b*t⁻¹) = a := congrArg Subtype.val hb
  have he' : ⁅(b : G),t⁆ = a := by
    simpa only [commutatorElement_def,div_eq_mul_inv,mul_inv_rev,inv_inv,mul_assoc] using he
  rw [←he',commutator_comm]
  exact commutator_mem_commutator b.property htR

private theorem sq_simple (i : Fin 2) : Q.simple i*Q.simple i = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2
private theorem right_commutator (A B : Subgroup (X ⧸ Q.D)) (n : X ⧸ Q.D) :
    rightConjugate ⁅A,B⁆ n = ⁅rightConjugate A n,rightConjugate B n⁆ := by
  simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]

variable {F E : Type*} [Field F] [Finite F] [CharP F 2]
  [Field E] [Finite E] [CharP E 2]

/-- The actual larger rank-one group moves the entire canonical radical.
The separating Cartan actor moves both larger middle roots; conjugating the
proved short commutator supplies the two outside roots as well. -/
theorem unequal_linear_radical_fully_moved
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* PSL(2,F))
    (si : RootReflection Q split i) (sj : RootReflection Q split j)
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b) :
    ⁅rankOne Q split j,simpleRemainder Q split j⁆ = simpleRemainder Q split j := by
  let R := rankOne Q split j
  let V := simpleRemainder Q split j
  let W := ⁅R,V⁆
  let A := simpleRoot Q split i
  let B := rootAt Q split j (Q.simple i)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let D := rootAt Q split j (Q.simple i*Q.simple j)
  let E₀ := rootAt Q split i (Q.simple j)
  have hMV := middleRoots_le_remainder Q split hm i j hij
  have hBV : B ≤ V := (le_sup_left.trans le_sup_left).trans hMV
  have hDV : D ≤ V := le_sup_right.trans hMV
  have hRV : R ≤ normalizer (V : Set (X ⧸ Q.D)) :=
    (rankOne_le_parabolic Q split j).trans (remainder_parabolic_normalizes Q split j hKj)
  have hWV : W ≤ V := le_normalizer_iff_commutator_le_right.mp hRV
  have hshort := unequal_linear_short_commutator Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF
  have hUD := congrArg (fun H => rightConjugate H (si.val : X ⧸ Q.D)) hshort
  rw [right_commutator,
    rootAt_right Q split j _ _ si.val si.class_eq,
    rootAt_right Q split j _ _ si.val si.class_eq,
    rootAt_right Q split i _ _ si.val si.class_eq,
    sq_simple,rootAt_one,orthogonal_root_stabilizer Q split hm j i hij.symm,
    mul_assoc,sq_simple,mul_one] at hUD
  have hEW : E₀ ≤ W := hUD.symm.le.trans
    (commutator_mono (show simpleRoot Q split j ≤ R from le_sup_left) hDV)
  have hAW : A ≤ W := by
    have hc := comap_mono (f := (MulAut.conj (sj.val : X ⧸ Q.D)).toMonoidHom) hEW
    change rightConjugate E₀ (sj.val : X ⧸ Q.D) ≤ rightConjugate W (sj.val : X ⧸ Q.D) at hc
    change rightConjugate (rootAt Q split i (Q.simple j)) (sj.val : X ⧸ Q.D) ≤ _ at hc
    rw [rootAt_right Q split i _ _ sj.val sj.class_eq,sq_simple,rootAt_one,
      rightConjugate_eq_self W (normalizer_commutator_ge_left R V sj.mem_rankOne)] at hc
    exact hc
  have hlong := unequal_linear_long_commutator Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF
  have hCW : C ≤ W := hlong.symm.le.trans
    ((commutator_mono hAW hEW).trans (commutator_le_self W))
  obtain ⟨r,hr,hrF,hrE⟩ := Theory.NumberTheory.exists_binary_separating_prime ha hab
  obtain ⟨t,ht,_,_,_,_,hBfree,hDfree⟩ := exists_prime_cartan_separation Q split i j
    hKi hKj μi μj si sj hr (by rwa [hF]) (by rwa [hE])
  have hBW : B ≤ W := (fixedFree_le_commutator R B t ht.2
    (rootAt_torus_normalizes Q split j _ ht.1) hBfree).trans (commutator_mono le_rfl hBV)
  have hDW : D ≤ W := (fixedFree_le_commutator R D t ht.2
    (rootAt_torus_normalizes Q split j _ ht.1) hDfree).trans (commutator_mono le_rfl hDV)
  apply le_antisymm hWV
  intro x hx
  have hx' : x ∈ (simpleRemainder Q split j : Set (X ⧸ Q.D)) := hx
  rw [radical_five_product Q split hm i j hij] at hx'
  obtain ⟨abcd,⟨abc,⟨ab,⟨a,ha,b,hb,rfl⟩,c,hc,rfl⟩,d,hd,rfl⟩,e,he,rfl⟩ := hx'
  exact W.mul_mem (W.mul_mem (W.mul_mem (W.mul_mem (hAW ha) (hBW hb)) (hCW hc)) (hDW hd)) (hEW he)

private def invariantSubsection (j : Fin 2) (A B : Subgroup (X ⧸ Q.D))
    (hAV : A ≤ simpleRemainder Q split j)
    (hRA : rankOne Q split j ≤ normalizer (A : Set (X ⧸ Q.D)))
    (hAB : A ≤ normalizer (B : Set (X ⧸ Q.D)))
    (hRB : rankOne Q split j ≤ normalizer (B : Set (X ⧸ Q.D))) : RootSection Q split j where
  numerator := A
  le_radical := hAV
  normalized := hRA
  denominator := B.subgroupOf A
  normal := normal_subgroupOf_of_le_normalizer hAB
  invariant r := by
    apply le_antisymm
    · rintro x ⟨y,hy,rfl⟩
      exact (mem_normalizer_iff.mp (hRB r.property) _).mp hy
    · intro x hx
      refine ⟨A.normalizerMonoidHom ⟨(r⁻¹ : rankOne Q split j),hRA (inv_mem r.property)⟩ x,?_,?_⟩
      · exact (mem_normalizer_iff.mp (hRB (inv_mem r.property)) _).mp hx
      · change (A.normalizerMonoidHom.comp (inclusion hRA)) r
          ((A.normalizerMonoidHom.comp (inclusion hRA)) r⁻¹ x) = x
        rw [map_inv]
        exact MulEquiv.apply_symm_apply _ x

private theorem section_commutator_le_of_trivial {j : Fin 2} (d : RootSection Q split j)
    (hd : d.action = 1) :
    ⁅rankOne Q split j,d.numerator⁆ ≤ d.denominator.map d.numerator.subtype := by
  apply commutator_le.mpr
  intro r hr x hx
  let r' : rankOne Q split j := ⟨r,hr⟩
  let x' : d.numerator := ⟨x,hx⟩
  have he : d.action r' (QuotientGroup.mk x') = QuotientGroup.mk x' := by rw [hd]; rfl
  rw [d.action_mk] at he
  have hmem := QuotientGroup.eq_iff_div_mem.mp he
  refine ⟨d.numeratorAction r' x' / x',hmem,?_⟩
  change (r*x*r⁻¹)/x = ⁅r,x⁆
  simp only [commutatorElement_def,div_eq_mul_inv]

/-- A section fixed modulo the middle root lies in that root. The three
subgroups lemma uses [R,V]=V and the two centralizations of V'. -/
theorem unequal_linear_fixed_section_le_derived
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* PSL(2,F))
    (si : RootReflection Q split i) (sj : RootReflection Q split j)
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b)
    (W : Subgroup (X ⧸ Q.D)) (hWV : W ≤ simpleRemainder Q split j)
    (hfixed : ⁅rankOne Q split j,W⁆ ≤ rootAt Q split i (Q.simple j*Q.simple i)) :
    W ≤ rootAt Q split i (Q.simple j*Q.simple i) := by
  let R := rankOne Q split j
  let V := simpleRemainder Q split j
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  have hder := unequal_linear_derived_eq_middle_root Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF
  have hVC := derived_middle_root_radical_centralized Q split j hm i hij hKi μi hKj hder
  have hRC := derived_middle_root_centralized Q split j hKj μj sj hm i hij hder (by omega) hF
    (by rw [simpleRoot_card Q split i hKi μi,hE]; exact Nat.pow_lt_pow_right (by decide) (by omega))
  have h1 : ⁅⁅V,W⁆,R⁆ = ⊥ := by
    apply bot_unique ((commutator_mono ((commutator_mono le_rfl hWV).trans hder.le) le_rfl).trans ?_)
    rw [commutator_comm]
    exact hRC.le
  have h2 : ⁅⁅W,R⁆,V⁆ = ⊥ := by
    rw [commutator_comm W R]
    apply bot_unique ((commutator_mono hfixed le_rfl).trans ?_)
    rw [commutator_comm]
    exact hVC.le
  have hh := commutator_commutator_eq_bot_of_rotate h1 h2
  rw [unequal_linear_radical_fully_moved Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF] at hh
  exact (le_inf hWV (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh))).trans
    (unequal_linear_radical_center Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF).le

private theorem radical_quotient_card (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* PSL(2,F))
    {a b : ℕ} (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b) :
    (rootAt Q split i (Q.simple j*Q.simple i)).relIndex (simpleRemainder Q split j) =
      (2^a)^2*(2^b)^2 := by
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let V := simpleRemainder Q split j
  have hCV : C ≤ V := (exchanged_roots_le_remainder Q split hm i j hij).2
  have hCcard : Nat.card C = 2^a := by
    simp only [C,rootAt,card_rightConjugate,simpleRoot_card Q split i hKi μi,hE]
  have hUi : Nat.card (simpleRoot Q split i) = 2^a := (simpleRoot_card Q split i hKi μi).trans hE
  have hUj : Nat.card (simpleRoot Q split j) = 2^b := (simpleRoot_card Q split j hKj μj).trans hF
  have hU : Nat.card split.U = (2^a*2^b)^3 := by
    have hu := unipotent_card_even Q split 3 hm
    have hi : i = 0 ∨ i = 1 := by omega
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (hij rfl).elim
    · rwa [hUi,hUj] at hu
    · rwa [hUj,hUi,mul_comm (2^b) (2^a)] at hu
    · exact (hij rfl).elim
  have hVcard : Nat.card V = (2^a)^3*(2^b)^2 := by
    have hh := unipotent_card_simple Q split j
    rw [hU,hUj] at hh
    apply Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide : 0 < 2))
    calc
      2^b * Nat.card V = (2^a*2^b)^3 := hh.symm
      _ = 2^b*((2^a)^3*(2^b)^2) := by ring
  have hh := (C.subgroupOf V).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hCV).toEquiv,hCcard,hVcard] at hh
  apply Nat.eq_of_mul_eq_mul_right (Nat.pow_pos (by decide : 0 < 2))
  calc
    C.relIndex V * 2^a = (2^a)^3*(2^b)^2 := hh
    _ = ((2^a)^2*(2^b)^2)*2^a := by ring

/-- The only R_j-invariant subgroups between the actual derived root and
radical are the endpoints. This is the subgroup form of irreducibility on
V_j/V_j', using the literal section actions and the binary degree bound. -/
theorem unequal_linear_invariant_radical_subgroups
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* PSL(2,F))
    (si : RootReflection Q split i) (sj : RootReflection Q split j)
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b)
    (W : Subgroup (X ⧸ Q.D))
    (hCW : rootAt Q split i (Q.simple j*Q.simple i) ≤ W)
    (hWV : W ≤ simpleRemainder Q split j)
    (hRW : rankOne Q split j ≤ normalizer (W : Set (X ⧸ Q.D))) :
    W = rootAt Q split i (Q.simple j*Q.simple i) ∨ W = simpleRemainder Q split j := by
  let R := rankOne Q split j
  let V := simpleRemainder Q split j
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  have hder := unequal_linear_derived_eq_middle_root Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF
  have hPN : Q.tits.standardParabolic {Q.simple j} ≤ normalizer (C : Set (X ⧸ Q.D)) := by
    dsimp only [C]
    rw [←hder]
    exact radical_commutator_normalized Q split j hKj
  have hVC : V ≤ normalizer (C : Set (X ⧸ Q.D)) :=
    (inf_le_left.trans (split.U_le.trans (Q.tits.B_le_standardParabolic _))).trans hPN
  have hRC : R ≤ normalizer (C : Set (X ⧸ Q.D)) := (rankOne_le_parabolic Q split j).trans hPN
  have hVW : V ≤ normalizer (W : Set (X ⧸ Q.D)) :=
    le_normalizer_iff_commutator_le_right.mpr
      (((commutator_mono le_rfl hWV).trans hder.le).trans hCW)
  let dW := invariantSubsection Q split j W C hWV hRW (hWV.trans hVC) hRC
  let dQ := radicalFactorSection Q split j hKj W hVW hRW
  have htower : Nat.card dW.Carrier * Nat.card dQ.Carrier = C.relIndex V :=
    relIndex_mul_relIndex C W V hCW hWV
  have htotal : Nat.card dW.Carrier * Nat.card dQ.Carrier < (2^(2*b))^2 := by
    rw [htower,radical_quotient_card Q split hm i j hij hKi hKj μi μj hE hF]
    have hl : 2^a < 2^b := Nat.pow_lt_pow_right (by decide) hab
    have hp : 0 < 2^b := Nat.pow_pos (by decide)
    have he : 2^(2*b) = (2^b)^2 := by rw [←pow_mul,Nat.mul_comm]
    rw [he,pow_two ((2^b)^2)]
    exact Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_left hl (by decide : 2 ≠ 0)) (Nat.pow_pos hp)
  by_cases hsmall : Nat.card dW.Carrier < 2^(2*b)
  · left
    have hact := linear_small_section_action Q split j hKj μj sj dW (by omega) hF hsmall
    have hc := section_commutator_le_of_trivial Q split dW hact
    change ⁅R,W⁆ ≤ (C.subgroupOf W).map W.subtype at hc
    rw [map_subgroupOf_eq_of_le hCW] at hc
    exact le_antisymm
      (unequal_linear_fixed_section_le_derived Q split hm i j hij hKi hKj μi μj si sj
        ha hab hE hF W hWV hc) hCW
  · right
    have hsmallQ : Nat.card dQ.Carrier < 2^(2*b) := by
      by_contra! hn
      have hh := Nat.mul_le_mul (Nat.le_of_not_lt hsmall) hn
      rw [←pow_two] at hh
      exact (not_lt_of_ge hh) htotal
    have hact := linear_small_section_action Q split j hKj μj sj dQ (by omega) hF hsmallQ
    have hc := section_commutator_le_of_trivial Q split dQ hact
    change ⁅R,V⁆ ≤ (W.subgroupOf V).map V.subtype at hc
    rw [map_subgroupOf_eq_of_le hWV,
      unequal_linear_radical_fully_moved Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF] at hc
    exact le_antisymm hWV hc


/-- The actual two linear local groups provide the binary scalar structure
on the literal radical abelianization, including an order-two endpoint. -/
theorem linear_pair_radicalQuotient_elementary
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* PSL(2,F)) :
    IsElementaryAbelian 2 (RadicalQuotient Q split j) := by
  apply radicalQuotient_elementary Q split hm _ j
  intro k
  by_cases hk : k = i
  · subst k; exact simpleRoot_elementary_of_linear Q split i μi
  · have hk' : k = j := by omega
    subst k; exact simpleRoot_elementary_of_linear Q split j μj

/-- Exact order of the actual radical abelianization in the unequal branch. -/
theorem unequal_linear_radicalQuotient_card
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* PSL(2,F))
    (si : RootReflection Q split i) (sj : RootReflection Q split j)
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b) :
    Nat.card (RadicalQuotient Q split j) = (2^a)^2*(2^b)^2 := by
  let V := simpleRemainder Q split j
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let q : V →* RadicalQuotient Q split j := Abelianization.of
  have hCV : C ≤ V := (exchanged_roots_le_remainder Q split hm i j hij).2
  have hder := unequal_linear_derived_eq_middle_root Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF
  have hker : q.ker = C.subgroupOf V := by
    apply map_injective V.subtype_injective
    rw [radicalProjection_kernel,map_subgroupOf_eq_of_le hCV,hder]
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q
    (Quotient.mk_surjective)).toEquiv,← index_eq_card,hker]
  exact radical_quotient_card Q split hm i j hij hKi hKj μi μj hE hF

/-- Irreducibility of the actual conjugation representation on V_j/V_j'.
Its field of scalars and action are constructed on this quotient itself. -/
theorem unequal_linear_radical_irreducible
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* PSL(2,F))
    (si : RootReflection Q split i) (sj : RootReflection Q split j)
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b) :
    let := linear_pair_radicalQuotient_elementary Q split hm i j hij μi μj
    (radicalRepresentation Q split j hKj).IsIrreducible := by
  let := linear_pair_radicalQuotient_elementary Q split hm i j hij μi μj
  let V := simpleRemainder Q split j
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let q : V →* RadicalQuotient Q split j := Abelianization.of
  let ρ := radicalRepresentation Q split j hKj
  have hCV : C ≤ V := (exchanged_roots_le_remainder Q split hm i j hij).2
  have hder := unequal_linear_derived_eq_middle_root Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF
  have hker : q.ker = C.subgroupOf V := by
    apply map_injective V.subtype_injective
    rw [radicalProjection_kernel,map_subgroupOf_eq_of_le hCV,hder]
  have hcard := unequal_linear_radicalQuotient_card Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF
  let : Nontrivial (RadicalQuotient Q split j) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hcard]
    have htwo : 2 ≤ 2^a := by simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) ha
    have hA : 4 ≤ (2^a)^2 := by nlinarith
    have hB : 1 ≤ (2^b)^2 := Nat.pow_pos (Nat.pow_pos (by decide))
    exact lt_of_lt_of_le (by decide : 1 < 4*1) (Nat.mul_le_mul hA hB))
  let : Nontrivial (Subrepresentation ρ) := by
    refine ⟨⟨⊥,⊤,?_⟩⟩
    intro hh
    obtain ⟨v,hv⟩ := exists_ne (0 : Additive (RadicalQuotient Q split j))
    have hb : v ∈ (⊥ : Subrepresentation ρ) := by rw [hh]; trivial
    exact hv hb
  refine { eq_bot_or_eq_top := ?_ }
  intro S
  let T : Subgroup (RadicalQuotient Q split j) := S.toSubmodule.toAddSubgroup.toSubgroup'
  let W := (T.comap q).map V.subtype
  have hWV : W ≤ V := by rintro x ⟨v,hv,rfl⟩; exact v.property
  have hCW : C ≤ W := by
    have hkW : q.ker ≤ T.comap q := by
      intro v hv
      change q v ∈ T
      change q v = 1 at hv
      rw [hv]
      exact one_mem _
    have hh := map_mono (f := V.subtype) hkW
    rw [hker,map_subgroupOf_eq_of_le hCV] at hh
    exact hh
  have hRW : rankOne Q split j ≤ normalizer (W : Set (X ⧸ Q.D)) := by
    apply le_normalizer_iff.mpr
    intro r hr x hx
    obtain ⟨v,hv,rfl⟩ := hx
    refine ⟨radicalAction Q split j hKj ⟨r,hr⟩ v,?_,?_⟩
    · have hh := S.apply_mem_toSubmodule ⟨r,hr⟩ hv
      change radicalRepresentation Q split j hKj ⟨r,hr⟩
        (Additive.ofMul (Abelianization.of v)) ∈ S at hh
      rw [radicalRepresentation_of] at hh
      exact hh
    · exact radicalAction_apply Q split j hKj ⟨r,hr⟩ v
  rcases unequal_linear_invariant_radical_subgroups Q split hm i j hij hKi hKj μi μj si sj
    ha hab hE hF W hCW hWV hRW with hW | hW
  · left
    apply le_antisymm _ bot_le
    intro v hv
    obtain ⟨x,hx⟩ := (Quotient.mk_surjective : Function.Surjective q) v.toMul
    change q x = v.toMul at hx
    have hxS : q x ∈ T := by
      change Additive.ofMul (q x) ∈ S
      rwa [hx]
    have hxW : (x : X ⧸ Q.D) ∈ W := mem_map_of_mem V.subtype hxS
    have hxC : (x : X ⧸ Q.D) ∈ C := by
      change W = C at hW
      exact hW ▸ hxW
    have hxker : x ∈ q.ker := by rw [hker]; exact hxC
    have hx1 : q x = 1 := hxker
    change v = 0
    exact Additive.toMul.injective (hx.symm.trans hx1)
  · right
    apply top_unique
    intro v _
    obtain ⟨x,hx⟩ := (Quotient.mk_surjective : Function.Surjective q) v.toMul
    change q x = v.toMul at hx
    have hxW : (x : X ⧸ Q.D) ∈ W := hW.symm ▸ x.property
    obtain ⟨y,hy,he⟩ := hxW
    have hyx : y = x := Subtype.ext he
    subst y
    change Additive.ofMul (q x) ∈ S at hy
    rwa [hx] at hy


/-- The irreducible source module has binary dimension 2a+2b, on the actual
radical quotient. This is the dimension entering the remaining cubic-ratio step. -/
theorem unequal_linear_radical_finrank
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* PSL(2,F))
    (si : RootReflection Q split i) (sj : RootReflection Q split j)
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b) :
    letI := linear_pair_radicalQuotient_elementary Q split hm i j hij μi μj
    Module.finrank (ZMod 2) (Additive (RadicalQuotient Q split j)) = 2*a+2*b := by
  let := linear_pair_radicalQuotient_elementary Q split hm i j hij μi μj
  have he := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := Additive (RadicalQuotient Q split j))
  simp only [Nat.card_zmod] at he
  change Nat.card (RadicalQuotient Q split j) = _ at he
  rw [unequal_linear_radicalQuotient_card Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF] at he
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  calc
    _ = (2^a)^2*(2^b)^2 := he.symm
    _ = 2^(2*a+2*b) := by
      rw [←pow_mul,←pow_mul,←pow_add]
      congr 1
      omega

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
