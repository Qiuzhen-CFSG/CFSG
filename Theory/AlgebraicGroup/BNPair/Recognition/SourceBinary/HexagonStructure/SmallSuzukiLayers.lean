module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SmallSuzuki

/-!
# Successive small Suzuki sections and the source cubic obstruction

For the solvable actor Sz(2), a reflection times a root involution has
order five. Its inverse moves every nontrivial element of the relevant
own-root conjugate into a disjoint conjugate radical. This detects the
actual action on each successive Frattini section. Consequently both
V/Φ(V) and Φ(V)/Φ²(V), for V = U_sj, have order at least sixteen.

When both simple roots have order four, the exact five-root product gives
|Φ²(V)| ≤ 4. An order-four element of the own-root conjugate inside Φ(V)
would contradict that bound, since its square moves the next section.
The two outer-root Frattini subgroups are independent of the middle
commutator. Their product gives 4|V′| ≤ |Φ(V)| ≤ 64, hence |V′| ≤ 16.

A six-term identity in the binary group algebra of C₅:C₄ proves the
specific Hall--Higman assertion needed here: a faithful representation
has nonzero cubic displacement for its order-four complement. Conjugacy
places that complement inside the actual canonical root. The induced
effective action is precisely the action on the source Frattini quotient.
Its displacement is the image of a literal commutator. If the opposite
radical had class at most two, the third displacement would vanish.
Thus its third lower-central term is nontrivial.

These are the small-pair structural constraints, not the full exclusion.
The remaining step in source (5H) is to show that these small radicals
have class at most two. The CFSG companion applies every constraint to
both original Sz(2) and D₁₀ constructors, retaining their true Sz(2) actor,
original/geometric marking and literal quotient map. No perfectness is
assumed for these solvable groups.

Source: Fong--Seitz I (3G), (5D)(b), (5H), printed pp.14--16,26--27,30.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open scoped MatrixGroups Pointwise IsMulCommutative commutatorElement
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates ReeSource GTwoSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- A nontrivial own-root element detects the actual odd product on a
section with trivial denominator. -/
theorem ownRoot_oddProduct_moves_section (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (s : RootReflection Q split j)
    (u : rankOne Q split j) (hu : (u : X ⧸ Q.D) ∈ simpleRoot Q split j)
    (d : RootSection Q split j) (hden : d.denominator = ⊥)
    (a : rootAt Q split j (Q.simple i)) (ha : a ≠ 1)
    (hax : (a : X ⧸ Q.D) ∈ d.numerator) :
    d.action ((⟨s.val,s.mem_rankOne⟩ : rankOne Q split j)*u) ≠ 1 := by
  let n := representative (Q.simple i)
  let W := rightConjugate (simpleRemainder Q split j) (n : X ⧸ Q.D)
  have hB : rootAt Q split j (Q.simple i) ≤ simpleRemainder Q split j :=
    (le_sup_left.trans le_sup_left).trans (middleRoots_le_remainder Q split hm i j hij)
  have hD : rootAt Q split j (Q.simple i*Q.simple j) ≤ simpleRemainder Q split j :=
    le_sup_right.trans (middleRoots_le_remainder Q split hm i j hij)
  have hUW : simpleRoot Q split j ≤ W := by
    have hh := comap_mono (f := (MulAut.conj (n : X ⧸ Q.D)).toMonoidHom) hB
    change rightConjugate (rootAt Q split j (Q.simple i)) (n : X ⧸ Q.D) ≤ W at hh
    rw [rootAt_right Q split j _ _ n (representative_spec _),
      show Q.simple i*Q.simple i = 1 from by
        simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2,
      rootAt_one] at hh
    exact hh
  have hDW : rootAt Q split j (Q.simple i*Q.simple j) ≤ W := by
    have hh := comap_mono (f := (MulAut.conj (n : X ⧸ Q.D)).toMonoidHom) hD
    change rightConjugate (rootAt Q split j (Q.simple i*Q.simple j)) (n : X ⧸ Q.D) ≤ W at hh
    rwa [rootAt_right Q split j _ _ n (representative_spec _),
      orthogonal_root_stabilizer Q split hm j i hij.symm] at hh
  intro he
  let c : rankOne Q split j := ⟨s.val,s.mem_rankOne⟩*u
  have hei : d.action c⁻¹ = 1 := by rw [map_inv,he,inv_one]
  let x : d.numerator := ⟨a,hax⟩
  let y := d.numeratorAction c⁻¹ x
  have hyx : y = x := by
    have hh := congrArg (fun f : MulAut d.Carrier => f (QuotientGroup.mk x)) hei
    rw [d.action_mk] at hh
    have hd := QuotientGroup.eq_iff_div_mem.mp hh
    rw [hden,mem_bot] at hd
    exact div_eq_one.mp hd
  have hy : (y : X ⧸ Q.D) =
      (u : X ⧸ Q.D)⁻¹*((s.val : X ⧸ Q.D)⁻¹*(a : X ⧸ Q.D)*s.val)*u := by
    dsimp only [y]
    rw [d.numeratorAction_apply]
    simp only [c,coe_inv,coe_mul,mul_inv_rev,inv_inv,mul_assoc]
    rfl
  have hsa : (s.val : X ⧸ Q.D)⁻¹*(a : X ⧸ Q.D)*s.val ∈ rootAt Q split j (Q.simple i*Q.simple j) := by
    rw [← rootAt_right Q split j (Q.simple i) (Q.simple j) s.val s.class_eq]
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)⁻¹*(a : X ⧸ Q.D)*s.val)*(s.val : X ⧸ Q.D)⁻¹ ∈ rootAt Q split j (Q.simple i)
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using a.property
  have haW : (a : X ⧸ Q.D) ∈ W := by
    have hyW : (y : X ⧸ Q.D) ∈ W := by
      rw [hy]
      exact W.mul_mem (W.mul_mem (W.inv_mem (hUW hu)) (hDW hsa)) (hUW hu)
    simpa only [hyx] using hyW
  have haU : (n : X ⧸ Q.D)*(a : X ⧸ Q.D)*(n : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split j := by
    exact a.property
  have hz : (n : X ⧸ Q.D)*(a : X ⧸ Q.D)*(n : X ⧸ Q.D)⁻¹ = 1 :=
    disjoint_def.mp (simpleRoot_disjoint_remainder Q split j) haU haW
  exact ha (Subtype.ext ((MulAut.conj (n : X ⧸ Q.D)).injective (hz.trans (map_one _).symm)))


/-- The effective quotient of a section containing a nontrivial own-root
conjugate has at least sixteen elements, including for the solvable actor. -/
theorem smallSuzuki_ownRoot_section_bound (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (μ : rankOne Q split j ≃* SuzukiMatrixGroup 0)
    (ν : simpleRoot Q split j ≃* SuzukiRootSubgroup 0)
    (d : RootSection Q split j) (hden : d.denominator = ⊥)
    (a : rootAt Q split j (Q.simple i)) (ha : a ≠ 1)
    (hax : (a : X ⧸ Q.D) ∈ d.numerator) :
    16 ≤ Nat.card (d.numerator ⧸ frattini d.numerator) := by
  obtain ⟨s,u,hu,hc⟩ := smallSuzuki_exists_oddProduct Q split j μ ν
  have hh := smallSuzuki_section_card_bound Q split j μ _ hc d
    (ownRoot_oddProduct_moves_section Q split hm i j hij s u hu d hden a ha hax)
  change 16 ≤ d.effectiveDenominator.index at hh
  rwa [d.effectiveDenominator_eq,hden,sup_bot_eq] at hh

/-- Both successive sections in the small Suzuki radical are effective on
an explicitly constructed order-five element. No perfectness is used. -/
theorem smallSuzuki_radical_two_layers (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : rankOne Q split j ≃* SuzukiMatrixGroup 0)
    (ν : simpleRoot Q split j ≃* SuzukiRootSubgroup 0) :
    16 ≤ Nat.card (simpleRemainder Q split j ⧸ frattini (simpleRemainder Q split j)) ∧
    16 ≤ Nat.card (frattini (simpleRemainder Q split j) ⧸
      frattini (frattini (simpleRemainder Q split j))) := by
  let d := radicalSection Q split j hKj
  let f := frattiniSection Q split j d
  have hB : rootAt Q split j (Q.simple i) ≤ d.numerator :=
    (le_sup_left.trans le_sup_left).trans (middleRoots_le_remainder Q split hm i j hij)
  obtain ⟨a,ha⟩ := suzuki_conjugate_exists_nontrivial_square Q split j i ν
  have hane : a ≠ 1 := fun he => ha (by rw [he,one_pow])
  refine ⟨smallSuzuki_ownRoot_section_bound Q split hm i j hij μ ν d rfl a hane
    (hB a.property),?_⟩
  let : Fact (IsPGroup 2 d.numerator) := ⟨d.isTwo⟩
  have hh := smallSuzuki_ownRoot_section_bound Q split hm i j hij μ ν f rfl (a^2) ha
    ⟨(inclusion hB a)^2,pth_power_mem_frattini_of_isPGroup (p := 2) _,rfl⟩
  let e : frattini d.numerator ≃* f.numerator :=
    (frattini d.numerator).equivMapOfInjective d.numerator.subtype d.numerator.subtype_injective
  have he := Nat.card_congr (QuotientGroup.congr _ _ e (frattini_map_equiv e)).toEquiv
  rwa [←he] at hh

/-- The exact second Frattini order bound from the two source actions and
the actual five-root product. The opposite root is left unrestricted. -/
theorem smallSuzuki_second_frattini_weighted_bound (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : rankOne Q split j ≃* SuzukiMatrixGroup 0)
    (ν : simpleRoot Q split j ≃* SuzukiRootSubgroup 0) :
    Nat.card (frattini (frattini (simpleRemainder Q split j))) * 16 ≤
      Nat.card (simpleRoot Q split i)^3 := by
  let V := simpleRemainder Q split j
  have hc : Nat.card (simpleRoot Q split j) = 4 := by
    rw [Nat.card_congr ν.toEquiv,matrixRoot_card]; norm_num
  have hU : Nat.card split.U = (Nat.card (simpleRoot Q split i)*4)^3 := by
    have hu := unipotent_card_even Q split 3 hm
    have hi : i = 0 ∨ i = 1 := by omega
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (hij rfl).elim
    · rwa [hc] at hu
    · rwa [hc,mul_comm 4] at hu
    · exact (hij rfl).elim
  have hV : Nat.card V = Nat.card (simpleRoot Q split i)^3*16 := by
    have hh := unipotent_card_simple Q split j
    rw [hU,hc] at hh
    dsimp only [V]
    nlinarith [hh]
  obtain ⟨h1,h2⟩ := smallSuzuki_radical_two_layers Q split hm i j hij hKj μ ν
  have he1 := (frattini V).card_mul_index
  have he2 := (frattini (frattini V)).card_mul_index
  change 16 ≤ (frattini V).index at h1
  change 16 ≤ (frattini (frattini V)).index at h2
  have hb := Nat.mul_le_mul_left (Nat.card (frattini (frattini V))) h2
  rw [he2] at hb
  have hb' := Nat.mul_le_mul_left (Nat.card (frattini V)) h1
  rw [he1,hV] at hb'
  nlinarith

/-- If the opposite root has order four, the second Frattini subgroup has
order at most four. This is a statement about the literal radical. -/
theorem smallSuzuki_second_frattini_card_le_four (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : rankOne Q split j ≃* SuzukiMatrixGroup 0)
    (ν : simpleRoot Q split j ≃* SuzukiRootSubgroup 0)
    (hi : Nat.card (simpleRoot Q split i) = 4) :
    Nat.card (frattini (frattini (simpleRemainder Q split j))) ≤ 4 := by
  have hh := smallSuzuki_second_frattini_weighted_bound Q split hm i j hij hKj μ ν
  rw [hi] at hh
  omega

/-- No element of order four from the own-root conjugate lies in the first
Frattini subgroup when the opposite root has order four. Such an element
would force the second Frattini section to have at least sixteen elements. -/
theorem smallSuzuki_frattini_root_square_eq_one (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : rankOne Q split j ≃* SuzukiMatrixGroup 0)
    (ν : simpleRoot Q split j ≃* SuzukiRootSubgroup 0)
    (hi : Nat.card (simpleRoot Q split i) = 4)
    (a : rootAt Q split j (Q.simple i))
    (ha : (a : X ⧸ Q.D) ∈ (frattiniSection Q split j (radicalSection Q split j hKj)).numerator) :
    a^2 = 1 := by
  let d := radicalSection Q split j hKj
  let f := frattiniSection Q split j d
  let g := frattiniSection Q split j f
  let : Fact (IsPGroup 2 f.numerator) := ⟨f.isTwo⟩
  by_contra hne
  have hlo := smallSuzuki_ownRoot_section_bound Q split hm i j hij μ ν g rfl (a^2) hne
    ⟨(⟨a,ha⟩ : f.numerator)^2,pth_power_mem_frattini_of_isPGroup (p := 2) _,rfl⟩
  have hsize : Nat.card (g.numerator ⧸ frattini g.numerator) ≤ Nat.card g.numerator :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  have he : Nat.card g.numerator = Nat.card (frattini (frattini d.numerator)) := by
    change Nat.card ((frattini f.numerator).map f.numerator.subtype) = _
    rw [card_map_of_injective f.numerator.subtype_injective]
    let e : frattini d.numerator ≃* f.numerator :=
      (frattini d.numerator).equivMapOfInjective d.numerator.subtype d.numerator.subtype_injective
    rw [←frattini_map_equiv e,card_map_of_injective e.injective]
  have hup := smallSuzuki_second_frattini_card_le_four Q split hm i j hij hKj μ ν hi
  have hh : Nat.card g.numerator ≤ 4 := he.trans_le hup
  exact (by omega : ¬ (16 ≤ Nat.card g.numerator)) (hlo.trans hsize)

/-- Two independent outer-root Frattini subgroups survive beside the middle
commutator. This bounds the actual derived subgroup in the two small-root row. -/
theorem smallSuzuki_pair_derived_card_le_sixteen (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup 0)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup 0)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup 0) :
    Nat.card (⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ : Subgroup (X ⧸ Q.D)) ≤ 16 := by
  let U := simpleRoot Q split i
  let V := simpleRemainder Q split j
  let D := ⁅V,V⁆
  let F := (frattini V).map V.subtype
  let A := (frattini U).map U.subtype
  let E := rootAt Q split i (Q.simple j)
  let C := (frattini E).map E.subtype
  let n := representative (Q.simple j)
  have hUcard : Nat.card U = 4 := by
    rw [Nat.card_congr νi.toEquiv,matrixRoot_card]; norm_num
  have hJcard : Nat.card (simpleRoot Q split j) = 4 := by
    rw [Nat.card_congr νj.toEquiv,matrixRoot_card]; norm_num
  let : IsMulCommutative U := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by exact hUcard)
  have hab : ⁅U,U⁆ = ⊥ := by
    rw [←map_subtype_commutator,commutator_eq_bot,Subgroup.map_bot]
  have hDM : D ≤ middleRoots Q split i j := radical_commutator_le_middle Q split hm i j hij hKi hab
  have hDV : D ≤ V := commutator_le_self _
  have hUV : U ≤ V := simpleRoot_le_other_remainder Q split hm i j hij
  have hEV : E ≤ V := (exchanged_roots_le_remainder Q split hm i j hij).1
  have hEU : E ≤ simpleRemainder Q split i :=
    (le_sup_left.trans le_sup_left).trans (middleRoots_le_remainder Q split hm j i hij.symm)
  let : Fact (IsPGroup 2 V) := ⟨split.isTwo.to_le inf_le_left⟩
  let : Fact (IsPGroup 2 U) := ⟨split.isTwo.to_le (simpleRoot_le Q split i)⟩
  let : Fact (IsPGroup 2 E) := ⟨split.isTwo.to_le (hEV.trans inf_le_left)⟩
  have hAF : A ≤ F := by
    rintro _ ⟨a,ha,rfl⟩
    exact ⟨inclusion hUV a,frattini_map_le_of_isPGroup (p := 2) (inclusion hUV)
      (mem_map_of_mem _ ha),rfl⟩
  have hCF : C ≤ F := by
    rintro _ ⟨a,ha,rfl⟩
    exact ⟨inclusion hEV a,frattini_map_le_of_isPGroup (p := 2) (inclusion hEV)
      (mem_map_of_mem _ ha),rfl⟩
  have hDF : D ≤ F := by
    dsimp only [D,F]
    rw [←map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  have hDC : Disjoint D C := by
    apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro x hx
    have hxE : x ∈ E := map_subtype_le _ hx.2
    have hxM := hDM hx.1
    have hxV := (middleRoots_eq_intersection Q split hm i j hij n (representative_spec _) ▸ hxM).2
    have hz := disjoint_def.mp (simpleRoot_disjoint_remainder Q split i) hxE hxV
    exact mem_bot.mpr ((MulAut.conj (n : X ⧸ Q.D)).injective (hz.trans (map_one _).symm))
  have hCN : C ≤ normalizer (D : Set (X ⧸ Q.D)) :=
    (map_subtype_le _).trans (hEV.trans (normalizer_commutator_ge_left V V))
  have hDc : Nat.card ↥(D ⊔ C) = Nat.card D * Nat.card C :=
    card_sup_eq_mul_of_normalizes_of_disjoint D C hCN hDC
  have hAVi : Disjoint A (D ⊔ C) :=
    (simpleRoot_disjoint_remainder Q split i).mono (map_subtype_le _)
      (sup_le (hDM.trans (middleRoots_le_other_remainder Q split hm i j hij))
        ((map_subtype_le _).trans hEU))
  let f : A × ↥(D ⊔ C) → F := fun x =>
    ⟨(x.1 : X ⧸ Q.D)*x.2,mul_mem (hAF x.1.property) ((sup_le hDF hCF) x.2.property)⟩
  have hf : Function.Injective f := fun _ _ h => mul_injective_of_disjoint hAVi (congrArg Subtype.val h)
  have hb := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod,hDc] at hb
  have hA2 : 2 ≤ Nat.card A := by
    have hn : frattini U ≠ ⊥ := by
      obtain ⟨a,ha⟩ := suzuki_root_exists_nontrivial_square 0
      intro he
      have hh := pth_power_mem_frattini_of_isPGroup (p := 2) (νi.symm a)
      rw [he,mem_bot] at hh
      have hhh := congrArg νi hh
      rw [map_pow,νi.apply_symm_apply,map_one] at hhh
      exact ha hhh
    have hh := (frattini U).one_lt_card_iff_ne_bot.mpr hn
    simpa only [A,card_map_of_injective U.subtype_injective] using (Nat.succ_le_iff.mpr hh)
  have hC2 : 2 ≤ Nat.card C := by
    let e : U ≃* E := (RootAction.conjugateEquiv U n).symm
    have he : Nat.card (frattini E) = Nat.card (frattini U) := by
      rw [←frattini_map_equiv e,card_map_of_injective e.injective]
    simpa only [C,A,card_map_of_injective E.subtype_injective,
      card_map_of_injective U.subtype_injective,he] using hA2
  have hF64 : Nat.card F ≤ 64 := by
    have hU := unipotent_card_even Q split 3 hm
    have hi : i = 0 ∨ i = 1 := by omega
    have hj : j = 0 ∨ j = 1 := by omega
    have hc : Nat.card split.U = 4096 := by
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact (hij rfl).elim
      · norm_num [show Nat.card (simpleRoot Q split 0) = 4 from hUcard,hJcard] at hU ⊢
        exact hU
      · norm_num [show Nat.card (simpleRoot Q split 1) = 4 from hUcard,hJcard] at hU ⊢
        exact hU
      · exact (hij rfl).elim
    have hv := unipotent_card_simple Q split j
    rw [hc,hJcard] at hv
    have hVcard : Nat.card V = 1024 := by dsimp only [V]; omega
    have hlo := (smallSuzuki_radical_two_layers Q split hm i j hij hKj μj νj).1
    have he := (frattini V).card_mul_index
    rw [hVcard] at he
    change 16 ≤ (frattini V).index at hlo
    rw [show Nat.card F = Nat.card (frattini V) from card_map_of_injective V.subtype_injective]
    nlinarith
  change Nat.card D ≤ 16
  nlinarith

private theorem fiveFour_cubic_certificate :
    let c := MonoidAlgebra.of (ZMod 2) FiveFour.Group FiveFour.c
    let a := MonoidAlgebra.of (ZMod 2) FiveFour.Group FiveFour.a
    let p := 1 + a + a^2 + a^3
    1+c = p + p*c*a^3 + c*p*c*a + c^2*p + c^3*p*c + c^3*p*c*a := by
  dsimp only
  simp only [mul_add,add_mul,mul_one,one_mul,←map_pow,←map_mul]
  ext g
  simp only [MonoidAlgebra.coeff_add,MonoidAlgebra.of_apply,MonoidAlgebra.one_def,
    MonoidAlgebra.coeff_single,Finsupp.add_apply,Finsupp.single_apply]
  revert g
  decide +kernel

/-- The Hall--Higman obstruction for the literal solvable actor: its
order-four complement cannot have cubic-zero displacement in a faithful
binary representation. A six-term group-algebra certificate proves this
without a general Hall--Higman theorem or a representation classification. -/
theorem smallSuzuki_cubic_displacement_ne_zero
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) FiveFour.Group V) (hf : Function.Injective ρ) :
    (ρ FiveFour.a - 1)^3 ≠ 0 := by
  intro hz
  have h2 (x : Module.End (ZMod 2) V) : x+x=0 := by
    ext v
    change x v + x v = 0
    rw [←two_smul (ZMod 2) (x v)]
    rw [show (2 : ZMod 2) = 0 from by decide,zero_smul]
  have h3 (x : Module.End (ZMod 2) V) : 3 • x = x := by
    rw [show (3 : ℕ) = 2+1 from rfl,add_nsmul,two_nsmul,one_nsmul,h2,zero_add]
  have h3z (x : Module.End (ZMod 2) V) : (3 : ℤ) • x = x := by
    exact (natCast_zsmul x 3).trans (h3 x)
  have hp : 1 + ρ FiveFour.a + ρ FiveFour.a^2 + ρ FiveFour.a^3 = 0 := by
    have he : (ρ FiveFour.a - 1)^3 = 1 + ρ FiveFour.a + ρ FiveFour.a^2 + ρ FiveFour.a^3 := by
      have hneg : -(1 : Module.End (ZMod 2) V) = 1 := by
        exact neg_eq_iff_add_eq_zero.mpr (h2 1)
      rw [sub_eq_add_neg,hneg]
      noncomm_ring
      simp only [h3z]
    exact he.symm.trans hz
  have hh := congrArg ρ.asAlgebraHom fiveFour_cubic_certificate
  simp only [map_add,map_mul,map_pow,map_one,Representation.asAlgebraHom_of,hp,
    zero_mul,mul_zero,add_zero] at hh
  have hc : ρ FiveFour.c = 1 := by
    have h2 : (1 : Module.End (ZMod 2) V) + 1 = 0 := by
      exact h2 1
    exact add_left_cancel (hh.trans h2.symm)
  exact (by decide : FiveFour.c ≠ 1) (hf (hc.trans (map_one ρ).symm))

private theorem fiveFour_four_conjugate (b : FiveFour.Group) (h2 : b^2 ≠ 1) (h4 : b^4 = 1) :
    ∃ g : FiveFour.Group, g*FiveFour.a*g⁻¹ = b ∨ g*FiveFour.a*g⁻¹ = b^3 := by
  exact (by decide +kernel : ∀ b : FiveFour.Group, b^2 ≠ 1 → b^4 = 1 →
    ∃ g : FiveFour.Group, g*FiveFour.a*g⁻¹ = b ∨ g*FiveFour.a*g⁻¹ = b^3) b h2 h4

/-- The cubic displacement obstruction is realized by an actual order-four
unipotent in the canonical simple root, on the literal effective section. -/
theorem smallSuzuki_section_cubic_movement (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (μ : rankOne Q split j ≃* SuzukiMatrixGroup 0)
    (ν : simpleRoot Q split j ≃* SuzukiRootSubgroup 0)
    (d : RootSection Q split j) (hden : d.denominator = ⊥)
    (x : rootAt Q split j (Q.simple i)) (hx : x ≠ 1)
    (hxd : (x : X ⧸ Q.D) ∈ d.numerator) :
    ∃ u : rankOne Q split j, (u : X ⧸ Q.D) ∈ simpleRoot Q split j ∧
      orderOf u = 4 ∧ (d.effectiveRepresentation u - 1)^3 ≠ 0 := by
  obtain ⟨s,v,hv,ho⟩ := smallSuzuki_exists_oddProduct Q split j μ ν
  have hd := d.effectiveRepresentation_injective
    (smallSuzuki_section_injective Q split j μ _ ho d
      (ownRoot_oddProduct_moves_section Q split hm i j hij s v hv d hden x hx hxd))
  have hc : Nat.card (simpleRoot Q split j) = 4 := by
    rw [Nat.card_congr ν.toEquiv,matrixRoot_card]; norm_num
  obtain ⟨z,hz⟩ := suzuki_root_exists_nontrivial_square 0
  let r : rankOne Q split j := inclusion (show simpleRoot Q split j ≤ rankOne Q split j from le_sup_left) (ν.symm z)
  have hr2 : r^2 ≠ 1 := by
    intro he
    have hh : (ν.symm z)^2 = 1 := Subtype.ext (congrArg (fun t : rankOne Q split j => (t : X ⧸ Q.D)) he)
    apply hz
    simpa only [map_pow,ν.apply_symm_apply,map_one] using congrArg ν hh
  have hr4 : r^4 = 1 := by
    apply Subtype.ext
    have hh := pow_card_eq_one' (x := ν.symm z)
    rw [hc] at hh
    exact congrArg (fun t : simpleRoot Q split j => (t : X ⧸ Q.D)) hh
  let e := μ.trans FiveFour.suzukiZeroEquiv.symm
  obtain ⟨g,hg⟩ := fiveFour_four_conjugate (e r)
    (fun he => hr2 (e.injective (by simpa only [map_pow,map_one] using he)))
    (by rw [←map_pow,hr4,map_one])
  let a : rankOne Q split j := e.symm ((MulAut.conj g) FiveFour.a)
  have ha : (a : X ⧸ Q.D) ∈ simpleRoot Q split j := by
    rcases hg with hg | hg
    · have he : a = r := by dsimp only [a]; rw [show (MulAut.conj g) FiveFour.a = e r from hg,e.symm_apply_apply]
      rw [he]
      exact (ν.symm z).property
    · have he : a = r^3 := by
        dsimp only [a]
        rw [show (MulAut.conj g) FiveFour.a = (e r)^3 from hg,←map_pow,e.symm_apply_apply]
      rw [he]
      exact pow_mem (ν.symm z).property 3
  let σ := d.effectiveRepresentation.comp (e.symm.toMonoidHom.comp (MulAut.conj g).toMonoidHom)
  have hσ : Function.Injective σ := hd.comp (e.symm.injective.comp (MulAut.conj g).injective)
  refine ⟨a,ha,?_,smallSuzuki_cubic_displacement_ne_zero σ hσ⟩
  exact (orderOf_injective e.symm.toMonoidHom e.symm.injective _).trans
    ((orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective _).trans
      (by
        have hd := orderOf_dvd_of_pow_eq_one FiveFour.a_four
        have hn : FiveFour.a^2 ≠ 1 := by decide +kernel
        have hh : orderOf FiveFour.a = 1 ∨ orderOf FiveFour.a = 2 ∨ orderOf FiveFour.a = 4 := by
          have hb := Nat.le_of_dvd (by decide : 0 < 4) hd
          interval_cases hk : orderOf FiveFour.a <;> omega
        rcases hh with hh | hh | hh
        · exact (hn (by rw [orderOf_eq_one_iff.mp hh,one_pow])).elim
        · exact (hn (hh ▸ pow_orderOf_eq_one FiveFour.a)).elim
        · exact hh))

/-- The literal radical Frattini quotient has the required order-four
root element with nonzero cubic displacement. -/
theorem smallSuzuki_radical_cubic_movement (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : rankOne Q split j ≃* SuzukiMatrixGroup 0)
    (ν : simpleRoot Q split j ≃* SuzukiRootSubgroup 0) :
    ∃ u : rankOne Q split j, (u : X ⧸ Q.D) ∈ simpleRoot Q split j ∧ orderOf u = 4 ∧
      ((radicalSection Q split j hKj).effectiveRepresentation u - 1)^3 ≠ 0 := by
  obtain ⟨a,ha⟩ := suzuki_conjugate_exists_nontrivial_square Q split j i ν
  exact smallSuzuki_section_cubic_movement Q split hm i j hij μ ν
    (radicalSection Q split j hKj) rfl a (fun he => ha (by rw [he,one_pow]))
    (((le_sup_left.trans le_sup_left).trans (middleRoots_le_remainder Q split hm i j hij)) a.property)

/-- The displacement on the actual quotient is the image of the literal
iterated commutator, with Lean's left conjugation convention. -/
theorem section_cubic_displacement_eq_zero
    (j : Fin 2) (d : RootSection Q split j) (u : rankOne Q split j)
    (h : ⁅zpowers (u : X ⧸ Q.D),⁅zpowers (u : X ⧸ Q.D),
      ⁅zpowers (u : X ⧸ Q.D),d.numerator⁆⁆⁆ = ⊥) :
    (d.effectiveRepresentation u - 1)^3 = 0 := by
  let δ : d.numerator → d.numerator := fun x => d.numeratorAction u x / x
  have hd (x : d.numerator) :
      (d.effectiveRepresentation u - 1) (Additive.ofMul (QuotientGroup.mk x)) =
        Additive.ofMul (QuotientGroup.mk (δ x)) := by
    rw [LinearMap.sub_apply,d.effectiveRepresentation_mk]
    change Additive.ofMul (QuotientGroup.mk' d.effectiveDenominator (d.numeratorAction u x) /
      QuotientGroup.mk' d.effectiveDenominator x) = _
    rw [←map_div]
    rfl
  have hc (x : d.numerator) :
      (δ x : X ⧸ Q.D) = ⁅(u : X ⧸ Q.D),(x : X ⧸ Q.D)⁆ := by
    change (d.numeratorAction u x : X ⧸ Q.D)/(x : X ⧸ Q.D) = _
    rw [d.numeratorAction_apply,div_eq_mul_inv,commutatorElement_def]
  have hz (x : d.numerator) : δ (δ (δ x)) = 1 := by
    apply Subtype.ext
    have hh := commutator_mem_commutator (mem_zpowers (u : X ⧸ Q.D))
      (commutator_mem_commutator (mem_zpowers (u : X ⧸ Q.D))
        (commutator_mem_commutator (mem_zpowers (u : X ⧸ Q.D)) x.property))
    rw [h,mem_bot] at hh
    simpa only [hc,coe_one] using hh
  ext v
  obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective d.effectiveDenominator v.toMul
  have hv : v = Additive.ofMul (QuotientGroup.mk x) := congrArg Additive.ofMul hx.symm
  rw [hv]
  change (d.effectiveRepresentation u - 1)
    ((d.effectiveRepresentation u - 1)
      ((d.effectiveRepresentation u - 1) (Additive.ofMul (QuotientGroup.mk x)))) = 0
  rw [hd,hd,hd,hz]
  rfl

/-- A small Suzuki endpoint forces the opposite radical to have nonzero
third lower-central term. This is the final obstruction in source (5H):
its proof uses the actual root-generated actor and effective module. -/
theorem smallSuzuki_opposite_radical_not_classTwo (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : rankOne Q split j ≃* SuzukiMatrixGroup 0)
    (ν : simpleRoot Q split j ≃* SuzukiRootSubgroup 0) :
    ⁅simpleRemainder Q split i,⁅simpleRemainder Q split i,simpleRemainder Q split i⁆⁆ ≠ ⊥ := by
  intro he
  obtain ⟨u,hu,_,hn⟩ := smallSuzuki_radical_cubic_movement Q split hm i j hij hKj μ ν
  apply hn
  apply section_cubic_displacement_eq_zero Q split j (radicalSection Q split j hKj) u
  let W := simpleRemainder Q split i
  let V := simpleRemainder Q split j
  have hUW : zpowers (u : X ⧸ Q.D) ≤ W := zpowers_le.mpr
    (simpleRoot_le_other_remainder Q split hm j i hij.symm hu)
  have hVN : V ≤ normalizer (W : Set (X ⧸ Q.D)) :=
    inf_le_left.trans (split.U_le.trans ((Q.tits.B_le_standardParabolic _).trans
      (remainder_parabolic_normalizes Q split i hKi)))
  have hfirst : ⁅zpowers (u : X ⧸ Q.D),V⁆ ≤ W :=
    (commutator_mono hUW le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hVN)
  apply bot_unique
  exact he ▸ (commutator_mono hUW (commutator_mono hUW hfirst))

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
