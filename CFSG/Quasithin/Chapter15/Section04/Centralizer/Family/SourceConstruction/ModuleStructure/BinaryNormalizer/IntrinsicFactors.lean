module

public import Theory.GroupTheory.ElementarySixteenNineNormalizer
public import Mathlib.GroupTheory.Complement

/-!
# The intrinsic pair in a faithful nine-on-sixteen action

A faithful elementary-nine actor on elementary binary sixteen has two uniquely
characterized order-three subgroups: precisely those with nontrivial fixed
subgroups, or equivalently with moved subgroups of order four. Their moved
subgroups are the opposite fixed planes and give the actual direct decomposition.

Coprime splitting and the smaller binary automorphism orders first eliminate
the common fixed subgroup. The existing fixed-factor theorem constructs a pair.
Uniqueness follows by decomposing a vector fixed by a third line: its two
coordinates would both be fixed by the whole actor. Intertwining automorphisms
therefore preserve the pair. An irreducible compatible actor must interchange it.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the normalizer
calculation used in 15.4.12(6), printed pp.1160--1161. This supplies the intrinsic
factor and permutation step, independently of the later full-model identification.
The initial coprime argument adapts the private fixed-point calculation in
`Theory.GroupTheory.ElementarySixteenNineNormalizer` to arbitrary faithful actions.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure.BinaryNormalizer

private instance elementary_subgroup
    {W : Type*} [Group W] [IsElementaryAbelian 2 W] (D : Subgroup W) :
    IsElementaryAbelian 2 D where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := (Monoid.exponent_dvd_of_monoidHom D.subtype D.subtype_injective).trans
    (IsElementaryAbelian.exponent_dvd_p 2 W)

variable {A W : Type*} [Group A] [Finite A] [Group W] [Finite W]
  [IsElementaryAbelian 3 A] [IsElementaryAbelian 2 W]
  [MulDistribMulAction A W] [FaithfulSMul A W]

omit [IsElementaryAbelian 3 A] in
/-- Faithfulness forces the common fixed subgroup to vanish in the minimal
binary degree for an elementary-nine actor. -/
theorem common_fixed_eq_bot (hA : Nat.card A = 9) (hW : Nat.card W = 16) :
    FixedPoints.subgroup A W = ⊥ := by
  let F := FixedPoints.subgroup A W
  let U := commutatorAction A W
  let : IsInvariant A W U := commutatorAction_isInvariant
  have hcompl : IsCompl F U :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (Group.isSolvable_of_comm (fun x y : W => mul_comm x y))
      (by rw [hA, hW]; decide) inferInstance
  have hcount : Nat.card F * Nat.card U = 16 := by
    have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes F U
      (by rw [normalizer_eq_top]; exact le_top)
    simpa only [hcompl.inf_eq_bot, hcompl.sup_eq_top, card_bot, card_top, one_mul, hW]
      using h
  have hfaith : Function.Injective (MulDistribMulAction.toMulAut A U) := by
    apply (injective_iff_map_eq_one _).mpr
    intro a ha
    apply FaithfulSMul.eq_of_smul_eq_smul (α := W)
    intro x
    obtain ⟨f, hf, u, hu, rfl⟩ := Subgroup.mem_sup.mp
      (show x ∈ F ⊔ U by rw [hcompl.sup_eq_top]; trivial)
    have hufix : a • u = u := by
      have hh := congrArg (fun b : MulAut U => b ⟨u, hu⟩) ha
      exact congrArg Subtype.val hh
    rw [smul_mul', hf a, hufix, one_smul]
  have hdiv := Subgroup.card_dvd_of_injective (MulDistribMulAction.toMulAut A U) hfaith
  have hUdiv : Nat.card U ∣ 2 ^ 4 := by
    simpa [hW] using U.card_subgroup_dvd_card
  obtain ⟨n, hn, hU⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hUdiv
  rw [hA, SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow U n hU] at hdiv
  have hUcard : Nat.card U = 16 := by
    interval_cases n <;> norm_num [Fin.prod_univ_succ] at hdiv
    exact hU
  rw [hUcard] at hcount
  exact Subgroup.card_eq_one.mp (by change Nat.card F = 1; omega)

private theorem lines_sup (hA : Nat.card A = 9) (K L : Subgroup A)
    (hK : Nat.card K = 3) (hL : Nat.card L = 3) (hne : K ≠ L) : K ⊔ L = ⊤ := by
  have hdiv : Nat.card (K ⊓ L : Subgroup A) ∣ 3 := hK ▸ card_dvd_of_le inf_le_left
  have hinf : K ⊓ L = ⊥ := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with hone | hthree
    · exact card_eq_one.mp hone
    · have heqK : K ⊓ L = K := eq_of_le_of_card_ge inf_le_left (by rw [hK,hthree])
      have heqL : K ⊓ L = L := eq_of_le_of_card_ge inf_le_right (by rw [hL,hthree])
      exact (hne (heqK.symm.trans heqL)).elim
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes K L
    (by rw [normalizer_eq_top]; exact le_top)
  rw [hK,hL,hinf,card_bot,one_mul] at hprod
  exact eq_of_le_of_card_ge le_top (by rw [card_top,hA,←hprod])

private theorem fixed_inf_eq_bot (hA : Nat.card A = 9) (hW : Nat.card W = 16)
    (K L : Subgroup A) (hK : Nat.card K = 3) (hL : Nat.card L = 3) (hne : K ≠ L) :
    FixedPoints.subgroup K W ⊓ FixedPoints.subgroup L W = ⊥ := by
  apply bot_unique
  intro x hx
  have hKst : K ≤ MulAction.stabilizer A x := fun a ha => hx.1 ⟨a,ha⟩
  have hLst : L ≤ MulAction.stabilizer A x := fun a ha => hx.2 ⟨a,ha⟩
  have ht : (⊤ : Subgroup A) ≤ MulAction.stabilizer A x :=
    lines_sup hA K L hK hL hne ▸ sup_le hKst hLst
  exact (common_fixed_eq_bot (W := W) hA hW).le (fun a => ht (mem_top a))

omit [Finite A] [Finite W] [IsElementaryAbelian 2 W] [FaithfulSMul A W] in
private theorem fixed_stable (K : Subgroup A) (a : A) (x : W)
    (hx : x ∈ FixedPoints.subgroup K W) : a • x ∈ FixedPoints.subgroup K W := by
  intro k
  change (k : A) • (a • x) = a • x
  rw [←mul_smul, mul_comm (k : A), mul_smul]
  exact congrArg (fun y : W => a • y) (hx k)

/-- Every third actor line has trivial fixed subgroup. This proves uniqueness
of the unordered pair, rather than imposing a permutation hypothesis. -/
theorem other_line_fixed_eq_bot (hA : Nat.card A = 9) (hW : Nat.card W = 16)
    (K L : Subgroup A) (hK : Nat.card K = 3) (hL : Nat.card L = 3)
    (hc : IsCompl (FixedPoints.subgroup K W) (FixedPoints.subgroup L W))
    (D : Subgroup A) (hD : Nat.card D = 3) (hDK : D ≠ K) (hDL : D ≠ L) :
    FixedPoints.subgroup D W = ⊥ := by
  apply bot_unique
  intro x hx
  obtain ⟨u, hu, v, hv, huv⟩ := Subgroup.mem_sup.mp
    (show x ∈ FixedPoints.subgroup K W ⊔ FixedPoints.subgroup L W by
      rw [hc.sup_eq_top]; trivial)
  have hfix (d : D) : (d : A) • u = u ∧ (d : A) • v = v := by
    have hh : ((d : A) • u) * ((d : A) • v) = u * v := by
      rw [← smul_mul', huv]
      exact hx d
    have he := Subgroup.mul_injective_of_disjoint hc.disjoint
      (a₁ := (⟨(d : A) • u, fixed_stable K d u hu⟩,
        ⟨(d : A) • v, fixed_stable L d v hv⟩))
      (a₂ := (⟨u, hu⟩, ⟨v, hv⟩)) hh
    exact ⟨congrArg (fun z => (z.1 : W)) he, congrArg (fun z => (z.2 : W)) he⟩
  have huone : u = 1 := (fixed_inf_eq_bot (W := W) hA hW K D hK hD hDK.symm).le
    ⟨hu, fun d => (hfix d).1⟩
  have hvone : v = 1 := (fixed_inf_eq_bot (W := W) hA hW L D hL hD hDL.symm).le
    ⟨hv, fun d => (hfix d).2⟩
  simpa only [←huv,huone,hvone,mul_one] using (show (1 : W) ∈ (⊥ : Subgroup W) from one_mem _)

/-- The two actor lines and their actual complementary fixed subgroups. -/
structure FactorPair where
  line : Bool → Subgroup A
  card : ∀ i, Nat.card (line i) = 3
  complement : IsCompl (line false) (line true)
  fixed_card : ∀ i, Nat.card (FixedPoints.subgroup (line i) W) = 4
  fixed_complement : IsCompl (FixedPoints.subgroup (line false) W)
    (FixedPoints.subgroup (line true) W)

/-- Construct the pair from a faithful nine-on-sixteen action. -/
theorem exists_factorPair (hA : Nat.card A = 9) (hW : Nat.card W = 16) :
    Nonempty (FactorPair (A := A) (W := W)) := by
  have hf : FixedPoints.subgroup (⊤ : Subgroup A) W = ⊥ := by
    apply bot_unique
    intro x hx
    exact (common_fixed_eq_bot (W := W) hA hW).le (fun a => hx ⟨a,mem_top a⟩)
  obtain ⟨K,L,hK,hL,hc,hFK,hFL,hFc⟩ := nine_sixteen_fixed_factor_decomposition hA hW hf
  exact ⟨⟨(fun i => if i then L else K), (by intro i; cases i <;> assumption), hc,
    (by intro i; cases i <;> assumption), hFc⟩⟩

omit [Finite A] [Finite W] [IsElementaryAbelian 3 A] [IsElementaryAbelian 2 W]
  [FaithfulSMul A W] in
theorem FactorPair.distinct (P : FactorPair (A := A) (W := W)) :
    Function.Injective P.line := by
  have hne : P.line false ≠ P.line true := by
    intro he
    have hb : P.line false = ⊥ := by
      have hh := P.complement.inf_eq_bot
      rwa [←he,inf_idem] at hh
    have hh := P.card false
    rw [hb,card_bot] at hh
    omega
  intro i j he
  cases i <;> cases j <;> simp_all

/-- Intrinsic characterization of the unordered pair by nontrivial fixed points. -/
theorem FactorPair.characterization (P : FactorPair (A := A) (W := W))
    (hA : Nat.card A = 9) (hW : Nat.card W = 16) (D : Subgroup A) :
    (Nat.card D = 3 ∧ FixedPoints.subgroup D W ≠ ⊥) ↔ ∃ i, D = P.line i := by
  constructor
  · rintro ⟨hD,hn⟩
    by_cases h0 : D = P.line false
    · exact ⟨false,h0⟩
    by_cases h1 : D = P.line true
    · exact ⟨true,h1⟩
    exact (hn (other_line_fixed_eq_bot hA hW _ _ (P.card false) (P.card true)
      P.fixed_complement D hD h0 h1)).elim
  · rintro ⟨i,rfl⟩
    refine ⟨P.card i, ?_⟩
    intro he
    have hh := P.fixed_card i
    rw [he,card_bot] at hh
    omega

omit [FaithfulSMul A W] in
/-- The moved subgroup of either line is the fixed plane of the other line. -/
theorem FactorPair.moved_eq_opposite_fixed (P : FactorPair (A := A) (W := W))
    (hW : Nat.card W = 16) (i : Bool) :
    commutatorAction (P.line i) W = FixedPoints.subgroup (P.line (!i)) W := by
  have hc : IsCompl (FixedPoints.subgroup (P.line i) W)
      (FixedPoints.subgroup (P.line (!i)) W) := by
    cases i
    · exact P.fixed_complement
    · exact P.fixed_complement.symm
  have hle : commutatorAction (P.line i) W ≤ FixedPoints.subgroup (P.line (!i)) W := by
    rw [commutatorAction_eq_closure, closure_le]
    rintro x ⟨a,w,rfl⟩
    obtain ⟨u,hu,v,hv,rfl⟩ := Subgroup.mem_sup.mp
      (show w ∈ FixedPoints.subgroup (P.line i) W ⊔
          FixedPoints.subgroup (P.line (!i)) W by rw [hc.sup_eq_top]; trivial)
    have he : (u * v)⁻¹ * a • (u * v) = v⁻¹ * a • v := by
      rw [smul_mul', hu a, mul_inv_rev]
      group
    rw [he]
    exact (FixedPoints.subgroup (P.line (!i)) W).mul_mem
      ((FixedPoints.subgroup (P.line (!i)) W).inv_mem hv)
      (fixed_stable (A := A) _ (a : A) v hv)
  have hsplit : IsCompl (FixedPoints.subgroup (P.line i) W)
      (commutatorAction (P.line i) W) :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (Group.isSolvable_of_comm (fun x y : W => mul_comm x y))
      (by rw [P.card i,hW]; decide) inferInstance
  have hn := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (FixedPoints.subgroup (P.line i) W) (commutatorAction (P.line i) W)
    (by rw [normalizer_eq_top]; exact le_top)
  rw [hsplit.inf_eq_bot,hsplit.sup_eq_top,card_bot,card_top,one_mul,P.fixed_card i,hW] at hn
  apply eq_of_le_of_card_ge hle
  rw [P.fixed_card (!i)]
  omega

omit [FaithfulSMul A W] in
/-- Both actual moved groups have order four and form a direct decomposition. -/
theorem FactorPair.moved_decomposition (P : FactorPair (A := A) (W := W))
    (hW : Nat.card W = 16) :
    (∀ i, Nat.card (commutatorAction (P.line i) W) = 4) ∧
      IsCompl (commutatorAction (P.line false) W) (commutatorAction (P.line true) W) := by
  constructor
  · intro i
    rw [P.moved_eq_opposite_fixed hW i]
    exact P.fixed_card (!i)
  · rw [P.moved_eq_opposite_fixed hW false,P.moved_eq_opposite_fixed hW true]
    exact P.fixed_complement.symm

/-- Equivalent intrinsic description using the actual moved groups. -/
theorem FactorPair.moved_characterization (P : FactorPair (A := A) (W := W))
    (hA : Nat.card A = 9) (hW : Nat.card W = 16) (D : Subgroup A) :
    (Nat.card D = 3 ∧ Nat.card (commutatorAction D W) = 4) ↔ ∃ i, D = P.line i := by
  constructor
  · rintro ⟨hD,hm⟩
    apply (P.characterization hA hW D).mp
    refine ⟨hD, ?_⟩
    intro hz
    have hs : IsCompl (FixedPoints.subgroup D W) (commutatorAction D W) :=
      isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
        (Group.isSolvable_of_comm (fun x y : W => mul_comm x y))
        (by rw [hD,hW]; decide) inferInstance
    have ht := hs.sup_eq_top
    rw [hz,bot_sup_eq] at ht
    rw [ht,card_top,hW] at hm
    omega
  · rintro ⟨i,rfl⟩
    exact ⟨P.card i,(P.moved_decomposition hW).1 i⟩

omit [Finite A] [Finite W] [IsElementaryAbelian 3 A] [IsElementaryAbelian 2 W]
  [FaithfulSMul A W] in
/-- Fixed spaces transport under an actual intertwining pair of automorphisms. -/
theorem fixed_map (f : MulAut A) (e : MulAut W)
    (he : ∀ a w, e (a • w) = f a • e w) (K : Subgroup A) :
    (FixedPoints.subgroup K W).map e.toMonoidHom =
      FixedPoints.subgroup (K.map f.toMonoidHom) W := by
  apply le_antisymm
  · rintro _ ⟨w,hw,rfl⟩ a
    obtain ⟨b,hb,hb'⟩ := a.property
    change (a : A) • e w = e w
    rw [←hb']
    change f b • e w = e w
    rw [←he]
    exact congrArg e (hw ⟨b,hb⟩)
  · intro w hw
    refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
    intro k
    apply e.injective
    change e ((k : A) • e.symm w) = e (e.symm w)
    rw [he,e.apply_symm_apply]
    exact hw ⟨f k, mem_map.mpr ⟨k,k.property,rfl⟩⟩

/-- Compatibility alone forces preservation of the intrinsic unordered pair. -/
theorem FactorPair.permuted (P : FactorPair (A := A) (W := W))
    (hA : Nat.card A = 9) (hW : Nat.card W = 16)
    (f : MulAut A) (e : MulAut W) (he : ∀ a w, e (a • w) = f a • e w) (i : Bool) :
    ∃ j, (P.line i).map f.toMonoidHom = P.line j := by
  apply (P.characterization hA hW _).mp
  refine ⟨(card_map_of_injective f.injective).trans (P.card i), ?_⟩
  rw [←fixed_map f e he]
  intro hz
  have hb := ((FixedPoints.subgroup (P.line i) W).map_eq_bot_iff_of_injective e.injective).mp hz
  have hh := P.fixed_card i
  rw [hb,card_bot] at hh
  omega

/-- An irreducible compatible actor must interchange the two lines. -/
theorem FactorPair.exists_swap (P : FactorPair (A := A) (W := W))
    (hA : Nat.card A = 9) (hW : Nat.card W = 16)
    {T : Type*} [Group T] (τ : T →* MulAut A)
    (hcompatible : ∀ t, ∃ e : MulAut W, ∀ a w, e (a • w) = τ t a • e w)
    (hirr : ∀ D : Subgroup A, (∀ t, D.map (τ t).toMonoidHom = D) → D = ⊥ ∨ D = ⊤) :
    ∃ t : T, (P.line false).map (τ t).toMonoidHom = P.line true ∧
      (P.line true).map (τ t).toMonoidHom = P.line false := by
  have hex : ∃ t : T, (P.line false).map (τ t).toMonoidHom = P.line true := by
    by_contra hn
    push Not at hn
    have hi (t : T) : (P.line false).map (τ t).toMonoidHom = P.line false := by
      obtain ⟨e,he⟩ := hcompatible t
      obtain ⟨j,hj⟩ := P.permuted hA hW (τ t) e he false
      cases j
      · exact hj
      · exact (hn t hj).elim
    rcases hirr (P.line false) hi with hb | ht
    · have hh := P.card false
      rw [hb,card_bot] at hh
      omega
    · have hh := P.card false
      rw [ht,card_top,hA] at hh
      omega
  obtain ⟨t,ht⟩ := hex
  obtain ⟨e,he⟩ := hcompatible t
  obtain ⟨j,hj⟩ := P.permuted hA hW (τ t) e he true
  refine ⟨t,ht,?_⟩
  cases j
  · exact hj
  · have heq := map_injective (τ t).injective (ht.trans hj.symm)
    exact Bool.false_ne_true (P.distinct heq) |>.elim

end CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure.BinaryNormalizer

namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure.BinaryNormalizer

/-- In particular the full automorphism normalizer preserves the pair. -/
theorem normalizer_preserves_pair {W : Type*} [Group W] [Finite W]
    [IsElementaryAbelian 2 W] (A : Subgroup (MulAut W)) [IsElementaryAbelian 3 A]
    (hA : Nat.card A = 9) (hW : Nat.card W = 16)
    (P : FactorPair (A := A) (W := W))
    (n : normalizer (A : Set (MulAut W))) (i : Bool) :
    ∃ j, (P.line i).map (A.normalizerMonoidHom n).toMonoidHom = P.line j := by
  apply P.permuted hA hW (A.normalizerMonoidHom n) (n : MulAut W) _ i
  intro a w
  change (n : MulAut W) ((a : MulAut W) w) =
    (((n : MulAut W) * (a : MulAut W) * (n : MulAut W)⁻¹) : MulAut W)
      ((n : MulAut W) w)
  simp only [MulAut.mul_apply, MulAut.inv_apply_self]

end CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure.BinaryNormalizer
