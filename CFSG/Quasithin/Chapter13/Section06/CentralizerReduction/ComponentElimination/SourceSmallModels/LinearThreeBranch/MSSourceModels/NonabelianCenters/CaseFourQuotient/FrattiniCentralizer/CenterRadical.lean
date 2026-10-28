module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer
import Mathlib.Tactic.LinearCombination

/-!
# Mixed commutators for the fourth-case center argument

Write Q for the MS commutator core, Z = Z(Q), P = Φ(Q), and D = C_Q(P).
An equivariant biadditive map from a dual natural module times a natural
module to the dual natural module is zero. Transvections give 27 independent
coefficient equations over F₂; explicit linear combinations prove their
vanishing. Restriction to the four pairs of summands handles doubled modules.

The section theorem transports this calculation through the literal
D/P, Q/D and P/Z quotients, retaining one common actor and conjugation of
both inputs and the output. It does not assume that the group commutator
already descends to those quotients. That construction remains necessary
before concluding [D,Q] ≤ Z.

The fixed/moved decomposition also proves that Z is elementary. Consequently
[D,Q] ≤ Z implies that all squares of D belong to Z. Elementarity of P and
the subsequent nonzero-radical argument are still needed for Z(D) = P.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
C.1.34(4), printed pp.136–137; Meierfrankenfeld–Stellmacher (1993),
Lemma 4.5, printed pp.895–900. The center conclusion is an additional
algebraic deduction, not a displayed clause of either source statement.
-/

public section

open Matrix Representation BinaryLinearThree
open BinaryLinearThree.AutomorphismAction
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.CenterRadical
private abbrev basis (i : Fin 3) : Vector := Pi.single i 1

private theorem shear_basis {p q : Fin 3} (hpq : p ≠ q) (i : Fin 3) :
    W (SpecialLinearGroup.transvection hpq (1 : ZMod 2)) (basis i) =
      basis i + if i = q then basis p else 0 := by
  change (1 + Matrix.single p q (1 : ZMod 2)) *ᵥ basis i = _
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  by_cases hi : i = q
  · subst i; simp [basis]
  · simp [basis, hi, Ne.symm hi]

private theorem shear_graph {p q : Fin 3} (hpq : p ≠ q) :
    graph (SpecialLinearGroup.transvection hpq (1 : ZMod 2)) =
      SpecialLinearGroup.transvection hpq.symm (1 : ZMod 2) := by
  apply Subtype.ext
  simp [graph_apply, SpecialLinearGroup.transvection_inv,
    SpecialLinearGroup.transvection_coe, Matrix.transpose_add,
    Matrix.transpose_single]

private theorem shear_apply {p q : Fin 3} (hpq : p ≠ q) (v : Vector) (k : Fin 3) :
    W (SpecialLinearGroup.transvection hpq (1 : ZMod 2)) v k =
      v k + if k = p then v q else 0 := by
  change ((1 + Matrix.single p q (1 : ZMod 2)) *ᵥ v) k = _
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply,
    Matrix.single_mulVec_eq, one_mul, Pi.smul_apply, smul_eq_mul]
  by_cases hk : k = p
  · subst k; simp
  · simp [hk]

private theorem mixed_coordinate_zero
    (b : Vector →+ (Vector →+ Vector))
    (hb : ∀ g : BinaryLinearThree.Group, ∀ x y,
      b (W (graph g) x) (W g y) = W (graph g) (b x y)) : b = 0 := by
  let a (i j k : Fin 3) := b (basis i) (basis j) k
  have ha (p q i j k : Fin 3) (hpq : p ≠ q) :
      (if i = p then a q j k else 0) +
      (if j = q then a i p k else 0) +
      (if i = p ∧ j = q then a q p k else 0) =
      (if k = q then a i j p else 0) := by
    have hh := congrFun (hb (SpecialLinearGroup.transvection hpq (1 : ZMod 2))
      (basis i) (basis j)) k
    rw [shear_graph, shear_basis, shear_basis, shear_apply] at hh
    by_cases hi : i = p <;> by_cases hj : j = q <;>
      simp only [hi, hj, if_true, if_false, and_self, and_false, false_and,
        map_add, AddMonoidHom.add_apply, add_zero, zero_add, Pi.add_apply] at hh ⊢
    all_goals dsimp [a] at *
    all_goals linear_combination hh
  have h0 := ha 0 1 0 0 0 (by decide)
  have h1 := ha 0 1 0 0 1 (by decide)
  have h2 := ha 0 1 0 0 2 (by decide)
  have h3 := ha 0 1 0 1 0 (by decide)
  have h4 := ha 0 1 0 1 1 (by decide)
  have h5 := ha 0 1 0 1 2 (by decide)
  have h6 := ha 0 1 0 2 0 (by decide)
  have h7 := ha 0 1 0 2 1 (by decide)
  have h8 := ha 0 1 0 2 2 (by decide)
  have h9 := ha 0 1 2 0 1 (by decide)
  have h10 := ha 0 1 2 1 1 (by decide)
  have h11 := ha 0 1 2 1 2 (by decide)
  have h12 := ha 0 1 2 2 1 (by decide)
  have h13 := ha 0 2 0 0 1 (by decide)
  have h14 := ha 0 2 0 0 2 (by decide)
  have h15 := ha 0 2 0 1 1 (by decide)
  have h16 := ha 0 2 0 1 2 (by decide)
  have h17 := ha 0 2 0 2 1 (by decide)
  have h18 := ha 0 2 0 2 2 (by decide)
  have h19 := ha 1 0 0 0 0 (by decide)
  have h20 := ha 1 0 0 0 1 (by decide)
  have h21 := ha 1 0 0 0 2 (by decide)
  have h22 := ha 1 0 0 2 0 (by decide)
  have h23 := ha 1 0 1 0 0 (by decide)
  have h24 := ha 1 0 1 2 2 (by decide)
  have h25 := ha 2 0 0 0 0 (by decide)
  have h26 := ha 2 0 1 0 1 (by decide)
  norm_num [Fin.ext_iff] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26
  have hbase (i j k : Fin 3) : a i j k = 0 := by
    fin_cases i <;> fin_cases j <;> fin_cases k
    · change a 0 0 0 = 0
      linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide])) h11 + h14
    · change a 0 0 1 = 0
      linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide])) h0 + h1 + h3 + h11 + h14 + h19 + h23
    · change a 0 0 2 = 0
      linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide])) h7 + h25 + h26
    · change a 0 1 0 = 0
      linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide])) h0 + h1 + h3 + h11 + h14 + h23
    · change a 0 1 1 = 0
      exact h20
    · change a 0 1 2 = 0
      exact h21
    · change a 0 2 0 = 0
      linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide])) h7 + h26
    · change a 0 2 1 = 0
      exact h22.symm
    · change a 0 2 2 = 0
      exact h24
    · change a 1 0 0 = 0
      exact h0
    · change a 1 0 1 = 0
      linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide])) h1 + h11 + h14
    · change a 1 0 2 = 0
      exact h2
    · change a 1 1 0 = 0
      linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide])) h0 + h3 + h11 + h14
    · change a 1 1 1 = 0
      linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide])) h1 + h4 + h11 + h14 + h19
    · change a 1 1 2 = 0
      linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide])) h2 + h5 + h7 + h25 + h26
    · change a 1 2 0 = 0
      exact h6
    · change a 1 2 1 = 0
      exact h26
    · change a 1 2 2 = 0
      exact h8
    · change a 2 0 0 = 0
      exact h9.symm
    · change a 2 0 1 = 0
      exact h13
    · change a 2 0 2 = 0
      exact h11
    · change a 2 1 0 = 0
      linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide])) h10 + h13
    · change a 2 1 1 = 0
      exact h15
    · change a 2 1 2 = 0
      linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide])) h0 + h1 + h3 + h11 + h14 + h16 + h23
    · change a 2 2 0 = 0
      exact h12.symm
    · change a 2 2 1 = 0
      linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide])) h0 + h1 + h3 + h11 + h13 + h14 + h17 + h19 + h23
    · change a 2 2 2 = 0
      linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide])) h11 + h18 + h25
  have he (i j : Fin 3) : b (Pi.single i 1) (Pi.single j 1) = 0 := by
    ext k
    exact hbase i j k
  apply AddMonoidHom.ext
  intro x
  apply AddMonoidHom.ext
  intro y
  funext k
  change b x y k = 0
  have hx : x = ∑ i : Fin 3, Pi.single i (x i) := (Finset.univ_sum_single x).symm
  have hy : y = ∑ i : Fin 3, Pi.single i (y i) := (Finset.univ_sum_single y).symm
  have hzero : b x y = 0 := by
    rw [hy, map_sum]
    apply Finset.sum_eq_zero
    intro j _
    change b.flip (Pi.single j (y j)) x = 0
    rw [hx, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    change b (Pi.single i (x i)) (Pi.single j (y j)) = 0
    have hxv : x i = 0 ∨ x i = 1 := (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (x i)
    have hyv : y j = 0 ∨ y j = 1 := (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (y j)
    rcases hxv with hxv | hxv <;> rcases hyv with hyv | hyv <;>
      simp [hxv, hyv, he]
  exact congrFun hzero k

local notation "DV" => Module.Dual (ZMod 2) Vector

/-- The mixed dual-natural tensor has no dual-natural quotient under the same actor. -/
theorem mixed_biadditive_eq_zero
    (b : DV →+ (Vector →+ DV))
    (hb : ∀ g : BinaryLinearThree.Group, ∀ x y,
      b (W.dual g x) (W g y) = W.dual g (b x y)) : b = 0 := by
  let f := graphNaturalDual.toLinearEquiv.toAddEquiv
  let c : Vector →+ (Vector →+ Vector) := {
    toFun x := f.symm.toAddMonoidHom.comp (b (f x))
    map_zero' := by ext y; simp
    map_add' x y := by ext z; simp }
  have he (g : BinaryLinearThree.Group) (v : Vector) :
      f (W (graph g) v) = W.dual g (f v) :=
    LinearMap.congr_fun (graphNaturalDual.isIntertwining' g) v
  have hc : c = 0 := mixed_coordinate_zero c (by
    intro g x y
    apply f.injective
    change f (f.symm (b (f (W (graph g) x)) (W g y))) =
      f (W (graph g) (f.symm (b (f x) y)))
    rw [f.apply_symm_apply, he, he, f.apply_symm_apply, hb])
  apply AddMonoidHom.ext
  intro x
  apply AddMonoidHom.ext
  intro y
  obtain ⟨v, rfl⟩ := f.surjective x
  have hh := congrArg (fun c : Vector →+ (Vector →+ Vector) => c v y) hc
  change f.symm (b (f v) y) = 0 at hh
  exact f.symm.injective (hh.trans f.symm.map_zero.symm)

/-- Vanishing for both doubled sections retains the common SL₃(2) marking. -/
theorem doubled_mixed_biadditive_eq_zero
    (b : (DV × DV) →+ ((Vector × Vector) →+ DV))
    (hb : ∀ g : BinaryLinearThree.Group, ∀ x y,
      b ((W.dual.prod W.dual) g x) ((W.prod W) g y) = W.dual g (b x y)) : b = 0 := by
  have hs (f₁ : DV →+ (DV × DV)) (f₂ : Vector →+ (Vector × Vector))
      (hf₁ : ∀ g x, f₁ (W.dual g x) = (W.dual.prod W.dual) g (f₁ x))
      (hf₂ : ∀ g y, f₂ (W g y) = (W.prod W) g (f₂ y)) :
      ∀ x y, b (f₁ x) (f₂ y) = 0 := by
    let c : DV →+ (Vector →+ DV) := {
      toFun x := (b (f₁ x)).comp f₂
      map_zero' := by ext y; simp
      map_add' x y := by ext z; simp }
    have hc : c = 0 := mixed_biadditive_eq_zero c (by
      intro g x y
      change b (f₁ (W.dual g x)) (f₂ (W g y)) = W.dual g (b (f₁ x) (f₂ y))
      rw [hf₁, hf₂, hb])
    intro x y
    exact congrArg (fun c : DV →+ (Vector →+ DV) => c x y) hc
  have hdl (g : BinaryLinearThree.Group) (x : DV) :
      AddMonoidHom.inl DV DV (W.dual g x) =
        (W.dual.prod W.dual) g (AddMonoidHom.inl DV DV x) := by
    change (W.dual g x, 0) = (W.dual g x, W.dual g 0)
    rw [map_zero]
  have hdr (g : BinaryLinearThree.Group) (x : DV) :
      AddMonoidHom.inr DV DV (W.dual g x) =
        (W.dual.prod W.dual) g (AddMonoidHom.inr DV DV x) := by
    change (0, W.dual g x) = (W.dual g 0, W.dual g x)
    rw [map_zero]
  have hnl (g : BinaryLinearThree.Group) (x : Vector) :
      AddMonoidHom.inl Vector Vector (W g x) =
        (W.prod W) g (AddMonoidHom.inl Vector Vector x) := by
    change (W g x, 0) = (W g x, W g 0)
    rw [map_zero]
  have hnr (g : BinaryLinearThree.Group) (x : Vector) :
      AddMonoidHom.inr Vector Vector (W g x) =
        (W.prod W) g (AddMonoidHom.inr Vector Vector x) := by
    change (0, W g x) = (W g 0, W g x)
    rw [map_zero]
  have hll := hs (.inl DV DV) (.inl Vector Vector) hdl hnl
  have hlr := hs (.inl DV DV) (.inr Vector Vector) hdl hnr
  have hrl := hs (.inr DV DV) (.inl Vector Vector) hdr hnl
  have hrr := hs (.inr DV DV) (.inr Vector Vector) hdr hnr
  apply AddMonoidHom.ext
  intro x
  apply AddMonoidHom.ext
  intro y
  change b x y = 0
  have hx : x = AddMonoidHom.inl DV DV x.1 + AddMonoidHom.inr DV DV x.2 := by simp
  have hy : y = AddMonoidHom.inl Vector Vector y.1 + AddMonoidHom.inr Vector Vector y.2 := by simp
  rw [hx, hy]
  simp only [map_add, AddMonoidHom.add_apply, hll, hlr, hrl, hrr, add_zero]


open Subgroup
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters

local notation "sCenter" => CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn

variable {G : Type*} [_root_.Group G] {K X A Y B T C : Subgroup G}

/-- Transport mixed-pairing vanishing through three literal section models.
The invariance condition includes the actual conjugate of an output representative. -/
theorem mixed_section_pairings_vanish
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (hX : HasSectionModel K X A (linearThreeActor e) (W.dual.prod W.dual))
    (hY : HasSectionModel K Y B (linearThreeActor e) (W.prod W))
    (hT : HasSectionModel K T C (linearThreeActor e) W.dual) :
    ∃ hnX : (A.subgroupOf X).Normal,
    ∃ hnY : (B.subgroupOf Y).Normal,
    ∃ hnT : (C.subgroupOf T).Normal,
      letI := hnX
      letI := hnY
      letI := hnT
      ∀ b : (X ⧸ A.subgroupOf X) → (Y ⧸ B.subgroupOf Y) → (T ⧸ C.subgroupOf T),
        (∀ x y z, b (x*y) z = b x z * b y z) →
        (∀ x y z, b x (y*z) = b x y * b x z) →
        (∀ (k : K) (x x' : X) (y y' : Y) (t t' : T),
          (x' : G) = k * (x : G) * (k : G)⁻¹ →
          (y' : G) = k * (y : G) * (k : G)⁻¹ →
          (t' : G) = k * (t : G) * (k : G)⁻¹ →
          b (QuotientGroup.mk' _ x) (QuotientGroup.mk' _ y) = QuotientGroup.mk' _ t →
          b (QuotientGroup.mk' _ x') (QuotientGroup.mk' _ y') = QuotientGroup.mk' _ t') →
        ∀ x y, b x y = 1 := by
  obtain ⟨_, hKX, _, hnX, fX, hfX⟩ := hX
  obtain ⟨_, hKY, _, hnY, fY, hfY⟩ := hY
  obtain ⟨_, hKT, _, hnT, fT, hfT⟩ := hT
  let := hnX
  let := hnY
  let := hnT
  refine ⟨hnX, hnY, hnT, ?_⟩
  intro b hm₁ hm₂ hb
  have bz₁ y : b 1 y = 1 := by
    have hh := hm₁ 1 1 y
    rw [one_mul] at hh
    exact mul_left_cancel (hh.symm.trans (mul_one _).symm)
  have bz₂ x : b x 1 = 1 := by
    have hh := hm₂ x 1 1
    rw [one_mul] at hh
    exact mul_left_cancel (hh.symm.trans (mul_one _).symm)
  let c : (DV × DV) →+ ((Vector × Vector) →+ DV) := {
    toFun x := {
      toFun y := Multiplicative.toAdd
        (fT (b (fX.symm (Multiplicative.ofAdd x)) (fY.symm (Multiplicative.ofAdd y))))
      map_zero' := by simp only [ofAdd_zero, map_one, bz₂, toAdd_one]
      map_add' y z := by
        simp only [ofAdd_add, map_mul, hm₂, toAdd_mul] }
    map_zero' := by
      apply AddMonoidHom.ext
      intro y
      change Multiplicative.toAdd (fT (b (fX.symm (Multiplicative.ofAdd 0))
        (fY.symm (Multiplicative.ofAdd y)))) = 0
      simp only [ofAdd_zero, map_one, bz₁, toAdd_one]
    map_add' x y := by
      apply AddMonoidHom.ext
      intro z
      change Multiplicative.toAdd (fT (b (fX.symm (Multiplicative.ofAdd (x+y)))
        (fY.symm (Multiplicative.ofAdd z)))) = _
      simp only [ofAdd_add, map_mul, hm₁, toAdd_mul]
      rfl }
  have heval (x : X) (y : Y) :
      c (Multiplicative.toAdd (fX (QuotientGroup.mk' _ x)))
        (Multiplicative.toAdd (fY (QuotientGroup.mk' _ y))) =
      Multiplicative.toAdd (fT (b (QuotientGroup.mk' _ x) (QuotientGroup.mk' _ y))) := by
    change Multiplicative.toAdd (fT (b (fX.symm (fX (QuotientGroup.mk' _ x)))
      (fY.symm (fY (QuotientGroup.mk' _ y))))) = _
    rw [fX.symm_apply_apply, fY.symm_apply_apply]
  have hc : c = 0 := doubled_mixed_biadditive_eq_zero c (by
    intro g x y
    obtain ⟨k, rfl⟩ := linearThreeActor_surjective e g
    have hsX : Function.Surjective (fun x : X =>
        Multiplicative.toAdd (fX (QuotientGroup.mk' _ x))) :=
      Multiplicative.toAdd.surjective.comp (fX.surjective.comp (QuotientGroup.mk'_surjective _))
    have hsY : Function.Surjective (fun y : Y =>
        Multiplicative.toAdd (fY (QuotientGroup.mk' _ y))) :=
      Multiplicative.toAdd.surjective.comp (fY.surjective.comp (QuotientGroup.mk'_surjective _))
    obtain ⟨x, rfl⟩ := hsX x
    obtain ⟨y, rfl⟩ := hsY y
    obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective (C.subgroupOf T)
      (b (QuotientGroup.mk' _ x) (QuotientGroup.mk' _ y))
    let x' := X.normalizerMonoidHom ⟨k, hKX k.property⟩ x
    let y' := Y.normalizerMonoidHom ⟨k, hKY k.property⟩ y
    let t' := T.normalizerMonoidHom ⟨k, hKT k.property⟩ t
    rw [← hfX k x x' rfl, ← hfY k y y' rfl, heval, heval,
      hb k x x' y y' t t' rfl rfl rfl ht.symm, ← ht]
    exact hfT k t t' rfl)
  intro x y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (A.subgroupOf X) x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (B.subgroupOf Y) y
  have hh := congrArg (fun c : (DV × DV) →+ ((Vector × Vector) →+ DV) =>
    c (Multiplicative.toAdd (fX (QuotientGroup.mk' _ x)))
      (Multiplicative.toAdd (fY (QuotientGroup.mk' _ y)))) hc
  rw [heval] at hh
  apply fT.injective
  exact hh.trans fT.map_one.symm

/-- The literal three sections of C.1.34(4) admit no equivariant mixed pairing.
This supplies the model calculation for descending [D,Q] modulo Z(Q). -/
theorem caseFour_mixed_pairings_vanish {R S : Subgroup G}
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e) :
    let Q := msQ K R
    let Z := sCenter Q
    let P := frattiniIn Q
    let D := Q ⊓ centralizer (P : Set G)
    ∃ hnD : (P.subgroupOf D).Normal,
    ∃ hnQ : (D.subgroupOf Q).Normal,
    ∃ hnP : (Z.subgroupOf P).Normal,
      letI := hnD
      letI := hnQ
      letI := hnP
      ∀ b : (D ⧸ P.subgroupOf D) → (Q ⧸ D.subgroupOf Q) → (P ⧸ Z.subgroupOf P),
        (∀ x y z, b (x*y) z = b x z * b y z) →
        (∀ x y z, b x (y*z) = b x y * b x z) →
        (∀ (k : K) (x x' : D) (y y' : Q) (t t' : P),
          (x' : G) = k * (x : G) * (k : G)⁻¹ →
          (y' : G) = k * (y : G) * (k : G)⁻¹ →
          (t' : G) = k * (t : G) * (k : G)⁻¹ →
          b (QuotientGroup.mk' _ x) (QuotientGroup.mk' _ y) = QuotientGroup.mk' _ t →
          b (QuotientGroup.mk' _ x') (QuotientGroup.mk' _ y') = QuotientGroup.mk' _ t') →
        ∀ x y, b x y = 1 :=
  mixed_section_pairings_vanish e h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.1


private theorem natural_section_square {D : Subgroup G}
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (h : HasSectionModel K D ⊥ (linearThreeActor e) W) (x : G) (hx : x ∈ D) : x^2 = 1 := by
  obtain ⟨_, _, _, hn, f, _⟩ := h
  let := hn
  have hi : Function.Injective (QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf D)) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [QuotientGroup.ker_mk', bot_subgroupOf]
  have hh : (⟨x,hx⟩ : D)^2 = 1 := by
    apply hi
    apply f.injective
    rw [map_pow, map_pow, map_one, map_one, pow_two]
    change Multiplicative.ofAdd
      ((f (QuotientGroup.mk' _ ⟨x,hx⟩)).toAdd + (f (QuotientGroup.mk' _ ⟨x,hx⟩)).toAdd) =
      Multiplicative.ofAdd 0
    congr 1
    ext i
    exact CharTwo.add_self_eq_zero _
  exact congrArg Subtype.val hh

/-- The stated fixed/moved decomposition makes the full center elementary. -/
theorem caseFour_center_elementary {R S : Subgroup G}
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e) :
    IsElementaryAbelian 2 (sCenter (msQ K R)) := by
  let Q := msQ K R
  let Z := sCenter Q
  let C := Q ⊓ centralizer (K : Set G)
  let U := ⁅Z,K⁆
  have hZQ : Z ≤ Q := map_subtype_le _
  have hZc : Z ≤ centralizer (Q : Set G) := (centerIn_eq Q).le.trans inf_le_right
  have hcomm (x y : G) (hx : x ∈ Z) (hy : y ∈ Z) : Commute x y :=
    (hZc hy x (hZQ hx))
  let E : Subgroup G := {
    carrier := {x | x ∈ Z ∧ x^2 = 1}
    one_mem' := ⟨Z.one_mem, one_pow 2⟩
    mul_mem' hx hy := ⟨Z.mul_mem hx.1 hy.1, by
      rw [(hcomm _ _ hx.1 hy.1).mul_pow, hx.2, hy.2, one_mul]⟩
    inv_mem' hx := ⟨Z.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hdecomp : Z = C ⊔ U := h.2.2.2.1
  have hZE : Z ≤ E := by
    rw [hdecomp]
    apply sup_le
    · intro x hx
      let : IsElementaryAbelian 2 C := h.1
      exact ⟨hdecomp ▸ mem_sup_left hx,
        elemPow_eq_one_of_isElementaryAbelian x hx⟩
    · intro x hx
      exact ⟨hdecomp ▸ mem_sup_right hx,
        natural_section_square e h.2.2.2.2.2.1 x hx⟩
  refine {
    toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (hcomm x y x.property y.property)⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  exact Subtype.ext (hZE x.property).2

open scoped commutatorElement

/-- Once the mixed commutator lies in Z(Q), elementary Z(Q) puts all squares
of the actual Frattini centralizer back in Z(Q). -/
theorem caseFour_centralizer_square_mem_center_of_mixed {R S : Subgroup G}
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e)
    (hmixed : ⁅msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G), msQ K R⁆ ≤
      sCenter (msQ K R)) :
    ∀ x ∈ msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G),
      x^2 ∈ sCenter (msQ K R) := by
  let Q := msQ K R
  let Z := sCenter Q
  let : IsElementaryAbelian 2 Z := caseFour_center_elementary e h
  intro x hx
  rw [centerIn_eq]
  refine ⟨Q.pow_mem hx.1 2, ?_⟩
  intro y hy
  have hc : ⁅x,y⁆ ∈ Z := hmixed (commutator_mem_commutator hx hy)
  have hcomm : x * ⁅x,y⁆ = ⁅x,y⁆ * x :=
    ((centerIn_eq Q).le hc).2 x hx.1
  have he : ⁅x^2,y⁆ = 1 := by
    rw [pow_two, commutatorElement_mul_left_eq_conj_mul, hcomm, mul_inv_cancel_right,
      ← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian _ hc
  exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.CenterRadical
