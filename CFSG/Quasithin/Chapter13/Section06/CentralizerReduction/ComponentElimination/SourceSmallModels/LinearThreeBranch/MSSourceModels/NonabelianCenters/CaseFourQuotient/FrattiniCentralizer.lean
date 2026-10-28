module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual

/-!
# Commutators in the fourth-case Frattini centralizer

For Q from C.1.34(4), put D = C_Q(Φ(Q)), Z = Z(Q), and U = [Z,K].
The three-subgroups lemma gives [D,D] ≤ Z. The commutator pairing on
D/Φ(Q), followed by Z → Z/U, is invariant under K. Every invariant
biadditive pairing on the doubled dual natural module with trivial target
vanishes: transvections kill each coefficient on a natural three-space,
and inverse transpose transports this fact to its dual. Consequently
[D,D] ≤ U, so [D,D] has trivial intersection with C_Q(K).

We also prove Φ(Q) ≤ Z(D). Thus the remaining center clause in
`FrattiniCentralizerControl` is exactly Z(D) = Φ(Q). That equality is not
proved in this module. The quotient and checked-map applications below
retain it as an explicit hypothesis, together with the independently owned
`FrattiniCommutatorLarge` hypothesis. They do not complete C.1.34(4)'s
application to 13.6.22.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
C.1.34(4), printed pp.136–137, and 13.6.22, printed pp.932–933.
The finer MS93 source is Lemma 4.5, printed pp.895–900. Neither that
statement nor C.1.34 explicitly states the remaining center equality.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer


open Matrix Representation
open BinaryLinearThree

variable {E : Type*} [AddCommGroup E]

private theorem natural_biadditive_eq_zero
    (b : Vector →+ (Vector →+ E))
    (hb : ∀ g : BinaryLinearThree.Group, ∀ x y, b (W g x) (W g y) = b x y) :
    b = 0 := by
  have hbase (i j : Fin 3) : b (Pi.single i 1) (Pi.single j 1) = 0 := by
    obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
      fin_cases i <;> fin_cases j <;> decide
    let g : BinaryLinearThree.Group := SpecialLinearGroup.transvection hki.symm (1 : ZMod 2)
    have hx : W g (Pi.single k 1) = Pi.single k 1 + Pi.single i 1 := by
      change g.val *ᵥ (Pi.single k 1) = _
      simp only [g, SpecialLinearGroup.transvection_coe, Matrix.add_mulVec,
        Matrix.one_mulVec, Matrix.single_mulVec_eq, Pi.single_eq_same,
        mul_one, one_smul]
    have hy : W g (Pi.single j 1) = Pi.single j 1 := by
      change g.val *ᵥ (Pi.single j 1) = _
      simp only [g, SpecialLinearGroup.transvection_coe, Matrix.add_mulVec,
        Matrix.one_mulVec, Matrix.single_mulVec_eq, Pi.single_eq_of_ne hkj,
        mul_zero, zero_smul, add_zero]
    have hh := hb g (Pi.single k 1) (Pi.single j 1)
    rw [hx, hy, map_add, AddMonoidHom.add_apply] at hh
    exact add_left_cancel (hh.trans (add_zero _).symm)
  apply AddMonoidHom.ext
  intro x
  apply AddMonoidHom.ext
  intro y
  change b x y = 0
  have hx : x = ∑ i : Fin 3, Pi.single i (x i) := (Finset.univ_sum_single x).symm
  have hy : y = ∑ i : Fin 3, Pi.single i (y i) := (Finset.univ_sum_single y).symm
  rw [hy, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  change b.flip (Pi.single j (y j)) x = 0
  rw [hx]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  change b (Pi.single i (x i)) (Pi.single j (y j)) = 0
  have hxv : x i = 0 ∨ x i = 1 := (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (x i)
  have hyv : y j = 0 ∨ y j = 1 := (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (y j)
  rcases hxv with hxv | hxv <;> rcases hyv with hyv | hyv <;>
    simp [hxv, hyv, hbase]


private theorem dual_biadditive_eq_zero
    (b : Module.Dual (ZMod 2) Vector →+ (Module.Dual (ZMod 2) Vector →+ E))
    (hb : ∀ g : BinaryLinearThree.Group, ∀ x y,
      b (W.dual g x) (W.dual g y) = b x y) : b = 0 := by
  let e := AutomorphismAction.graphNaturalDual.toLinearEquiv.toAddEquiv
  let c : Vector →+ (Vector →+ E) := {
    toFun x := (b (e x)).comp e.toAddMonoidHom
    map_zero' := by ext y; simp
    map_add' x y := by ext z; simp }
  have he (g : BinaryLinearThree.Group) (x : Vector) :
      e (W g x) = W.dual (AutomorphismAction.graph g) (e x) := by
    have hh := LinearMap.congr_fun
      (AutomorphismAction.graphNaturalDual.isIntertwining' (AutomorphismAction.graph g)) x
    change e (W (AutomorphismAction.graph (AutomorphismAction.graph g)) x) =
      W.dual (AutomorphismAction.graph g) (e x) at hh
    rwa [AutomorphismAction.graph_graph] at hh
  have hc : c = 0 := natural_biadditive_eq_zero c (by
    intro g x y
    change b (e (W g x)) (e (W g y)) = b (e x) (e y)
    rw [he, he, hb])
  ext x y
  obtain ⟨v, rfl⟩ := e.surjective x
  obtain ⟨w, rfl⟩ := e.surjective y
  exact congrArg (fun f : Vector →+ (Vector →+ E) => f v w) hc


private abbrev DV := Module.Dual (ZMod 2) Vector

private theorem doubled_dual_biadditive_eq_zero
    (b : (DV × DV) →+ ((DV × DV) →+ E))
    (hb : ∀ g : BinaryLinearThree.Group, ∀ x y,
      b ((W.dual.prod W.dual) g x) ((W.dual.prod W.dual) g y) = b x y) : b = 0 := by
  have hs (f₁ f₂ : DV →+ (DV × DV))
      (hf₁ : ∀ g x, f₁ (W.dual g x) = (W.dual.prod W.dual) g (f₁ x))
      (hf₂ : ∀ g x, f₂ (W.dual g x) = (W.dual.prod W.dual) g (f₂ x)) :
      ∀ x y, b (f₁ x) (f₂ y) = 0 := by
    let c : DV →+ (DV →+ E) := {
      toFun x := (b (f₁ x)).comp f₂
      map_zero' := by ext y; simp
      map_add' x y := by ext z; simp }
    have hc : c = 0 := dual_biadditive_eq_zero c (by
      intro g x y
      change b (f₁ (W.dual g x)) (f₂ (W.dual g y)) = b (f₁ x) (f₂ y)
      rw [hf₁, hf₂, hb])
    intro x y
    exact congrArg (fun c : DV →+ (DV →+ E) => c x y) hc
  have hl (g : BinaryLinearThree.Group) (x : DV) :
      AddMonoidHom.inl DV DV (W.dual g x) =
        (W.dual.prod W.dual) g (AddMonoidHom.inl DV DV x) := by
    change (W.dual g x, 0) = (W.dual g x, W.dual g 0)
    rw [map_zero]
  have hr (g : BinaryLinearThree.Group) (x : DV) :
      AddMonoidHom.inr DV DV (W.dual g x) =
        (W.dual.prod W.dual) g (AddMonoidHom.inr DV DV x) := by
    change (0, W.dual g x) = (W.dual g 0, W.dual g x)
    rw [map_zero]
  have hll := hs (AddMonoidHom.inl DV DV) (AddMonoidHom.inl DV DV) hl hl
  have hlr := hs (AddMonoidHom.inl DV DV) (AddMonoidHom.inr DV DV) hl hr
  have hrl := hs (AddMonoidHom.inr DV DV) (AddMonoidHom.inl DV DV) hr hl
  have hrr := hs (AddMonoidHom.inr DV DV) (AddMonoidHom.inr DV DV) hr hr
  ext x y
  change b x y = 0
  have hx : x = AddMonoidHom.inl DV DV x.1 + AddMonoidHom.inr DV DV x.2 := by simp
  have hy : y = AddMonoidHom.inl DV DV y.1 + AddMonoidHom.inr DV DV y.2 := by simp
  rw [hx, hy]
  simp only [map_add, AddMonoidHom.add_apply, hll, hlr, hrl, hrr, add_zero]


open Subgroup
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters

variable {G : Type*} [_root_.Group G] {K D P : Subgroup G}

/-- A doubled-dual section has no invariant bicharacter with a trivial target.
Invariance is stated on the literal quotient and actual conjugates. -/
theorem section_pairings_vanish
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (h : HasSectionModel K D P (linearThreeActor e) (W.dual.prod W.dual)) :
    ∃ hn : (P.subgroupOf D).Normal, letI := hn
      ∀ {H : Type*} [CommGroup H]
        (b : (D ⧸ P.subgroupOf D) →* ((D ⧸ P.subgroupOf D) →* H)),
        (∀ (k : K) (x x' y y' : D),
          (x' : G) = k * (x : G) * (k : G)⁻¹ →
          (y' : G) = k * (y : G) * (k : G)⁻¹ →
          b (QuotientGroup.mk' _ x') (QuotientGroup.mk' _ y') =
            b (QuotientGroup.mk' _ x) (QuotientGroup.mk' _ y)) → b = 1 := by
  obtain ⟨_, hnD, _, hn, f, hf⟩ := h
  let := hn
  refine ⟨hn, ?_⟩
  intro H _ b hb
  let c : (DV × DV) →+ ((DV × DV) →+ Additive H) := {
    toFun x := ((b (f.symm (Multiplicative.ofAdd x))).comp f.symm.toMonoidHom).toAdditive
    map_zero' := by
      ext y
      change b (f.symm 1) (f.symm (Multiplicative.ofAdd y)) = 1
      simp
    map_add' x y := by
      ext z
      change b (f.symm (Multiplicative.ofAdd x * Multiplicative.ofAdd y))
          (f.symm (Multiplicative.ofAdd z)) =
        b (f.symm (Multiplicative.ofAdd x)) (f.symm (Multiplicative.ofAdd z)) *
          b (f.symm (Multiplicative.ofAdd y)) (f.symm (Multiplicative.ofAdd z))
      rw [map_mul, map_mul, MonoidHom.mul_apply] }
  have heval (x y : D) :
      c (Multiplicative.toAdd (f (QuotientGroup.mk' _ x)))
          (Multiplicative.toAdd (f (QuotientGroup.mk' _ y))) =
        Additive.ofMul (b (QuotientGroup.mk' _ x) (QuotientGroup.mk' _ y)) := by
    change Additive.ofMul (b (f.symm (f (QuotientGroup.mk' _ x)))
      (f.symm (f (QuotientGroup.mk' _ y)))) = _
    rw [f.symm_apply_apply, f.symm_apply_apply]
  have hc : c = 0 := doubled_dual_biadditive_eq_zero c (by
    intro g x y
    obtain ⟨k, rfl⟩ := linearThreeActor_surjective e g
    have hs : Function.Surjective (fun d : D =>
        Multiplicative.toAdd (f (QuotientGroup.mk' _ d))) :=
      Multiplicative.toAdd.surjective.comp (f.surjective.comp (QuotientGroup.mk'_surjective _))
    obtain ⟨d, rfl⟩ := hs x
    obtain ⟨u, rfl⟩ := hs y
    let d' := D.normalizerMonoidHom ⟨k, hnD k.property⟩ d
    let u' := D.normalizerMonoidHom ⟨k, hnD k.property⟩ u
    rw [← hf k d d' rfl, ← hf k u u' rfl, heval, heval]
    exact congrArg Additive.ofMul (hb k d d' u u' rfl rfl))
  apply MonoidHom.ext
  intro x
  apply MonoidHom.ext
  intro y
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (P.subgroupOf D) x
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (P.subgroupOf D) y
  have hh := congrArg (fun c : (DV × DV) →+ ((DV × DV) →+ Additive H) =>
    c (Multiplicative.toAdd (f (QuotientGroup.mk' _ d)))
      (Multiplicative.toAdd (f (QuotientGroup.mk' _ u)))) hc
  rw [heval] at hh
  exact hh


open scoped commutatorElement

private theorem exists_section_commutator_pairing
    {H : Type*} [CommGroup H] (D P Z : Subgroup G)
    [(P.subgroupOf D).Normal] (hDD : ⁅D,D⁆ ≤ Z)
    (hZ : Z ≤ centralizer (D : Set G)) (hP : P ≤ centralizer (D : Set G))
    (f : Z →* H) :
    ∃ b : (D ⧸ P.subgroupOf D) →* ((D ⧸ P.subgroupOf D) →* H),
      ∀ x y : D, b (QuotientGroup.mk' _ x) (QuotientGroup.mk' _ y) =
        f ⟨⁅(x : G),(y : G)⁆, hDD (commutator_mem_commutator x.property y.property)⟩ := by
  let c (x y : D) : Z :=
    ⟨⁅(x : G),(y : G)⁆, hDD (commutator_mem_commutator x.property y.property)⟩
  have hz (x y z : D) : (z : G) * (c x y : G) = (c x y : G) * z :=
    hZ (c x y).property z z.property
  have cr (x y z : D) : c x (y*z) = c x y * c x z := by
    apply Subtype.ext
    change ⁅(x : G),(y : G) * z⁆ = ⁅(x : G),(y : G)⁆ * ⁅(x : G),(z : G)⁆
    rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc _ (y : G), hz x z y,
      ← mul_assoc, mul_inv_cancel_right]
  have cl (x y z : D) : c (x*y) z = c y z * c x z := by
    apply Subtype.ext
    change ⁅(x : G) * y,(z : G)⁆ = ⁅(y : G),(z : G)⁆ * ⁅(x : G),(z : G)⁆
    rw [commutatorElement_mul_left_eq_conj_mul, hz y z x, mul_inv_cancel_right]
  have cp₁ (x y : D) (hx : (x : G) ∈ P) : c x y = 1 := by
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hP hx y y.property).symm
  have cp₂ (x y : D) (hy : (y : G) ∈ P) : c x y = 1 := by
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hP hy x x.property)
  let r (x : D) : D →* H := {
    toFun y := f (c x y)
    map_one' := by rw [cp₂ x 1 P.one_mem, map_one]
    map_mul' y z := by rw [cr, map_mul] }
  let t (x : D) : (D ⧸ P.subgroupOf D) →* H :=
    QuotientGroup.lift (P.subgroupOf D) (r x) (by
      intro y hy
      change f (c x y) = 1
      rw [cp₂ x y hy, map_one])
  let s : D →* ((D ⧸ P.subgroupOf D) →* H) := {
    toFun := t
    map_one' := by
      apply MonoidHom.ext
      intro y
      obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (P.subgroupOf D) y
      change f (c 1 y) = 1
      rw [cp₁ 1 y P.one_mem, map_one]
    map_mul' x y := by
      apply MonoidHom.ext
      intro z
      obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective (P.subgroupOf D) z
      change f (c (x*y) z) = f (c x z) * f (c y z)
      rw [cl, map_mul, mul_comm] }
  refine ⟨QuotientGroup.lift (P.subgroupOf D) s ?_, fun _ _ => rfl⟩
  intro x hx
  apply MonoidHom.ext
  intro y
  obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (P.subgroupOf D) y
  change f (c x y) = 1
  rw [cp₁ x y hx, map_one]


local notation "sCenter" => CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn

variable [Finite G]

private theorem centralizer_derived (Q : Subgroup G) (hQ : IsPGroup 2 Q) :
    let D := Q ⊓ centralizer (frattiniIn Q : Set G)
    ⁅D,D⁆ ≤ sCenter Q := by
  let D := Q ⊓ centralizer (frattiniIn Q : Set G)
  have hPhi : ⁅Q,Q⁆ ≤ frattiniIn Q := by
    let : Fact (IsPGroup 2 Q) := ⟨hQ⟩
    rw [← map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  have hc : frattiniIn Q ≤ centralizer (D : Set G) :=
    fun x hx y hy => (hy.2 x hx).symm
  have hDQ : ⁅⁅D,Q⁆,D⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact ((commutator_mono inf_le_left le_rfl).trans hPhi).trans hc
  have hQD : ⁅⁅Q,D⁆,D⁆ = ⊥ := by rwa [commutator_comm Q D]
  rw [centerIn_eq]
  exact le_inf ((commutator_le_self D).trans inf_le_left)
    (commutator_eq_bot_iff_le_centralizer.mp
      (commutator_commutator_eq_bot_of_rotate hDQ hQD))

omit [Finite G] in
/-- The displayed denominator Φ(Q) lies in the center of its centralizer. -/
theorem caseFour_frattini_le_center_centralizer {K R S : Subgroup G}
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e) :
    frattiniIn (msQ K R) ≤
      sCenter (msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G)) := by
  obtain ⟨_, _, _, _, _, _, _, hD, _, _⟩ := h
  rw [centerIn_eq]
  exact le_inf hD.1 (fun x hx y hy => (hy.2 x hx).symm)

/-- The derived subgroup of the literal Frattini centralizer lies in U. -/
theorem caseFour_centralizer_derived_le_moved_center {K R S : Subgroup G} {κ : CFSG.Quasithin.GroupClass}
    (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e) :
    let Q := msQ K R
    let D := Q ⊓ centralizer (frattiniIn Q : Set G)
    ⁅D,D⁆ ≤ ⁅sCenter Q,K⁆ := by
  let Q := msQ K R
  let Z := sCenter Q
  let P := frattiniIn Q
  let D := Q ⊓ centralizer (P : Set G)
  let U := ⁅Z,K⁆
  have hQ : IsPGroup 2 Q := by
    apply (isPGroup_pCoreIn 2 K).to_le
    change msQ K R ≤ K.pCoreIn 2
    rw [msQ_eq_ambient_blockU K R (msPair_core_hypotheses hMS).1 (msPair_core_hypotheses hMS).2]
    exact map_mono CFSG.Quasithin.ChapterC.blockU_le_core
  have hDD : ⁅D,D⁆ ≤ Z := centralizer_derived Q hQ
  have hPc : P ≤ centralizer (D : Set G) :=
    (caseFour_frattini_le_center_centralizer e h).trans ((centerIn_eq D).le.trans inf_le_right)
  have hZQ : Z ≤ Q := map_subtype_le _
  have hZcQ : Z ≤ centralizer (Q : Set G) :=
    (centerIn_eq Q).le.trans inf_le_right
  have hZc : Z ≤ centralizer (D : Set G) := hZcQ.trans (centralizer_le inf_le_left)
  let : IsMulCommutative Z := ⟨⟨fun x y => Subtype.ext
    ((hZcQ x.property) y (hZQ y.property)).symm⟩⟩
  let : CommGroup Z := IsMulCommutative.instCommGroup
  let q := QuotientGroup.mk' (U.subgroupOf Z)
  obtain ⟨hn,hzero⟩ := section_pairings_vanish e h.2.2.2.2.2.2.2.1
  let := hn
  obtain ⟨b,hb⟩ := exists_section_commutator_pairing D P Z hDD hZc hPc q
  have hb0 : b = 1 := hzero b (by
    intro k x x' y y' hx hy
    rw [hb, hb]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change ⁅(x' : G),(y' : G)⁆ / ⁅(x : G),(y : G)⁆ ∈ U
    rw [hx, hy, ← conjugate_commutatorElement]
    rw [div_eq_mul_inv, ← commutatorElement_def]
    rw [show U = ⁅K,Z⁆ from commutator_comm Z K]
    exact commutator_mem_commutator k.property
      (hDD (commutator_mem_commutator x.property y.property)))
  apply commutator_le.mpr
  intro x hx y hy
  let x' : D := ⟨x,hx⟩
  let y' : D := ⟨y,hy⟩
  have hh := congrArg (fun b : (D ⧸ P.subgroupOf D) →*
      ((D ⧸ P.subgroupOf D) →* (Z ⧸ U.subgroupOf Z)) =>
    b (QuotientGroup.mk' _ x') (QuotientGroup.mk' _ y')) hb0
  rw [hb] at hh
  change q ⟨⁅x,y⁆, hDD (commutator_mem_commutator hx hy)⟩ = 1 at hh
  exact (QuotientGroup.eq_one_iff (N := U.subgroupOf Z)
    ⟨⁅x,y⁆, hDD (commutator_mem_commutator hx hy)⟩).mp hh

variable {R S : Subgroup G} {κ : CFSG.Quasithin.GroupClass}

/-- The second clause of the parent's control predicate follows from the
genuine fourth alternative, without any additional structural premise. -/
theorem caseFour_centralizer_derived_inf_fixed_eq_bot
    (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e) :
    let Q := msQ K R
    let D := Q ⊓ centralizer (frattiniIn Q : Set G)
    ⁅D,D⁆ ⊓ (Q ⊓ centralizer (K : Set G)) = ⊥ := by
  apply le_bot_iff.mp
  exact (inf_le_inf_right _ (caseFour_centralizer_derived_le_moved_center hMS e h)).trans_eq
    ((inf_comm _ _).trans h.2.2.2.2.1)

/-- Only the center containment remains in the structural control contract. -/
theorem caseFour_control_iff_center_le
    (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e) :
    FrattiniCentralizerControl (msQ K R) (msQ K R ⊓ centralizer (K : Set G)) ↔
      sCenter (msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G)) ≤
        frattiniIn (msQ K R) :=
  ⟨fun hD => hD.1, fun hz => ⟨hz, caseFour_centralizer_derived_inf_fixed_eq_bot hMS e h⟩⟩

/-- The proposed stronger center equality is equivalent to the remaining
containment, since Φ(Q) is already central in D. -/
theorem caseFour_control_iff_center_eq
    (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e) :
    FrattiniCentralizerControl (msQ K R) (msQ K R ⊓ centralizer (K : Set G)) ↔
      sCenter (msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G)) =
        frattiniIn (msQ K R) := by
  rw [caseFour_control_iff_center_le hMS e h]
  exact ⟨fun hz => le_antisymm hz (caseFour_frattini_le_center_centralizer e h), Eq.le⟩

/-- Apply the derived-subgroup theorem to the published quotient consumer.
The center equality and the independent large-commutator input remain explicit. -/
theorem caseFour_quotient_control_of_center {H : Type*} [_root_.Group H]
    (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e)
    (f : K →* H) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hcard : Nat.card f.ker ∣ 2)
    (hN : f.ker.map K.subtype ≤ sCenter (K ⊔ R))
    (hZ : sCenter (msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G)) ≤
      frattiniIn (msQ K R))
    (hPhi : FrattiniCommutatorLarge (msQ K R)) :
    ⁅(sCenter (pCore 2 H)).comap f, (⊤ : Subgroup K)⁆ ≤ sCenter (pCore 2 K) ∧
    ⁅(sCenter (pCore 2 H)).comap f, (⊤ : Subgroup K)⁆ =
      ⁅sCenter (pCore 2 K), (⊤ : Subgroup K)⁆ :=
  caseFour_quotient_control_of_structure
    (msPair_core_hypotheses hMS).1 (msPair_core_hypotheses hMS).2 e h
    f hf hk hcard hN ((caseFour_control_iff_center_le hMS e h).mpr hZ) hPhi

open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction

/-- The literal checked-map application now needs only the remaining center
containment and the separately owned Frattini pairing theorem. -/
theorem caseFour_checked_commutator_of_center
    (T : Subgroup G) (v : G) (hK : K ≤ Gv v) (hv : v ^ 2 = 1)
    (hMS : LinearThreeMSPair κ K (Tv T v) 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K (Tv T v) S e)
    (hZ : sCenter (msQ K (Tv T v) ⊓
      centralizer (frattiniIn (msQ K (Tv T v)) : Set G)) ≤ frattiniIn (msQ K (Tv T v)))
    (hPhi : FrattiniCommutatorLarge (msQ K (Tv T v))) :
    ⁅sourceZ0 K v hK,K⁆ = sourceU K :=
  caseFour_checked_commutator_of_structure T v hK hv hMS e h
    ((caseFour_control_iff_center_le hMS e h).mpr hZ) hPhi

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer
