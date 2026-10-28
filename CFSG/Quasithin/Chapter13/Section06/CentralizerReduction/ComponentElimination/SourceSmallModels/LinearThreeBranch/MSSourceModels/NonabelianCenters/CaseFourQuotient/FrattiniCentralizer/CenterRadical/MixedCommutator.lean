module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.CenterRadical
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Linear

/-!
# Mixed commutators and elementary Frattini subgroup in the fourth MS case

Write Q = msQ K R, Z = Z(Q), P = Φ(Q), and D = C_Q(P).
The genuine MS core lies in O₂(K), which acts trivially on D/P and P/Z.
Thus [D,Q] ≤ P and [P,Q] ≤ Z. Together with [D,D] ≤ [Z,K] ≤ Z,
these inclusions make the group commutator descend to the literal pairing
D/P × Q/D → P/Z. Its conjugation invariance retains the output representative
and the common actor. The mixed-pairing theorem makes it zero, so [D,Q] ≤ Z.
The elementary-center square reduction then gives squares(D) ⊆ Z.

The source decomposition Z = C ⊕ U makes Z elementary, and P ≤ Z(D)
makes P abelian. Consequently squaring descends to a homomorphism P/Z → Z.
Modulo U = [Z,K] its target has trivial action; transvections show that this
invariant homomorphism from the dual natural module is zero. The remaining
map has image in the actual natural U, where the covector-stabilizer theorem
makes it zero too. The graph/dot-product equivalence compares the two dual
coordinate conventions without changing the actor. Hence P is elementary.

These deductions require neither nonabelianness of D nor elementary lifts.
They supply the square and exponent inputs for the parent's radical argument.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, C.1.34(4),
printed pp.136–137 (PDF147–148); Meierfrankenfeld–Stellmacher (1993),
Lemma 4.5, printed pp.895–900 (PDF72–77).
-/

public section

open Subgroup Matrix Representation BinaryLinearThree
open scoped commutatorElement
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.CenterRadical

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.CenterRadical.MixedCommutator

local notation "sCenter" => CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
variable {G : Type*} [_root_.Group G]

private theorem core_commutator_section {K P Z : Subgroup G}
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) BinaryLinearThree.Group V)
    (h : HasSectionModel K P Z (linearThreeActor e) ρ) :
    ⁅K.pCoreIn 2,P⁆ ≤ Z := by
  obtain ⟨_, hKP, _, hn, f, he⟩ := h
  let := hn
  apply commutator_le.mpr
  intro x hx y hy
  obtain ⟨k,hk,rfl⟩ := hx
  let y' := P.normalizerMonoidHom ⟨k,hKP k.property⟩ ⟨y,hy⟩
  have ha : linearThreeActor e k = 1 := by
    change k ∈ (linearThreeActor e).ker
    rwa [linearThreeActor_kernel]
  have hh : f (QuotientGroup.mk' _ y') = f (QuotientGroup.mk' _ ⟨y,hy⟩) := by
    apply Multiplicative.toAdd.injective
    simpa only [ha, map_one, Module.End.one_apply] using he k ⟨y,hy⟩ y' rfl
  have hd := QuotientGroup.eq_iff_div_mem.mp (f.injective hh)
  change (k : G) * y * (k : G)⁻¹ / y ∈ Z at hd
  simpa only [div_eq_mul_inv, commutatorElement_def, Subgroup.coe_subtype] using hd

private theorem exists_mixed_pairing (D Q P Z : Subgroup G)
    [(P.subgroupOf D).Normal] [(D.subgroupOf Q).Normal] [(Z.subgroupOf P).Normal]
    [IsMulCommutative (P ⧸ Z.subgroupOf P)]
    (hDQ : D ≤ Q) (hP : Q ≤ normalizer P)
    (hDP : ⁅D,Q⁆ ≤ P) (hPZ : ⁅Q,P⁆ ≤ Z) (hDD : ⁅D,D⁆ ≤ Z) :
    ∃ b : (D ⧸ P.subgroupOf D) → (Q ⧸ D.subgroupOf Q) → (P ⧸ Z.subgroupOf P),
      (∀ x y z, b (x*y) z = b x z * b y z) ∧
      (∀ x y z, b x (y*z) = b x y * b x z) ∧
      (∀ x : D, ∀ y : Q, b (QuotientGroup.mk' _ x) (QuotientGroup.mk' _ y) =
        QuotientGroup.mk' _ ⟨⁅(x : G),(y : G)⁆,
          hDP (commutator_mem_commutator x.property y.property)⟩) := by
  let : CommGroup (P ⧸ Z.subgroupOf P) := IsMulCommutative.instCommGroup
  let q := QuotientGroup.mk' (Z.subgroupOf P)
  let c (x : D) (y : Q) : P :=
    ⟨⁅(x : G),(y : G)⁆, hDP (commutator_mem_commutator x.property y.property)⟩
  let act (x : Q) := P.normalizerMonoidHom ⟨x,hP x.property⟩
  have hact (x : Q) (z : P) : q (act x z) = q z := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (x : G) * z * (x : G)⁻¹ / z ∈ Z
    exact hPZ (by simpa only [div_eq_mul_inv, commutatorElement_def] using
      commutator_mem_commutator x.property z.property)
  have hr (x : D) (y z : Q) : q (c x (y*z)) = q (c x y) * q (c x z) := by
    have he : c x (y*z) = c x y * act y (c x z) := by
      apply Subtype.ext
      change ⁅(x : G), (y : G) * z⁆ =
        ⁅(x : G), (y : G)⁆ * ((y : G) * ⁅(x : G), (z : G)⁆ * (y : G)⁻¹)
      simpa only [mul_assoc] using
        commutatorElement_mul_right_eq_mul_conj (x : G) (y : G) (z : G)
    rw [he, map_mul, hact]
  have hl (x y : D) (z : Q) : q (c (x*y) z) = q (c x z) * q (c y z) := by
    have he : c (x*y) z = act ⟨x,hDQ x.property⟩ (c y z) * c x z := by
      apply Subtype.ext
      exact commutatorElement_mul_left_eq_conj_mul _ _ _
    rw [he, map_mul, hact, mul_comm]
  have hp (x : D) (y : Q) (hx : (x : G) ∈ P) : q (c x y) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact (show ⁅P,Q⁆ ≤ Z by rwa [commutator_comm])
      (commutator_mem_commutator hx y.property)
  have hd (x : D) (y : Q) (hy : (y : G) ∈ D) : q (c x y) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact hDD (commutator_mem_commutator x.property hy)
  let r (x : D) : Q →* (P ⧸ Z.subgroupOf P) := {
    toFun y := q (c x y)
    map_one' := hd x 1 D.one_mem
    map_mul' := hr x }
  let t (x : D) : (Q ⧸ D.subgroupOf Q) →* (P ⧸ Z.subgroupOf P) :=
    QuotientGroup.lift (D.subgroupOf Q) (r x) (by
      intro y hy
      exact hd x y hy)
  let s : D →* ((Q ⧸ D.subgroupOf Q) →* (P ⧸ Z.subgroupOf P)) := {
    toFun := t
    map_one' := by
      apply MonoidHom.ext
      intro y
      obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (D.subgroupOf Q) y
      exact hp 1 y P.one_mem
    map_mul' x y := by
      apply MonoidHom.ext
      intro z
      obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective (D.subgroupOf Q) z
      exact hl x y z }
  let b := QuotientGroup.lift (P.subgroupOf D) s (by
    intro x hx
    apply MonoidHom.ext
    intro y
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (D.subgroupOf Q) y
    exact hp x y hx)
  exact ⟨fun x y => b x y, fun x y z => congrArg (fun f => f z) (b.map_mul x y),
    fun x y z => (b x).map_mul y z, fun _ _ => rfl⟩

variable [Finite G] {K R S : Subgroup G} {κ : CFSG.Quasithin.GroupClass}

/-- The genuine core and the three section actions make the mixed commutator central. -/
theorem caseFour_mixed_commutator_le_center
    (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e) :
    ⁅msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G), msQ K R⁆ ≤
      sCenter (msQ K R) := by
  let Q := msQ K R
  let Z := sCenter Q
  let P := frattiniIn Q
  let D := Q ⊓ centralizer (P : Set G)
  have hQcore : Q ≤ K.pCoreIn 2 := by
    dsimp [Q]
    rw [msQ_eq_ambient_blockU K R (msPair_core_hypotheses hMS).1
      (msPair_core_hypotheses hMS).2]
    exact map_mono CFSG.Quasithin.ChapterC.blockU_le_core
  have hQK : Q ≤ K := hQcore.trans (map_subtype_le _)
  have hPQ : ⁅Q,P⁆ ≤ Z :=
    (commutator_mono hQcore le_rfl).trans
      (core_commutator_section e W.dual h.2.2.2.2.2.2.1)
  have hDQ : ⁅D,Q⁆ ≤ P := by
    rw [commutator_comm]
    exact (commutator_mono hQcore le_rfl).trans
      (core_commutator_section e (W.dual.prod W.dual) h.2.2.2.2.2.2.2.1)
  have hDD : ⁅D,D⁆ ≤ Z :=
    (caseFour_centralizer_derived_le_moved_center hMS e h).trans
      (le_sup_right.trans_eq h.2.2.2.1.symm)
  obtain ⟨hnD,hnQ,hnP,hzero⟩ := caseFour_mixed_pairings_vanish e h
  let := hnD
  let := hnQ
  let := hnP
  obtain ⟨_,hKP,_,_,fP,_⟩ := h.2.2.2.2.2.2.1
  let : IsMulCommutative (P ⧸ Z.subgroupOf P) := ⟨⟨fun x y =>
    fP.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
  obtain ⟨b,hm₁,hm₂,hb⟩ := exists_mixed_pairing D Q P Z inf_le_left
    (hQK.trans hKP) hDQ hPQ hDD
  have hb0 := hzero b hm₁ hm₂ (by
    intro k x x' y y' t t' hx hy ht hh
    rw [hb] at hh ⊢
    have hm := QuotientGroup.eq_iff_div_mem.mp hh
    apply QuotientGroup.eq_iff_div_mem.mpr
    change ⁅(x' : G),(y' : G)⁆ / (t' : G) ∈ Z
    rw [hx, hy, ht, ← conjugate_commutatorElement]
    have hzK : K ≤ normalizer Z := h.2.2.2.2.2.2.1.2.2.1
    have hh := (mem_normalizer_iff.mp (hzK k.property)
      (⁅(x : G),(y : G)⁆ / (t : G))).mp hm
    simpa only [div_eq_mul_inv, _root_.mul_inv_rev, inv_inv, mul_assoc,
      inv_mul_cancel_left] using hh)
  apply commutator_le.mpr
  intro x hx y hy
  have hh := hb0 (QuotientGroup.mk' _ ⟨x,hx⟩) (QuotientGroup.mk' _ ⟨y,hy⟩)
  rw [hb] at hh
  exact (QuotientGroup.eq_one_iff (N := Z.subgroupOf P)
    ⟨⁅x,y⁆, hDQ (commutator_mem_commutator hx hy)⟩).mp hh

/-- Application of the elementary-center square reduction to the actual centralizer. -/
theorem caseFour_centralizer_square_mem_center
    (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e) :
    ∀ x ∈ msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G),
      x ^ 2 ∈ sCenter (msQ K R) :=
  caseFour_centralizer_square_mem_center_of_mixed e h
    (caseFour_mixed_commutator_le_center hMS e h)

private abbrev DV := Module.Dual (ZMod 2) Vector

private theorem invariant_dual_hom_zero {E : Type*} [AddCommGroup E]
    (b : DV →+ E) (hb : ∀ g x, b (W.dual g x) = b x) : b = 0 := by
  let f := AutomorphismAction.graphNaturalDual.toLinearEquiv.toAddEquiv
  let c := b.comp f.toAddMonoidHom
  have hc (g : BinaryLinearThree.Group) (x : Vector) : c (W g x) = c x := by
    have he := LinearMap.congr_fun
      (AutomorphismAction.graphNaturalDual.isIntertwining' (AutomorphismAction.graph g)) x
    change f (W (AutomorphismAction.graph (AutomorphismAction.graph g)) x) =
      W.dual (AutomorphismAction.graph g) (f x) at he
    rw [AutomorphismAction.graph_graph] at he
    change b (f (W g x)) = b (f x)
    rw [he, hb]
  have hbase (i : Fin 3) : c (Pi.single i 1) = 0 := by
    obtain ⟨j,hji⟩ : ∃ j : Fin 3, j ≠ i := by fin_cases i <;> decide
    let g : BinaryLinearThree.Group := SpecialLinearGroup.transvection hji.symm (1 : ZMod 2)
    have he : W g (Pi.single j 1) = Pi.single j 1 + Pi.single i 1 := by
      change g.val *ᵥ (Pi.single j 1) = _
      simp only [g, SpecialLinearGroup.transvection_coe, Matrix.add_mulVec,
        Matrix.one_mulVec, Matrix.single_mulVec_eq, Pi.single_eq_same,
        mul_one, one_smul]
    have hh := hc g (Pi.single j 1)
    rw [he, map_add] at hh
    exact add_left_cancel (hh.trans (add_zero _).symm)
  have hc0 (x : Vector) : c x = 0 := by
    conv_lhs => rw [show x = ∑ i : Fin 3, Pi.single i (x i) from
      (Finset.univ_sum_single x).symm]
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (x i) with hi | hi
    · simp [hi]
    · rw [hi, hbase]
  apply AddMonoidHom.ext
  intro x
  obtain ⟨x,rfl⟩ := f.surjective x
  exact hc0 x

private theorem dual_natural_map_zero (f : DV → Vector)
    (hf : ∀ g x, f (W.dual g x) = W g (f x)) : ∀ x, f x = 0 := by
  let E := AutomorphismAction.graphNaturalDual.toLinearEquiv
  have he (g : BinaryLinearThree.Group) (x : Vector) :
      E (CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Linear.dual g x) =
        W.dual g (E x) :=
    LinearMap.congr_fun (AutomorphismAction.graphNaturalDual.isIntertwining' g) x
  intro x
  obtain ⟨x,rfl⟩ := E.surjective x
  apply CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Linear.equivariantDualMap_zero
    (fun y => f (E y)) _ x
  intro g y
  rw [he, hf]
  rfl

omit [Finite G] in
private theorem dual_center_hom_zero {Z : Subgroup G}
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    [IsMulCommutative Z]
    (hU : HasSectionModel K ⁅Z,K⁆ ⊥ (linearThreeActor e) W)
    (F : Multiplicative DV →* Z)
    (hF : ∀ (k : K) (v : DV),
      (F (Multiplicative.ofAdd (W.dual (linearThreeActor e k) v)) : G) =
        k * (F (Multiplicative.ofAdd v) : G) * (k : G)⁻¹) :
    ∀ v, F v = 1 := by
  let : CommGroup Z := IsMulCommutative.instCommGroup
  let U := ⁅Z,K⁆
  let q := QuotientGroup.mk' (U.subgroupOf Z)
  let b : DV →+ Additive (Z ⧸ U.subgroupOf Z) := (q.comp F).toAdditive
  have hb : b = 0 := invariant_dual_hom_zero b (by
    intro g v
    obtain ⟨k,rfl⟩ := linearThreeActor_surjective e g
    change q (F (Multiplicative.ofAdd (W.dual (linearThreeActor e k) v))) =
      q (F (Multiplicative.ofAdd v))
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (F (Multiplicative.ofAdd (W.dual (linearThreeActor e k) v)) : G) /
      (F (Multiplicative.ofAdd v) : G) ∈ U
    rw [hF, div_eq_mul_inv, ← commutatorElement_def]
    rw [show U = ⁅K,Z⁆ from commutator_comm Z K]
    exact commutator_mem_commutator k.property (F (Multiplicative.ofAdd v)).property)
  have hmem (v : Multiplicative DV) : (F v : G) ∈ U := by
    have hh := congrArg (fun b : DV →+ Additive (Z ⧸ U.subgroupOf Z) => b v.toAdd) hb
    exact (QuotientGroup.eq_one_iff (N := U.subgroupOf Z) (F v)).mp hh
  let FU : Multiplicative DV →* U := {
    toFun v := ⟨F v, hmem v⟩
    map_one' := Subtype.ext (congrArg (fun z : Z => (z : G)) F.map_one)
    map_mul' v w := Subtype.ext (congrArg (fun z : Z => (z : G)) (F.map_mul v w)) }
  obtain ⟨_,_,_,hn,f,hf⟩ := hU
  let := hn
  let u := f.toMonoidHom.comp (QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf U))
  have hu : Function.Injective u := by
    apply f.injective.comp
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [QuotientGroup.ker_mk', bot_subgroupOf]
  have hz := dual_natural_map_zero (fun v => (u (FU (Multiplicative.ofAdd v))).toAdd) (by
    intro g v
    obtain ⟨k,rfl⟩ := linearThreeActor_surjective e g
    exact hf k (FU (Multiplicative.ofAdd v))
      (FU (Multiplicative.ofAdd (W.dual (linearThreeActor e k) v))) (hF k v))
  intro v
  have hh : FU v = 1 := hu ((hz v.toAdd).trans u.map_one.symm)
  exact Subtype.ext (congrArg (fun z : U => (z : G)) hh)

/-- The square map on the actual dual Frattini section vanishes in the center. -/
theorem caseFour_frattini_elementary
    (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e) :
    IsElementaryAbelian 2 (frattiniIn (msQ K R)) := by
  let Q := msQ K R
  let Z := sCenter Q
  let P := frattiniIn Q
  let D := Q ⊓ centralizer (P : Set G)
  have hPD : P ≤ sCenter D := caseFour_frattini_le_center_centralizer e h
  have hPcomm (x y : P) : Commute (x : G) (y : G) :=
    ((centerIn_eq D).le (hPD y.property)).2 x ((centerIn_eq D).le (hPD x.property)).1
  let : IsMulCommutative P := ⟨⟨fun x y => Subtype.ext (hPcomm x y)⟩⟩
  let : CommGroup P := IsMulCommutative.instCommGroup
  let : IsElementaryAbelian 2 Z := caseFour_center_elementary e h
  let : CommGroup Z := IsMulCommutative.instCommGroup
  have hs (x : P) : (x : G)^2 ∈ Z :=
    caseFour_centralizer_square_mem_center hMS e h x ((centerIn_eq D).le (hPD x.property)).1
  let s : P →* Z := {
    toFun x := ⟨(x : G)^2, hs x⟩
    map_one' := Subtype.ext (one_pow 2)
    map_mul' x y := Subtype.ext ((hPcomm x y).mul_pow 2) }
  obtain ⟨_,hKP,_,hn,f,hf⟩ := h.2.2.2.2.2.2.1
  let := hn
  let sq : (P ⧸ Z.subgroupOf P) →* Z := QuotientGroup.lift (Z.subgroupOf P) s (by
    intro x hx
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (x : G) (show (x : G) ∈ Z from hx))
  let F := sq.comp f.symm.toMonoidHom
  have hF (k : K) (v : DV) :
      (F (Multiplicative.ofAdd (W.dual (linearThreeActor e k) v)) : G) =
        k * (F (Multiplicative.ofAdd v) : G) * (k : G)⁻¹ := by
    obtain ⟨x,hx⟩ := (f.surjective.comp (QuotientGroup.mk'_surjective _))
      (Multiplicative.ofAdd v)
    change f (QuotientGroup.mk' _ x) = Multiplicative.ofAdd v at hx
    let x' := P.normalizerMonoidHom ⟨k,hKP k.property⟩ x
    have hv : (f (QuotientGroup.mk' _ x)).toAdd = v := congrArg Multiplicative.toAdd hx
    have hx' : f (QuotientGroup.mk' _ x') =
        Multiplicative.ofAdd (W.dual (linearThreeActor e k) v) := by
      apply Multiplicative.toAdd.injective
      rw [hf k x x' rfl, hv]
      rfl
    change (sq (f.symm (Multiplicative.ofAdd (W.dual (linearThreeActor e k) v))) : G) =
      k * (sq (f.symm (Multiplicative.ofAdd v)) : G) * (k : G)⁻¹
    rw [← hx', ← hx, f.symm_apply_apply, f.symm_apply_apply]
    change ((k : G) * (x : G) * (k : G)⁻¹)^2 = k * (x : G)^2 * (k : G)⁻¹
    exact conj_pow
  have hz := dual_center_hom_zero e h.2.2.2.2.2.1 F hF
  refine {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  have hh := hz (f (QuotientGroup.mk' _ x))
  change sq (f.symm (f (QuotientGroup.mk' _ x))) = 1 at hh
  rw [f.symm_apply_apply] at hh
  exact Subtype.ext (congrArg (fun z : Z => (z : G)) hh)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.CenterRadical.MixedCommutator
