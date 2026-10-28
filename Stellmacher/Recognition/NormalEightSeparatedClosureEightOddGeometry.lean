module

public import Stellmacher.Recognition.NormalEightSeparatedClosureEightOddActionData
public import Theory.GroupTheory.IndexTwoConjugateCentralizer
public import Theory.GroupAction.SixOnElementaryEightMovingPlane
public import Theory.GroupTheory.SylowKernelInvertedOddLift

/-!
# Index geometry for the odd action on an order-eight closure

The image of the local Sylow subgroup in the order-six automizer has order
two. Its kernel is the closure centralizer inside the involution centralizer,
so the latter relative index is two. An outside conjugate of the elementary
eight then supplies an involution normalizing the closure centralizer with
fixed subgroup of index two.

These are the Sylow and conjugate-centralizer steps in Janko–Thompson,
Math. Z. 113 (1970), Lemma 3.1, printed p.388. The moving plane and lifted
odd actor complete the structure `OddActionData`. The actor is lifted through
the normalizer of the Sylow subgroup of the action kernel, extracting the full
odd part so that its order-three image survives. Conjugation then transports
the inversion relation and moving-plane properties to the closure centralizer.
Source: refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf.
-/

namespace Stellmacher.Recognition.NormalEightSeparatedClosureEight
open Subgroup NormalEightSeparatedCentralizers
variable {G : Type*} [Group G] [Finite G]

/-- The order-six closure action has an order-two Sylow image. Its kernel
is the intrinsic closure centralizer. -/
public theorem closureCentralizer_relIndex_of_action_card_six {S : Sylow 2 G} {W : Subgroup S} {i : S} (d : CentralizerSetup S W i)
    (hact6 : Nat.card (MulAut.conjNormal (H := d.closure) : d.H →* MulAut d.closure).range = 6) :
    (closureCentralizer d).relIndex (centralizer ({i} : Set S)) = 2 := by
  let C := centralizer ({i} : Set S)
  let P := d.T.subtype d.sylow_le
  let α : d.H →* MulAut d.closure := MulAut.conjNormal
  let j : C →* d.H := {
    toFun := fun c => ⟨⟨c.val, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp c.property))⟩,
      d.sylow_le (by rw [d.sylow_eq]; exact c.val.property)⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let f : C →* MulAut d.closure := α.comp j
  have hj : j.range = P := by
    ext a
    constructor
    · rintro ⟨c, rfl⟩
      change (j c).val ∈ (d.T : Subgroup _)
      rw [d.sylow_eq]
      exact c.val.property
    · intro ha
      have haS : (a : G) ∈ (S : Subgroup G) := by
        change a.val ∈ (d.T : Subgroup _) at ha
        rwa [d.sylow_eq] at ha
      refine ⟨⟨⟨a, haS⟩, mem_centralizer_singleton_iff.mpr ?_⟩, rfl⟩
      exact Subtype.ext (mem_centralizer_singleton_iff.mp a.val.property)
  let Q := P.mapSurjective α.rangeRestrict_surjective
  have hQ : Nat.card Q = 2 := by
    rw [Q.card_eq_multiplicity, hact6]
    decide +kernel
  have hfcard : Nat.card f.range = 2 := by
    have hfr : f.range = (P : Subgroup d.H).map α := by
      rw [MonoidHom.range_comp, hj]
    rw [hfr]
    have hmap : (Q : Subgroup α.range).map α.range.subtype = (P : Subgroup d.H).map α := by
      rw [Sylow.coe_mapSurjective, map_map]
      rfl
    rw [← hmap, card_map_of_injective α.range.subtype_injective]
    exact hQ
  have hker : f.ker = (closureCentralizer d).subgroupOf C := by
    ext c
    rw [MonoidHom.mem_ker]
    constructor
    · intro hc v hv
      obtain ⟨vC, ⟨vH, hvH, rfl⟩, he⟩ := hv
      have hh := congrArg (fun a : MulAut d.closure => (a ⟨vH,hvH⟩ : d.H)) hc
      change j c * vH * (j c)⁻¹ = vH at hh
      have heq := congrArg (fun a : d.H => ((a : centralizer ({(i : G)} : Set G)) : G))
        (mul_inv_eq_iff_eq_mul.mp hh)
      apply Subtype.ext
      change (v : G) * (c : S) = (c : S) * (v : G)
      change (vH : G) = (v : G) at he
      change (c : S) * (vH : G) = (vH : G) * (c : S) at heq
      simpa only [he] using heq.symm
    · intro hc
      apply MulEquiv.ext
      intro v
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      change (c : S) * (v : G) * (c : S)⁻¹ = (v : G)
      apply mul_inv_eq_iff_eq_mul.mpr
      have hvS : (v : G) ∈ (S : Subgroup G) :=
        closureImage_le_sylow d (mem_map_of_mem _ (mem_map_of_mem _ v.property))
      have hv : (⟨(v : G), hvS⟩ : S) ∈ closureInSylow d :=
        mem_map_of_mem _ (mem_map_of_mem _ v.property)
      exact congrArg Subtype.val (hc _ hv).symm
  rw [relIndex, ← hker, index_ker, hfcard]

/-- The outside-conjugate involution has fixed subgroup of index two in the
closure centralizer, as well as the required order and containment. -/
public theorem exists_outside_fixed_index_two_of_action_card_six
    (S : Sylow 2 G) (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (z : S) (hzW : z ∈ W) (hzC : z ∈ center S)
    (hz : orderOf z = 2) (i : S) (hiW : i ∈ W) (hi : orderOf i = 2)
    (hiC : i ∉ center S)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (d : CentralizerSetup S W i) (hc : Nat.card d.closure = 8)
    (hact6 : Nat.card (MulAut.conjNormal (H := d.closure) :
      d.H →* MulAut d.closure).range = 6) :
    ∃ t x : S, t ∉ centralizer ({i} : Set S) ∧
      x ∈ (closureInSylow d).map (MulAut.conj t).toMonoidHom ∧
      orderOf x = 2 ∧ x ∈ centralizer ({i} : Set S) ∧
      x ∉ closureCentralizer d ∧
      ∃ hn : x ∈ normalizer (closureCentralizer d : Set S),
        (MulAut.fixedSubgroup
          ((closureCentralizer d).normalizerMonoidHom ⟨x, hn⟩)).index = 2 := by
  classical
  let C := centralizer ({i} : Set S)
  have hex : ∃ t : S, t ∉ C := by
    by_contra! h
    apply hiC
    apply mem_center_iff.mpr
    intro t
    exact mem_centralizer_singleton_iff.mp (h t)
  obtain ⟨t, ht⟩ := hex
  obtain ⟨x, hx, hx2, hxC, hxT⟩ := exists_outside_conjugate_involution
    S W hW z hzW hzC hz i hiW hi hiC hno d hc t ht
  refine ⟨t, x, ht, hx, hx2, hxC, hxT, ?_⟩
  let : C.Normal := normal_of_index_eq_two
    (centralizer_involution_index S W hW z hzW hzC hz i hiW hi hiC)
  let : IsElementaryAbelian 2 (closureInSylow d) := closureInSylow_elementary d
  have hTC : closureCentralizer d ≤ C := centralizer_le
    (Set.singleton_subset_iff.mpr (four_le_closureInSylow hiW d hiW))
  exact fixed_index_two_of_mem_conjugate (closureInSylow d) C
    (le_centralizer _) hTC (closureCentralizer_relIndex_of_action_card_six d hact6)
    t x hx hxC hxT

open scoped IsMulCommutative

/-- An order-six closure action supplies the moving plane, the outside
involution, and an inverted odd actor on the closure centralizer. The trivial
two-core of the actual action removes any need for a separate noncommutativity
hypothesis. -/
public theorem nonempty_oddActionData_of_action_card_six
    (S : Sylow 2 G) (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (z : S) (hzW : z ∈ W) (hzC : z ∈ center S)
    (hz : orderOf z = 2)
    (i : S) (hiW : i ∈ W) (hi : orderOf i = 2)
    (hiC : i ∉ center S)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (d : CentralizerSetup S W i) (hc : Nat.card d.closure = 8)
    (hact6 : Nat.card (MulAut.conjNormal (H := d.closure) : d.H →* MulAut d.closure).range = 6) :
    Nonempty (OddActionData d z) := by
  classical
  let C : Subgroup S := centralizer ({i} : Set S)
  let T : Subgroup S := closureCentralizer d
  let E : Subgroup S := closureInSylow d
  let α : d.H →* MulAut d.closure := MulAut.conjNormal
  let P : Sylow 2 d.H := d.T.subtype d.sylow_le
  have hidx := closureCentralizer_relIndex_of_action_card_six d hact6
  obtain ⟨mover, outside, hmover, houtmap, hout2, houtC, houtT, houtN, houtFix⟩ :=
    exists_outside_fixed_index_two_of_action_card_six S W hW z hzW hzC hz i hiW hi hiC hno d hc hact6
  have hQcard : Nat.card α.range = 6 := hact6
  have hcore : pCore 2 α.range = ⊥ := closure_action_twoCore_eq_bot d
  let w : d.H := ⟨⟨outside, mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp houtC))⟩,
    d.sylow_le (by rw [d.sylow_eq]; exact outside.property)⟩
  have hwP : w ∈ (P : Subgroup d.H) := by
    change w.val ∈ (d.T : Subgroup _)
    rw [d.sylow_eq]
    exact outside.property
  have houtPow : outside ^ 2 = 1 := (orderOf_eq_iff (by decide)).mp hout2 |>.1
  have hw2 : w ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun q : S => (q : G)) houtPow
  have hwα : α w ≠ 1 := by
    intro hh
    apply houtT
    change outside ∈ centralizer (E : Set S)
    intro v hv
    obtain ⟨vC, ⟨vH, hvH, rfl⟩, he⟩ := hv
    have hhv := congrArg (fun a : MulAut d.closure => (a ⟨vH, hvH⟩ : d.H)) hh
    change w * vH * w⁻¹ = vH at hhv
    have heq := congrArg (fun a : d.H => ((a : centralizer ({(i : G)} : Set G)) : G))
      (mul_inv_eq_iff_eq_mul.mp hhv)
    apply Subtype.ext
    change (v : G) * (outside : G) = (outside : G) * (v : G)
    change (vH : G) = (v : G) at he
    simpa [he] using heq.symm
  obtain ⟨r, hrN, hrOdd, hr3, hrInv⟩ :=
    Sylow.exists_inverted_odd_normalizing_inf_ker_of_card_six P α.rangeRestrict α.rangeRestrict_surjective
      hQcard hcore w hwP hw2 (by
        intro hh
        apply hwα
        exact congrArg Subtype.val hh)
  let K : Subgroup d.H := (P : Subgroup d.H) ⊓ α.rangeRestrict.ker
  have hrK : r ∈ normalizer (K : Set d.H) := hrN
  have hker_to_T : ∀ q : K, (⟨(q : G), by
      have hqT : (q : d.H) ∈ (P : Subgroup d.H) := q.property.1
      change (q : d.H).val ∈ (d.T : Subgroup _) at hqT
      have hqC : (q : d.H).val ∈ (S : Subgroup G).subgroupOf
          (centralizer ({(i : G)} : Set G)) := by
        rw [← d.sylow_eq]
        exact hqT
      exact hqC⟩ : S) ∈ T := by
    intro q
    change (⟨(q : G), _⟩ : S) ∈ centralizer (E : Set S)
    intro v hv
    obtain ⟨vC, ⟨vH, hvH, rfl⟩, he⟩ := hv
    have hqker : α.rangeRestrict (q : d.H) = 1 := q.property.2
    have hhv := congrArg (fun a : MulAut d.closure => (a ⟨vH, hvH⟩ : d.H))
      (show α (q : d.H) = 1 by exact congrArg Subtype.val hqker)
    change (q : d.H) * vH * (q : d.H)⁻¹ = vH at hhv
    have heq := congrArg (fun a : d.H => ((a : centralizer ({(i : G)} : Set G)) : G))
      (mul_inv_eq_iff_eq_mul.mp hhv)
    change (vH : G) = (v : G) at he
    apply Subtype.ext
    simpa [he] using heq.symm
  let k : K →* T := {
    toFun := fun q => ⟨⟨(q : G), by
      have hqT : (q : d.H) ∈ (P : Subgroup d.H) := q.property.1
      change (q : d.H).val ∈ (d.T : Subgroup _) at hqT
      have hqC : (q : d.H).val ∈ (S : Subgroup G).subgroupOf
          (centralizer ({(i : G)} : Set G)) := by
        rw [← d.sylow_eq]
        exact hqT
      exact hqC⟩, hker_to_T q⟩
    map_one' := by rfl
    map_mul' := by intro a b; rfl }
  have hk_inj : Function.Injective k := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    simpa [k] using congrArg (fun u : T => (u : S)) hab
  have hk_surj : Function.Surjective k := by
    intro y
    have hiE : i ∈ E := four_le_closureInSylow hiW d hiW
    let yC : centralizer ({(i : G)} : Set G) := ⟨y.1, by
      exact mem_centralizer_singleton_iff.mpr
        ((congrArg Subtype.val (y.property i hiE)).symm)⟩
    let yH : d.H := ⟨yC, d.sylow_le (by rw [d.sylow_eq]; exact y.1.property)⟩
    have hyP : yH ∈ (P : Subgroup d.H) := by
      change yH.val ∈ (d.T : Subgroup _)
      rw [d.sylow_eq]
      exact y.1.property
    have hyker : α.rangeRestrict yH = 1 := by
      apply Subtype.ext
      apply MulEquiv.ext
      intro v
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      have hvE : (⟨(v : G), closureImage_le_sylow d
          (mem_map_of_mem _ (mem_map_of_mem _ v.property))⟩ : S) ∈ E :=
        mem_map_of_mem _ (mem_map_of_mem _ v.property)
      have hcomm := y.property _ hvE
      apply mul_inv_eq_iff_eq_mul.mpr
      change (y : G) * (v : G) = (v : G) * (y : G)
      exact (congrArg Subtype.val hcomm).symm
    refine ⟨⟨yH, hyP, hyker⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl
  let kEquiv : K ≃* T := MulEquiv.ofBijective k ⟨hk_inj, hk_surj⟩
  let β : MulAut K := K.normalizerMonoidHom ⟨r, hrK⟩
  let actor : MulAut T := (MulAut.congr kEquiv) β
  have hβodd : Odd (orderOf β) := by
    apply Odd.of_dvd_nat hrOdd
    simpa [β, orderOf_injective (normalizer (K : Set d.H)).subtype Subtype.coe_injective] using
      (orderOf_map_dvd K.normalizerMonoidHom ⟨r, hrK⟩)
  have hactorOdd : Odd (orderOf actor) := by
    rw [show orderOf actor = orderOf β by
      exact orderOf_injective (MulAut.congr kEquiv).toMonoidHom
        (MulAut.congr kEquiv).injective β]
    exact hβodd
  have hwK : w ∈ normalizer (K : Set d.H) := inf_normalizer_le_normalizer_inf
    ⟨le_normalizer hwP, subset_normalizer_of_normal (Set.mem_univ w)⟩
  let δK : MulAut K := K.normalizerMonoidHom ⟨w, hwK⟩
  let δT : MulAut T := T.normalizerMonoidHom ⟨outside, houtN⟩
  have hcomp : ∀ b : K, δT (kEquiv b) = kEquiv (δK b) := by
    intro b
    apply Subtype.ext
    apply Subtype.ext
    dsimp [δT, δK, kEquiv, k, w]
    rfl
  have hδeq : δT = (MulAut.congr kEquiv) δK := by
    apply MulEquiv.ext
    intro a
    obtain ⟨b, rfl⟩ := kEquiv.surjective a
    simpa only [MulAut.congr_apply, MulEquiv.trans_apply, kEquiv.symm_apply_apply] using hcomp b
  have hβδ : δK * β * δK⁻¹ = β⁻¹ := by
    have hh : (⟨w, hwK⟩ : normalizer (K : Set d.H)) * ⟨r, hrK⟩ *
        (⟨w, hwK⟩ : normalizer (K : Set d.H))⁻¹ = ⟨r, hrK⟩⁻¹ :=
      Subtype.ext hrInv
    simpa only [map_mul, map_inv] using congrArg K.normalizerMonoidHom hh
  have hδ : δT * actor * δT⁻¹ = actor⁻¹ := by
    rw [hδeq]
    change (MulAut.congr kEquiv) δK * (MulAut.congr kEquiv) β *
      ((MulAut.congr kEquiv) δK)⁻¹ = ((MulAut.congr kEquiv) β)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, hβδ, map_inv]
  -- Identify the elementary closure with its image in the original Sylow.
  let e : d.closure →* S := {
    toFun := fun v => ⟨(v : G), closureImage_le_sylow d
      (mem_map_of_mem _ (mem_map_of_mem _ v.property))⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have he_inj : Function.Injective e := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun s : S => (s : G)) h
  have he_range : e.range = E := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact mem_map_of_mem _ (mem_map_of_mem _ a.property)
    · rintro ⟨vC, ⟨vH, hvH, rfl⟩, he⟩
      exact ⟨⟨vH, hvH⟩, Subtype.ext he⟩
  have hiE : i ∈ E := four_le_closureInSylow hiW d hiW
  have hzE : z ∈ E := four_le_closureInSylow hiW d hzW
  obtain ⟨vi, hvi⟩ := (show i ∈ e.range from he_range ▸ hiE)
  obtain ⟨vz, hvz⟩ := (show z ∈ e.range from he_range ▸ hzE)
  have hvi2 : orderOf vi = 2 := by rw [← orderOf_injective e he_inj, hvi, hi]
  have hfix : ∀ q ∈ α.range, q vi = vi := by
    rintro q ⟨a, rfl⟩
    apply he_inj
    apply Subtype.ext
    change (a : G) * (vi : G) * (a : G)⁻¹ = (vi : G)
    have hvig : (vi : G) = (i : G) := congrArg Subtype.val hvi
    rw [hvig]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp a.val.property)
  let : IsElementaryAbelian 2 d.closure := d.elementary
  have har3 : orderOf (α r) = 3 := by
    exact (orderOf_injective α.range.subtype Subtype.coe_injective (α.rangeRestrict r)).trans hr3
  obtain ⟨A, hAcard, hAstable, hAfree, hAfaith, hline, _⟩ :=
    MulAut.exists_invariant_moving_plane_of_card_six hc α.range hact6 vi hvi2 hfix
      (α r) (⟨r, rfl⟩) har3
  let plane := A.map e
  have hplane_le : plane ≤ E := by rw [← he_range]; exact map_le_range e A
  let : IsElementaryAbelian 2 E := closureInSylow_elementary d
  have hET : E ≤ T := E.le_centralizer
  have hplane_normal : C ≤ normalizer (plane : Set S) := by
    apply le_normalizer_iff.mpr
    intro c hc a ha
    let cH : d.H := ⟨⟨c, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc))⟩,
      d.sylow_le (by rw [d.sylow_eq]; exact c.property)⟩
    obtain ⟨v, hv, rfl⟩ := ha
    refine ⟨α cH v, hAstable _ (⟨cH, rfl⟩) _ hv, ?_⟩
    rfl
  have hactor_coe (b : T) : (actor b : G) = (r : G) * (b : G) * (r : G)⁻¹ := by
    have hkval (u : K) : (kEquiv u : G) = (u : G) := rfl
    have hsymm : (kEquiv.symm b : G) = (b : G) := by
      rw [← hkval, kEquiv.apply_symm_apply]
    change ((MulAut.congr kEquiv) β b : G) = _
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hkval]
    change (r : G) * (kEquiv.symm b : G) * (r : G)⁻¹ = _
    rw [hsymm]
  have hactor_e (v : d.closure) :
      actor ⟨e v, hET (he_range ▸ ⟨v, rfl⟩)⟩ =
        ⟨e (α r v), hET (he_range ▸ ⟨_, rfl⟩)⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    exact hactor_coe _
  have hactor_stable : ∀ a : T, (a : S) ∈ plane → (actor a : S) ∈ plane := by
    intro a ha
    obtain ⟨v, hv, he⟩ := ha
    have haeq : a = ⟨e v, hET (he_range ▸ ⟨v, rfl⟩)⟩ := Subtype.ext he.symm
    rw [haeq, hactor_e]
    exact mem_map_of_mem e (hAstable _ (⟨r, rfl⟩) _ hv)
  have hactor_free : ∀ a : T, (a : S) ∈ plane → actor a = a → a = 1 := by
    intro a ha hfixa
    obtain ⟨v, hv, he⟩ := ha
    have haeq : a = ⟨e v, hET (he_range ▸ ⟨v, rfl⟩)⟩ := Subtype.ext he.symm
    rw [haeq, hactor_e] at hfixa
    have hvfix : α r v = v := he_inj (congrArg Subtype.val hfixa)
    have hv1 := hAfree v hv hvfix
    apply Subtype.ext
    change (a : S) = 1
    rw [← he, hv1, map_one]
  have hout_moves : ∃ a ∈ plane, ¬ Commute outside a := by
    obtain ⟨a, ha, hne⟩ := hAfaith _ (⟨w, rfl⟩) hwα
    refine ⟨e a, mem_map_of_mem e ha, ?_⟩
    intro hcomm
    apply hne
    apply he_inj
    change outside * e a * outside⁻¹ = e a
    exact mul_inv_eq_iff_eq_mul.mpr hcomm.eq
  have hiT : i ∈ T := hET hiE
  have hzT : z ∈ T := hET hzE
  have hactor_i : actor ⟨i, hiT⟩ = ⟨i, hiT⟩ := by
    have hh := hactor_e vi
    have hvfix := hfix _ (⟨r, rfl⟩)
    simpa only [hvfix, hvi] using hh
  have hactor_z : actor ⟨z, hzT⟩ ≠ ⟨z, hzT⟩ := by
    intro hzfix
    have hh := hactor_e vz
    have hvfix : α r vz = vz := by
      apply he_inj
      have hh' := congrArg Subtype.val hh
      simpa only [hvz, hzfix] using hh'.symm
    have hzline : z ∈ zpowers i := by
      have hh := mem_map_of_mem e ((hline vz).mp hvfix)
      rwa [MonoidHom.map_zpowers, hvi, hvz] at hh
    have hzoptions : z = 1 ∨ z = i := by
      have hh : ∃ n ≤ 1, i ^ n = z := by
        simpa [mem_zpowers_iff_mem_range_orderOf, hi] using hzline
      obtain ⟨n, hn, he⟩ := hh
      interval_cases n
      · left; simpa only [pow_zero] using he.symm
      · right; simpa only [pow_one] using he.symm
    rcases hzoptions with hz1 | hzi
    · simp [hz1] at hz
    · exact hiC (hzi ▸ hzC)
  exact ⟨{
    plane := plane
    plane_elementary := by
      let : IsElementaryAbelian 2 A := {
        toIsMulCommutative := inferInstance
        exponent_dvd_p :=
          (Monoid.exponent_dvd_of_monoidHom A.subtype A.subtype_injective).trans
            (IsElementaryAbelian.exponent_dvd_p 2 d.closure) }
      exact IsElementaryAbelian.map e
    plane_card := (card_map_of_injective he_inj).trans hAcard
    plane_le := hplane_le
    plane_normalized := hplane_normal
    index := hidx
    mover := mover
    mover_outside := hmover
    outside := outside
    outside_mem_conjugate := houtmap
    outside_order := hout2
    outside_not_centralizing := houtT
    outside_mem_centralizer := houtC
    outside_normalizes := houtN
    outside_fixed_index := houtFix
    outside_moves_plane := hout_moves
    actor := actor
    actor_odd := hactorOdd
    actor_plane_stable := hactor_stable
    actor_plane_free := hactor_free
    actor_inverted := hδ
    involution_mem := hiT
    central_mem := hzT
    actor_fixes_involution := hactor_i
    actor_moves_central := hactor_z }⟩

end Stellmacher.Recognition.NormalEightSeparatedClosureEight
