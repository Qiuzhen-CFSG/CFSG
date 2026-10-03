module

public import Stellmacher.Recognition.FongWreathedCoordinates
public import ABG.ChapterII.Section1.WreathedFusionFrame
public import ABG.ChapterII.Section1.WreathedUFrattiniAction
public import ABG.ChapterII.Section2.QDCharacterization
public import Mathlib.GroupTheory.Subgroup.Simple
public import Theory.GroupTheory.SpecificGroups.CyclicFourSquareAction

/-!
# The two base-normalizer fusion alternatives in the wreathed order-32 case

For every height-two presentation of a Sylow subgroup of a finite simple group,
the actual base normalizer simultaneously fuses `F², XF²` either to `EX, EJ` or
to `EXJ, E`. No orientation of the presentation is assumed.

The base has coordinates `C₄ × C₄`. Lift the Frattini-quotient action of
`A₀(x,y) = (y⁻¹, x*y⁻¹)` to the normalizer. Its faithful quotient action gives
the relations `A³ = 1` and `BABA = 1`, where conjugation by the presentation
involution is the coordinate swap `B`. Squaring factors through the Frattini
quotient, so the lift sends `(2,2)` to `(2,0)`. The finite coordinate calculation
then gives the two alternatives, both realized by the same normalizer element.

Source: P. Fong, *Some Sylow subgroups of order 32 and a characterization
of U(3,3)*, J. Algebra 6 (1967), 65–76, printed p. 70 before equation (5).
The square-map argument follows the one in `WreathedUHighInvolutions`.
-/

open scoped IsMulCommutative
open CyclicFourSquare

private def threeCycle : MulAut CyclicFourSquare where
  toFun x := (x.2⁻¹, x.1 * x.2⁻¹)
  invFun x := (x.2 * x.1⁻¹, x.1⁻¹)
  left_inv x := by ext <;> simp [mul_comm]
  right_inv x := by ext <;> simp [mul_comm]
  map_mul' x y := by ext <;> simp [mul_mul_mul_comm, add_comm]

private def swapAut : MulAut CyclicFourSquare := MulEquiv.prodComm

private theorem threeCycle_cube : threeCycle ^ 3 = 1 := by
  ext x : 1
  change threeCycle (threeCycle (threeCycle x)) = x
  revert x
  decide +kernel

private theorem swap_threeCycle : swapAut * threeCycle * swapAut * threeCycle = 1 := by
  ext x : 1
  change (threeCycle (threeCycle x).swap).swap = x
  revert x
  decide +kernel

private theorem square_kills_frattini
    {A : Type*} [Group A] [Finite A] [IsMulCommutative A]
    (hA : IsPGroup 2 A) (hk : ∀ a : A, a ^ 4 = 1) :
    frattini A ≤ (powMonoidHom 2 : A →* A).ker := by
  let : Fact (IsPGroup 2 A) := ⟨hA⟩
  rw [frattini_eq_closure_commutator_union_powers (p := 2)]
  apply (Subgroup.closure_le _).mpr
  rintro a (ha | ⟨b, rfl⟩)
  · have hc : _root_.commutator A = ⊥ := by
      rw [commutator_eq_bot_iff_center_eq_top]
      exact Subgroup.center_eq_top
    rw [hc] at ha
    have ha' : a = 1 := ha
    simp [ha']
  · change (b ^ 2) ^ 2 = 1
    rw [← pow_mul]
    exact hk b

private theorem normalizer_alternatives
    {G : Type*} [Group G] [Finite G] (U : Subgroup G)
    [IsMulCommutative U] (e : U ≃* CyclicFourSquare)
    (hU : IsPGroup 2 U)
    (hfaith : Function.Injective ((Subgroup.quotientAut (frattini U)).comp
      U.normalizerMonoidHom.range.subtype))
    (hfull : Function.Surjective ((Subgroup.quotientAut (frattini U)).comp
      U.normalizerMonoidHom))
    (hswap : (MulAut.congr e.symm) swapAut ∈ U.normalizerMonoidHom.range) :
    ∃ g : Subgroup.normalizer (U : Set G),
      let f := (MulAut.congr e) (U.normalizerMonoidHom g)
      (f (coord 1 1) = coord 3 0 ∧ f (coord 3 1) = coord 3 2) ∨
      (f (coord 1 1) = coord 1 2 ∧ f (coord 3 1) = coord 1 0) := by
  let q := Subgroup.quotientAut (frattini U)
  let c := MulAut.congr e.symm
  let a₀ := c threeCycle
  let b := c swapAut
  obtain ⟨g, hg⟩ := hfull (q a₀)
  let a := U.normalizerMonoidHom g
  have hqa : q a = q a₀ := hg
  have ha : a ∈ U.normalizerMonoidHom.range := ⟨g, rfl⟩
  -- Faithfulness applies only to automorphisms induced by the normalizer.
  have heq (x y : MulAut U) (hx : x ∈ U.normalizerMonoidHom.range)
      (hy : y ∈ U.normalizerMonoidHom.range) (h : q x = q y) : x = y :=
    congrArg Subtype.val (hfaith (show
      ((Subgroup.quotientAut (frattini U)).comp U.normalizerMonoidHom.range.subtype)
        ⟨x, hx⟩ =
      ((Subgroup.quotientAut (frattini U)).comp U.normalizerMonoidHom.range.subtype)
        ⟨y, hy⟩ from h))
  have ha₀ : a₀ ^ 3 = 1 := by
    rw [← map_pow, threeCycle_cube, map_one]
  have hb₀ : b * a₀ * b * a₀ = 1 := by
    change c swapAut * c threeCycle * c swapAut * c threeCycle = 1
    rw [← map_mul, ← map_mul, ← map_mul, swap_threeCycle, map_one]
  have hacube : a ^ 3 = 1 := by
    apply heq _ _ (U.normalizerMonoidHom.range.pow_mem ha 3)
      U.normalizerMonoidHom.range.one_mem
    rw [map_pow, hqa, ← map_pow, ha₀]
  have hba : b * a * b * a = 1 := by
    apply heq _ _ (U.normalizerMonoidHom.range.mul_mem
      (U.normalizerMonoidHom.range.mul_mem
        (U.normalizerMonoidHom.range.mul_mem hswap ha) hswap) ha)
      U.normalizerMonoidHom.range.one_mem
    simp only [map_mul, hqa]
    rw [← map_mul, ← map_mul, ← map_mul, hb₀]
  have hperiod (x : U) : x ^ 4 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    have hh : ∀ y : CyclicFourSquare, y ^ 4 = 1 := by decide +kernel
    exact hh _
  -- Equality on the Frattini quotient implies equality on every square.
  let sq := QuotientGroup.lift (frattini U) (powMonoidHom 2 : U →* U)
    (square_kills_frattini hU hperiod)
  have hsquare (x : U) : a (x ^ 2) = a₀ (x ^ 2) := by
    have h := DFunLike.congr_fun hqa (QuotientGroup.mk' (frattini U) x)
    change q a (QuotientGroup.mk' (frattini U) x) = q a₀ (QuotientGroup.mk' (frattini U) x) at h
    dsimp only [q] at h
    rw [Subgroup.quotientAut_apply_mk, Subgroup.quotientAut_apply_mk] at h
    have hh := congrArg sq h
    change (a x) ^ 2 = (a₀ x) ^ 2 at hh
    simpa only [map_pow] using hh
  refine ⟨g, action_images_of_cube_swap ((MulAut.congr e) a).toMonoidHom ?_ ?_ ?_⟩
  · intro x
    have h := DFunLike.congr_fun hacube (e.symm x)
    change a (a (a (e.symm x))) = e.symm x at h
    simpa using congrArg e h
  · intro x
    have h := DFunLike.congr_fun hba (e.symm x)
    change b (a (b (a (e.symm x)))) = e.symm x at h
    simpa [b, c, swapAut] using congrArg e h
  · change e (a (e.symm (coord 2 2))) = coord 2 0
    have h := hsquare (e.symm (coord 1 1))
    have hpow : (coord 1 1) ^ 2 = coord 2 2 := by decide +kernel
    rw [← map_pow, hpow] at h
    have hh := congrArg e h
    change e (a (e.symm (coord 2 2))) = e (e.symm (threeCycle (e (e.symm (coord 2 2))))) at hh
    have ht : threeCycle (coord 2 2) = coord 2 0 := by decide +kernel
    simpa only [MulEquiv.apply_symm_apply, ht] using hh

namespace Stellmacher.Recognition.FongWreathedIntrinsic
open ABG
variable {G : Type*} [Group G] [Finite G]
  (S : Sylow 2 G) (P : Wreathed.Presentation S 2)

private noncomputable def baseCoordinates :
    (P.U.map (S : Subgroup G).subtype) ≃* CyclicFourSquare :=
  (P.U.equivMapOfInjective (S : Subgroup G).subtype
    (S : Subgroup G).subtype_injective).symm.trans P.baseEquiv

omit [Finite G] in
private theorem baseCoordinates_symm_apply (v : CyclicFourSquare) :
    ((baseCoordinates S P).symm v : G) =
      ((P.s ^ v.1.toAdd.val * P.t ^ v.2.toAdd.val : S) : G) :=
  congrArg Subtype.val (P.baseEquiv_symm_apply v)

omit [Finite G] in
private theorem base_swap_mem_range :
    (MulAut.congr (baseCoordinates S P).symm) swapAut ∈
      (P.U.map (S : Subgroup G).subtype).normalizerMonoidHom.range := by
  let U := P.U.map (S : Subgroup G).subtype
  let e := baseCoordinates S P
  have : P.U.Normal := Subgroup.normal_of_index_eq_two P.index_U
  have hzN : (P.z : G) ∈ Subgroup.normalizer (U : Set G) :=
    P.U.le_normalizer_map (S : Subgroup G).subtype
      (Subgroup.mem_map.mpr ⟨P.z, by rw [P.U.normalizer_eq_top]; trivial, rfl⟩)
  let gz : Subgroup.normalizer (U : Set G) := ⟨P.z, hzN⟩
  have hs : (MulAut.conj P.z) P.s = P.t := by
    simpa only [MulAut.conj_apply, P.z_inv] using P.conj_s
  have ht : (MulAut.conj P.z) P.t = P.s := by
    simpa only [MulAut.conj_apply, P.z_inv] using P.conj_t
  have h (v : CyclicFourSquare) : U.normalizerMonoidHom gz (e.symm v) =
      e.symm v.swap := by
    apply Subtype.ext
    change (P.z : G) * (e.symm v : G) * (P.z : G)⁻¹ = (e.symm v.swap : G)
    rw [baseCoordinates_symm_apply, baseCoordinates_symm_apply]
    exact congrArg Subtype.val (show
      (MulAut.conj P.z) (P.s ^ v.1.toAdd.val * P.t ^ v.2.toAdd.val) =
        P.s ^ v.2.toAdd.val * P.t ^ v.1.toAdd.val by
      rw [map_mul, map_pow, map_pow, hs, ht]
      exact ((show Commute P.s P.t from P.commute).pow_pow _ _).eq.symm)
  refine ⟨gz, ?_⟩
  ext u : 1
  obtain ⟨v, rfl⟩ := e.symm.surjective u
  change U.normalizerMonoidHom gz (e.symm v) = e.symm ((e (e.symm v)).swap)
  rw [e.apply_symm_apply]
  exact h v


private theorem baseFusion_of_action
    (hfaith : Function.Injective
      ((Subgroup.quotientAut (frattini (P.U.map (S : Subgroup G).subtype))).comp
        (P.U.map (S : Subgroup G).subtype).normalizerMonoidHom.range.subtype))
    (hfull : Function.Surjective
      ((Subgroup.quotientAut (frattini (P.U.map (S : Subgroup G).subtype))).comp
        (P.U.map (S : Subgroup G).subtype).normalizerMonoidHom)) :
    (IsConj ((F P ^ 2 : S) : G) ((E P * X P : S) : G) ∧
      IsConj ((X P * F P ^ 2 : S) : G) ((E P * J P : S) : G)) ∨
    (IsConj ((F P ^ 2 : S) : G) ((E P * X P * J P : S) : G) ∧
      IsConj ((X P * F P ^ 2 : S) : G) ((E P : S) : G)) := by
  let U := P.U.map (S : Subgroup G).subtype
  let e := baseCoordinates S P
  let : IsMulCommutative U := (P.fusionFrame S).2.2.1
  have hU : IsPGroup 2 U :=
    (S.isPGroup'.to_subgroup P.U).of_equiv
      (P.U.equivMapOfInjective (S : Subgroup G).subtype (S : Subgroup G).subtype_injective)
  obtain ⟨g, hg⟩ := normalizer_alternatives U e hU hfaith hfull (base_swap_mem_range S P)
  let f := (MulAut.congr e) (U.normalizerMonoidHom g)
  have hc (v w : CyclicFourSquare) (h : f v = w) :
      IsConj (e.symm v : G) (e.symm w : G) := by
    apply isConj_iff.mpr
    refine ⟨g, ?_⟩
    have hh := congrArg e.symm h
    have he : U.normalizerMonoidHom g (e.symm v) = e.symm w := by
      simpa [f] using hh
    exact congrArg Subtype.val he
  -- Identify the six coordinates in the finite calculation with Fong's words.
  have h11 : (e.symm (coord 1 1) : G) = ((F P ^ 2 : S) : G) := by
    rw [baseCoordinates_symm_apply, F_sq]
    change ((P.s ^ 1 * P.t ^ 1 : S) : G) = ((P.s * P.t : S) : G)
    simp
  have h31 : (e.symm (coord 3 1) : G) = ((X P * F P ^ 2 : S) : G) := by
    rw [baseCoordinates_symm_apply, F_sq]
    apply congrArg Subtype.val
    change P.s ^ 3 * P.t ^ 1 = P.s ^ 2 * (P.s * P.t)
    group
  have h30 : (e.symm (coord 3 0) : G) = ((E P * X P : S) : G) := by
    rw [baseCoordinates_symm_apply]
    apply congrArg Subtype.val
    change P.s ^ 3 * P.t ^ 0 = P.s * P.s ^ 2
    group
  have h32 : (e.symm (coord 3 2) : G) = ((E P * J P : S) : G) := by
    rw [baseCoordinates_symm_apply]
    apply congrArg Subtype.val
    change P.s ^ 3 * P.t ^ 2 = P.s * (P.s * P.t) ^ 2
    rw [(show Commute P.s P.t from P.commute).mul_pow]
    group
  have h12 : (e.symm (coord 1 2) : G) = ((E P * X P * J P : S) : G) := by
    rw [baseCoordinates_symm_apply]
    apply congrArg Subtype.val
    change P.s ^ 1 * P.t ^ 2 = P.s * P.s ^ 2 * (P.s * P.t) ^ 2
    rw [(show Commute P.s P.t from P.commute).mul_pow]
    have hs : P.s ^ 4 = 1 := P.s_pow
    calc
      _ = P.s * P.s ^ 4 * P.t ^ 2 := by rw [hs]; simp
      _ = _ := by group
  have h10 : (e.symm (coord 1 0) : G) = ((E P : S) : G) := by
    rw [baseCoordinates_symm_apply]
    change ((P.s ^ 1 * P.t ^ 0 : S) : G) = (P.s : G)
    simp
  rcases hg with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl ⟨by simpa only [h11, h30] using hc _ _ h₁,
      by simpa only [h31, h32] using hc _ _ h₂⟩
  · exact Or.inr ⟨by simpa only [h11, h12] using hc _ _ h₁,
      by simpa only [h31, h10] using hc _ _ h₂⟩

/-- The actual base normalizer gives one of the two compatible fusion pairs,
for any supplied presentation, before choosing its orientation. -/
public theorem baseFusion_alternatives [IsSimpleGroup G] :
    (IsConj ((F P ^ 2 : S) : G) ((E P * X P : S) : G) ∧
      IsConj ((X P * F P ^ 2 : S) : G) ((E P * J P : S) : G)) ∨
    (IsConj ((F P ^ 2 : S) : G) ((E P * X P * J P : S) : G) ∧
      IsConj ((X P * F P ^ 2 : S) : G) ((E P : S) : G)) := by
  have hf := P.fusionFrame S
  have hno : HasNoNormalIndexTwoSubgroup G := by
    intro K hKn hKi
    rcases hKn.eq_bot_or_eq_top with rfl | rfl
    · rw [Subgroup.index_bot] at hKi
      have hdvd := (S : Subgroup G).card_subgroup_dvd_card
      rw [P.card, hKi] at hdvd
      norm_num at hdvd
    · simp at hKi
  have hQD := wreathed_qdPattern_of_no_normal_index_two S 2 _ _ hf hno
  exact baseFusion_of_action S P
    (Wreathed.u_frattini_action S 2 _ _ hf).2
    (Wreathed.u_frattini_action_surjective S 2 _ _ hf hQD.2.2.1)

end Stellmacher.Recognition.FongWreathedIntrinsic
