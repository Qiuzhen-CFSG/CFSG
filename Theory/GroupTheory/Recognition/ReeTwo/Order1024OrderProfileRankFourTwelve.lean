module

public import Theory.GroupTheory.Recognition.ReeTwo.Order1024OrderProfileData
public import Theory.GroupTheory.Recognition.ReeTwo.Order1024RankFourTwelveCoordinates

/-!
# The rank-four order profile of residual representative twelve

Each fiber of the quotient constructed in `Order1024RankFourTwelveCoordinates`
is parametrized by six binary coordinates. On the eight-dimensional core slice,
the root-one action is linear. Its verified formula supplies a small squaring
calculation, and kernel reduction checks the counts of orders 1, 2 and 4 in all
sixteen fibers. These counts realize the table in `Order1024OrderProfileData`.

Source: Shinoda (1975), (2.3), pp. 81–82, through the verified core normal form
and root action. The finite certificates use only Lean kernel reduction.
-/

namespace ReeTwo.SylowModel.RankFourTwelve
set_option maxRecDepth 16384
set_option synthInstance.maxSize 4096
private abbrev U := residualCandidate 12
private abbrev V := OrderProfileQuotient 4

private def core (v : Fin 8 → ZMod 2) : Core :=
  ⟨0,0,v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7⟩
private def scale (t : ZMod 2) (x : Core) : Core :=
  ⟨t*x.b0,t*x.b1,t*x.b2,t*x.b3,t*x.b4,t*x.b5,t*x.b6,t*x.b7,t*x.b8,t*x.b9⟩
private theorem pow_binary (x : Core) (t : ZMod 2) : x ^ t.val = scale t x := by
  rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) t with rfl | rfl
  · change (1 : Core) = scale 0 x
    apply Core.ext <;> simp [scale] <;> rfl
  · change x ^ 1 = scale 1 x
    rw [pow_one]
    apply Core.ext <;> simp [scale]
private def linearA (v : Fin 8 → ZMod 2) : Fin 8 → ZMod 2 :=
  ![v 0,v 1,v 2+v 1,v 3,v 4+v 3,v 5+v 4,v 6+v 3+v 4+v 5,v 7+v 3+v 4]
set_option maxHeartbeats 2000000 in
private theorem a_core (v : Fin 8 → ZMod 2) : Core.a (core v) = core (linearA v) := by
  have h2 : Core.aRoot 2 = (⟨0,0,1,0,0,0,0,0,0,0⟩ : Core) := by decide +kernel
  have h3 : Core.aRoot 3 = (⟨0,0,0,1,1,0,0,0,0,0⟩ : Core) := by decide +kernel
  have h4 : Core.aRoot 4 = (⟨0,0,0,0,1,0,0,0,0,0⟩ : Core) := by decide +kernel
  have h5 : Core.aRoot 5 = (⟨0,0,0,0,0,1,1,0,1,1⟩ : Core) := by decide +kernel
  have h6 : Core.aRoot 6 = (⟨0,0,0,0,0,0,1,1,1,1⟩ : Core) := by decide +kernel
  have h7 : Core.aRoot 7 = (⟨0,0,0,0,0,0,0,1,1,0⟩ : Core) := by decide +kernel
  have h8 : Core.aRoot 8 = (⟨0,0,0,0,0,0,0,0,1,0⟩ : Core) := by decide +kernel
  have h9 : Core.aRoot 9 = (⟨0,0,0,0,0,0,0,0,0,1⟩ : Core) := by decide +kernel
  change Core.aMap (core v) = _
  unfold Core.aMap Core.normalWord Core.coords
  simp only [core, Matrix.cons_val_zero, ZMod.val_zero,
    pow_zero, one_mul,h2,h3,h4,h5,h6,h7,h8,h9,pow_binary]
  apply Core.ext <;> simp [scale, linearA,
    show ∀ x y : Core, x*y = Core.mul x y from fun _ _ => rfl, Core.mul] <;> ring

private theorem action_core (t : FiveFour.Cyclic 4) (v : Fin 8 → ZMod 2) :
    Core.complementAction (SemidirectProduct.inr t) (core v) = core (linearA^[t.toAdd.val] v) := by
  have hp (n : ℕ) : (Core.a ^ n) (core v) = core (linearA^[n] v) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, a_core, Function.iterate_succ_apply']
  conv_lhs => rw [← FiveFour.generator_pow_val t, map_pow, map_pow]
  exact hp _

private abbrev RawParameters := FiveFour.Cyclic 4 × (Fin 8 → ZMod 2)
private def raw (p : RawParameters) : SylowModel := ⟨core p.2,p.1⟩
private def square (p : RawParameters) : RawParameters :=
  let c := core p.2 * core (linearA^[p.1.toAdd.val] p.2)
  (p.1*p.1, ![c.b2,c.b3,c.b4,c.b5,c.b6,c.b7,c.b8,c.b9])
private theorem raw_square (p : RawParameters) : raw (square p) = raw p ^ 2 := by
  rw [pow_two]
  apply SemidirectProduct.ext
  · change core _ = core p.2 * Core.complementAction (SemidirectProduct.inr p.1) (core p.2)
    rw [action_core]
    apply Core.ext <;> rfl
  · rfl

private abbrev Parameters := Fin 6 → ZMod 2

private def fiberElement (v : V) (p : Parameters) : U :=
  ⟨⟨⟨0, 0, v.toAdd 1, v.toAdd 0, p 0, v.toAdd 3, p 1, p 2, p 3, p 4⟩,
    Multiplicative.ofAdd ((v.toAdd 2).val + 2 * (p 5).val : ℕ)⟩,
    (mem_candidate _).mpr ⟨rfl, rfl⟩⟩

private theorem coordinates_fiberElement (v : V) (p : Parameters) :
    coordinates (fiberElement v p) = v := by
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact (by decide +kernel : ∀ a b : ZMod 2,
      (parity (Multiplicative.ofAdd (a.val + 2 * b.val : ℕ))).toAdd = a) _ _
  · rfl

private def fiberEquiv (v : V) : {g : U // coordinates g = v} ≃ Parameters where
  toFun g := ![g.val.val.left.b4, g.val.val.left.b6, g.val.val.left.b7,
    g.val.val.left.b8, g.val.val.left.b9, (g.val.val.right.toAdd.val / 2 : ℕ)]
  invFun p := ⟨fiberElement v p, coordinates_fiberElement v p⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    apply SemidirectProduct.ext
    · obtain ⟨h0,h1⟩ := (mem_candidate g.val.val).mp g.val.property
      have hv (i : Fin 4) := congrFun (congrArg Multiplicative.toAdd g.property) i
      apply Core.ext
      · exact h0.symm
      · exact h1.symm
      · exact (hv 1).symm
      · exact (hv 0).symm
      · rfl
      · exact (hv 3).symm
      · rfl
      · rfl
      · rfl
      · rfl
    · have hv := congrFun (congrArg Multiplicative.toAdd g.property) 2
      change (parity g.val.val.right).toAdd = v.toAdd 2 at hv
      change Multiplicative.ofAdd (((v.toAdd 2).val +
        2 * ((g.val.val.right.toAdd.val / 2 : ℕ) : ZMod 2).val : ℕ) : ZMod 4) = g.val.val.right
      rw [← hv]
      exact (by decide +kernel : ∀ t : FiveFour.Cyclic 4,
        Multiplicative.ofAdd (((parity t).toAdd.val +
          2 * ((t.toAdd.val / 2 : ℕ) : ZMod 2).val : ℕ) : ZMod 4) = t) _
  right_inv p := by
    funext i
    fin_cases i
    all_goals try rfl
    exact (by decide +kernel : ∀ a b : ZMod 2,
      (((((a.val + 2 * b.val : ℕ) : ZMod 4).val / 2 : ℕ)) : ZMod 2) = b) _ _

private def selectedOrder {G : Type*} [Group G] [DecidableEq G] (g : G) : ℕ :=
  if g = 1 then 1 else if g ^ 2 = 1 then 2 else if g ^ 4 = 1 then 4 else 0

private theorem selectedOrder_eq_iff {G : Type*} [Group G] [DecidableEq G]
    (g : G) (n : ℕ) (hn : n = 1 ∨ n = 2 ∨ n = 4) :
    orderOf g = n ↔ selectedOrder g = n := by
  rcases hn with rfl | rfl | rfl
  · simp only [orderOf_eq_one_iff, selectedOrder]
    split_ifs <;> simp_all
  · constructor
    · intro h
      have hs : g^2 = 1 := h ▸ pow_orderOf_eq_one g
      have hg : g ≠ 1 := by intro hg; simp [hg] at h
      simp [selectedOrder, hg, hs]
    · intro h
      unfold selectedOrder at h
      split_ifs at h with hg hs
      · contradiction
      · exact orderOf_eq_prime hs hg
      · contradiction
  · constructor
    · intro h
      have hs : g^4 = 1 := h ▸ pow_orderOf_eq_one g
      have hg : g ≠ 1 := by intro hg; simp [hg] at h
      have h2 : g^2 ≠ 1 := by
        intro h2
        have hd := orderOf_dvd_of_pow_eq_one h2
        rw [h] at hd
        norm_num at hd
      simp [selectedOrder,hg,h2,hs]
    · intro h
      unfold selectedOrder at h
      split_ifs at h with hg h2 h4
      · contradiction
      · contradiction
      · exact @orderOf_eq_prime_pow _ _ g 1 2 ⟨Nat.prime_two⟩ h2 h4

private theorem fiber_count (v : V) (n : ℕ) (hn : n = 1 ∨ n = 2 ∨ n = 4) :
    Subgroup.fiberProfile coordinates orderOf v n =
      (Finset.univ.filter (fun p : Parameters => selectedOrder (fiberElement v p).val = n)).card := by
  have hprofile : Subgroup.fiberProfile coordinates orderOf v n =
      Nat.card {g : U // coordinates g = v ∧ orderOf g = n} := by
    classical
    let : Fintype U := Fintype.ofFinite U
    rw [Subgroup.fiberProfile_eq_card_filter, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hprofile]
  let e : {g : U // coordinates g = v ∧ orderOf g = n} ≃
      {p : Parameters // selectedOrder (fiberElement v p).val = n} := {
    toFun := fun g => ⟨fiberEquiv v ⟨g.val,g.property.1⟩, by
      have he := congrArg Subtype.val ((fiberEquiv v).symm_apply_apply ⟨g.val,g.property.1⟩)
      change fiberElement v (fiberEquiv v ⟨g.val,g.property.1⟩) = g.val at he
      rw [he]
      apply (selectedOrder_eq_iff _ n hn).mp
      simpa only [Subgroup.orderOf_coe] using g.property.2⟩
    invFun := fun p => ⟨fiberElement v p.val, coordinates_fiberElement v p.val, by
      have h := (selectedOrder_eq_iff _ n hn).mpr p.property
      simpa only [Subgroup.orderOf_coe] using h⟩
    left_inv := by
      intro g
      apply Subtype.ext
      exact congrArg (fun z : {g : U // coordinates g = v} => z.val)
        ((fiberEquiv v).symm_apply_apply ⟨g.val,g.property.1⟩)
    right_inv := fun p => Subtype.ext ((fiberEquiv v).apply_symm_apply p.val) }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]

private def fastSelected (p : RawParameters) : ℕ :=
  if raw p = 1 then 1 else if raw (square p) = 1 then 2
    else if raw (square (square p)) = 1 then 4 else 0

private theorem fastSelected_eq (p : RawParameters) :
    fastSelected p = selectedOrder (raw p) := by
  simp only [fastSelected, selectedOrder, raw_square, ← pow_mul]

private def fiberParameters (v : V) (p : Parameters) : RawParameters :=
  (Multiplicative.ofAdd ((v.toAdd 2).val + 2 * (p 5).val : ℕ),
    ![v.toAdd 1,v.toAdd 0,p 0,v.toAdd 3,p 1,p 2,p 3,p 4])

private theorem fast_fiber_label (v : V) (p : Parameters) :
    fastSelected (fiberParameters v p) = selectedOrder (fiberElement v p).val :=
  fastSelected_eq _

set_option maxHeartbeats 8000000 in
private theorem fast_counts_check : ∀ v : V,
    ((Finset.univ.filter (fun p : Parameters => fastSelected (fiberParameters v p) = 1)).card,
     (Finset.univ.filter (fun p : Parameters => fastSelected (fiberParameters v p) = 2)).card,
     (Finset.univ.filter (fun p : Parameters => fastSelected (fiberParameters v p) = 4)).card) =
       orderProfileCounts 12 v := by
  unfold orderProfileCounts orderProfileColor orderProfileRank
  decide +kernel

private theorem counts_check (v : V) :
    ((Finset.univ.filter (fun p : Parameters => selectedOrder (fiberElement v p).val = 1)).card,
     (Finset.univ.filter (fun p : Parameters => selectedOrder (fiberElement v p).val = 2)).card,
     (Finset.univ.filter (fun p : Parameters => selectedOrder (fiberElement v p).val = 4)).card) =
       orderProfileCounts 12 v := by
  have hf (n : ℕ) :
      Finset.univ.filter (fun p : Parameters => selectedOrder (fiberElement v p).val = n) =
      Finset.univ.filter (fun p : Parameters => fastSelected (fiberParameters v p) = n) := by
    apply Finset.filter_congr
    intro p _
    rw [fast_fiber_label]
  rw [hf 1, hf 2, hf 4]
  exact fast_counts_check v

/-- Exact counts of orders 1, 2 and 4 in every quotient fiber. -/
public theorem counts (v : OrderProfileQuotient 4) :
    (Subgroup.fiberProfile coordinates orderOf v 1,
      Subgroup.fiberProfile coordinates orderOf v 2,
      Subgroup.fiberProfile coordinates orderOf v 4) = orderProfileCounts 12 v := by
  rw [fiber_count v 1 (by simp), fiber_count v 2 (by simp), fiber_count v 4 (by simp)]
  exact counts_check v

end ReeTwo.SylowModel.RankFourTwelve

namespace ReeTwo.SylowModel

/-- Residual representative twelve realizes the specified rank-four order profile. -/
public theorem orderProfileModel_rankFour_twelve : OrderProfileModel 12 :=
  OrderProfileModel.of_counts 12 RankFourTwelve.coordinates
    RankFourTwelve.coordinates_surjective RankFourTwelve.kernel_eq_frattini RankFourTwelve.counts

end ReeTwo.SylowModel
