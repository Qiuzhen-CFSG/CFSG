module

public import Stellmacher.Recognition.SuzukiThreeRootExponent
public import Mathlib.Logic.Equiv.Option
public import Theory.GroupAction.TernaryThreeEightNormalForm
public import Theory.GroupAction.TernaryThreeEightObstruction

/-!
# Noncommutativity of Suzuki's root group at q = 3

Identify the permutation domain with the root group together with a point at
infinity. Root elements act by left translation, and the two-point stabilizer
acts by conjugation. Consequently every element fixing infinity is affine in
these coordinates. If the root group were abelian, its order and exponent
would identify it with ternary three-space. The fixed-free order-eight torus
has the standard normal form after possibly inverting its generator. The
swapping involution then contradicts the kernel-checked finite obstruction
for this affine stabilizer. This gives the q = 3 noncommutativity conclusion
without using simplicity or unitary recognition.

Source: M. Suzuki, *A characterization of the 3-dimensional projective unitary
group over a finite field of odd characteristic*, J. Algebra 2 (1965),
Section II, Lemma 1, and Section III, Lemma 12.
-/

namespace Stellmacher.Recognition.SuzukiThreeHypotheses

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]
    {a : Ω} {Q : Subgroup (stabilizer G a)} [Q.Normal]
    (h : SuzukiThreeHypotheses G Ω a Q)

/-- Root coordinates, with `none` the base point and `some 1` the second point. -/
public noncomputable def rootPointEquiv (b : Ω) (hb : b ≠ a) : Option Q ≃ Ω := by
  classical
  exact (h.rootEquivComplement b hb).optionCongr.trans (Equiv.optionSubtypeNe a)

public theorem rootPointEquiv_none (b : Ω) (hb : b ≠ a) :
    h.rootPointEquiv b hb none = a := by rfl

public theorem rootPointEquiv_some (b : Ω) (hb : b ≠ a) (q : Q) :
    h.rootPointEquiv b hb (some q) = ((q : stabilizer G a) : G) • b := by
  exact h.rootEquivComplement_apply b hb q

/-- The original action expressed in root coordinates. -/
public noncomputable def rootCoordinateAction (b : Ω) (hb : b ≠ a) :
    G →* Equiv.Perm (Option Q) where
  toFun g := (h.rootPointEquiv b hb).trans
    ((MulAction.toPerm g).trans (h.rootPointEquiv b hb).symm)
  map_one' := by ext x; simp
  map_mul' g k := by ext x; simp [mul_smul]

public theorem rootCoordinateAction_apply (b : Ω) (hb : b ≠ a) (g : G)
    (x : Option Q) :
    h.rootCoordinateAction b hb g x =
      (h.rootPointEquiv b hb).symm (g • h.rootPointEquiv b hb x) := by rfl

public theorem rootCoordinateAction_none_iff (b : Ω) (hb : b ≠ a) (g : G) :
    h.rootCoordinateAction b hb g none = none ↔ g ∈ stabilizer G a := by
  rw [rootCoordinateAction_apply, Equiv.symm_apply_eq, rootPointEquiv_none]
  rfl

/-- Root elements become translations on the finite part of the domain. -/
public theorem rootCoordinateAction_root (b : Ω) (hb : b ≠ a) (q : Q) :
    h.rootCoordinateAction b hb ((q : stabilizer G a) : G) =
      (Equiv.mulLeft q).optionCongr := by
  apply Equiv.ext
  intro x
  rw [rootCoordinateAction_apply, Equiv.symm_apply_eq]
  cases x with
  | none => exact q.val.property
  | some r =>
    change _ = h.rootPointEquiv b hb (some (q * r))
    rw [rootPointEquiv_some, rootPointEquiv_some]
    exact (mul_smul _ _ _).symm

/-- The conjugation action of the two-point stabilizer on the root group. -/
public def torusRootAut (b : Ω) : stabilizer (stabilizer G a) b →* MulAut Q :=
  (MulAut.conjNormal (H := Q)).comp (stabilizer (stabilizer G a) b).subtype

/-- Torus elements become automorphisms of the finite root coordinates. -/
public theorem rootCoordinateAction_torus (b : Ω) (hb : b ≠ a)
    (k : stabilizer (stabilizer G a) b) :
    h.rootCoordinateAction b hb ((k : stabilizer G a) : G) =
      (torusRootAut (Q := Q) b k).toEquiv.optionCongr := by
  apply Equiv.ext
  intro x
  rw [rootCoordinateAction_apply, Equiv.symm_apply_eq]
  cases x with
  | none => exact k.val.property
  | some q =>
    change _ = h.rootPointEquiv b hb (some (torusRootAut (Q := Q) b k q))
    rw [rootPointEquiv_some, rootPointEquiv_some]
    change ((k : stabilizer G a) : G) • (((q : stabilizer G a) : G) • b) =
      (((k : stabilizer G a) : G) * ((q : stabilizer G a) : G) *
        ((k : stabilizer G a) : G)⁻¹) • b
    rw [mul_smul, mul_smul]
    have hk : ((k : stabilizer G a) : G)⁻¹ • b = b :=
      inv_smul_eq_iff.mpr k.property.symm
    rw [hk]

/-- Every element fixing infinity is a root translation followed by a torus
automorphism. This is the constraint used to exclude abelian root coordinates. -/
public theorem rootCoordinateAction_affine (b : Ω) (hb : b ≠ a) (g : G)
    (hg : h.rootCoordinateAction b hb g none = none) :
    ∃ (q : Q) (k : stabilizer (stabilizer G a) b),
      h.rootCoordinateAction b hb g = (Equiv.mulLeft q).optionCongr *
        (torusRootAut (Q := Q) b k).toEquiv.optionCongr := by
  have hga : g • a = a := (h.rootCoordinateAction_none_iff b hb g).mp hg
  have hgb : g • b ≠ a := by
    intro he
    exact hb ((MulAction.injective g) (he.trans hga.symm))
  obtain ⟨q, hq, _⟩ := h.regular b (g • b) hb hgb
  let kG := ((q : stabilizer G a) : G)⁻¹ * g
  have hka : kG • a = a := by
    dsimp [kG]
    rw [mul_smul, hga]
    exact inv_smul_eq_iff.mpr q.val.property.symm
  have hkb : kG • b = b := by
    dsimp [kG]
    rw [mul_smul]
    exact inv_smul_eq_iff.mpr hq.symm
  let k : stabilizer (stabilizer G a) b := ⟨⟨kG, hka⟩, hkb⟩
  have he : g = ((q : stabilizer G a) : G) * ((k : stabilizer G a) : G) := by
    change g = _ * (_⁻¹ * g)
    group
  refine ⟨q, k, ?_⟩
  rw [he, map_mul, h.rootCoordinateAction_root, h.rootCoordinateAction_torus]

/-- With a chosen torus generator, the affine linear part has one of eight
possible values. -/
public theorem rootCoordinateAction_affine_generator (b : Ω) (hb : b ≠ a)
    (k : stabilizer (stabilizer G a) b) (hk : orderOf k = 8) (g : G)
    (hg : h.rootCoordinateAction b hb g none = none) :
    ∃ (q : Q) (n : Fin 8),
      h.rootCoordinateAction b hb g = (Equiv.mulLeft q).optionCongr *
        h.rootCoordinateAction b hb ((k : stabilizer G a) : G) ^ (n : ℕ) := by
  classical
  let K := stabilizer (stabilizer G a) b
  let : Finite K := Nat.finite_of_card_ne_zero (by rw [h.twoPoint_card b hb]; decide)
  have htop : Subgroup.zpowers k = ⊤ :=
    (Subgroup.card_eq_iff_eq_top _).mp (by
      rw [Nat.card_zpowers, hk, h.twoPoint_card b hb])
  obtain ⟨q, l, hl⟩ := h.rootCoordinateAction_affine b hb g hg
  have hlmem : l ∈ Subgroup.zpowers k := htop ▸ Subgroup.mem_top l
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp
    (mem_zpowers_iff_mem_range_orderOf.mp hlmem)
  refine ⟨q, ⟨n, by simpa only [Finset.mem_range, hk] using hn⟩, ?_⟩
  rw [← h.rootCoordinateAction_torus b hb l, ← he] at hl
  simpa only [Subgroup.coe_pow, map_pow] using hl

include h in
/-- The fifth-power swapping involution in root coordinates. -/
public theorem exists_rootCoordinate_swap [FaithfulSMul G Ω] (b : Ω) (hb : b ≠ a)
    (k : stabilizer (stabilizer G a) b) :
    ∃ τ : Equiv.Perm (Option Q),
      τ ∈ (h.rootCoordinateAction b hb).range ∧ τ ^ 2 = 1 ∧
      τ none = some 1 ∧
      τ⁻¹ * h.rootCoordinateAction b hb ((k : stabilizer G a) : G) * τ =
        h.rootCoordinateAction b hb ((k : stabilizer G a) : G) ^ 5 := by
  obtain ⟨t, ht, hta, _, htk⟩ := h.exists_swap_pow_five b hb
  refine ⟨h.rootCoordinateAction b hb t, ⟨t, rfl⟩, ?_, ?_, ?_⟩
  · rw [← map_pow, ht, map_one]
  · rw [rootCoordinateAction_apply, Equiv.symm_apply_eq,
      rootPointEquiv_none, rootPointEquiv_some, hta]
    simp
  · rw [← map_inv, ← map_mul, ← map_mul, htk, map_pow]

include h in
/-- The torus acts faithfully on root coordinates. -/
public theorem torusRootAut_injective [FaithfulSMul G Ω] (b : Ω) (hb : b ≠ a) :
    Function.Injective (torusRootAut (Q := Q) b) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro k hk
  apply h.twoPoint_eq_one_of_centralizes_root b hb k
  intro q
  have he := congrArg (fun f : MulAut Q => ((f q : stabilizer G a) : G)) hk
  change ((k : stabilizer G a) : G) * ((q : stabilizer G a) : G) *
    ((k : stabilizer G a) : G)⁻¹ = ((q : stabilizer G a) : G) at he
  calc
    _ = (((k : stabilizer G a) : G) * ((q : stabilizer G a) : G) *
      ((k : stabilizer G a) : G)⁻¹) * ((k : stabilizer G a) : G) := by group
    _ = _ := by rw [he]

include h in
/-- A generator of the order-eight torus fixes only the identity in the root
group. This uses the global swapping element, not just the local group order. -/
public theorem torusRootAut_fixed_free [FaithfulSMul G Ω] (b : Ω) (hb : b ≠ a)
    (k : stabilizer (stabilizer G a) b) (hk : orderOf k = 8)
    (q : Q) (hq : torusRootAut (Q := Q) b k q = q) : q = 1 := by
  obtain ⟨t, _, hta, htb, htK⟩ := h.exists_swap_pow_five b hb
  have hmove : t⁻¹ * ((k : stabilizer G a) : G) * t ≠
      ((k : stabilizer G a) : G) := by
    rw [htK]
    intro he
    have hk4 : (((k : stabilizer G a) : G)) ^ 4 = 1 := by
      apply mul_right_cancel (b := ((k : stabilizer G a) : G))
      simpa only [← pow_succ, one_mul] using he
    have hd := orderOf_dvd_of_pow_eq_one hk4
    simp only [Subgroup.orderOf_coe, hk] at hd
    norm_num at hd
  apply h.root_eq_one_of_commute_of_swap_conj_ne b hb t hta htb k hmove q
  have he := congrArg (fun r : Q => ((r : stabilizer G a) : G)) hq
  change ((k : stabilizer G a) : G) * ((q : stabilizer G a) : G) *
    ((k : stabilizer G a) : G)⁻¹ = ((q : stabilizer G a) : G) at he
  calc
    _ = (((k : stabilizer G a) : G) * ((q : stabilizer G a) : G) *
      ((k : stabilizer G a) : G)⁻¹) * ((k : stabilizer G a) : G) := by group
    _ = _ := by rw [he]

include h

/-- Standard ternary root coordinates contradict the affine stabilizer and the
fifth-power swapping involution. -/
private theorem false_of_root_normal_form [FaithfulSMul G Ω]
    (b : Ω) (hb : b ≠ a) (k : stabilizer (stabilizer G a) b)
    (hk : orderOf k = 8) (e : Q ≃* TernaryThreeEight.V)
    (he : ∀ q, e (torusRootAut (Q := Q) b k q) = TernaryThreeEight.torus (e q)) :
    False := by
  let E := e.toEquiv.optionCongr
  let C := E.permCongrHom
  let F := C.toMonoidHom.comp (h.rootCoordinateAction b hb)
  have htrans (q : Q) :
      C (h.rootCoordinateAction b hb ((q : stabilizer G a) : G)) =
        TernaryThreeEight.translation (e q) := by
    rw [h.rootCoordinateAction_root b hb q]
    apply Equiv.ext
    intro x
    cases x with
    | none => rfl
    | some v =>
      change some (e (q * e.symm v)) = some (e q * v)
      simp only [map_mul, MulEquiv.apply_symm_apply]
  have htor : C (h.rootCoordinateAction b hb ((k : stabilizer G a) : G)) =
      TernaryThreeEight.linear := by
    rw [h.rootCoordinateAction_torus b hb k]
    apply Equiv.ext
    intro x
    cases x with
    | none => rfl
    | some v =>
      change some (e (torusRootAut (Q := Q) b k (e.symm v))) =
        some (TernaryThreeEight.torus v)
      rw [he, e.apply_symm_apply]
  have htranslations (v : TernaryThreeEight.V) :
      TernaryThreeEight.translation v ∈ F.range := by
    refine ⟨((e.symm v : stabilizer G a) : G), ?_⟩
    change C (h.rootCoordinateAction b hb ((e.symm v : stabilizer G a) : G)) = _
    simpa only [MulEquiv.apply_symm_apply] using htrans (e.symm v)
  have haff (s : Equiv.Perm (Option TernaryThreeEight.V))
      (hs : s ∈ F.range) (hsnone : s none = none) :
      ∃ (v : TernaryThreeEight.V) (n : Fin 8),
        s = TernaryThreeEight.translation v * TernaryThreeEight.linear ^ n.val := by
    obtain ⟨g, rfl⟩ := hs
    have hg : h.rootCoordinateAction b hb g none = none := by
      apply E.injective
      exact hsnone
    obtain ⟨q, n, hn⟩ := h.rootCoordinateAction_affine_generator b hb k hk g hg
    refine ⟨e q, n, ?_⟩
    change C (h.rootCoordinateAction b hb g) = _
    rw [← h.rootCoordinateAction_root b hb q] at hn
    rw [hn, map_mul, map_pow, htrans, htor]
  obtain ⟨τ, hτ, hsq, hn, hc⟩ := h.exists_rootCoordinate_swap b hb k
  apply TernaryThreeEight.swap_obstruction F.range htranslations haff (C τ)
  · obtain ⟨t, rfl⟩ := hτ
    exact ⟨t, rfl⟩
  · rw [← map_pow, hsq, map_one]
  · change E (τ none) = some 1
    rw [hn]
    change some (e 1) = some 1
    rw [map_one]
  · have hc' := congrArg C hc
    simpa only [map_mul, map_inv, map_pow, htor] using hc'

/-- Suzuki's root group is noncommutative, from the original action hypotheses.
The abelian alternative contradicts the finite ternary swap obstruction. -/
public theorem root_noncommuting [FaithfulSMul G Ω] (b : Ω) (hb : b ≠ a) :
    ∃ x y : Q, x * y ≠ y * x := by
  classical
  by_contra hn
  have hcomm : ∀ x y : Q, x * y = y * x := by
    simpa only [not_exists, not_not] using hn
  let : CommGroup Q := { (inferInstance : Group Q) with mul_comm := hcomm }
  let : Finite G := h.finite_group
  let K := stabilizer (stabilizer G a) b
  let : IsCyclic K := h.twoPoint_cyclic b hb
  obtain ⟨k, hk⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := K)
  have hk8 : orderOf k = 8 := hk.trans (h.twoPoint_card b hb)
  have hf : orderOf (torusRootAut (Q := Q) b k) = 8 :=
    (orderOf_injective _ (h.torusRootAut_injective b hb) k).trans hk8
  obtain ⟨e, he | he⟩ := TernaryThreeEight.exists_normal_form h.root_card
    (h.root_cube b hb) (torusRootAut (Q := Q) b k) hf
    (h.torusRootAut_fixed_free b hb k hk8)
  · exact h.false_of_root_normal_form b hb k hk8 e he
  · apply h.false_of_root_normal_form b hb k⁻¹ (by simpa only [orderOf_inv] using hk8) e
    intro q
    simpa only [map_inv] using he q

end Stellmacher.Recognition.SuzukiThreeHypotheses
