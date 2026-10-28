module

public import Theory.SpecificGroups.SymmetricThreeProduct.Parabolics.Basic
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Theory.GroupAction.TypedCosetGeometry

/-!
# Structure and coset geometry of S₃ × S₃

The two coordinate parabolics are exactly the maximal subgroups over the
chosen Sylow two-subgroup. Conjugation gives the exhaustive pair over every
Sylow two-subgroup. To prove exhaustiveness, conjugate a coordinate transposition
by an element moving zero: the resulting two transpositions generate that
entire S₃ factor. An overgroup escaping both parabolics is therefore the whole
group. The six words in these transpositions are checked by finite enumeration.

The ambient two-core is trivial. Each parabolic has an order-two core in its
restricted coordinate, and projection onto the opposite coordinate identifies
its core quotient with S₃. The existing symmetric-three kernel theorem supplies
the core calculation.

The actual coset spaces are equivariantly equivalent to the two three-letter
sets. Their incidence, in the existing typed coset geometry, is complete. Each
coset action has the opposite full factor as kernel; their joint action is an
isomorphism onto the product of the two full symmetric groups.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.5.3
and I.5.7, printed pp. 419–420.
-/

public section

namespace SymmetricThreeProduct

private def t : S3 := Equiv.swap 1 2
private theorem six_words : ∀ a b : S3, a 0 ≠ 0 →
    b = 1 ∨ b = t ∨ b = a * t * a⁻¹ ∨ b = t * (a * t * a⁻¹) ∨
    b = (a * t * a⁻¹) * t ∨ b = t * (a * t * a⁻¹) * t := by
  decide +kernel

private theorem coordinate_mem (U : Subgroup G) (hB : borel ≤ U)
    (x : G) (hx : x ∈ U) (hx0 : x.1 0 ≠ 0) (a : S3) : (a, 1) ∈ U := by
  have ht : (t, (1 : S3)) ∈ U := hB (by decide)
  have hc : (x.1 * t * x.1⁻¹, (1 : S3)) ∈ U := by
    simpa only [Prod.mul_def, Prod.fst_inv, Prod.snd_inv, mul_one, one_mul, mul_inv_cancel] using
      U.mul_mem (U.mul_mem hx ht) (U.inv_mem hx)
  rcases six_words x.1 a hx0 with h | h | h | h | h | h <;> rw [h]
  · exact U.one_mem
  · exact ht
  · exact hc
  · exact U.mul_mem ht hc
  · exact U.mul_mem hc ht
  · exact U.mul_mem (U.mul_mem ht hc) ht

private theorem coordinate_mem' (U : Subgroup G) (hB : borel ≤ U)
    (x : G) (hx : x ∈ U) (hx0 : x.2 0 ≠ 0) (a : S3) : (1, a) ∈ U := by
  have ht : ((1 : S3), t) ∈ U := hB (by decide)
  have hc : ((1 : S3), x.2 * t * x.2⁻¹) ∈ U := by
    simpa only [Prod.mul_def, Prod.fst_inv, Prod.snd_inv, mul_one, one_mul, mul_inv_cancel] using
      U.mul_mem (U.mul_mem hx ht) (U.inv_mem hx)
  rcases six_words x.2 a hx0 with h | h | h | h | h | h <;> rw [h]
  · exact U.one_mem
  · exact ht
  · exact hc
  · exact U.mul_mem ht hc
  · exact U.mul_mem hc ht
  · exact U.mul_mem (U.mul_mem ht hc) ht

theorem coatom_over_borel (U : Subgroup G) (hU : IsCoatom U) (hB : borel ≤ U) :
    U = leftParabolic ∨ U = rightParabolic := by
  by_cases hl : U ≤ leftParabolic
  · exact Or.inl (eq_of_le_of_not_lt hl (fun h => leftParabolic_isCoatom.1 (hU.2 _ h)))
  by_cases hr : U ≤ rightParabolic
  · exact Or.inr (eq_of_le_of_not_lt hr (fun h => rightParabolic_isCoatom.1 (hU.2 _ h)))
  obtain ⟨x, hx, hxL⟩ := SetLike.not_le_iff_exists.mp hl
  obtain ⟨y, hy, hyR⟩ := SetLike.not_le_iff_exists.mp hr
  apply False.elim
  apply hU.1
  apply top_unique
  intro g _
  have h1 := coordinate_mem U hB x hx (by simpa [mem_leftParabolic] using hxL) g.1
  have h2 := coordinate_mem' U hB y hy (by simpa [mem_rightParabolic] using hyR) g.2
  simpa using U.mul_mem h1 h2

theorem borel_le_leftParabolic : borel ≤ leftParabolic := by
  rw [← parabolics_inf]
  exact inf_le_left

theorem borel_le_rightParabolic : borel ≤ rightParabolic := by
  rw [← parabolics_inf]
  exact inf_le_right

/-- Exactly the two coordinate parabolics are maximal over the chosen Sylow subgroup. -/
theorem coatom_over_borel_iff (P : Subgroup G) :
    IsCoatom P ∧ borel ≤ P ↔ P = leftParabolic ∨ P = rightParabolic := by
  constructor
  · rintro ⟨hP, hB⟩
    exact coatom_over_borel P hP hB
  · rintro (rfl | rfl)
    · exact ⟨leftParabolic_isCoatom, borel_le_leftParabolic⟩
    · exact ⟨rightParabolic_isCoatom, borel_le_rightParabolic⟩

/-- Conjugation transports the exhaustive pair to any Sylow two-subgroup. -/
theorem coatom_over_sylow (T : Sylow 2 G) :
    ∃ g : G, (MulAut.conj g).mapSubgroup borel = (T : Subgroup G) ∧
      ∀ P : Subgroup G, (IsCoatom P ∧ (T : Subgroup G) ≤ P) ↔
        P = (MulAut.conj g).mapSubgroup leftParabolic ∨
        P = (MulAut.conj g).mapSubgroup rightParabolic := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G sylow T
  let e := (MulAut.conj g).mapSubgroup
  have he : e borel = (T : Subgroup G) := by
    change ((g • sylow : Sylow 2 G) : Subgroup G) = (T : Subgroup G)
    rw [hg]
  refine ⟨g, he, ?_⟩
  intro P
  constructor
  · rintro ⟨hP, hTP⟩
    have hc : IsCoatom (e.symm P) := (e.symm.isCoatom_iff P).2 hP
    have hb : borel ≤ e.symm P := by
      have hh := e.symm.monotone hTP
      rwa [← he, e.symm_apply_apply] at hh
    rcases coatom_over_borel (e.symm P) hc hb with h | h
    · left
      exact (e.apply_symm_apply P).symm.trans (congrArg e h)
    · right
      exact (e.apply_symm_apply P).symm.trans (congrArg e h)
  · rintro (rfl | rfl)
    · exact ⟨(e.isCoatom_iff _).2 leftParabolic_isCoatom,
        he ▸ e.monotone borel_le_leftParabolic⟩
    · exact ⟨(e.isCoatom_iff _).2 rightParabolic_isCoatom,
        he ▸ e.monotone borel_le_rightParabolic⟩

/-- Every Sylow two-subgroup lies in precisely two maximal subgroups. -/
theorem exists_parabolics_over_sylow (T : Sylow 2 G) :
    ∃ P Q : Subgroup G, P ≠ Q ∧ P ⊓ Q = (T : Subgroup G) ∧
      ∀ U : Subgroup G, (IsCoatom U ∧ (T : Subgroup G) ≤ U) ↔ U = P ∨ U = Q := by
  obtain ⟨g, hg, h⟩ := coatom_over_sylow T
  let e := (MulAut.conj g).mapSubgroup
  refine ⟨e leftParabolic, e rightParabolic, ?_, ?_, h⟩
  · exact fun hh => parabolics_ne (e.injective hh)
  · rw [← e.map_inf, parabolics_inf]
    exact hg

/-- Projection of the left parabolic onto its unrestricted S₃ coordinate. -/
def leftQuotientMap : leftParabolic →* S3 := rightAction.comp leftParabolic.subtype
/-- Projection of the right parabolic onto its unrestricted S₃ coordinate. -/
def rightQuotientMap : rightParabolic →* S3 := leftAction.comp rightParabolic.subtype

theorem leftQuotientMap_surjective : Function.Surjective leftQuotientMap := by
  intro a
  exact ⟨⟨(1, a), (mem_leftParabolic _).2 rfl⟩, rfl⟩
theorem rightQuotientMap_surjective : Function.Surjective rightQuotientMap := by
  intro a
  exact ⟨⟨(a, 1), (mem_rightParabolic _).2 rfl⟩, rfl⟩

theorem card_ker_leftQuotientMap : Nat.card leftQuotientMap.ker = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_ker_rightQuotientMap : Nat.card rightQuotientMap.ker = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem left_twoCore : pCore 2 leftParabolic = leftQuotientMap.ker := by
  exact (ker_eq_twoCore_of_surjective_perm_three _ leftQuotientMap_surjective
    (IsPGroup.of_card (n := 1) (by simpa using card_ker_leftQuotientMap))).symm

theorem right_twoCore : pCore 2 rightParabolic = rightQuotientMap.ker := by
  exact (ker_eq_twoCore_of_surjective_perm_three _ rightQuotientMap_surjective
    (IsPGroup.of_card (n := 1) (by simpa using card_ker_rightQuotientMap))).symm

theorem map_left_twoCore : (pCore 2 leftParabolic).map leftParabolic.subtype =
    pointStabilizer.prod ⊥ := by
  rw [left_twoCore]
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property.1, hx⟩
  · intro h
    exact ⟨⟨g, ⟨h.1, Subgroup.mem_top _⟩⟩, h.2, rfl⟩

theorem map_right_twoCore : (pCore 2 rightParabolic).map rightParabolic.subtype =
    (⊥ : Subgroup S3).prod pointStabilizer := by
  rw [right_twoCore]
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, x.property.2⟩
  · intro h
    exact ⟨⟨g, ⟨Subgroup.mem_top _, h.2⟩⟩, h.1, rfl⟩

noncomputable def leftCoreQuotientEquiv : leftParabolic ⧸ pCore 2 leftParabolic ≃* S3 :=
  (QuotientGroup.quotientMulEquivOfEq left_twoCore).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ leftQuotientMap_surjective)

noncomputable def rightCoreQuotientEquiv : rightParabolic ⧸ pCore 2 rightParabolic ≃* S3 :=
  (QuotientGroup.quotientMulEquivOfEq right_twoCore).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ rightQuotientMap_surjective)

private theorem s3_twoCore : pCore 2 S3 = ⊥ := by
  have h := ker_eq_twoCore_of_surjective_perm_three (MonoidHom.id S3)
    Function.surjective_id (by rw [MonoidHom.ker_id]; exact IsPGroup.of_bot)
  simpa using h.symm

private theorem core_le_ker (f : G →* S3) (hf : Function.Surjective f) :
    pCore 2 G ≤ f.ker := by
  have hn : ((pCore 2 G).map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hle : (pCore 2 G).map f ≤ pCore 2 S3 :=
    le_sSup ⟨hn, pCore_isPGroup.map f⟩
  rw [s3_twoCore] at hle
  exact (Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp hle)

theorem twoCore_eq_bot : pCore 2 G = ⊥ := by
  apply le_bot_iff.mp
  intro g hg
  apply Prod.ext
  · exact core_le_ker leftAction (fun a => ⟨(a, 1), rfl⟩) hg
  · exact core_le_ker rightAction (fun a => ⟨(1, a), rfl⟩) hg

private def cosetCoordinate (P : Subgroup G) (f : G →* S3)
    (hP : ∀ g, g ∈ P ↔ f g 0 = 0) : G ⧸ P → Fin 3 :=
  Quotient.lift (fun g => f g 0) (by
    intro a b h
    have hh := (hP (a⁻¹ * b)).1 (QuotientGroup.leftRel_apply.mp h)
    calc f a 0 = f a (f (a⁻¹ * b) 0) := congrArg (f a) hh.symm
         _ = f b 0 := by simp)

private theorem cosetCoordinate_bijective (P : Subgroup G) (f : G →* S3)
    (hP : ∀ g, g ∈ P ↔ f g 0 = 0) (hf : Function.Surjective f) :
    Function.Bijective (cosetCoordinate P f hP) := by
  constructor
  · intro q r
    induction q using Quotient.inductionOn with | h a =>
      induction r using Quotient.inductionOn with | h b =>
        intro h
        apply Quotient.sound
        apply (QuotientGroup.leftRel_apply (s := P)).2
        rw [hP]
        change f a 0 = f b 0 at h
        simp [← h]
  · intro i
    obtain ⟨g, hg⟩ := hf (Equiv.swap 0 i)
    exact ⟨QuotientGroup.mk g, by simp [cosetCoordinate, hg]⟩

/-- The first-coordinate identification of cosets of the left parabolic with three points. -/
noncomputable def leftCosetEquiv : G ⧸ leftParabolic ≃ Fin 3 :=
  Equiv.ofBijective (cosetCoordinate leftParabolic leftAction mem_leftParabolic)
    (cosetCoordinate_bijective _ _ mem_leftParabolic (fun a => ⟨(a, 1), rfl⟩))

/-- The second-coordinate identification of cosets of the right parabolic with three points. -/
noncomputable def rightCosetEquiv : G ⧸ rightParabolic ≃ Fin 3 :=
  Equiv.ofBijective (cosetCoordinate rightParabolic rightAction mem_rightParabolic)
    (cosetCoordinate_bijective _ _ mem_rightParabolic (fun a => ⟨(1, a), rfl⟩))

@[simp] theorem leftCosetEquiv_mk (g : G) : leftCosetEquiv (QuotientGroup.mk g) = g.1 0 := by rfl
@[simp] theorem rightCosetEquiv_mk (g : G) : rightCosetEquiv (QuotientGroup.mk g) = g.2 0 := by rfl

theorem leftCosetEquiv_smul (g : G) (q : G ⧸ leftParabolic) :
    leftCosetEquiv (g • q) = leftAction g (leftCosetEquiv q) := by
  induction q using Quotient.inductionOn with | h a => rfl

theorem rightCosetEquiv_smul (g : G) (q : G ⧸ rightParabolic) :
    rightCosetEquiv (g • q) = rightAction g (rightCosetEquiv q) := by
  induction q using Quotient.inductionOn with | h a => rfl

/-- The two types of the digon coset geometry. -/
@[expose] def digonFamily : Bool → Subgroup G
  | false => leftParabolic
  | true => rightParabolic

/-- Incidence in the actual typed coset geometry. -/
abbrev CosetIncident (q : G ⧸ leftParabolic) (r : G ⧸ rightParabolic) : Prop :=
  Subgroup.CosetGeometry.Incident digonFamily ⟨false, q⟩ ⟨true, r⟩

theorem coset_incidence_complete (q : G ⧸ leftParabolic) (r : G ⧸ rightParabolic) :
    CosetIncident q r := by
  induction q using Quotient.inductionOn with | h a =>
    induction r using Quotient.inductionOn with | h b =>
      refine ⟨(a.1, b.2), leftCosetEquiv.injective ?_, rightCosetEquiv.injective ?_⟩ <;> rfl

/-- Every pair of the two three-point parts is incident. -/
theorem coset_incidence_digon (i j : Fin 3) :
    CosetIncident (leftCosetEquiv.symm i) (rightCosetEquiv.symm j) :=
  coset_incidence_complete _ _

/-- The first actual coset permutation representation. -/
noncomputable def leftCosetAction : G →* Equiv.Perm (G ⧸ leftParabolic) :=
  MulAction.toPermHom G _

/-- The second actual coset permutation representation. -/
noncomputable def rightCosetAction : G →* Equiv.Perm (G ⧸ rightParabolic) :=
  MulAction.toPermHom G _

theorem leftCosetAction_coordinate (g : G) :
    leftCosetEquiv.permCongr (leftCosetAction g) = leftAction g := by
  apply Equiv.ext
  intro i
  change leftCosetEquiv (g • leftCosetEquiv.symm i) = leftAction g i
  rw [leftCosetEquiv_smul, leftCosetEquiv.apply_symm_apply]

theorem rightCosetAction_coordinate (g : G) :
    rightCosetEquiv.permCongr (rightCosetAction g) = rightAction g := by
  apply Equiv.ext
  intro i
  change rightCosetEquiv (g • rightCosetEquiv.symm i) = rightAction g i
  rw [rightCosetEquiv_smul, rightCosetEquiv.apply_symm_apply]

theorem ker_leftCosetAction : leftCosetAction.ker = (⊥ : Subgroup S3).prod ⊤ := by
  rw [← ker_leftAction]
  ext g
  change leftCosetAction g = 1 ↔ leftAction g = 1
  rw [← leftCosetAction_coordinate]
  exact ⟨fun h => by rw [h]; exact leftCosetEquiv.permCongr_refl,
    fun h => leftCosetEquiv.permCongr.injective (h.trans leftCosetEquiv.permCongr_refl.symm)⟩

theorem ker_rightCosetAction : rightCosetAction.ker = (⊤ : Subgroup S3).prod ⊥ := by
  rw [← ker_rightAction]
  ext g
  change rightCosetAction g = 1 ↔ rightAction g = 1
  rw [← rightCosetAction_coordinate]
  exact ⟨fun h => by rw [h]; exact rightCosetEquiv.permCongr_refl,
    fun h => rightCosetEquiv.permCongr.injective (h.trans rightCosetEquiv.permCongr_refl.symm)⟩

/-- The two actual coset representations together are faithful. -/
theorem joint_coset_action_faithful {g h : G}
    (hl : ∀ q : G ⧸ leftParabolic, g • q = h • q)
    (hr : ∀ q : G ⧸ rightParabolic, g • q = h • q) : g = h := by
  apply joint_action_faithful
  · intro i
    have hh := congrArg leftCosetEquiv (hl (leftCosetEquiv.symm i))
    simpa only [leftCosetEquiv_smul, leftCosetEquiv.apply_symm_apply] using hh
  · intro i
    have hh := congrArg rightCosetEquiv (hr (rightCosetEquiv.symm i))
    simpa only [rightCosetEquiv_smul, rightCosetEquiv.apply_symm_apply] using hh

/-- Arbitrary permutations on the two actual coset spaces can be prescribed independently. -/
theorem independent_coset_actions (a : Equiv.Perm (G ⧸ leftParabolic))
    (b : Equiv.Perm (G ⧸ rightParabolic)) :
    ∃ g : G, leftCosetAction g = a ∧ rightCosetAction g = b := by
  obtain ⟨g, hl, hr⟩ := independent_actions (leftCosetEquiv.permCongr a)
    (rightCosetEquiv.permCongr b)
  refine ⟨g, leftCosetEquiv.permCongr.injective ?_, rightCosetEquiv.permCongr.injective ?_⟩
  · rw [leftCosetAction_coordinate, hl]
  · rw [rightCosetAction_coordinate, hr]

theorem card_left_twoCore : Nat.card (pCore 2 leftParabolic) = 2 := by
  rw [left_twoCore]
  exact card_ker_leftQuotientMap

theorem card_right_twoCore : Nat.card (pCore 2 rightParabolic) = 2 := by
  rw [right_twoCore]
  exact card_ker_rightQuotientMap

@[simp] theorem mem_left_twoCore (x : leftParabolic) :
    x ∈ pCore 2 leftParabolic ↔ x.val.2 = 1 := by
  rw [left_twoCore]
  rfl

@[simp] theorem mem_right_twoCore (x : rightParabolic) :
    x ∈ pCore 2 rightParabolic ↔ x.val.1 = 1 := by
  rw [right_twoCore]
  rfl

/-- The joint coset action identifies the group with the full product of the two
symmetric groups. In particular the induced factors are independent. -/
noncomputable def jointCosetActionEquiv :
    G ≃* Equiv.Perm (G ⧸ leftParabolic) × Equiv.Perm (G ⧸ rightParabolic) :=
  MulEquiv.ofBijective (leftCosetAction.prod rightCosetAction) (by
    constructor
    · intro g h he
      apply joint_coset_action_faithful
      · intro q
        exact congrArg (fun a : Equiv.Perm (G ⧸ leftParabolic) => a q) (congrArg Prod.fst he)
      · intro q
        exact congrArg (fun a : Equiv.Perm (G ⧸ rightParabolic) => a q) (congrArg Prod.snd he)
    · rintro ⟨a, b⟩
      obtain ⟨g, hl, hr⟩ := independent_coset_actions a b
      exact ⟨g, Prod.ext hl hr⟩)

/-- The left parabolic induces its S₃ quotient on the opposite coset type. -/
theorem ker_rightCosetAction_on_leftParabolic :
    (rightCosetAction.comp leftParabolic.subtype).ker = pCore 2 leftParabolic := by
  ext x
  change x.val ∈ rightCosetAction.ker ↔ x ∈ pCore 2 leftParabolic
  rw [ker_rightCosetAction, mem_left_twoCore]
  simp only [Subgroup.mem_prod, Subgroup.mem_top, Subgroup.mem_bot, true_and]

/-- The right parabolic induces its S₃ quotient on the opposite coset type. -/
theorem ker_leftCosetAction_on_rightParabolic :
    (leftCosetAction.comp rightParabolic.subtype).ker = pCore 2 rightParabolic := by
  ext x
  change x.val ∈ leftCosetAction.ker ↔ x ∈ pCore 2 rightParabolic
  rw [ker_leftCosetAction, mem_right_twoCore]
  simp only [Subgroup.mem_prod, Subgroup.mem_top, Subgroup.mem_bot, and_true]

end SymmetricThreeProduct
