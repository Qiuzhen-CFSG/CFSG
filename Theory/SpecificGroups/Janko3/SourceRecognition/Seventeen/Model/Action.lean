module
public import Theory.SpecificGroups.PSL2.BinaryFourFieldExtension
public import BenderSuzuki.Converse.PSL2
public import Theory.GroupAction.MaximalCosetOrbit

/-!
# The actual seventeen-point model action and its stabilizers

Entrywise field transport acts semilinearly on the genuine projective line.
Its compatibility with the matrix action defines the action of the extension
by fourth-power Frobenius. Faithfulness follows because a field automorphism
inducing an inner projective automorphism is trivial.

The point and pair groups are the literal stabilizers of infinity and of
{infinity, zero}. They generate the extension, have orders 480 and 60, and
intersect in a subgroup of order 30 consisting of diagonal matrices and the
field actor. The distinguished field involution lies in this intersection.
The abstract types of these subgroups remain to be identified separately.

Source: Baumeister, *A geometry for groups of J₃-type* (2007), p.498,
the model amalgam preceding Lemma 2.9 and Corollary 2.10.
-/

@[expose] public noncomputable section
open Subgroup MulAction Matrix Projectivization
open scoped Pointwise
open BenderSuzuki.Converse
open Theory.PSL2
open Theory.PSL2.BinaryFourFieldExtension
namespace Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam
abbrev F := BinaryField 4
abbrev Points := P1 F

def fieldVector (σ : F ≃+* F) : (Fin 2 → F) →ₛₗ[σ.toRingHom] (Fin 2 → F) where
  toFun v i := σ (v i)
  map_add' v w := funext fun i => σ.map_add (v i) (w i)
  map_smul' a v := funext fun i => σ.map_mul a (v i)

theorem fieldVector_injective (σ : F ≃+* F) : Function.Injective (fieldVector σ) := by
  intro v w h
  exact funext fun i => σ.injective (congrFun h i)

def fieldPoint (σ : F ≃+* F) : Points → Points :=
  Projectivization.map (fieldVector σ) (fieldVector_injective σ)

theorem fieldPoint_mk (σ : F ≃+* F) (v : Fin 2 → F) (hv : v ≠ 0) :
    fieldPoint σ (mk F v hv) = mk F (fieldVector σ v)
      (map_zero (fieldVector σ) ▸ (fieldVector_injective σ).ne hv) := rfl

theorem fieldPoint_mul (σ τ : F ≃+* F) (p : Points) :
    fieldPoint (σ * τ) p = fieldPoint σ (fieldPoint τ p) := by
  induction p using Projectivization.ind with
  | h v hv => rfl

theorem fieldPoint_one (p : Points) : fieldPoint 1 p = p := by
  induction p using Projectivization.ind with
  | h v hv => rfl

def fieldPerm (σ : F ≃+* F) : Equiv.Perm Points where
  toFun := fieldPoint σ
  invFun := fieldPoint σ⁻¹
  left_inv p := by rw [← fieldPoint_mul, inv_mul_cancel, fieldPoint_one]
  right_inv p := by rw [← fieldPoint_mul, mul_inv_cancel, fieldPoint_one]

def fieldPermHom : (F ≃+* F) →* Equiv.Perm Points where
  toFun := fieldPerm
  map_one' := Equiv.ext fieldPoint_one
  map_mul' σ τ := Equiv.ext (fieldPoint_mul σ τ)

theorem fieldPoint_sl2 (σ : F ≃+* F) (g : SL2 F) (p : Points) :
    fieldPoint σ (g • p) = sl2FieldAut σ g • fieldPoint σ p := by
  induction p using Projectivization.ind with
  | h v hv =>
    simp only [smul_mk, fieldPoint_mk]
    rw [Projectivization.mk_eq_mk_iff']
    refine ⟨1, ?_⟩
    rw [one_smul]
    ext i
    change (∑ j : Fin 2, σ (g.val i j) * σ (v j)) = σ (∑ j : Fin 2, g.val i j * v j)
    simp only [map_sum, map_mul]

theorem fieldPoint_psl2 (σ : F ≃+* F) (g : BinaryGroup 4) (p : Points) :
    fieldPoint σ (g • p) = fieldAut σ g • fieldPoint σ p := by
  obtain ⟨g, rfl⟩ := quotientMap_surjective F g
  rw [fieldAut_apply_quotientMap]
  exact fieldPoint_sl2 σ g p

def permutation : Model →* Equiv.Perm Points :=
  SemidirectProduct.lift (toPermHom (BinaryGroup 4) Points)
    (fieldPermHom.comp Actor.subtype) (by
      intro a
      apply MonoidHom.ext
      intro g
      apply Equiv.ext
      intro p
      change fieldAut a.val g • p =
        fieldPoint a.val (g • fieldPoint a.val⁻¹ p)
      rw [fieldPoint_psl2, ← fieldPoint_mul, mul_inv_cancel, fieldPoint_one])

theorem permutation_apply (x : Model) (p : Points) :
    permutation x p = x.left • fieldPoint x.right.val p := rfl

theorem permutation_inl (g : BinaryGroup 4) :
    permutation (linearInclusion g) = toPermHom (BinaryGroup 4) Points g :=
  SemidirectProduct.lift_inl _ _ _ g

theorem permutation_inr (a : Actor) :
    permutation (SemidirectProduct.inr a) = fieldPerm a.val :=
  SemidirectProduct.lift_inr _ _ _ a

theorem permutation_injective : Function.Injective permutation := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have hxperm : permutation x = 1 := hx
  have hfield : fieldAut x.right.val = MulAut.conj x.left⁻¹ := by
    ext g
    apply MulAction.toPerm_injective (β := Points)
    apply Equiv.ext
    intro p
    have he : ∀ q : Points, fieldPoint x.right.val q = x.left⁻¹ • q := by
      intro q
      have hq := Equiv.congr_fun hxperm q
      change x.left • fieldPoint x.right.val q = q at hq
      exact (eq_inv_smul_iff.mpr hq)
    have hcov := fieldPoint_psl2 x.right.val g (x.left • p)
    rw [he, he, inv_smul_smul] at hcov
    simpa only [MulAction.toPerm_apply, MulAut.conj_apply, inv_inv, mul_smul] using hcov.symm
  have ha : x.right = 1 := Subtype.ext
    (fieldAut_eq_conj_implies_refl x.right.val x.left⁻¹ hfield)
  have hg : x.left = 1 := by
    apply MulAction.toPerm_injective (β := Points)
    apply Equiv.ext
    intro p
    have hp := Equiv.congr_fun hxperm p
    change x.left • fieldPoint x.right.val p = p at hp
    simpa only [MulAction.toPerm_apply, one_smul, ha, Subgroup.coe_one, fieldPoint_one] using hp
  exact SemidirectProduct.ext hg ha

def point : Subgroup Model := (stabilizer (Equiv.Perm Points) (pInf F)).comap permutation

def pair : Subgroup Model :=
  (stabilizer (Equiv.Perm Points) ({pInf F, pZero F} : Set Points)).comap permutation

theorem fieldPoint_inf (σ : F ≃+* F) : fieldPoint σ (pInf F) = pInf F := by
  change mk F (fieldVector σ ![1, 0]) _ = mk F ![1, 0] _
  have h : fieldVector σ ![1, 0] = ![1, 0] := by
    ext i
    change σ ((![1, 0] : Fin 2 → F) i) = (![1, 0] : Fin 2 → F) i
    fin_cases i <;> simp
  simp only [h]

theorem fieldPoint_zero (σ : F ≃+* F) : fieldPoint σ (pZero F) = pZero F := by
  change mk F (fieldVector σ ![0, 1]) _ = mk F ![0, 1] _
  have h : fieldVector σ ![0, 1] = ![0, 1] := by
    ext i
    change σ ((![0, 1] : Fin 2 → F) i) = (![0, 1] : Fin 2 → F) i
    fin_cases i <;> simp
  simp only [h]

theorem mem_point (x : Model) : x ∈ point ↔ x.left ∈ PBorel F := by
  change permutation x (pInf F) = pInf F ↔ x.left • pInf F = pInf F
  rw [permutation_apply, fieldPoint_inf]

theorem involution_mem_overlap : involution ∈ point ⊓ pair := by
  constructor
  · change involution ∈ point
    rw [mem_point]
    exact (PBorel F).one_mem
  · change permutation involution • ({pInf F, pZero F} : Set Points) = _
    rw [Set.smul_set_insert, Set.smul_set_singleton]
    change {permutation involution (pInf F), permutation involution (pZero F)} = _
    simp only [permutation_apply, involution, SemidirectProduct.left_inr,
      SemidirectProduct.right_inr, fieldPoint_inf, fieldPoint_zero, one_smul]

instance : MulAction Model Points := MulAction.compHom Points permutation

theorem model_smul (x : Model) (p : Points) :
    x • p = x.left • fieldPoint x.right.val p := rfl

instance : FaithfulSMul Model Points := by
  apply faithfulSMul_iff.mpr
  intro g h
  apply permutation_injective
  apply Equiv.ext
  intro p
  change g • p = (permutation 1) p
  rw [map_one]
  exact h p

instance : IsMultiplyPretransitive Model Points 2 := by
  apply is_two_pretransitive_iff.mpr
  intro a b c d hab hcd
  obtain ⟨g, hg, hg'⟩ := (is_two_pretransitive_iff.mp
    (inferInstance : IsMultiplyPretransitive (BinaryGroup 4) Points 2)) hab hcd
  exact ⟨linearInclusion g, by
    change permutation (linearInclusion g) a = c
    rw [permutation_inl]
    exact hg, by
    change permutation (linearInclusion g) b = d
    rw [permutation_inl]
    exact hg'⟩

theorem points_card : Nat.card Points = 17 := by
  rw [Projectivization.card_of_finrank_two F (Fin 2 → F) (by simp), field_card]

instance : Nontrivial Points := Finite.one_lt_card_iff_nontrivial.mp (by
  rw [points_card]
  decide)

instance : Finite Model := Nat.finite_of_card_ne_zero (by rw [model_card]; decide)

instance : IsPretransitive Model Points := by
  constructor
  intro p q
  obtain ⟨g, hg⟩ := exists_smul_eq (BinaryGroup 4) p q
  refine ⟨linearInclusion g, ?_⟩
  change permutation (linearInclusion g) p = q
  rw [permutation_inl]
  exact hg

theorem point_eq_stabilizer : point = stabilizer Model (pInf F) := rfl

theorem pair_eq_stabilizer : pair = stabilizer Model ({pInf F, pZero F} : Set Points) := rfl

theorem point_card : Nat.card point = 480 := by
  have hi : point.index = 17 := by
    rw [point_eq_stabilizer, index_stabilizer_of_transitive, points_card]
  have hc := point.card_mul_index
  rw [hi, model_card] at hc
  omega

def swap : Model := linearInclusion (PWeyl F)

theorem swap_inf : swap • pInf F = pZero F := by
  change permutation (linearInclusion (PWeyl F)) (pInf F) = pZero F
  rw [permutation_inl]
  exact PWeyl_smul_pInf

theorem swap_square : swap * swap = 1 := by
  change linearInclusion (PWeyl F) * linearInclusion (PWeyl F) = 1
  rw [← map_mul]
  have hw : PWeyl F * PWeyl F = 1 := by
    change pi F (weyl F) * pi F (weyl F) = 1
    rw [← map_mul, weyl_sq, map_one]
  rw [hw, map_one]

theorem swap_zero : swap • pZero F = pInf F := by
  rw [← swap_inf, ← mul_smul, swap_square, one_smul]

theorem pair_generated : pair =
    (stabilizer Model (pInf F) ⊓ stabilizer Model (pZero F)) ⊔ zpowers swap := by
  rw [pair_eq_stabilizer]
  exact stabilizer_pair_eq_sup swap_inf swap_zero

theorem swap_mem_pair : swap ∈ pair := by
  rw [pair_generated]
  exact (show zpowers swap ≤ _ from le_sup_right) (mem_zpowers _)

theorem generated : point ⊔ pair = ⊤ := by
  let Q := (point ⊔ pair).comap linearInclusion
  have hB : PBorel F ≤ Q := by
    intro g hg
    apply (show point ≤ point ⊔ pair from le_sup_left)
    exact (mem_point _).mpr hg
  have hw : PWeyl F ∈ Q := (show pair ≤ point ⊔ pair from le_sup_right) swap_mem_pair
  have hm : IsCoatom (PBorel F) :=
    IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (BinaryGroup 4) (pInf F)
  have hQ : Q = ⊤ := hm.2 Q (lt_of_le_of_ne hB (by
    intro he
    exact PWeyl_notMem_PBorel (he.symm ▸ hw)))
  apply top_unique
  intro x _
  rw [← SemidirectProduct.inl_left_mul_inr_right x]
  apply Subgroup.mul_mem
  · exact (show x.left ∈ Q from hQ ▸ mem_top _)
  · apply (show point ≤ point ⊔ pair from le_sup_left)
    rw [mem_point]
    exact (PBorel F).one_mem

/-- The two distinguished projective points are distinct. -/
theorem inf_ne_zero : pInf F ≠ pZero F := by
  intro h
  apply PWeyl_notMem_PBorel (F := F)
  change PWeyl F • pInf F = pInf F
  exact PWeyl_smul_pInf.trans h.symm

theorem mem_pair (x : Model) : x ∈ pair ↔
    (x.left • pInf F = pInf F ∧ x.left • pZero F = pZero F) ∨
    (x.left • pInf F = pZero F ∧ x.left • pZero F = pInf F) := by
  change permutation x • ({pInf F, pZero F} : Set Points) = _ ↔ _
  rw [Set.smul_set_insert, Set.smul_set_singleton, Set.pair_eq_pair_iff]
  change (permutation x (pInf F) = pInf F ∧ permutation x (pZero F) = pZero F) ∨
    (permutation x (pInf F) = pZero F ∧ permutation x (pZero F) = pInf F) ↔ _
  rw [permutation_apply, permutation_apply, fieldPoint_inf, fieldPoint_zero]

theorem mem_overlap (x : Model) : x ∈ point ⊓ pair ↔ x.left ∈ PTorus F := by
  change x ∈ point ∧ x ∈ pair ↔ _
  rw [mem_point, mem_pair, PTorus_eq]
  change (x.left • pInf F = pInf F) ∧ _ ↔
    (x.left • pInf F = pInf F) ∧ (x.left • pZero F = pZero F)
  constructor
  · rintro ⟨hp, h | h⟩
    · exact h
    · exact False.elim (inf_ne_zero (hp.symm.trans h.1))
  · intro h
    exact ⟨h.1, Or.inl h⟩

def overlapSetEquiv : (point ⊓ pair : Subgroup Model) ≃ (PTorus F × Actor) where
  toFun x := (⟨x.val.left, (mem_overlap x.val).mp x.property⟩, x.val.right)
  invFun x := ⟨⟨x.1, x.2⟩, (mem_overlap _).mpr x.1.property⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

theorem overlap_card : Nat.card (point ⊓ pair : Subgroup Model) = 30 := by
  rw [Nat.card_congr overlapSetEquiv, Nat.card_prod, PTorus_card,
    Nat.card_units, field_card, Nat.card_zpowers, fieldInvolution_order]

theorem pair_orbit : orbit pair (pInf F) = ({pInf F, pZero F} : Set Points) := by
  ext p
  constructor
  · rintro ⟨g, rfl⟩
    rcases (mem_pair g.val).mp g.property with h | h
    · change g.val • pInf F ∈ _
      rw [model_smul, fieldPoint_inf, h.1]
      exact Set.mem_insert _ _
    · change g.val • pInf F ∈ _
      rw [model_smul, fieldPoint_inf, h.1]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  · intro hp
    rcases hp with h | h
    · subst p
      exact mem_orbit_self _
    · have hp' : p = pZero F := h
      subst p
      exact ⟨⟨swap, swap_mem_pair⟩, swap_inf⟩

theorem pair_card : Nat.card pair = 60 := by
  have horb : Nat.card (orbit pair (pInf F)) = 2 := by
    rw [pair_orbit]
    exact Set.ncard_pair inf_ne_zero
  have hstab : stabilizer pair (pInf F) = point.subgroupOf pair := rfl
  have he : point.subgroupOf pair = (point ⊓ pair).subgroupOf pair := by
    ext x
    exact ⟨fun h => ⟨h, x.property⟩, fun h => h.1⟩
  have hc := Nat.card_congr (orbitProdStabilizerEquivGroup pair (pInf F))
  rw [Nat.card_prod, horb, hstab, he,
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : point ⊓ pair ≤ pair)).toEquiv] at hc
  rw [overlap_card] at hc
  omega

end Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam
