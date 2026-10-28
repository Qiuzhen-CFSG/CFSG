module
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.Actions
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupAction.OddCommutatorImage

/-!
# Actual actions on the symplectic Borel torus

An automorphism stabilizing the standard unipotent subgroup stabilizes its
normalizer and the normalizer's two-residual. Restriction and passage to the
two-core quotient give a homomorphism from the full stabilizer to the actual
rank-two torus automorphism group. Surjectivity of the residual characters
identifies the source three-residual fixer and realizes every torus displacement
in the cyclic action commutator, giving the required quotient lower bound.
No involution reduction or equality of the residual with the Borel is used.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ActorReduction
variable {F : Type*} [Field F] [Finite F]

abbrev stabilizer : Subgroup (MulAut (Sp F)) :=
  MulAction.stabilizer (MulAut (Sp F)) (unipotent (F := F))

omit [Finite F] in
theorem map_borel (a : stabilizer (F := F)) :
    borel.map a.val.toMonoidHom = borel := by
  have h : unipotent.map a.val.toMonoidHom = unipotent := a.property
  rw [borel_eq_normalizer_unipotent, map_equiv_normalizer_eq, h]

theorem map_residual (a : stabilizer (F := F)) :
    residual.map a.val.toMonoidHom = residual := by
  rw [residual, map_embedded_pResidual, map_borel]

def borelAction : stabilizer (F := F) →* MulAut (borel (F := F)) where
  toFun a := DiagramAutomorphisms.restrict a.val borel (map_borel a)
  map_one' := by ext b; rfl
  map_mul' a b := by ext x; rfl

def torusAction {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    stabilizer (F := F) →* MulAut (Fˣ × Fˣ) :=
  (MulAut.congr (quotientTorusEquiv hF)).toMonoidHom.comp
    ((pCore 2 (borel (F := F))).quotientAut.comp borelAction)

theorem quotientTorusEquiv_mk {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (b : borel (F := F)) :
    quotientTorusEquiv hF (QuotientGroup.mk' _ b) = borelCharacters b := rfl

theorem torusAction_characters {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (a : stabilizer (F := F)) (b : borel (F := F)) :
    torusAction hF a (borelCharacters b) = borelCharacters (borelAction a b) := by
  rw [← quotientTorusEquiv_mk hF b]
  change quotientTorusEquiv hF
    ((pCore 2 (borel (F := F))).quotientAut (borelAction a)
      ((quotientTorusEquiv hF).symm (quotientTorusEquiv hF (QuotientGroup.mk' _ b)))) = _
  rw [MulEquiv.symm_apply_apply, quotientAut_apply_mk, quotientTorusEquiv_mk]

theorem residualAction_characters {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (a : stabilizer (F := F)) (b : residual (F := F)) :
    charactersOn residual_le_borel
      (DiagramAutomorphisms.restrict a.val residual (map_residual a) b) =
      torusAction hF a (charactersOn residual_le_borel b) :=
  (torusAction_characters hF a (inclusion residual_le_borel b)).symm

theorem displacement_mem_core_iff {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (a : stabilizer (F := F)) (b : residual (F := F)) :
    b.val⁻¹ * a.val b.val ∈ residual.pCoreIn 2 ↔
      torusAction hF a (charactersOn residual_le_borel b) =
        charactersOn residual_le_borel b := by
  let aB := DiagramAutomorphisms.restrict a.val residual (map_residual a)
  change residual.subtype (b⁻¹ * aB b) ∈ (pCore 2 residual).map residual.subtype ↔ _
  rw [mem_map_iff_mem Subtype.val_injective, ← charactersOn_ker_eq_twoCore hF residual_le_borel,
    MonoidHom.mem_ker, map_mul, map_inv]
  change (charactersOn residual_le_borel b)⁻¹ *
    charactersOn residual_le_borel (aB b) = 1 ↔ _
  rw [inv_mul_eq_one, residualAction_characters hF a b]
  exact eq_comm

/-- The source's concrete residual fixer is the fixer of the torus three-residual. -/
theorem fixes_residual_iff {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (a : stabilizer (F := F)) :
    (∀ b ∈ (pResidual 3 (residual (F := F))).map residual.subtype ⊔ residual.pCoreIn 2,
      b⁻¹ * a.val b ∈ residual.pCoreIn 2) ↔
    ∀ x ∈ pResidual 3 (Fˣ × Fˣ), torusAction hF a x = x := by
  let f := charactersOn (residual_le_borel (F := F))
  have hr : (pResidual 3 residual).map f = pResidual 3 (Fˣ × Fˣ) :=
    map_pResidual_of_surjective 3 f (residual_characters_surjective hF)
  have hk : (pCore 2 residual).map f = ⊥ := by
    rw [← charactersOn_ker_eq_twoCore hF residual_le_borel]
    exact (Subgroup.map_eq_bot_iff f.ker).mpr le_rfl
  constructor
  · intro h x hx
    obtain ⟨b, hb, rfl⟩ := hr.ge hx
    exact (displacement_mem_core_iff hF a b).mp
      (h b (Subgroup.mem_sup_left (mem_map_of_mem residual.subtype hb)))
  · intro h b hb
    rw [pCoreIn, ← Subgroup.map_sup] at hb
    obtain ⟨b, hb, rfl⟩ := hb
    apply (displacement_mem_core_iff hF a b).mpr
    apply h
    have hx := mem_map_of_mem f hb
    rwa [Subgroup.map_sup, hr, hk, sup_bot_eq] at hx

/-- Generator displacements in the full residual realize the computed torus image. -/
theorem displacement_card_le {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (a : stabilizer (F := F)) :
    Nat.card (torusDisplacement (torusAction hF a)).range ≤
      Nat.card (commutatorSubgroup (zpowers a.val) (Sp F) residual ⧸
        pCore 2 (commutatorSubgroup (zpowers a.val) (Sp F) residual)) := by
  apply Theory.GroupAction.OddCommutatorImage.card_le_cyclic_commutator_quotient
    residual a.val (map_residual a) (charactersOn residual_le_borel)
    (Nat.coprime_two_left.mp (torus_odd hF)) (torusDisplacement (torusAction hF a))
  intro x
  obtain ⟨b, rfl⟩ := residual_characters_surjective hF x
  refine ⟨b, ?_⟩
  let aB := DiagramAutomorphisms.restrict a.val residual (map_residual a)
  change torusAction hF a (charactersOn residual_le_borel b) *
      (charactersOn residual_le_borel b)⁻¹ =
    charactersOn residual_le_borel (b⁻¹ * aB b)
  rw [map_mul, map_inv, residualAction_characters hF a b, mul_comm]

end Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ActorReduction
