module
public import GorensteinWalter.Classification
public import Theory.PPrimeCore

/-!
# Source-stage characteristic powers

ABG II.3 Definitions 1 and 2 (article p23) attach an odd field order to
an actual characteristic SL2 subgroup of the odd-core quotient of a Q-group,
and then to an involution centralizer in a QD-group. The predicates record
these data; the Q/QD and Sylow-shape domain hypotheses are imposed by their
existence theorems. This also permits the extension to Q-subgroups made in
Lemma 2 without changing the data being recorded.

The QD predicate chooses an involution, as in the source definition.
Independence of that choice and uniqueness of the order are proved later,
not built into these predicates. Neither predicate assumes the final
GL2/GU2 centralizer model of the main theorems.

Isomorphisms transport the actual odd core and its quotient. Mapping a
characteristic subgroup through the quotient equivalence preserves its
characteristic property and SL2 model, proving the transport theorem used
for conjugate involution centralizers. The characteristic-subgroup transport
is also public for the odd-core idempotence step in source Lemma 1.
-/

namespace ABG
universe u

/-- The characteristic SL2 constituent datum of the source Q-group definition. -/
@[expose] public def HasSourceQCharacteristicPower (G : Type u) [Group G] (q : ℕ) : Prop :=
  ∃ (F : Type u) (instF : Field F) (_ : Finite F),
    let : Field F := instF
    GorensteinWalter.IsOddPrimePower (Nat.card F) ∧ Nat.card F = q ∧
      ∃ L : Subgroup (G ⧸ pPrimeCore 2 G), L.Characteristic ∧
        Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) F)

/-- The source-stage characteristic power, chosen through an involution centralizer. -/
@[expose] public def HasSourceCharacteristicPower (G : Type u) [Group G] (q : ℕ) : Prop :=
  ∃ x : G, orderOf x = 2 ∧ HasSourceQCharacteristicPower (Subgroup.centralizer {x}) q

/-- A group isomorphism preserves characteristicity of the actual subgroup image. -/
public theorem characteristic_map_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (L : Subgroup G) (hL : L.Characteristic) :
    (L.map e.toMonoidHom).Characteristic := by
  apply Subgroup.characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨e.symm (a (e y)), ?_, e.apply_symm_apply _⟩
  exact Subgroup.characteristic_iff_le_comap.mp hL (e.trans (a.trans e.symm)) hy

/-- The characteristic constituent datum is invariant under group isomorphism. -/
public theorem HasSourceQCharacteristicPower.mulEquiv
    {G H : Type u} [Group G] [Group H] {q : ℕ}
    (h : HasSourceQCharacteristicPower G q) (e : G ≃* H) :
    HasSourceQCharacteristicPower H q := by
  obtain ⟨F, iF, fF, hF, hq, L, hL, ⟨eL⟩⟩ := h
  let : Field F := iF
  let : Finite F := fF
  let eQ : (G ⧸ pPrimeCore 2 G) ≃* (H ⧸ pPrimeCore 2 H) :=
    QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)
  exact ⟨F, iF, fF, hF, hq, L.map eQ.toMonoidHom,
    characteristic_map_equiv eQ L hL,
    ⟨(Subgroup.equivMapOfInjective L eQ.toMonoidHom eQ.injective).symm.trans eL⟩⟩

end ABG
