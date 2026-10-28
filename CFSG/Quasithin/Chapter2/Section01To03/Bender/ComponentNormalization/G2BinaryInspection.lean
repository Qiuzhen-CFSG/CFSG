module

public import Theory.SpecificGroups.G2.BinaryMarkedStrongClosure
public import Theory.AtlasPort.LinearGroups.G2.FieldTransport
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.MarkedQuotient
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Excluding the actual derived binary G₂ component in the Bender inspection

The marked-pair theorem is internal to the literal group G₂(2)′. Applying
the marked-quotient adapter excludes any permitted component whose actual
quotient L/O₂(L) is this group. In source row (a), the supplied simplicity
and component perfectness give O₂(L)=1, so the original equivalence of L
itself supplies this quotient. A coefficientwise field transport also
handles any alternative field of order two. The final application keeps
the original involution centralizer, Sylow inclusions and distinguished z.

Source: Aschbacher--Smith 1.1.5(3)(a), Theorem C(3), Remark A.2.4 and
Proposition 2.2.2, printed pp.33, 501--503 and 519--520
(combined 1 March 2004 manuscript).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

/-- The marked quotient obstruction for the actual commutator subgroup
of G₂(2), with every source-permitted central two-kernel allowed. -/
theorem LocalControlWitness.false_of_inner_g2_binary_twoCore_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  apply w.false_of_marked_twoCore_component H S hUS hST hcore L hL hLM e hinner
  intro R v hv ho hc
  exact Atlas.G2.BinaryMarkedStrongClosure.sylow_noncommuting_conjugates v
    ⟨ho, R, hv, fun x hx => mem_centralizer_singleton_iff.mpr (hc x hx).symm.eq⟩ R

/-- Source simplicity supplies the quotient of the original component;
no simplicity theorem for the octonion model is required. -/
theorem LocalControlWitness.false_of_inner_g2_binary_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (hsimple : IsSimpleGroup L)
    (e : L ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  let : IsQuasisimple L := hL.quasisimple
  let : IsSimpleGroup L := hsimple
  have hc : center L = ⊥ := center_eq_bot_of_simple_perfect
  have hp : pCore 2 L = ⊥ :=
    bot_unique ((IsQuasisimple.pCore_le_center 2).trans hc.le)
  let e' : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2)) :=
    ((QuotientGroup.quotientMulEquivOfEq hp).trans QuotientGroup.quotientBot).trans e
  exact w.false_of_inner_g2_binary_twoCore_component H S hUS hST hcore L hL hLM e' hinner

/-- The literal `g2_derived` alternative in the source Theorem C(3) list. -/
theorem LocalControlWitness.false_of_inner_g2_binary_model
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (hsimple : IsSimpleGroup L)
    (hm : Nonempty (L ≃* commutator (Atlas.G2.Model (ZMod 2))))
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  obtain ⟨e⟩ := hm
  exact w.false_of_inner_g2_binary_component H S hUS hST hcore L hL hLM hsimple e hinner

/-- Coefficientwise transport restricts to the actual commutator subgroups
when the source uses another carrier for the field of order two. -/
theorem LocalControlWitness.false_of_inner_g2_binary_field_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (hsimple : IsSimpleGroup L) (F : Type*) [Field F] [Finite F]
    (hF : Nat.card F = 2) (e : L ≃* commutator (Atlas.G2.Model F))
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  let E := Atlas.G2.fieldEquiv eF
  let eD : commutator (Atlas.G2.Model F) ≃* commutator (Atlas.G2.Model (ZMod 2)) :=
    (E.subgroupMap _).trans (MulEquiv.subgroupCongr (by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr E.surjective, ← commutator_def]))
  exact w.false_of_inner_g2_binary_component H S hUS hST hcore L hL hLM hsimple
    (e.trans eD) hinner

/-- Apply the exact source-model row to the selected component in C_G(u),
retaining its actual Sylow maps and the original inner action of z. -/
theorem LocalControlWitness.false_of_inner_g2_binary_centralizer_component
    (w : LocalControlWitness T M) (u : G)
    (S : Sylow 2 (centralizer ({u} : Set G)))
    (hUS : w.U ≤ (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype)
    (hST : (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 (centralizer ({u} : Set G)) = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L (centralizer ({u} : Set G)))
    (hLM : ¬L ≤ M) (hsimple : IsSimpleGroup L)
    (hm : Nonempty (L ≃* commutator (Atlas.G2.Model (ZMod 2))))
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False :=
  w.false_of_inner_g2_binary_model (centralizer ({u} : Set G)) S hUS hST
    hcore L hL hLM hsimple hm hinner

end CFSG.Quasithin.Chapter2.BenderFusion
