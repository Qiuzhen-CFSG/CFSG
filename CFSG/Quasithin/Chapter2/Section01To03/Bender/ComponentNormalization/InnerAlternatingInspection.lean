module

public import Theory.SpecificGroups.AlternatingSix.MarkedStrongClosure
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360
public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.MarkedQuotient

/-!
# Excluding the inner A₆ occurrence in the Bender inspection

The marked noncommuting Sylow pair in A₆ contradicts the returning-conjugate
consequence of abelian strong closure. The existing quotient adapter supplies
the actual component Sylow, central two-kernel and nontrivial quotient marker
from O(H)=1, L not contained in M, and the original inner action of z.

The simple A₆ consumer and the concrete PSp₄(2)′ and PSL₂(9) equivalences
supply the source row (a) applications. The final consumer uses the literal
centralizer C_G(u), its selected Sylow and its ambient embeddings. Source row
selection remains an earlier input; no fusion or returning-pair premise remains.

Source: Aschbacher--Smith 1.1.5(3)(a), pp.501--503, and Proposition 2.2.2,
pp.519--520 (combined 1 March 2004 manuscript). The original marker acts
innerly; the transposition action of row (c) is treated separately.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

/-- An A₆ quotient with the original inner marker is incompatible with
abelian strong closure, for every central two-kernel allowed by the source. -/
theorem LocalControlWitness.false_of_inner_alternatingSix_twoCore_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  apply w.false_of_marked_twoCore_component H S hUS hST hcore L hL hLM e hinner
  intro R v _ hv _
  exact AlternatingSix.ShadowLocal.sylow_noncommuting_conjugates R v hv

/-- Exclude the simple A₆ occurrence in source row (a). Simplicity of the
actual model makes its two-core trivial before applying the quotient result. -/
theorem LocalControlWitness.false_of_inner_alternatingSix_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (e : L ≃* alternatingGroup (Fin 6))
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  let : IsQuasisimple L := hL.quasisimple
  let : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup L := e.isSimpleGroup
  have hc : center L = ⊥ := center_eq_bot_of_simple_perfect
  have hp : pCore 2 L = ⊥ :=
    bot_unique ((IsQuasisimple.pCore_le_center 2).trans hc.le)
  let e' : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6) :=
    ((QuotientGroup.quotientMulEquivOfEq hp).trans QuotientGroup.quotientBot).trans e
  exact w.false_of_inner_alternatingSix_twoCore_component H S hUS hST hcore
    L hL hLM e' hinner

/-- The binary symplectic endpoint uses the literal commutator of PSp₄(2),
with the central quotient taken before the commutator subgroup. -/
theorem LocalControlWitness.false_of_inner_psp4_two_derived_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (e : L ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False :=
  w.false_of_inner_alternatingSix_component H S hUS hST hcore L hL hLM
    (e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)
    hinner

/-- The PSL₂(9) overlap is excluded through the existing concrete equivalence,
uniformly for every field of order nine. -/
theorem LocalControlWitness.false_of_inner_psl2_nine_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (F : Type*) [Field F] [Finite F] (hF : Nat.card F = 9)
    (e : L ≃* PSL(2,F))
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False :=
  w.false_of_inner_alternatingSix_component H S hUS hST hcore L hL hLM
    (e.trans (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hF)) hinner

/-- Apply the quotient exclusion to the actual bad-centralizer component
of Proposition 2.2.2, preserving its selected Sylow and the original z. -/
theorem LocalControlWitness.false_of_inner_alternatingSix_centralizer_component
    (w : LocalControlWitness T M) (u : G)
    (S : Sylow 2 (centralizer ({u} : Set G)))
    (hUS : w.U ≤ (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype)
    (hST : (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 (centralizer ({u} : Set G)) = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L (centralizer ({u} : Set G)))
    (hLM : ¬L ≤ M) (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False :=
  w.false_of_inner_alternatingSix_twoCore_component (centralizer ({u} : Set G))
    S hUS hST hcore L hL hLM e hinner

end CFSG.Quasithin.Chapter2.BenderFusion
