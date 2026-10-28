module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.FixedSpace
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.StructureInput
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.PPrimeCore

/-!
# The internal product conclusion of B.1.12

The index set is the set of distinct T-conjugates, so there is no repeated
factor. `ThreeConjugatesConclusion` is conclusion data, not an existence
theorem or an extra source hypothesis. Its constructor must be supplied by
the remaining factor argument.

The two product equivalences respect subgroup inclusions. The quotient is
literally M/O₂(M), and each factor's odd core is the image of the prescribed
conjugate of K. The T-action is induced by conjugation on M and then passed
through its characteristic two-core; equivariance and transitivity refer to
this actual action. SL₂(2) is the faithful matrix model of L₂(2).

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.1.12, printed p. 73 (PDF p. 84).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ThreeConjugates
open Subgroup Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Every member of the distinct-conjugate family belongs to its generated subgroup. -/
theorem conjugate_le_closure (K T : Subgroup G) (i : conjugateFamily K T) :
    (i : Subgroup G) ≤ conjugateClosure K T := by
  obtain ⟨t, ht⟩ := i.property
  rw [← ht]
  exact le_iSup (fun t : T => K.map (MulAut.conj (t : G)).toMonoidHom) t

/-- Conjugation by T on the actual subgroup M. -/
noncomputable def mixedConjugation (K T : Subgroup G) : T →* MulAut (mixedSubgroup ρ K T) :=
  (mixedSubgroup ρ K T).normalizerMonoidHom.comp
    (inclusion ((show T ≤ K ⊔ T from le_sup_right).trans
      (le_normalizer_mixedSubgroup ρ K T)))

/-- The induced T-action on M/O₂(M). -/
noncomputable def mixedQuotientAction (K T : Subgroup G) :
    T →* MulAut (mixedSubgroup ρ K T ⧸ pCore 2 (mixedSubgroup ρ K T)) :=
  (quotientAut (pCore 2 (mixedSubgroup ρ K T))).comp (mixedConjugation ρ K T)

@[simp] theorem mixedQuotientAction_mk (K T : Subgroup G) (t : T) (m : mixedSubgroup ρ K T) :
    mixedQuotientAction ρ K T t (QuotientGroup.mk' (pCore 2 (mixedSubgroup ρ K T)) m) =
      QuotientGroup.mk' (pCore 2 (mixedSubgroup ρ K T)) (mixedConjugation ρ K T t m) :=
  quotientAut_apply_mk _ _ _

@[simp] theorem mixedConjugation_apply (K T : Subgroup G) (t : T) (m : mixedSubgroup ρ K T) :
    (mixedConjugation ρ K T t m : G) = (t : G) * (m : G) * (t : G)⁻¹ := rfl

/-- The correctly typed image of a conjugate of K in M/O₂(M). -/
noncomputable def quotientConjugate (K T : Subgroup G) (i : conjugateFamily K T) :
    Subgroup (mixedSubgroup ρ K T ⧸ pCore 2 (mixedSubgroup ρ K T)) :=
  ((i : Subgroup G).subgroupOf (mixedSubgroup ρ K T)).map
    (QuotientGroup.mk' (pCore 2 (mixedSubgroup ρ K T)))

/-- Full conclusion data for B.1.12. No inhabitant is asserted here. The
single-coordinate clauses express compatibility with the actual inclusions. -/
structure ThreeConjugatesConclusion (K T : Subgroup G) where
  groupProduct : ((i : conjugateFamily K T) → (i : Subgroup G)) ≃* conjugateClosure K T
  groupProduct_single : letI := Classical.decEq (conjugateFamily K T)
    ∀ (i : conjugateFamily K T) (k : (i : Subgroup G)),
      (groupProduct (Pi.mulSingle i k) : G) = (k : G)
  quotientFactor : conjugateFamily K T →
    Subgroup (mixedSubgroup ρ K T ⧸ pCore 2 (mixedSubgroup ρ K T))
  quotientProduct : ((i : conjugateFamily K T) → quotientFactor i) ≃*
    (mixedSubgroup ρ K T ⧸ pCore 2 (mixedSubgroup ρ K T))
  quotientProduct_single : letI := Classical.decEq (conjugateFamily K T)
    ∀ (i : conjugateFamily K T) (g : quotientFactor i),
      quotientProduct (Pi.mulSingle i g) = g
  factorModel : ∀ i, quotientFactor i ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
  oddCore : ∀ i, (pPrimeCore 2 (quotientFactor i)).map (quotientFactor i).subtype =
    quotientConjugate ρ K T i
  equivariant : ∀ (t : T) (i j : conjugateFamily K T),
    (i : Subgroup G).map (MulAut.conj (t : G)).toMonoidHom = (j : Subgroup G) →
      (quotientFactor i).map (mixedQuotientAction ρ K T t).toMonoidHom = quotientFactor j
  transitive : ∀ i j, ∃ t : T,
    (quotientFactor i).map (mixedQuotientAction ρ K T t).toMonoidHom = quotientFactor j

end CFSG.Quasithin.ChapterB.ThreeConjugates
