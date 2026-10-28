module

public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import CFSG.Quasithin.ChapterB.Section01.Restriction
public import Theory.Representation.BinaryOffender.SectionOffender

/-!
# B.1.5(8): quasisimple invariant sections

Let `L = F*(G)` be quasisimple, with `O₂(G) = 1`, and let the best offender
`A` act on a genuine `G`-invariant section `S = W/U` on which `L` acts
nontrivially. The section is the literal quotient of the invariant subspace
`W` by the comap of `U`; its representation is induced by the original action.
`actionImage` is `Aut_G(S)`, and `actionSubgroup` is the actual image `Aut_A(S)`.
Their tautological representation is faithful, and `actionQuotientEquiv`
identifies the image with the quotient by the actual relative action kernel.

The group argument proves `C_G(S) ≤ Z(L)`, faithfulness of `A` on `S`, and
`[L,A] = L`. Fixed-codimension comparisons then give an offender on the section.
At quadratic ratio one, Thompson replacement excludes strong offenders; the
equalities force `A` to centralize `U` and `V/W`, and give `W + C_V(A) = V`.
Commutator generation promotes both centralization conclusions to `A ⊔ L`.
Since `L` is normal, this join is the source's product `AL`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, B.1.5(8), printed pp. 69–70 (PDF pp. 80–81).
This argument does not use B.7.2 or irreducible-section invariance.
-/

public section

namespace CFSG.Quasithin.ChapterB
open Representation.BinaryOffender Theory.GroupTheory
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Source B.1.5(8), including faithfulness, the actual image isomorphism,
existence of a best offender in that image, and every clause of the `q = 1` case. -/
theorem source_lemma_B_1_5_8 (_hfaithful : Function.Injective ρ)
    {A : Subgroup G} (hA : IsBestOffender ρ A)
    (hL : IsQuasisimple (generalizedFitting G)) (hcore : pCore 2 G = ⊥)
    {U W : Subrepresentation ρ} (hUW : U ≤ W)
    (hmove : subspaceCommutator (sectionRepresentation ρ U W) ⊤
      (generalizedFitting G) ≠ ⊥) :
    (∀ a ∈ A, (∀ s, sectionRepresentation ρ U W a s = s) → a = 1) ∧
    Nonempty (A ≃* actionSubgroup (sectionRepresentation ρ U W) A) ∧
    (∃ B ≤ actionSubgroup (sectionRepresentation ρ U W) A,
      IsBestOffender (imageRepresentation (sectionRepresentation ρ U W)) B) ∧
    (quadraticRatio (imageRepresentation (sectionRepresentation ρ U W)) = 1 →
      IsBestOffender (imageRepresentation (sectionRepresentation ρ U W))
          (actionSubgroup (sectionRepresentation ρ U W) A) ∧
        U.toSubmodule ≤ fixedSpace ρ (A ⊔ generalizedFitting G) ∧
        (∀ g ∈ A ⊔ generalizedFitting G, ∀ v, W.quotientRepresentation g v = v) ∧
        W.toSubmodule ⊔ fixedSpace ρ A = ⊤) := by
  let σ := sectionRepresentation ρ U W
  have hnontriv : ¬ generalizedFitting G ≤ (actionHom σ).ker := by
    intro hk
    apply hmove
    apply (subspaceCommutator_eq_bot_iff σ ⊤ (generalizedFitting G)).mpr
    intro s _ l
    exact (actionHom_eq_one_iff σ l).mp (hk l.property) s
  let _ : IsElementaryAbelian 2 A := hA.1.2
  have hp : IsPGroup 2 A := IsElementaryAbelian.isPGroup 2 A
  have hfaithS : ∀ a ∈ A, (∀ s, σ a s = s) → a = 1 := by
    intro a ha hs
    exact QuasisimpleSections.faithful_on_nontrivial_fitting_image hcore hL
      (actionHom σ) hnontriv hp a ha ((actionHom_eq_one_iff σ a).mpr hs)
  have hcomm := QuasisimpleSections.commutator_fitting_eq hcore hL hA.1.1 hp
  exact ⟨hfaithS, ⟨faithfulActionEquiv σ A hfaithS⟩,
    hA.section_contains_bestOffender ρ U W hfaithS,
    fun hq => hA.section_equality_sup ρ hUW hfaithS hcomm hq⟩

end CFSG.Quasithin.ChapterB
