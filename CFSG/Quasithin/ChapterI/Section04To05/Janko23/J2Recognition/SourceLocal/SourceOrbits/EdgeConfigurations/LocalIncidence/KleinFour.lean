module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.EdgeConfigurations.Basic
public import Theory.SpecificGroups.Alternating.FourPairCore

/-!
# The embedded Klein four subgroup of an inner edge intersection

The subgroup E is the ambient image of O₂(F ∩ Fᵍ), not an abstract
four-group attached to the intersection. Its A₄ model identifies it with
the characteristic Klein four-group. The literal centralizer contains
X, Y, gY and every X-translate of gY. These are the inputs to the root
centralizer calculation in the inner branch of 47.6; no SL₂(3) join is
asserted by this module.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 47.6(1), p.264.
-/

@[expose] public section
open Subgroup MulAction
open scoped Pointwise
open Theory.GroupTheory.GraphUniquenessSystem
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations
variable {G : Type*} [Group G] [Finite G]

/-- The precise O₂ intersection used in the source proof, embedded in G. -/
def intersectionCore (D : Seed G) (Y : D.Vertex) (g : G) : Subgroup G :=
  (intersection D Y g).pCoreIn 2

theorem intersectionCore_le (D : Seed G) (Y : D.Vertex) (g : G) :
    intersectionCore D Y g ≤ intersection D Y g := pCoreIn_le 2 _

/-- The equivalence is induced by the given actual intersection model. -/
noncomputable def intersectionCoreEquiv (D : Seed G) (Y : D.Vertex) (g : G)
    (e : intersection D Y g ≃* alternatingGroup (Fin 4)) :
    intersectionCore D Y g ≃* alternatingGroup.kleinFour (Fin 4) :=
  ((pCore 2 (intersection D Y g)).equivMapOfInjective
    (intersection D Y g).subtype (intersection D Y g).subtype_injective).symm.trans
    (((pCore 2 (intersection D Y g)).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (by rw [pCore_map_iso, AlternatingFourPair.twoCore_eq_kleinFour])))

theorem intersectionCore_isKleinFour (D : Seed G) (Y : D.Vertex) (g : G)
    (e : intersection D Y g ≃* alternatingGroup (Fin 4)) :
    IsKleinFour (intersectionCore D Y g) where
  card_four := by
    rw [Nat.card_congr (intersectionCoreEquiv D Y g e).toEquiv]
    exact alternatingGroup.kleinFour_card_of_card_eq_four (by norm_num)
  exponent_two := by
    rw [Monoid.exponent_eq_of_mulEquiv (intersectionCoreEquiv D Y g e)]
    exact alternatingGroup.exponent_kleinFour_of_card_eq_four (by norm_num)

/-- The actual embedding in the full triple centralizer is preserved. -/
theorem intersectionCore_le_triple_centralizer (D : Seed G) (Y : D.Vertex)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5))) (g : localNormalizer D) :
    intersectionCore D Y g ≤
      centralizer ((D.X ⊔ Y.val ⊔ ((g : G) • Y).val : Subgroup G) : Set G) := by
  rw [← intersection_eq_triple_centralizer D Y hF g]
  exact intersectionCore_le D Y g

/-- Source-class fusion of the fixer also applies to every involution of E. -/
theorem intersectionCore_involutions (D : Seed G) (Y : D.Vertex) (g : G)
    (hclass : ∀ t ∈ fixer D Y, orderOf t = 2 → IsConj D.z t)
    (t : G) (ht : t ∈ intersectionCore D Y g) (ho : orderOf t = 2) : IsConj D.z t :=
  hclass t (intersectionCore_le D Y g ht).1 ho

/-- Centralizing X makes the same literal E work for every X-translate. -/
theorem triple_le_intersectionCore_centralizer (D : Seed G) (Y : D.Vertex)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (g : localNormalizer D) (x : D.X) :
    D.X ⊔ Y.val ⊔ ((x : G) • ((g : G) • Y)).val ≤
      centralizer (intersectionCore D Y g : Set G) := by
  have ht := triple_le_centralizer D Y hF g _ (intersectionCore_le D Y g)
  have hX := (le_sup_left : D.X ≤ D.X ⊔ Y.val).trans (le_sup_left.trans ht)
  exact sup_le (le_sup_left.trans ht)
    (conj_smul_le_of_le (le_sup_right.trans ht) ⟨x, hX x.property⟩)

/-- Inner conjugates are outside the endpoint orbit, without any join-type input. -/
theorem inner_not_endpointOrbit (D : Seed G) (Y U : D.Vertex)
    (hU : U ∈ innerSet D Y) : U ∉ endpointOrbit D Y := by
  obtain ⟨g, hg, hgA, rfl⟩ := hU
  rintro ⟨x, hx⟩
  have hgN := (centralizer_le_normalizer (D.X : Set G)) hg
  have hfx : (x : G)⁻¹ * g ∈ fixer D Y := by
    constructor
    · exact normalizer_fixes_base D
        ⟨(x : G)⁻¹ * g, (localNormalizer D).mul_mem
          ((localNormalizer D).inv_mem (D.X.le_normalizer x.property)) hgN⟩
    · change ((x : G)⁻¹ * g) • Y = Y
      rw [mul_smul, ← hx]
      exact inv_smul_smul (x : G) Y
  have hmem := (actor D Y).mul_mem
    ((le_sup_right : D.X ≤ actor D Y) x.property)
    ((le_sup_left : fixer D Y ≤ actor D Y) hfx)
  exact hgA (by simpa using hmem)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations
