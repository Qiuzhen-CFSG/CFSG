module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Basic
public import Theory.GroupTheory.PCoreImage
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Comparing the marked parabolic fixed spaces

A subgroup P of Q containing O₂(Q) also contains it normally, hence
O₂(Q) ≤ O₂(P). This proves the fixed-space comparison needed on printed
p.956. We retain the intrinsic cores before taking their ambient images.
The genuine star quotient carries each local core onto the core of its
image because its kernel is a two-group. Equivariant linear coordinates
then transport a fixed-line calculation for the marked model radical.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.21(2), combined manuscript of 1 March 2004. The actual parabolic
placement and code recognition are separate obligations, not conclusions
of these transport lemmas.
-/

public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu

variable {A D V W : Type*} [Group A] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

/-- Only normality relative to Q is used to compare the two actual cores. -/
theorem core_le_core (P Q : Subgroup A) (hPQ : P ≤ Q) (hcore : Q.pCoreIn 2 ≤ P) :
    Q.pCoreIn 2 ≤ P.pCoreIn 2 := by
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 Q) hcore
    (hPQ.trans (by
      have h := (pCore 2 Q).le_normalizer_map Q.subtype
      simpa only [Subgroup.pCoreIn, Subgroup.normalizer_eq_top,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype] using h))

/-- The fixed-space containment follows from placement of the larger radical. -/
theorem fixed_core_compare (ρ : Representation (ZMod 2) A V)
    (P Q : Subgroup A) (hPQ : P ≤ Q) (hcore : Q.pCoreIn 2 ≤ P) :
    fixedSpace ρ (P.pCoreIn 2) ≤ fixedSpace ρ (Q.pCoreIn 2) := by
  intro v hv q
  exact hv ⟨q, core_le_core P Q hPQ hcore q.property⟩

/-- Lift a placement from a quotient only when its entire kernel lies in P.
This kernel clause is essential; quotient images are not actual two-cores. -/
theorem core_le_of_image_le (f : A →* D) (P Q : Subgroup A)
    (hker : f.ker ≤ P) (himage : (Q.pCoreIn 2).map f ≤ P.map f) :
    Q.pCoreIn 2 ≤ P := by
  have h := (map_le_iff_le_comap).mp himage
  rwa [comap_map_eq_self hker] at h

/-- An intertwining equivalence identifies dimensions of literal fixed spaces. -/
theorem finrank_fixed_transport (ρ : Representation (ZMod 2) A V)
    (σ : Representation (ZMod 2) D W) (f : A →* D) (e : V ≃ₗ[ZMod 2] W)
    (he : ∀ a v, e (ρ a v) = σ (f a) (e v)) (P : Subgroup A) :
    Module.finrank (ZMod 2) (fixedSpace ρ P) =
      Module.finrank (ZMod 2) (fixedSpace σ (P.map f)) := by
  have h := e.finrank_map_eq (fixedSpace ρ P)
  rw [fixedSpace_map_equivariant ρ σ f e he] at h
  exact h.symm

/-- Coordinates are needed only for the marked local actor Q. The source
application uses Q = K₁T and R equal to the genuine hexad kernel. -/
theorem fixed_line_of_local_model (ρ : Representation (ZMod 2) A V)
    (Q : Subgroup A) (σ : Representation (ZMod 2) D W)
    (f : Q →* D) (e : V ≃ₗ[ZMod 2] W)
    (he : ∀ q v, e (ρ q.val v) = σ (f q) (e v))
    (R : Subgroup D) (hR : (pCore 2 Q).map f = R)
    (hline : Module.finrank (ZMod 2) (fixedSpace σ R) = 1) :
    Module.finrank (ZMod 2) (fixedSpace ρ (Q.pCoreIn 2)) = 1 := by
  change Module.finrank (ZMod 2) (fixedSpace ρ ((pCore 2 Q).map Q.subtype)) = 1
  rw [← fixedSpace_comp_map ρ Q.subtype (pCore 2 Q)]
  rw [finrank_fixed_transport (ρ.comp Q.subtype) σ f e he, hR, hline]

/-- For the code-module application only the two-core must act through the
native M₂₂ kernel. No extension of the model action to all of Q is required. -/
theorem fixed_line_of_radical_model (ρ : Representation (ZMod 2) A V)
    (Q : Subgroup A) (σ : Representation (ZMod 2) D W)
    (f : Q.pCoreIn 2 →* D) (e : V ≃ₗ[ZMod 2] W)
    (he : ∀ q v, e (ρ q.val v) = σ (f q) (e v))
    (R : Subgroup D) (hR : f.range = R)
    (hline : Module.finrank (ZMod 2) (fixedSpace σ R) = 1) :
    Module.finrank (ZMod 2) (fixedSpace ρ (Q.pCoreIn 2)) = 1 := by
  have h := finrank_fixed_transport (ρ.comp (Q.pCoreIn 2).subtype) σ f e he ⊤
  rw [fixedSpace_comp_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    ← MonoidHom.range_eq_map, hR] at h
  exact h.trans hline

variable {G : Type*} [Group G] [Finite G]

/-- The core in a source subgroup of H and the core of its star image have
identical fixed spaces under the actual quotient action. -/
theorem fixedSpace_star_core (H P : Subgroup G)
    (ρ : Representation (ZMod 2) (Source.Hstar H) V) :
    fixedSpace (ρ.comp (QuotientGroup.mk' (pCore 2 H)))
        ((P.subgroupOf H).pCoreIn 2) =
      fixedSpace ρ ((Source.starImage H P).pCoreIn 2) := by
  rw [fixedSpace_comp_map,
    map_pCoreIn_of_ker_isPGroup (QuotientGroup.mk' (pCore 2 H))
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)]
  rfl

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu
