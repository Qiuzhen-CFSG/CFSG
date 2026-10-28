module

public import CFSG.Quasithin.ChapterK.Section01To04.Preliminaries
public import Theory.Representation.QuadraticDuality
public import Theory.Representation.DualCommutator
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Linear steps in the Mathieu restriction argument

The displacement images connect quadraticity on a hyperplane with quadraticity
on the ambient module. An invariant hyperplane retaining one whole displacement
image loses at most one dimension from the span of that image and a second one.
Annihilator duality then turns the retained commutator dimension into the fixed
codimension on the dual. M22Restriction applies this calculation to the literal
code hyperplane and its coordinate-paired cocode quotient.

These are conditional linear steps, not the missing octad subgroup geometry.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.4.3–4 and
the M12 subsection, printed pp.458–460.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterK.Mathieu

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

theorem commutator_eq_coinvariants (ρ : Representation (ZMod 2) G V) (A : Subgroup G) :
    subspaceCommutator ρ ⊤ A = Coinvariants.ker (ρ.comp A.subtype) := by
  unfold subspaceCommutator Coinvariants.ker
  congr 1
  ext v
  constructor
  · rintro ⟨a, ha, w, _, rfl⟩
    exact ⟨(⟨a, ha⟩, w), rfl⟩
  · rintro ⟨⟨a, w⟩, rfl⟩
    exact ⟨a, a.property, w, Submodule.mem_top, rfl⟩

theorem quadratic_iff_dual (ρ : Representation (ZMod 2) G V)
    [FiniteDimensional (ZMod 2) V] (A : Subgroup G) :
    IsQuadratic ρ A ↔ IsQuadratic ρ.dual A := by
  have hρ : IsQuadratic ρ A ↔
      Coinvariants.ker (ρ.comp A.subtype) ≤ Representation.invariants (ρ.comp A.subtype) := by
    rw [commutator_le_invariants_iff]
    exact ⟨fun h g t v => h g g.property t t.property v,
      fun h g hg t ht v => h ⟨g,hg⟩ ⟨t,ht⟩ v⟩
  have hdual : IsQuadratic ρ.dual A ↔
      Coinvariants.ker (Representation.dual (ρ.comp A.subtype)) ≤ Representation.invariants (Representation.dual (ρ.comp A.subtype)) := by
    rw [commutator_le_invariants_iff]
    exact ⟨fun h g t v => h g g.property t t.property v,
      fun h g hg t ht v => h ⟨g,hg⟩ ⟨t,ht⟩ v⟩
  exact hρ.trans ((commutator_le_invariants_iff_dual _).trans hdual.symm)

theorem fixedCodim_dual_eq_commutator (ρ : Representation (ZMod 2) G V)
    (A : Subgroup G) : fixedCodim ρ.dual A =
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) := by
  rw [commutator_eq_coinvariants]
  exact finrank_dual_quotient_invariants (ρ.comp A.subtype)

theorem restricted_commutator_map (ρ : Representation (ZMod 2) G V)
    (W : Subrepresentation ρ) (A : Subgroup G) :
    (subspaceCommutator W.toRepresentation ⊤ A).map W.toSubmodule.subtype =
      subspaceCommutator ρ W.toSubmodule A := by
  have h := subspaceCommutator_map_embedding ρ W.toRepresentation (MonoidHom.id G)
    W.toSubmodule.subtype (fun _ _ => rfl) A ⊤
  simpa only [Subgroup.map_id, Submodule.map_top, Submodule.range_subtype] using h.symm

theorem quadratic_of_restricted_displacements (ρ : Representation (ZMod 2) G V)
    (W : Subrepresentation ρ) {A : Subgroup G}
    (hq : IsQuadratic W.toRepresentation A)
    (himages : ∀ a ∈ A, W.toSubmodule.map (displacement ρ a) =
      LinearMap.range (displacement ρ a)) : IsQuadratic ρ A := by
  intro a ha b hb v
  obtain ⟨w, hw, he⟩ := (himages b hb).symm ▸
    (show displacement ρ b v ∈ LinearMap.range (displacement ρ b) from ⟨v, rfl⟩)
  change ρ a (displacement ρ b v) = displacement ρ b v
  rw [← he]
  exact congrArg Subtype.val (hq a ha b hb ⟨w, hw⟩)


theorem sup_range_finrank_le (W I : Submodule (ZMod 2) V)
    [FiniteDimensional (ZMod 2) V] (f : V →ₗ[ZMod 2] V) :
    Module.finrank (ZMod 2) (I ⊔ LinearMap.range f : Submodule (ZMod 2) V) ≤
      Module.finrank (ZMod 2) (I ⊔ W.map f : Submodule (ZMod 2) V) + Module.finrank (ZMod 2) (V ⧸ W) := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  have hsum : I ⊔ LinearMap.range f = (I ⊔ W.map f) ⊔ C.map f := by
    rw [sup_assoc, ← Submodule.map_sup, hC.sup_eq_top, Submodule.map_top]
  have hc := Submodule.finrank_add_eq_of_isCompl hC
  have hw := W.finrank_quotient_add_finrank
  have hm := Submodule.finrank_map_le f C
  have hs := (I ⊔ W.map f).finrank_sup_add_finrank_inf_eq (C.map f)
  rw [← hsum] at hs
  omega

theorem displacement_map_le_commutator (ρ : Representation (ZMod 2) G V)
    (W : Submodule (ZMod 2) V) {A : Subgroup G} {z : G} (hz : z ∈ A) :
    W.map (displacement ρ z) ≤ subspaceCommutator ρ W A := by
  rintro _ ⟨v, hv, rfl⟩
  exact Submodule.subset_span ⟨z, hz, v, hv, rfl⟩

theorem retained_displacement_pair_bound (ρ : Representation (ZMod 2) G V)
    [FiniteDimensional (ZMod 2) V] (W : Subrepresentation ρ)
    {A : Subgroup G} {z d : G} (hz : z ∈ A) (hd : d ∈ A)
    (hzfull : W.toSubmodule.map (displacement ρ z) =
      LinearMap.range (displacement ρ z)) :
    Module.finrank (ZMod 2) (LinearMap.range (displacement ρ z) ⊔
      LinearMap.range (displacement ρ d) : Submodule (ZMod 2) V) ≤
      fixedCodim W.toRepresentation.dual A + Module.finrank (ZMod 2) (V ⧸ W.toSubmodule) := by
  have h := sup_range_finrank_le W.toSubmodule
    (LinearMap.range (displacement ρ z)) (displacement ρ d)
  have hle : LinearMap.range (displacement ρ z) ⊔ W.toSubmodule.map (displacement ρ d) ≤
      subspaceCommutator ρ W.toSubmodule A := by
    rw [← hzfull]
    exact sup_le (displacement_map_le_commutator ρ _ hz)
      (displacement_map_le_commutator ρ _ hd)
  have hdims := Submodule.finrank_mono hle
  have he := Submodule.finrank_map_subtype_eq W.toSubmodule
    (subspaceCommutator W.toRepresentation ⊤ A)
  rw [restricted_commutator_map] at he
  rw [fixedCodim_dual_eq_commutator]
  omega

theorem fixedCodim_of_pairing {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G U)
    (E : V ≃ₗ[ZMod 2] Module.Dual (ZMod 2) U)
    (hE : ∀ g v, E (ρ g v) = σ.dual g (E v)) (A : Subgroup G) :
    fixedCodim σ A = Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) := by
  have hc := subspaceCommutator_map_embedding σ.dual ρ (MonoidHom.id G)
    E.toLinearMap (fun g v => (hE g v).symm) A ⊤
  simp only [Subgroup.map_id, Submodule.map_top, LinearEquiv.range] at hc
  have he := (Submodule.equivMapOfInjective E.toLinearMap E.injective
    (subspaceCommutator ρ ⊤ A)).finrank_eq
  rw [← hc, commutator_eq_coinvariants σ.dual A] at he
  exact (finrank_quotient_invariants_eq_dual_commutator (σ.comp A.subtype)).trans he.symm

theorem restricted_displacement_eq_of_codim_eq
    (ρ : Representation (ZMod 2) G V) [FiniteDimensional (ZMod 2) V]
    (W : Subrepresentation ρ) (z : G)
    (heq : fixedCodim W.toRepresentation (Subgroup.zpowers z) =
      fixedCodim ρ (Subgroup.zpowers z)) :
    W.toSubmodule.map (displacement ρ z) = LinearMap.range (displacement ρ z) := by
  have hmap : (LinearMap.range (displacement W.toRepresentation z)).map W.toSubmodule.subtype =
      W.toSubmodule.map (displacement ρ z) := by
    ext v
    constructor
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, w.property, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨displacement W.toRepresentation z ⟨w,hw⟩, ⟨⟨w,hw⟩,rfl⟩,rfl⟩
  have hdim := Submodule.finrank_map_subtype_eq W.toSubmodule
    (LinearMap.range (displacement W.toRepresentation z))
  rw [hmap] at hdim
  apply Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨v, _, rfl⟩; exact ⟨v, rfl⟩)
  rw [fixedCodim_zpowers_eq_displacement_rank,
    fixedCodim_zpowers_eq_displacement_rank] at heq
  exact hdim.trans heq

end CFSG.Quasithin.ChapterK.Mathieu
