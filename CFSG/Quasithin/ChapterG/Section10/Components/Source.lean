module
public import CFSG.Quasithin.ChapterG.Section10.Components.Containment
public import CFSG.Quasithin.ChapterG.Section09.Setup
public import Theory.ElementaryAbelian.GeneratorRank
/-!
# G.9.3 from an irreducible normal component orbit

The G.10 degree bound and original elementary actor supply the setup of
G.9.3. If the normal orbit of a moved component is irreducible on the original
module and has at most two component conjugates, it has the required one-
or two-component shape. Ambient conjugation gives the actual group and
linear equivalences in the second case. The SQTK cover is preserved as a
cover; no quasithinness of an arbitrary quotient is asserted.

This is the direct irreducible-orbit consumer in G.11.7, Aschbacher--Smith,
printed p.366. The adjacent homogeneous module supplies the irreducibility
premise in its nondegenerate marked-constituent branch.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem orbit_pair (L : Subgroup G) (hi : (normalizer (L : Set G)).index ≤ 2) :
    componentOrbit L ⊤ = L ∨ ∃ g : G,
      componentOrbit L ⊤ = L ⊔ L.map (MulAut.conj g).toMonoidHom := by
  classical
  by_cases hn : L.Normal
  · let := hn
    left
    apply le_antisymm ?_ (le_componentOrbit L ⊤)
    exact iSup_conjugates_le_of_le_normalizer L ⊤ L le_rfl (by rw [normalizer_eq_top_iff.mpr hn])
  have hidx : (normalizer (L : Set G)).index = 2 := by
    have hp := (normalizer (L : Set G)).index_ne_zero_of_finite
    have h1 : (normalizer (L : Set G)).index ≠ 1 := by
      intro he
      exact hn (normalizer_eq_top_iff.mp (index_eq_one.mp he))
    omega
  have hN : normalizer (L : Set G) ≠ ⊤ := fun he => hn (normalizer_eq_top_iff.mp he)
  have hex : ∃ g : G, g ∉ normalizer (L : Set G) := by
    by_contra! hall
    exact hN (eq_top_iff.mpr (fun g _ => hall g))
  obtain ⟨g,hg⟩ := hex
  right
  refine ⟨g,le_antisymm ?_ (sup_le (le_componentOrbit L ⊤) ?_)⟩
  · refine iSup_le fun a => ?_
    by_cases ha : (a : G) ∈ normalizer (L : Set G)
    · have he : L.map (MulAut.conj (a : G)).toMonoidHom = L :=
        mem_normalizer_iff_map_conj_eq.mp ha
      rw [he]
      exact le_sup_left
    have hga : g⁻¹ * (a : G) ∈ normalizer (L : Set G) :=
      (mul_mem_iff_of_index_two hidx).mpr (iff_of_false (by simpa using hg) ha)
    have he : L.map (MulAut.conj (a : G)).toMonoidHom = L.map (MulAut.conj g).toMonoidHom := by
      calc
        _ = (L.map (MulAut.conj (g⁻¹ * (a : G))).toMonoidHom).map
            (MulAut.conj g).toMonoidHom := by
          rw [map_map]
          congr 1
          ext x
          simp [MulAut.conj_apply,mul_assoc]
        _ = _ := congrArg (map (MulAut.conj g).toMonoidHom)
          (mem_normalizer_iff_map_conj_eq.mp hga)
    rw [he]
    exact le_sup_right
  · exact le_iSup (fun a : (⊤ : Subgroup G) => L.map (MulAut.conj (a : G)).toMonoidHom)
      ⟨g,mem_top g⟩

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- Ambient conjugation gives the literal group and module equivalence used
in the two-component clause of G.9.3. -/
theorem quasiequivalent_conjugate (ρ : Representation (ZMod 2) G V)
    (L : Subgroup G) (g : G) :
    Section09.Quasiequivalent (ρ.comp L.subtype)
      (ρ.comp (L.map (MulAut.conj g).toMonoidHom).subtype) := by
  refine ⟨(MulAut.conj g).subgroupMap L,
    LinearEquiv.ofBijective (ρ g) (Representation.apply_bijective ρ g),?_⟩
  intro l w
  change ρ g (ρ (l : G) w) = ρ (g * (l : G) * g⁻¹) (ρ g w)
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group

namespace Hypothesis
variable {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

/-- G.10.2, the actual SQTK cover, and an irreducible component orbit supply
all fields of G.9.3 for the original action and original elementary actor. -/
theorem componentHypothesis_of_orbit_irreducible {K : GroupClass.{u}}
    (cover : Nonempty (Section09.SQTKCover K G))
    {L : Subgroup G} (hL : IsComponent G L) (hm : ⁅L,X⁆ ≠ ⊥)
    (hind : (normalizer (L : Set G)).index ≤ 2)
    (hi : IsIrreducible (ρ.comp (componentOrbit L ⊤).subtype)) :
    Section09.ComponentHypothesis K ρ X L (componentOrbit L ⊤)
      (finrank (ZMod 2) (Additive X)) := by
  refine { faithful := h.faithful
           elementary := inferInstance
           card_actor := ?_
           degree_le := ?_
           quotient := cover
           component := hL
           noncentral := hm
           normal_H := componentOrbit_top_normal L
           irreducible := hi
           components := ?_ }
  · change Nat.card (Additive X) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  · have hr := (Group.rank_le_of_surjective (QuotientGroup.mk' X₀)
      (QuotientGroup.mk'_surjective X₀)).trans (IsElementaryAbelian.rank_le_finrank (p := 2) X)
    exact h.dimension_bound.1.trans (by omega)
  · rcases orbit_pair L hind with he | ⟨g,he⟩
    · exact Or.inl he
    · exact Or.inr ⟨_,hL.map_equiv (MulAut.conj g),he,Or.inl (quasiequivalent_conjugate ρ L g)⟩

end Hypothesis
end CFSG.Quasithin.ChapterG.Section10
