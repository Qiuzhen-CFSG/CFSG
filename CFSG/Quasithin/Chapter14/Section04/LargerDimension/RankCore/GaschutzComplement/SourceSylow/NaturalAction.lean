module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.GaschutzComplement.Basic
public import Theory.SpecificGroups.PSL3Two.SourceFlag
public import Theory.PGroupCore

/-!
# The marked natural action in the Sylow step of 14.4.7

Transport the literal conjugation of I on V to binary matrix coordinates.
The kernel is C_I(V), and the elements fixing V₂ pointwise are precisely the
preimage of the coordinate-plane fixer. Intersecting with U therefore gives
the source root-group image from G.2.5(1).

The frame retains the three independent source lines in the order
(V₁ᵍ,V₁,V₁ˡ), including their containment in V. These are actual coordinates
and an intertwining identity, rather than group-family tags.

Source: Aschbacher--Smith G.2.5(1), 14.3.10 and 14.4.7,
printed pp.335,993,1009. The earlier-source producers retain construction
of these coordinates; this module proves their pointwise-fixed implications.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.GaschutzComplement
open Matrix.PSL3Two
variable {G : Type*} [Group G]

/-- Coordinates for the literal conjugation action, not an unconnected
isomorphism type. -/
structure SourceNaturalAction (I V : Subgroup G) (hIV : I ≤ normalizer (V : Set G)) where
  actor : I →* SL
  space : V ≃* Multiplicative Fano.Vector
  intertwines : ∀ (x : I) (v : V),
    (space (V.normalizerMonoidHom (inclusion hIV x) v)).toAdd =
      (actor x).val.mulVec (space v).toAdd

variable {I V : Subgroup G} {hIV : I ≤ normalizer (V : Set G)}
namespace SourceNaturalAction
variable (m : SourceNaturalAction I V hIV)

theorem fixes_iff (x : I) (v : V) :
    (m.actor x).val.mulVec (m.space v).toAdd = (m.space v).toAdd ↔
      (v : G) * x = (x : G) * v := by
  rw [← m.intertwines]
  change m.space (V.normalizerMonoidHom (inclusion hIV x) v) = m.space v ↔ _
  rw [m.space.injective.eq_iff, Subtype.ext_iff]
  change (x : G) * v * (x : G)⁻¹ = v ↔ _
  rw [mul_inv_eq_iff_eq_mul, eq_comm]

theorem ker_eq : m.actor.ker = (centralizer (V : Set G)).subgroupOf I := by
  ext x
  rw [MonoidHom.mem_ker, SourceFlag.eq_one_iff]
  change (∀ w, _) ↔ ∀ v ∈ V, v * (x : G) = (x : G) * v
  constructor
  · intro h v hv
    exact (m.fixes_iff x ⟨v,hv⟩).mp (h _)
  · intro h w
    obtain ⟨v, hv⟩ := m.space.surjective (Multiplicative.ofAdd w)
    have hh := (m.fixes_iff x v).mpr (h v v.property)
    simpa only [hv, toAdd_ofAdd] using hh

/-- Pointwise fixation of the actual V₂ is the marked plane fixer. -/
theorem centralizer_plane (V₂ : Subgroup G) (h₂V : V₂ ≤ V)
    (hplane : ∀ v : V, (v : G) ∈ V₂ ↔ (m.space v).toAdd 2 = 0) (x : I) :
    (x : G) ∈ centralizer (V₂ : Set G) ↔ m.actor x ∈ SourceFlag.planeFixer := by
  rw [SourceFlag.planeFixer_iff]
  constructor
  · intro hx w hw
    obtain ⟨v, hv⟩ := m.space.surjective (Multiplicative.ofAdd w)
    have hv₂ : (v : G) ∈ V₂ := (hplane v).mpr (by simpa only [hv, toAdd_ofAdd] using hw)
    have hh := (m.fixes_iff x v).mpr (mem_centralizer_iff.mp hx v hv₂)
    simpa only [hv, toAdd_ofAdd] using hh
  · intro hx
    apply mem_centralizer_iff.mpr
    intro v hv
    exact (m.fixes_iff x ⟨v,h₂V hv⟩).mp (hx _ ((hplane ⟨v,h₂V hv⟩).mp hv))

/-- The middle source factor has the literal root-group image. -/
theorem map_centralizer_plane (U V₂ : Subgroup G) (h₂V : V₂ ≤ V)
    (hplane : ∀ v : V, (v : G) ∈ V₂ ↔ (m.space v).toAdd 2 = 0)
    (hU : (U.subgroupOf I).map m.actor = SourceFlag.secondRadical) :
    ((U ⊓ centralizer (V₂ : Set G)).subgroupOf I).map m.actor = SourceFlag.root := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, (m.centralizer_plane V₂ h₂V hplane x).mp hx.2⟩
    rw [← hU]
    exact mem_map_of_mem m.actor hx.1
  · intro hy
    have hyU : y ∈ (U.subgroupOf I).map m.actor := hU ▸ hy.1
    obtain ⟨x,hx,rfl⟩ := hyU
    exact ⟨x, ⟨hx, (m.centralizer_plane V₂ h₂V hplane x).mpr hy.2⟩, rfl⟩
end SourceNaturalAction
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.GaschutzComplement

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.GaschutzComplement
open Matrix.PSL3Two
variable {G : Type*} [Group G]

/-- The natural coordinates are adapted to the independent source lines in the
order (V₁ᵍ,V₁,V₁ˡ). The plane V₂ is their first two coordinate directions. -/
structure SourceNaturalFrame (U V V₁ V₂ L : Subgroup G) (g l : G)
    (hIV : conjugateSpan U L ≤ normalizer (V : Set G))
    extends SourceNaturalAction (conjugateSpan U L) V hIV where
  plane_le : V₂ ≤ V
  plane : ∀ v : V, (v : G) ∈ V₂ ↔ (space v).toAdd 2 = 0
  line_g : ∀ v : V, (v : G) ∈ rightConjugate V₁ g ↔
    (space v).toAdd 1 = 0 ∧ (space v).toAdd 2 = 0
  line_one : ∀ v : V, (v : G) ∈ V₁ ↔
    (space v).toAdd 0 = 0 ∧ (space v).toAdd 2 = 0
  line_l : ∀ v : V, (v : G) ∈ rightConjugate V₁ l ↔
    (space v).toAdd 0 = 0 ∧ (space v).toAdd 1 = 0
  line_g_le : rightConjugate V₁ g ≤ V
  line_one_le : V₁ ≤ V
  line_l_le : rightConjugate V₁ l ≤ V

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.GaschutzComplement
