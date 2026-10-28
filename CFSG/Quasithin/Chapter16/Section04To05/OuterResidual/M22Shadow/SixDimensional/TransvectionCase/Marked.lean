module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.M22Shadow.SixDimensional.TransvectionCase.Centerless

/-!
# The marked normalizer construction required by the transvection branch

`MarkedTransvections` specifies two elements of the actual relative
normalizers, with their centers, axes, and cross-displacements. It is a
construction target, not a hypothesis of Lemma 16.4.7. In particular there
is no assertion here that this structure is inhabited.

The centerless adapter proves centralization of Q from the two actual
commuting Sylow groups and Q ≤ L ∩ L′, then applies the proved endgame.
Source: Aschbacher–Smith, proof of Lemma 16.4.7, printed p.1187.
-/

@[expose] public section

open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow.SixDimensional.TransvectionCase
open Subgroup BinaryLinear BinaryTransvectionGroups
variable {G : Type*} [Group G]
variable (T : Sylow 2 G) (L : Subgroup G) (g r z : G)
variable [IsElementaryAbelian 2 (shadowSpace L r z)]

/-- The required output of the relative-normalizer construction. Its
elements lie in M itself; no lifting of another group into M is involved. -/
structure MarkedTransvections where
  first : shadowOvergroup L g r z
  second : shadowOvergroup L g r z
  first_mem : (first : G) ∈ commutingSylow T L
  second_mem : (second : G) ∈ (commutingSylow T L).conjBy g
  first_displacement : linearAction L g r z first ∈ quotientFixer (centerLine (zVector L r z))
  second_displacement : linearAction L g r z second ∈ quotientFixer (centerLine (rVector L r z))
  first_moves : linearAction L g r z first (rVector L r z) - rVector L r z = zVector L r z
  second_moves : linearAction L g r z second (zVector L r z) - zVector L r z = rVector L r z
  first_axis : ∀ v, linearAction L g r z first v = v ↔
    v ∈ subspace L r z (residualCore L r ⊔ zpowers z)
  second_axis : ∀ v, linearAction L g r z second v = v ↔
    v ∈ subspace L r z (residualCore L r ⊔ zpowers r)

variable {T L g r z}

/-- The first marked element centralizes Q because it belongs to T_C. -/
theorem MarkedTransvections.first_centralizesCore (d : MarkedTransvections T L g r z)
    (q : G) (hq : q ∈ residualCore L r) :
    (d.first : G) * q = q * (d.first : G) := by
  exact (d.first_mem.2 q (residualCore_le_component L r hq)).symm

/-- The second centralization uses the genuine placement Q ≤ L′. -/
theorem MarkedTransvections.second_centralizesCore (d : MarkedTransvections T L g r z)
    (hQ : residualCore L r ≤ L.conjBy g) (q : G) (hq : q ∈ residualCore L r) :
    (d.second : G) * q = q * (d.second : G) := by
  have hle : commutingSylow T L ≤ centralizer (L : Set G) := inf_le_right
  have hcen : (commutingSylow T L).conjBy g ≤ centralizer (L.conjBy g : Set G) := by
    change (commutingSylow T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)
    rintro a ⟨b, hb, rfl⟩ q ⟨q₀, hq₀, rfl⟩
    simpa only [map_mul] using congrArg (MulAut.conj g).toMonoidHom (hle hb q₀ hq₀)
  exact (hcen d.second_mem q (hQ hq)).symm

/-- The displacement equality in the faithful image, derived from the two
constructed marked actions. -/
theorem MarkedTransvections.displacement_eq (d : MarkedTransvections T L g r z) :
    displacementSpan (zpowers (linearAction L g r z d.first) ⊔
      zpowers (linearAction L g r z d.second)) =
        centerLine (rVector L r z) ⊔ centerLine (zVector L r z) :=
  pair_displacementSpan _ _ _ _ d.first_displacement d.second_displacement
    d.first_moves d.second_moves

omit [IsElementaryAbelian 2 (shadowSpace L r z)] in
/-- The local normalizer embeds in the actual M by definition. -/
theorem localNormalizer_le :
    L ⊓ normalizer (shadowSpace L r z : Set G) ≤ shadowOvergroup L g r z :=
  (inf_le_inf_right _ L.le_normalizer).trans le_sup_left

/-- Final centerless implication from the constructed marking and the
trivial two-core. The source construction of these premises remains open. -/
theorem centerless_of_marking (d : MarkedTransvections T L g r z)
    (hQsym : residualCore L r ≤ L.conjBy g)
    (hQ : shadowOvergroup L g r z ≤ normalizer (residualCore L r : Set G))
    (hcore : pCore 2 (image L g r z) = ⊥)
    (hdis : Disjoint (residualCore L r) (zpowers r ⊔ zpowers z))
    (hlocal : ∀ n ∈ L ⊓ normalizer (shadowSpace L r z : Set G),
      ∀ v ∈ shadowSpace L r z, n * v * n⁻¹ * v⁻¹ ∈ residualCore L r)
    (hmove : ∃ n ∈ L ⊓ normalizer (shadowSpace L r z : Set G), n * r * n⁻¹ ≠ r) :
    False := by
  obtain ⟨n, hn, hnr⟩ := hmove
  apply centerless_endgame L g r z hQ hcore hdis d.first d.second
    d.first_displacement d.second_displacement d.first_moves d.second_moves
    d.first_centralizesCore (d.second_centralizesCore hQsym)
  exact ⟨⟨n, localNormalizer_le hn⟩, hlocal n hn, hnr⟩

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow.SixDimensional.TransvectionCase
