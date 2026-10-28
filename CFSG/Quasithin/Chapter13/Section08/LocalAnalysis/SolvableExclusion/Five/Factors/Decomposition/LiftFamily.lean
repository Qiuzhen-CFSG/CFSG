module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.Lift

/-!
# Lifting a family of star factors into P

The existing lift uses the actual isomorphism P → P* and then the
inclusion P → G. Injectivity preserves disjointness, homomorphisms
preserve commutators, and surjectivity transports generation of P* to
generation of the supplied P. No family is assumed to exist here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed p.951, the internal five-primary product.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
variable {G : Type*} [Group G] {H P : Subgroup G}

theorem liftFiveFactor_disjoint (hPH : P ≤ H) (hP : IsPGroup 5 P)
    {X Y : Subgroup (Source.Hstar H)} (hXY : Disjoint X Y) :
    Disjoint (liftFiveFactor hPH hP X) (liftFiveFactor hPH hP Y) := by
  apply disjoint_map P.subtype_injective
  apply disjoint_map (fiveStarEquiv hPH hP).symm.injective
  apply disjoint_iff.mpr
  apply bot_unique
  intro x hx
  apply Subtype.ext
  exact hXY.le_bot hx

theorem liftFiveFactor_commutator (hPH : P ≤ H) (hP : IsPGroup 5 P)
    {X Y : Subgroup (Source.Hstar H)}
    (hX : X ≤ Source.starImage H P) (hY : Y ≤ Source.starImage H P)
    (hXY : ⁅X, Y⁆ = ⊥) :
    ⁅liftFiveFactor hPH hP X, liftFiveFactor hPH hP Y⁆ = ⊥ := by
  have hi : ⁅X.subgroupOf (Source.starImage H P), Y.subgroupOf (Source.starImage H P)⁆ = ⊥ := by
    apply map_injective (Source.starImage H P).subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hX, map_subgroupOf_eq_of_le hY,
      hXY, Subgroup.map_bot]
  unfold liftFiveFactor
  rw [← map_commutator, ← map_commutator, hi, Subgroup.map_bot, Subgroup.map_bot]

theorem liftFiveFactor_iSup (hPH : P ≤ H) (hP : IsPGroup 5 P)
    {ι : Sort*} (X : ι → Subgroup (Source.Hstar H))
    (hX : ∀ i, X i ≤ Source.starImage H P)
    (hgen : (⨆ i, X i) = Source.starImage H P) :
    (⨆ i, liftFiveFactor hPH hP (X i)) = P := by
  let F := Source.starImage H P
  have hi : (⨆ i, (X i).subgroupOf F) = ⊤ := by
    apply map_injective F.subtype_injective
    rw [Subgroup.map_iSup]
    have hm (i : ι) : ((X i).subgroupOf F).map F.subtype = X i :=
      map_subgroupOf_eq_of_le (hX i)
    simp_rw [hm]
    rw [hgen, ← MonoidHom.range_eq_map, F.range_subtype]
  simp only [liftFiveFactor]
  rw [← Subgroup.map_iSup, ← Subgroup.map_iSup, hi,
    map_top_of_surjective _ (fiveStarEquiv hPH hP).symm.surjective,
    ← MonoidHom.range_eq_map, P.range_subtype]

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
end
