module
public import Theory.GroupAction.AutomorphismFixerCardinality.SylowInner
public import Theory.SpecificGroups.BinaryComponentResidual
public import Theory.SpecificGroups.BinaryLinear.SylowCenters
public import Theory.SpecificGroups.BinaryLinear.SylowPointwiseInner
public import Theory.SpecificGroups.Tits.SylowPointwiseInner
public import Theory.SpecificGroups.Tits.ThreeRankLowerBound
public import Theory.SpecificGroups.Tits.OuterOddSubgroups
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.BinarySylowFixers
public import Theory.GroupTheory.PGroup.AbelianOmega
public import Theory.GroupAction.ElementarySylowFixerBound
/-!
# Small binary Lie component Sylow fixers

For L4(2), L5(2), G2(2)' and the Tits group, an elementary subgroup of
pointwise Sylow fixers has order at most two. The linear cases use innerness
and the Sylow center; G2 uses its certified omega-center and innerness; the
Tits case embeds the fixer into the certified restriction kernel. These are
the intrinsic bounds used in Aschbacher--Smith15.1.22(4),(7).
-/
public section
open Subgroup Theory.GroupAction
open scoped MatrixGroups
namespace Theory.SpecificGroups.BinaryComponentResidual

theorem linear_fixers {n : ℕ} (hn : n = 4 ∨ n = 5)
    (P : Sylow 2 SL(n,ZMod 2)) (A : Subgroup (MulAut SL(n,ZMod 2)))
    (hfix : ∀ a ∈ A, ∀ x ∈ P, a x = x) : Nat.card A ≤ 2 := by
  let e := BinaryLinear.OuterCyclic.slEquivLinear n
  let : Finite (BinaryLinear.OuterCyclic.LinearGroup n) := Finite.of_equiv SL(n,ZMod 2) e.toEquiv
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  apply automorphism_fixer_card_le_of_equiv e P Q rfl 2 _ A hfix
  intro B hb
  exact (sylow_fixer_card_le_center_of_inner Q
    (BinaryLinear.OuterCyclic.sylow_fixing_inner hn Q) B hb).trans
      (BinaryLinear.linear_sylow_center_card_le_two (by omega) Q)

theorem tits_facts : Facts Tits.Atlas1600Group :=
  ⟨Tits.RelativeSylowMarking.atlas_center_eq_bot, Tits.ThreeRank.rank_two_le,
    Tits.OuterOddSubgroups.parrott_outer_isPGroup.of_equiv
      (MulAut.outerCongr Tits.parrottFiniteImageEquiv)⟩

theorem tits_fixers (P : Sylow 2 Tits.Atlas1600Group)
    (A : Subgroup (MulAut Tits.Atlas1600Group))
    (hfix : ∀ a ∈ A, ∀ x ∈ P, a x = x) : Nat.card A ≤ 2 := by
  apply sylow_fixer_card_le_of_standard Tits.atlas1600SylowTwo 2 _ P A hfix
  intro B hb
  change ∀ a ∈ B, ∀ x ∈ (Tits.atlas1600SylowTwo : Subgroup Tits.Atlas1600Group), a x = x at hb
  rw [Tits.atlas1600SylowTwo_coe] at hb
  let f : B → Tits.OuterOddSubgroups.sylowRestriction.ker := fun a => by
    have hm : Tits.atlas1600SylowTwoSubgroup.map a.val.toMonoidHom =
        Tits.atlas1600SylowTwoSubgroup := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        change a.val y ∈ Tits.atlas1600SylowTwoSubgroup
        rw [hb a a.property y hy]
        exact hy
      · intro hx
        exact ⟨x,hx,hb a a.property x hx⟩
    exact ⟨⟨a,hm⟩,(Tits.OuterOddSubgroups.mem_sylowRestriction_ker_iff _).mpr
      (fun x hx => hb a a.property x hx)⟩
  have hf : Function.Injective f := fun a b he =>
    Subtype.ext (congrArg (fun c : Tits.OuterOddSubgroups.sylowRestriction.ker => c.val.val) he)
  exact (Nat.card_le_card_of_injective f hf).trans
    Tits.SharpOuterBound.sylowRestriction_kernel_card_le_two

theorem g2_fixers (P : Sylow 2 (commutator (Atlas.G2.Model (ZMod 2))))
    (A : Subgroup (MulAut (commutator (Atlas.G2.Model (ZMod 2)))))
    [IsElementaryAbelian 2 A]
    (hfix : ∀ a ∈ A, ∀ x ∈ P, a x = x) : Nat.card A ≤ 2 := by
  have hcenter : IsCyclic (center P) := by
    let Q := Atlas.G2.BinaryParabolicPair.derivedSylow
    have hQ : Nat.card (omega₁ (center Q) (p := 2)) = 2 := by
      have hh := congrArg (fun B : Subgroup Atlas.G2.BinaryParabolicPair.DerivedModel => Nat.card B)
        Atlas.G2.BinaryParabolicPair.derivedSylow_omega_center_in_model
      rw [card_map_of_injective Atlas.G2.BinaryParabolicPair.derivedSylow.toSubgroup.subtype_injective,
        card_map_of_injective (center Atlas.G2.BinaryParabolicPair.derivedSylow).subtype_injective,
        Atlas.G2.BinaryParabolicPair.card_derivedDistinguished] at hh
      exact hh
    let : IsCyclic (center Q) :=
      (Q.isPGroup'.to_subgroup (center Q)).isCyclic_of_card_omega_one_le_two hQ.le
    exact (centerCongr (Q.equiv P)).isCyclic.mp inferInstance
  let := hcenter
  apply elementary_sylow_fixer_card_le_two_of_inner P
    Theory.SpecificGroups.g2_derived_two_center_eq_bot _ A hfix
  intro a _ ha
  obtain ⟨g,_,hg⟩ := Atlas.G2.EvenInvolutionGeometry.binary_fixing_sylow_inner
    Atlas.G2.LieAutomorphismExtensions.binaryConjugation_bijective P a
    (fun x hx => ha ⟨x,hx⟩)
  exact ⟨g,hg⟩
end Theory.SpecificGroups.BinaryComponentResidual
