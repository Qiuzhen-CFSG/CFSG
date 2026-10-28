module

public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootGeometry.SimpleRecognition.ParabolicIntersections
public import Theory.SpecificGroups.Triality.FullParabolicActions
public import Theory.GroupTheory.SelfCentralizingCorePGroupJoin

/-!
# Invariant triality parabolics and their two-group extensions

An automorphism preserving the positive Sylow subgroup preserves its Borel
normalizer and permutes the two root parabolics. Their distinct Borel indices
q³ + 1 and q + 1 force both nodes to be fixed, including when q = 2. This
uses the proved concrete Tits geometry, without assuming automorphism coverage
or certifying simplicity independently.

The root radical of each full parabolic is a normal two-group containing
its centralizer. Thus its two-core is self-centralizing. This remains true
after any faithful embedding and adjoining a normalizing two-group: the
quotient by the embedded parabolic is a two-group. Working in this literal
extension retains the entire conjugation kernel.

Sources: Aschbacher–Smith E.6.8, printed pp.247–248, and F.1.11–12,
printed pp.262–264 (`refs/quasithin.pdf`); GLS3 §§2.3–2.6
(`refs/KGroup/GLS3/chapter2.tex`).
-/

public section
noncomputable section
namespace Triality.Standard.Parabolics
open Subgroup
open OuterOdd.Coverage OuterOdd.Coverage.RootGeometry.SimpleRecognition

/-- Each of the two original parabolics is fixed by any positive-Sylow
stabilizing automorphism, with no exception for the smallest field. -/
theorem parabolic_map_eq_of_unipotent_invariant (P : Parameters) (hp : P.prime = 2)
    (a : Node) (β : MulAut (Carrier P))
    (hβ : (unipotent P).map β.toMonoidHom = unipotent P) :
    (parabolic P a).map β.toMonoidHom = parabolic P a := by
  obtain ⟨f, hf, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
  let P := binaryParameters f hf
  have hB := map_borel_eq_of_unipotent_invariant P rfl β hβ
  obtain ⟨b, hb⟩ := map_parabolic_eq_of_borel_invariant f hf β hB a
  have hi := Subgroup.relIndex_map_map_of_injective (f := β.toMonoidHom)
    (borel P) (parabolic P a) β.injective
  rw [hB, hb, borel_relIndex_parabolic, borel_relIndex_parabolic] at hi
  have hq : P.q < P.q ^ 3 := lt_self_pow₀ (by have := P.q_ge_two; omega) (by decide)
  have hab : b = a := by
    cases a <;> cases b
    · rfl
    · have he : P.q + 1 = P.q ^ 3 + 1 := hi
      omega
    · have he : P.q ^ 3 + 1 = P.q + 1 := hi
      omega
    · rfl
  exact hb.trans (congrArg (parabolic P) hab)

/-- The full parabolic has self-centralizing two-core, using the actual
root radical and the proved faithful full-Levi action. -/
theorem parabolic_centralizer_twoCore_le (P : Parameters) (hp : P.prime = 2) (a : Node) :
    centralizer (pCore 2 (parabolic P a) : Set (parabolic P a)) ≤
      pCore 2 (parabolic P a) := by
  have hcore : (radical P a).subgroupOf (parabolic P a) ≤ pCore 2 (parabolic P a) :=
    le_sSup ⟨radical_normal P a, (RadicalCoordinates.radical_isPGroup P hp a).comap_subtype⟩
  intro x hx
  apply hcore
  apply parabolic_centralizer_radical_le P hp a
  refine ⟨x.property, ?_⟩
  intro y hy
  exact congrArg Subtype.val
    (hx ⟨y, radical_le_parabolic P a hy⟩ (hcore hy))

/-- The literal embedded full parabolic joined with a normalizing two-group
has self-centralizing two-core. Faithful conjugation on the carrier is not
required: the original ambient join is used throughout. -/
theorem embedded_parabolic_sup_centralizer_twoCore_le
    {G : Type*} [Group G] (P : Parameters) (hp : P.prime = 2) (a : Node)
    (ι : Carrier P →* G) (hι : Function.Injective ι)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hN : Q ≤ normalizer ((parabolic P a).map ι : Set G)) :
    centralizer (pCore 2 ((parabolic P a).map ι ⊔ Q : Subgroup G) :
      Set ((parabolic P a).map ι ⊔ Q : Subgroup G)) ≤
      pCore 2 ((parabolic P a).map ι ⊔ Q : Subgroup G) :=
  Theory.GroupTheory.centralizer_pCore_sup_le 2 _ Q
    ((Theory.Quasithin.centralizer_pCore_le_iff 2
      ((parabolic P a).equivMapOfInjective ι hι)).mp
        (parabolic_centralizer_twoCore_le P hp a)) hQ hN

end Triality.Standard.Parabolics
