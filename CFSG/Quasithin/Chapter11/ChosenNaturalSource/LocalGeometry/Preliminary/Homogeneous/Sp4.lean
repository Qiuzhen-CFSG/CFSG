module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Homogeneous.Sylow
public import Theory.Representation.SymplecticConjugatePair.Ambient.Transport

/-!
# Homogeneity of the full chosen-natural symplectic quotient

Inner-field automorphisms preserve the natural binary type. Their subgroup
is the kernel of the action on at most two parabolic classes. The original
Sylow subgroup stabilizes the seed, so the type stabilizer has odd index and
index dividing two, hence equals the full normalizer. The literal quotient
therefore consists of one isotypic component, including the fixed-free case.

Source: Aschbacher--Smith, 11.0.3(2), printed p.760, using 11.0.2 and 3.2.2(3).
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Representation.BinaryOffender.Homogeneous
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Source 11.0.3(2) for Sp₄, on the literal full central quotient with its
original normalizer conjugation action. -/
theorem fullModule_sp4_homogeneous
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))) :
    letI := fullModule_elementary D S
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    ∃ σ : Representation (ZMod 2) M
        (Additive (U ⧸ (centralizer (L : Set G)).subgroupOf U)),
      (∃ I : Subrepresentation (σ.comp (L.subgroupOf M).subtype),
        IsIrreducible I.toRepresentation ∧ homogeneousPart I ⊤ = ⊤) ∧
      (∀ (g : M) (v : U),
        σ g (Additive.ofMul (QuotientGroup.mk'
          ((centralizer (L : Set G)).subgroupOf U) v)) =
          Additive.ofMul (QuotientGroup.mk' ((centralizer (L : Set G)).subgroupOf U)
            ⟨(g : G) * (v : G) * (g : G)⁻¹,
              (mem_normalizer_iff.mp (le_normalizer_componentOrbit V M g.property) v).mp
                v.property⟩)) := by
  have hq : 2 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) S.nonbinary
  let π := (parabolicClassAction hq).comp (markedNormalizerAut D m)
  have hc : Nat.card (Equiv.Perm (parabolicClasses hq)) ∣ 2 := by
    let := Fintype.ofFinite (parabolicClasses hq)
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    have hh : Fintype.card (parabolicClasses hq) ≤ 2 := by
      simpa only [Nat.card_eq_fintype_card] using card_parabolicClasses_le_two hq
    simpa using Nat.factorial_dvd_factorial hh
  apply fullModule_homogeneous_of_two_quotient D S π hc
  intro g hg
  have ha : PreservesDiagram (markedNormalizerAut D m g) :=
    (mem_parabolicClassAction_ker_iff hq _).mp hg
  obtain ⟨x, φ, hx⟩ := SemilinearClassification.inner_field_of_preservesDiagram _ ha
  apply chosen_central_twist_of_marked D m g
    (SymplecticConjugatePair.Ambient.innerFieldVector x φ)
  intro l v
  rw [hx]
  exact SymplecticConjugatePair.Ambient.innerFieldVector_intertwines x φ l v

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
