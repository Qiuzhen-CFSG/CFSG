module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.RankTwoQuotient
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.Commutator
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.MSPairs

/-!
# Complete MS-pair hypotheses for the small marked alternative

The source SQTK hypothesis is retained with its catalogue parameter. The
C-component is transported from J(I) to I, the genuine earlier relative
normality supplies the literal product I=LS, and the marked quotient
calculation supplies the derived rank-two condition. For MS2(a) use H=S:
a proper Sylow subgroup has odd index and is its own two-core. MS3 is
exactly the earlier conclusion 15.3.29(1).

`SmallMSPair` specializes C.1.31 to the three small derived models and
MS2(a); it retains every MS hypothesis. It is not a classification output.
The elementary conjunction `local_ms_conditions` deliberately omits the
rank-two clause; `smallMSPair_of_source` discharges it with the actual
model comparison in `RankTwoQuotient`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.31,
printed p.135; 15.3.26–29 and proof of 15.3.31, pp.1130–1132.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G]

private theorem pCore_eq_top_of_pGroup {H : Type*} [Group H] (hp : IsPGroup 2 H) :
    pCore 2 H = ⊤ := by
  apply top_unique
  exact le_sSup ⟨inferInstance, hp.of_equiv topEquiv.symm⟩

/-- A proper Sylow subgroup supplies MS2(a), by choosing H=S itself. -/
theorem sylow_msOddIndex [Finite G] {L S : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 S (L ⊔ S)) (hproper : S < L ⊔ S) :
    MSOddIndex L S := by
  obtain ⟨P, hP⟩ := hS
  have hPS : S.subgroupOf (L ⊔ S) = (P : Subgroup (L ⊔ S : Subgroup G)) := by
    apply map_injective (L ⊔ S).subtype_injective
    rw [map_subgroupOf_eq_of_le le_sup_right, hP]
  refine ⟨S, hproper, ?_, ?_⟩
  · rw [hPS]
    exact Nat.not_even_iff_odd.mp (fun h => P.not_dvd_index (even_iff_two_dvd.mp h))
  · have hp : IsPGroup 2 S := hP ▸ P.isPGroup'.map (L ⊔ S).subtype
    change (pCore 2 S).map S.subtype = S
    rw [pCore_eq_top_of_pGroup hp, ← MonoidHom.range_eq_map, range_subtype]

/-- In the outside-component configuration, the common Sylow subgroup is proper. -/
theorem sylow_proper (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) : d.S < c.L ⊔ d.S := by
  refine lt_of_le_of_ne le_sup_right ?_
  intro he
  apply c.outside
  have hLS : c.L ≤ d.S := he.symm ▸ le_sup_left
  exact hLS.trans (inf_le_left.trans d.sylow_le)

/-- The local source hypotheses supply SQTK, characteristic two, the genuine
C-component, MS2(a), and MS3 inside LS. The rank-two quotient condition is a
separate model comparison, and is deliberately not asserted by this theorem. -/
theorem local_ms_conditions [Finite G] {κ : GroupClass.{u}}
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hSQTK : IsSQTK κ I) (hf : HasCharacteristicTwo I)
    (hI : I = c.L ⊔ d.S) (hS : Chapter1.IsSylowIn 2 d.S I)
    (h29 : ∀ C : Subgroup d.S, C.Characteristic → C ≠ ⊥ →
      ¬ ((C.map d.S.subtype).subgroupOf I).Normal) :
    IsSQTK κ (c.L ⊔ d.S : Subgroup G) ∧
      Theory.GroupTheory.generalizedFitting (c.L ⊔ d.S : Subgroup G) =
        pCore 2 (c.L ⊔ d.S : Subgroup G) ∧
      (c.L.subgroupOf (c.L ⊔ d.S)).IsCComponent ∧
      MSOddIndex c.L d.S ∧ MSNoCharacteristicNormal c.L d.S := by
  refine ⟨hI ▸ hSQTK, hI ▸ hf, ?_, ?_, ?_⟩
  · rw [← hI]
    exact LocalData.thompson_component_in c.le_thompson c.component
  · exact sylow_msOddIndex (hI ▸ hS) (sylow_proper d c)
  · intro C hc hn
    by_contra hne
    exact h29 C hc hne (hI ▸ hn)

/-- C.1.31 for the three actual small rank-two models, in MS2(a). All MS1
clauses, the literal product, the proper odd-index radical and MS3 are
retained. The exceptional MS2(b) is not needed in this Sylow application. -/
structure SmallMSPair (κ : GroupClass.{u}) (L R : Subgroup G) : Prop where
  finite : Finite (L ⊔ R : Subgroup G)
  sqtk : IsSQTK κ (L ⊔ R : Subgroup G)
  fitting : Theory.GroupTheory.generalizedFitting (L ⊔ R : Subgroup G) =
    pCore 2 (L ⊔ R : Subgroup G)
  product : ∀ g ∈ L ⊔ R, ∃ l ∈ L, ∃ r ∈ R, l * r = g
  component : (L.subgroupOf (L ⊔ R)).IsCComponent
  rankTwo : SmallRankTwoQuotient L
  radical : MSOddIndex L R
  characteristic : MSNoCharacteristicNormal L R

private theorem product_of_relative_normal {L S : Subgroup G}
    (hn : (L.subgroupOf (L ⊔ S)).Normal) :
    ∀ g ∈ L ⊔ S, ∃ l ∈ L, ∃ s ∈ S, l * s = g := by
  let := hn
  intro g hg
  have hm : (⟨g, hg⟩ : (L ⊔ S : Subgroup G)) ∈
      L.subgroupOf (L ⊔ S) ⊔ S.subgroupOf (L ⊔ S) := by
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
    trivial
  obtain ⟨l, hl, s, hs, he⟩ := mem_sup_of_normal_left.mp hm
  exact ⟨l, hl, s, hs, congrArg Subtype.val he⟩

/-- Assemble every MS-pair hypothesis from the genuine earlier conclusions
and the marked alternative 15.3.28(2). No module classification is an input. -/
theorem smallMSPair_of_source [Finite G] {κ : GroupClass.{u}}
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hSQTK : IsSQTK κ I) (hf : HasCharacteristicTwo I)
    (hI : I = c.L ⊔ d.S) (hnormal : (c.L.subgroupOf I).Normal)
    (hS : Chapter1.IsSylowIn 2 d.S I)
    (h29 : ∀ C : Subgroup d.S, C.Characteristic → C ≠ ⊥ →
      ¬ ((C.map d.S.subtype).subgroupOf I).Normal)
    (hm : Parabolics.SmallParabolicMarking d I c.L) : SmallMSPair κ c.L d.S := by
  obtain ⟨hq, hf, hc, hr, hchar⟩ := local_ms_conditions d c hSQTK hf hI hS h29
  obtain ⟨P, hP⟩ := hS
  exact ⟨inferInstance, hq, hf, product_of_relative_normal (hI ▸ hnormal), hc,
    smallRankTwoQuotient_of_marking d c hnormal P hP hm, hr, hchar⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

end
