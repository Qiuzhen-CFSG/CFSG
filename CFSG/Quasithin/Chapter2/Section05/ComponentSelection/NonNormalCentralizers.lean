module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSourceClassification
public import Theory.SpecificGroups.AlternatingSix.CommutingLocalRank
public import Theory.SpecificGroups.PSL2.AdjacentPowerOddCore
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Involution centralizers in the original nonnormal component

The source small-component classification and nonnormality leave exactly
the prime PSL₂ family, including PSL₃(2) through its actual PSL₂(7)
isomorphism. The A₆ row is normal by quasithin local rank; PSL₃(3) and M₁₁
are normal by their elementary nine-subgroups. Each surviving field order
has an adjacent power of two, so the full intrinsic involution centralizer
is a two-group. The final statement transports this to the literal ambient
intersection needed in the paired residual argument.

Source: Aschbacher--Smith 2.5.8 and the nonnormal-component argument in
2.5.20, printed pp.556 and 563--565.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- Nonnormality removes all three higher cubic-rank rows from the actual
source catalogue. The binary linear row is the prime-seven endpoint. -/
theorem MathieuSourceSetup.nonnormal_component_prime_model
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hn : ¬ (K.subgroupOf H).Normal) :
    ∃ p : ℕ, IsFermatOrMersennePrime p ∧ 7 ≤ p ∧ Nonempty (K ≃* PSL(2, ZMod p)) := by
  let eK : K.subgroupOf H ≃* K := subgroupOfEquivOfLe c.component_le
  rcases MathieuSourceSetup.small_remaining_component c hG hempty hgen hb with
    ⟨e⟩ | ⟨e⟩ | ⟨e⟩ | ⟨e⟩ | ⟨p, hp, hlarge, he⟩
  · obtain ⟨e⟩ := e
    exact (hn (alternatingGroup.normal_of_component_a6_of_quasithin
      (hG.quasithin.subgroup H) (K.subgroupOf H) (eK.trans e) c.component)).elim
  · obtain ⟨e⟩ := e
    exact ⟨7, ⟨by decide, Or.inr ⟨3, by decide⟩⟩, le_rfl,
      ⟨e.trans Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm⟩⟩
  · obtain ⟨e⟩ := e
    exact (hn (small_component_normal hG.quasithin c.gamma (K.subgroupOf H)
      c.component (Or.inl ⟨eK.trans e⟩))).elim
  · obtain ⟨e⟩ := e
    exact (hn (small_component_normal hG.quasithin c.gamma (K.subgroupOf H)
      c.component (Or.inr ⟨eK.trans e⟩))).elim
  · exact ⟨p, hp, hlarge.le, he⟩

/-- Every involution of the original nonnormal component has a two-group
centralizer in that component. -/
theorem MathieuSourceSetup.nonnormal_component_involution_centralizer_isTwoGroup
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hn : ¬ (K.subgroupOf H).Normal)
    (i : K) (hi : orderOf i = 2) :
    IsPGroup 2 (centralizer ({i} : Set K)) := by
  obtain ⟨p, hp, hlarge, ⟨e⟩⟩ :=
    MathieuSourceSetup.nonnormal_component_prime_model c hG hempty hgen hb hn
  let : Fact p.Prime := ⟨hp.1⟩
  have hodd : Odd p := hp.1.odd_of_ne_two (by omega)
  obtain ⟨k, hk⟩ : ∃ k, p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k := by
    rcases hp.2 with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨2 ^ k, Or.inl (by omega)⟩
    · exact ⟨k, Or.inr hk⟩
  have hm := Theory.PSL2.involutionCentralizer_isTwoGroup_of_adjacent_power
    (F := ZMod p) ⟨p, 1, hp.1, hodd, by decide, by simp⟩
    (by simpa using (show 3 < p by omega)) (by simpa using hk)
    (e i) ((e.orderOf_eq i).trans hi)
  exact hm.of_equiv (CentralizerSmallKernelTransport.centralizerEquiv e i).symm

/-- The same conclusion on the literal intersection in the ambient group,
with the original involution rather than an independently chosen model mark. -/
theorem MathieuSourceSetup.nonnormal_component_ambient_centralizer_isTwoGroup
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hn : ¬ (K.subgroupOf H).Normal)
    (i : G) (hiK : i ∈ K) (hi : orderOf i = 2) :
    IsPGroup 2 (K ⊓ centralizer ({i} : Set G) : Subgroup G) := by
  let iK : K := ⟨i, hiK⟩
  have hp := MathieuSourceSetup.nonnormal_component_involution_centralizer_isTwoGroup
    c hG hempty hgen hb hn iK (by simpa only [iK, Subgroup.orderOf_mk] using hi)
  let f : (K ⊓ centralizer ({i} : Set G) : Subgroup G) →*
      centralizer ({iK} : Set K) :=
    { toFun := fun x => ⟨⟨x, x.property.1⟩,
        mem_centralizer_singleton_iff.mpr (Subtype.ext
          (mem_centralizer_singleton_iff.mp x.property.2))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact hp.of_injective f (fun _ _ h => Subtype.ext
    (congrArg (fun x : centralizer ({iK} : Set K) => ((x : K) : G)) h))

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
