module
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Source
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.MathieuSource
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168

/-!
# The remaining original empty-family source cases

The proved original component catalogue is dispatched without altering the
source tuple. The complete A₆ argument and original Mathieu exclusion remove
their branches; PSL₃(2) is the actual PSL₂(7) carrier. Only the independent
prime-component and PSL₃(3) source contradictions remain as inputs.

Source: Aschbacher--Smith 2.5.15--16 and completion of §2.5, pp.559--570.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The actual original catalogue reduces to its two remaining independent
source branches. The A₆ and Mathieu alternatives are discharged internally. -/
theorem MathieuSourceSetup.source_false_of_prime_and_ternary
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (hprime : ∀ (p : ℕ) [Fact p.Prime], 7 ≤ p → IsFermatOrMersennePrime p →
      (K ≃* PSL(2,ZMod p)) → False)
    (hternary : (K ≃* Matrix.PSL3Three.PSL) → False) : False := by
  rcases MathieuSourceSetup.small_remaining_component c hG hempty hgen hb with
    hA | hB | hL | hM | hP
  · obtain ⟨e⟩ := hA
    exact MathieuSourceSetup.alternating_six_source_false c hG hempty hgen hb hstar e
  · obtain ⟨e⟩ := hB
    let : Fact (Nat.Prime 7) := ⟨by decide⟩
    exact hprime 7 (by decide) ⟨by decide,Or.inr ⟨3,by decide⟩⟩
      (e.trans Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm)
  · obtain ⟨e⟩ := hL
    exact hternary e
  · obtain ⟨e⟩ := hM
    let : (K.subgroupOf H).Normal := small_component_normal hG.quasithin c.gamma _ c.component
      (Or.inr ⟨(subgroupOfEquivOfLe c.component_le).trans e⟩)
    obtain ⟨U,L,hpair,hUS,_,hbig,_⟩ := exists_saturated_pair_aligned c.gamma S
      (c.sylow_lt.le.trans c.sylow_le)
    exact mathieu_component_false_of_source c hG hempty hgen hb ⟨hpair,hbig hstar⟩ hUS e
  · obtain ⟨p,hfm,hp,⟨e⟩⟩ := hP
    let : Fact p.Prime := ⟨hfm.1⟩
    exact hprime p hp.le hfm e

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
