module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.ComponentBorels
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentModels.Paired
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedOddLinearTwo.Small
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# Complete Borel markings for the paired component source

The genuine paired catalogue has binary PSL2, Suzuki and odd-prime PSL2
rows. The first two acquire their actual original Borel markings. The
field-five coincidence is transported to PSL2(4), while the solvable
field-three group is excluded using the actual component. Thus the only
unmarked row is an odd prime at least seven; its separate rank-one
E-generation bound is the numerical input needed by the final dispatcher.
No Borel or model classification premise is assumed here.

Source: Aschbacher–Smith E.2.2(1), printed pp.215–216.
-/

public section
open Subgroup Theory.GroupTheory Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}
theorem source_exchanged_marked_cases
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremC κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬K.Normal) :
    (∃ f : ℕ, 1 < f ∧ ExchangedModel (ChapterB.minimalParabolicMax T hP) K f) ∨
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ 7 ≤ p ∧
      ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 2 p) := by
  rcases Structure.source_original_paired_models hA hC hH T hP hs K hK hgen hn with
    ⟨f,hf,hm⟩ | ⟨m,hm,he⟩ | ⟨p,hp,ho,hm⟩
  · exact Or.inl ⟨f,by omega,source_component_linear_borel_model hA hH T hP hs K hK hgen hf hm⟩
  · exact Or.inl ⟨2*m+1,by omega,source_component_suzuki_borel_model hA hH T hP hs K hK hgen hm he⟩
  · let : Fact p.Prime := ⟨hp⟩
    obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
    have h3 : p ≠ 3 := by
      intro he
      exact Witnesses.PairedOddLinearTwo.component_not_equiv_field_three (hcard.trans he)
        (Structure.source_component_simple_image T hP hs K hK hgen).2.1 e
    by_cases h5 : p = 5
    · let : Fintype F := Fintype.ofFinite F
      let eF : ZMod 5 ≃+* F := ZMod.ringEquivOfPrime F (by decide)
        (by simpa only [Nat.card_eq_fintype_card] using hcard.trans h5)
      let eA := (e.trans (GorensteinWalter.psl2RingEquiv eF).symm).trans
        GorensteinWalter.alternatingGroupFive_equiv_PSL2.some.symm
      have hfour : Nat.card (GaloisField 2 2) = 4 := by
        rw [GaloisField.card 2 2 (by decide)]; norm_num
      have hmodel : ClassicalGroup.IsPSL
          (sourceImage (ChapterB.minimalParabolicMax T hP) K) 2 (2^2) :=
        ⟨GaloisField 2 2,inferInstance,inferInstance,hfour,
          ⟨eA.trans Atlas.Comparisons.Exceptional.psl2FourEquivAlt5.symm⟩⟩
      exact Or.inl ⟨2,by decide,source_component_linear_borel_model hA hH T hP hs K hK hgen
        (by decide) hmodel⟩
    · have h7 : 7 ≤ p := by
        have hp2 := hp.two_le
        obtain ⟨k, hk⟩ := ho
        omega
      exact Or.inr ⟨p,hp,ho,h7,F,hF,hfin,hcard,⟨e⟩⟩
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
