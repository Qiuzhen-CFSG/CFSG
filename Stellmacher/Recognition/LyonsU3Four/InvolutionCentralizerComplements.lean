module

public import Stellmacher.Recognition.LyonsU3Four.InvolutionCentralizerQuotients
public import Stellmacher.Recognition.LyonsU3Four.InvolutionCentralizerZStar
public import Stellmacher.Recognition.LyonsU3Four.InvolutionCentralizerNormalizer
public import BenderSuzuki.External.Huppert.IV.CentralQuotientComplement

/-!
# Normal complements in involution centralizers under index three

The local argument has two inputs: the image of Z(S) is central after
factoring C_G(z) by its odd core, and the further quotient has a Sylow
subgroup central in its normalizer. Burnside transfer supplies a normal
two-complement in the latter quotient. Lift first through the central
kernel, then through the odd core. Neither lift assumes local solvability
or a trivial local odd core.

Z-star supplies the first input, and automizer index three supplies the
second. Thus every nonidentity element of Z(S) has a centralizer with a
normal two-complement.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), Lemma 1,
pp. 372–373, the paragraph beginning “Suppose |K| = 3”.
-/

namespace Stellmacher.Recognition.LyonsU3Four

/-- Burnside transfer and the two justified lifts in Lyons's local argument. -/
public theorem involutionCentralizer_hasNormalPComplement_of_quotient_data
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) {z : G} (hz : z ∈ centerImage S)
    (hcentral : centralizerCenterModOddCore S z ≤ Subgroup.center
      (Subgroup.centralizer ({z} : Set G) ⧸
        pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))))
    (hburnside :
      let Q := (Subgroup.centralizer ({z} : Set G) ⧸
        pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))) ⧸
          centralizerCenterClosure S z
      let T : Sylow 2 Q := centralizerReducedSylow S hz
      (T : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (T : Set Q))) :
    HasNormalPComplement 2 (Subgroup.centralizer ({z} : Set G)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply hasNormalPComplement_of_quotient 2
    (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G)))
    (pPrimeCore_coprime_card (p := 2))
  apply BenderSuzuki.External.hasNormalPComplement_of_central_quotient
    (centralizerCenterClosure S z)
    (Subgroup.normalClosure_le_normal hcentral)
  exact BenderSuzuki.External.hkt_hasNormalPComplement_of_sylow_le_center_normalizer
    (centralizerReducedSylow S hz) hburnside

/-- In the index-three case, each nonidentity Sylow-center element has an
involution centralizer with a normal two-complement (Lyons, Lemma 1). -/
public theorem involutionCentralizer_hasNormalPComplement_of_automizerIndex_eq_three
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) (hthree : automizerIndex S = 3) :
    ∀ z ∈ centerImage S, z ≠ 1 →
      HasNormalPComplement 2 (Subgroup.centralizer ({z} : Set G)) := by
  intro z hz hz1
  have hcentral := centralizerCenterModOddCore_le_center S h hz hz1
  exact involutionCentralizer_hasNormalPComplement_of_quotient_data S hz hcentral
    (centralizerReducedSylow_le_center_normalizer_of_automizerIndex_eq_three
      S h hthree z hz hz1 hcentral)

end Stellmacher.Recognition.LyonsU3Four
