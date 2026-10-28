module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage.EvenChecks
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage.Reduction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InnerInvolutionCores.Fusion
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InnerInvolutionCores.Coverage

/-!
# Coverage of every even-order Hall--Janko element

Every even-order element commutes with its involutory power. The proved
involution fusion moves that power to one of the two fixed involutions.
The original element then belongs to a certified centralizer enumeration,
and the checked four-point conjugators place it in one of the 21 fixed classes.
Thus the conclusion holds for every even-order element of the literal carrier.

Source: the ATLAS `J2G1-p100B0` tables and the intrinsic involution fusion in
`InnerInvolutionCores.Fusion`. The finite witnesses and conventions are retained
in `Coverage/source/`; no external class-count assertion is used.
-/

public section
namespace Sporadic.LeechRelated.J2.PowerFusionCertificate
open GeneratorPair.SecondOrbitCertificate EvenCertificates

private theorem central_fusion (i : Fin 1920) : IsConj (representative (centralClass i))
    (GeneratorPair.FirstFusion.centralizerElement i) := by
  apply isConj_of_base _ _ (element (centralConjugator i))
  intro k
  change normalForm (centralConjugator i)
      (normalForm (representativeIndex (centralClass i)) _) =
    inclusion (GeneratorPair.FirstFusion.centralizerElement i)
      (normalForm (centralConjugator i) _)
  rw [GeneratorPair.FirstFusion.LocalCertificate.value_spec]
  exact central_check i k

private theorem noncentral_fusion (i : Fin 240) : IsConj (representative (noncentralClass i))
    (GeneratorPair.SecondOrbitCertificate.conjugator i) := by
  apply isConj_of_base _ _ (element (noncentralConjugator i))
  intro k
  change normalForm (noncentralConjugator i)
      (normalForm (representativeIndex (noncentralClass i)) _) =
    inclusion (GeneratorPair.SecondOrbitCertificate.conjugator i)
      (normalForm (noncentralConjugator i) _)
  rw [conjugator_inclusion]
  exact noncentral_check i k

theorem covered_of_two_dvd (g : Carrier) (hg : 2 ∣ orderOf g) :
    ∃ i : Fin 21, IsConj (representative i) g := by
  apply covered_of_power_centralizers 2 ?_ g hg
  intro x hx z hcomm
  rcases InnerInvolutionCores.involution_fusion x hx with ha | ht
  · apply covered_of_conjugate_centralizer ?_ ha.symm hcomm
    intro y hy
    obtain ⟨i, rfl⟩ := InnerInvolutionCores.a_centralizer_cover y hy
    exact ⟨noncentralClass i, noncentral_fusion i⟩
  · apply covered_of_conjugate_centralizer ?_ ht.symm hcomm
    intro y hy
    obtain ⟨i, rfl⟩ := GeneratorPair.FirstFusion.centralizerElement_cover y hy
    exact ⟨centralClass i, central_fusion i⟩

end Sporadic.LeechRelated.J2.PowerFusionCertificate
