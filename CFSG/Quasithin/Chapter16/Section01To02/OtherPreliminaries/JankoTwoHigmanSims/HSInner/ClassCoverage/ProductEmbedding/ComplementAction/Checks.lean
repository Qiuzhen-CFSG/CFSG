module
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding.ComplementAction.Data

/-!
# Word, separation, and noncommutation checks for the HS complement

Kernel reduction checks the word-parent certificates, a decoder on the images
of three points, and the point witness excluding each nonidentity row from the
centralizer of `D`. The transition check is isolated in `Transitions`.
Source: Aschbacher–Smith 16.1.5(10), p.1172; GLS3 Table 5.3m.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding.ComplementCertificate
open Theory.GroupTheory Sporadic.LeechRelated.HS
open Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false

theorem letterValue_spec : ∀ (s : Fin 4) (p : Fin 100),
    letterValue s p = inclusion (hLetter s) p := by
  apply allFin
  decide +kernel

theorem inverseLetter_spec (s : Fin 4) :
    hLetter (inverseLetter s) = (hLetter s)⁻¹ := by
  apply Sporadic.LeechRelated.HS.inclusion_injective
  apply Equiv.ext
  apply allFin
  revert s
  apply allFin
  decide +kernel

theorem word_data : ∀ i : Fin 1440, i ≠ 0 →
    (parent i).val < i.val ∧
    words i = words (parent i) ++ [parentLetter i] ∧
    next (parent i) (parentLetter i) = i := by
  apply allFin
  decide +kernel

theorem value_zero : ∀ p : Fin 100, value 0 p = p := by
  apply allFin
  decide +kernel

theorem decode_value : ∀ i : Fin 1440, decode (value i 0) (value i 1) (value i 2) = i := by
  apply allFin
  decide +kernel

theorem dValue_spec : ∀ (s : Fin 2) (p : Fin 100),
    dValue s p = inclusion (dGenerator s) p := by
  apply allFin
  decide +kernel

theorem noncentral_value : ∀ i : Fin 1440, i ≠ 0 →
    value i (dValue (badGenerator i) (badPoint i)) ≠
      dValue (badGenerator i) (value i (badPoint i)) := by
  apply allFin
  decide +kernel

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding.ComplementCertificate
