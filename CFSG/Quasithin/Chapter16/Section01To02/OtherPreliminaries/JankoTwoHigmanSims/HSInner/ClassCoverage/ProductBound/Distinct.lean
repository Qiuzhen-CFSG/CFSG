module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductBound.Checks00
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductBound.Checks01
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductBound.Checks02
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductBound.Checks03
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductBound.Checks04
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductBound.Checks05
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductBound.Checks06
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductBound.Checks07
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductBound.Checks08
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductBound.Checks09
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductBound.Checks10
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductBound.Checks11
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductBound.Checks12
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductBound.Checks13
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductBound.Checks14
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductBound.Checks15
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductBound.Checks16
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductBound.Checks17
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductBound.Checks18
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductBound.Checks19
public import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# Distinctness of 15,400 HS conjugates

The kernel checks show that every stored word gives its stored five-point
signature. Those signatures are strictly increasing, hence the actual
conjugates are distinct. Orbit exhaustion is unnecessary.

Source: Aschbacher–Smith 16.1.5(10), printed p.1172; GLS3, Table 5.3m.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductBoundCertificate
open Certificate Sporadic.LeechRelated.HS
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option Elab.async false

private theorem all_blocks (block : Fin 20) : ∀ i : Fin 770,
    codeSignature (wordCode (entry block i)) = key (entry block i) := by
  fin_cases block
  · exact checked00
  · exact checked01
  · exact checked02
  · exact checked03
  · exact checked04
  · exact checked05
  · exact checked06
  · exact checked07
  · exact checked08
  · exact checked09
  · exact checked10
  · exact checked11
  · exact checked12
  · exact checked13
  · exact checked14
  · exact checked15
  · exact checked16
  · exact checked17
  · exact checked18
  · exact checked19

/-- Every stored signature is the signature of an actual conjugate of `t`. -/
theorem signature_checked (i : Fin 15400) :
    codeSignature (wordCode i) = key i := by
  have h : entry (Fin.divNat (m := 20) (n := 770) i) (Fin.modNat (m := 20) (n := 770) i) = i := by
    apply Fin.ext
    exact Nat.div_add_mod i.val 770
  simpa only [h] using all_blocks (Fin.divNat (m := 20) (n := 770) i) (Fin.modNat (m := 20) (n := 770) i)

private theorem key_strictMono : StrictMono key := by
  apply Fin.strictMono_iff_lt_succ.mpr
  apply allFin
  decide +kernel

/-- The 15,400 certified words yield distinct conjugates in the exact carrier. -/
theorem conjugate_injective : Function.Injective
    (fun i : Fin 15400 => conjugate (wordCode i)) := by
  intro i j h
  apply key_strictMono.injective
  rw [← signature_checked i, ← signature_checked j,
    codeSignature_spec, codeSignature_spec]
  exact congrArg (fun x : Carrier => signature (inclusion x)) h

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductBoundCertificate
