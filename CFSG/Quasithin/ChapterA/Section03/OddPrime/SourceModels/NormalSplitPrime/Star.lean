module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
public import Theory.GroupTheory.PPrimeCoreSurjection

/-!
# Comparing the exact star quotients through a coprime kernel

A surjection with p-prime kernel pulls back the target p-prime core to the
source p-prime core. Its composite with the target star map therefore induces
an equivalence H/O_{p′}(H) ≃ Q/O_{p′}(Q). We restrict that equivalence to the
actual component images and to O^{p′}; the equations on representatives retain
the original quotient maps.

These comparisons connect the two-core reduction of normal split-prime
A.3.18 to its source alternatives. They do not identify a two-core with a
prime-to-p core or a core with a residual.
Source: Aschbacher–Smith A.3.18, printed pp.51–53.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
variable {H Q : Type*} [Group H] [Finite H] [Group Q] [Finite Q]
variable (p : ℕ) [Fact p.Prime] (f : H →* Q) (hf : Function.Surjective f)
  (hc : Nat.Coprime p (Nat.card f.ker))

include hf hc in
theorem starComposite_ker : ((starMap p Q).comp f).ker = pPrimeCore p H := by
  rw [← MonoidHom.comap_ker, starMap, QuotientGroup.ker_mk']
  exact pPrimeCore_comap_eq_of_surjective_coprime p f hf hc

def starEquiv : Star p H ≃* Star p Q :=
  (QuotientGroup.quotientMulEquivOfEq (starComposite_ker p f hf hc).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ((starMap p Q).comp f)
      ((QuotientGroup.mk'_surjective _).comp hf))

theorem starEquiv_mk (x : H) :
    starEquiv p f hf hc (starMap p H x) = starMap p Q (f x) := rfl

theorem starEquiv_component_map (K : Subgroup H) :
    (starComponent p K).map (starEquiv p f hf hc).toMonoidHom =
      starComponent p (K.map f) := by
  change (K.map (starMap p H)).map (starEquiv p f hf hc).toMonoidHom =
    (K.map f).map (starMap p Q)
  rw [map_map, map_map]
  rfl

def starComponentEquiv (K : Subgroup H) :
    starComponent p K ≃* starComponent p (K.map f) :=
  ((starEquiv p f hf hc).subgroupMap _).trans
    (MulEquiv.subgroupCongr (starEquiv_component_map p f hf hc K))

theorem starComponentEquiv_mk (K : Subgroup H) (x : K) :
    (starComponentEquiv p f hf hc K ((starMap p H).subgroupMap K x) : Star p Q) =
      starMap p Q (f x) := rfl

def starResidualEquiv : primeToResidual p (Star p H) ≃* primeToResidual p (Star p Q) :=
  primeToResidualEquiv p (starEquiv p f hf hc)

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
