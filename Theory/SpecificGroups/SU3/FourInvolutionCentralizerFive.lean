module

public import Theory.SpecificGroups.SU3.EvenInvolutionTwoGroupExclusion

/-!
# A quintic element in every PSU₃(4) involution centralizer

Conjugate the involution to a long-root element. The norm-one torus gives
a nontrivial projective element whose fifth power is one and which
centralizes that root element. Transport through an actual Hermitian form
equivalence preserves the original centralizer. Hence five divides its order.

Application: the PSU₃(4) row in the opposite-centralizer catalogue cannot
have fixed-subgroup order dividing 384.
Source: Aschbacher--Smith G.4.1 and 14.3.22, printed pp.342,999.
-/

public section
open Subgroup
namespace BenderSuzuki.MatrixGroups.HermitianForm.EvenInvolutionTwoGroup
open Matrix BenderSuzuki.External BenderSuzuki.MatrixGroups
variable {E : Type*} [Field E] [Finite E] [CharP E 2]
private theorem five_dvd_standard_four_involution_centralizer
    (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = 4^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 4)
    (x : ProjectiveSpecialUnitaryMatrixGroup J) (hx : orderOf x = 2) :
    5 ∣ Nat.card (centralizer ({x} : Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨g,z,_,he,_,_⟩ := BinaryInvolutionTable.involution_root_geometry
    J hJ (n := 2) (by decide) hcard hfixed x hx
  rw [Nat.card_congr (Matrix.SU3.InnerThreeRank.centralizerEquiv (MulAut.conj g) x).toEquiv,he]
  obtain ⟨k,hkpow,_,hkne,hkconj⟩ :=
    exists_hermitian_norm_one_torus_cube_ne_one J 4 hcard hfixed hJ (by decide)
  have hzsq : (hermitianUnipotentPSU J hJ z)^2=1 := by
    have hxpow : x^2=1 := hx ▸ pow_orderOf_eq_one x
    rw [←he, ←map_pow, hxpow, map_one]
  let t : centralizer ({hermitianUnipotentPSU J hJ z} : Set _) :=
    ⟨hermitianTorusPSU J hJ k, mem_centralizer_singleton_iff.mpr
      (hermitianTorusPSU_commute_unipotent_of_sq_eq_one J hJ k hkconj z hzsq)⟩
  have htne : t≠1 := fun hh => hkne (congrArg Subtype.val hh)
  have ht5 : t^5 = 1 := by
    apply Subtype.ext
    change (hermitianTorusPSU J hJ k)^5=1
    rw [←map_pow, show k^5=1 from Units.ext (by simpa using hkpow),map_one]
  have ho : orderOf t=5 := orderOf_eq_prime ht5 htne
  exact ho ▸ orderOf_dvd_natCard t

theorem five_dvd_four_involution_centralizer
    (J : HermitianForm 3 E) (hcard : Nat.card E = 4^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 4)
    (x : ProjectiveSpecialUnitaryMatrixGroup J) (hx : orderOf x = 2) :
    5 ∣ Nat.card (centralizer ({x} : Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  obtain ⟨e⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv J 4 hcard hfixed
  rw [Nat.card_congr (Matrix.SU3.InnerThreeRank.centralizerEquiv e x).toEquiv]
  exact five_dvd_standard_four_involution_centralizer
    (OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J) rfl hcard hfixed
    (e x) ((e.orderOf_eq x).trans hx)
end BenderSuzuki.MatrixGroups.HermitianForm.EvenInvolutionTwoGroup
