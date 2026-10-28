module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.MaximalOvergroups
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.OuterPlacement
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.OddSections
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.Structure

/-!
# Escape for a prescribed outer four-group

The actual prime-field maximal-overgroup classification discharges the
model premise of the low-torus witness. Self-centrality identifies tau with
the original actor, so this is an odd E-member of degree one for that actor.
The field of order seven is included.

Source: Aschbacher–Smith E.1.14(6) and E.2.2, printed pp.214–216.
-/

public section

open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.SameActor

local instance {F : Type*} [Field F] [Finite F] : Finite (PGL2 F) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

theorem outer_odd_eMember_escape
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hpgt : 5 < p) (hFcard : Nat.card F=p)
    (T : Sylow 2 (PGL2 F)) (A M : Subgroup (PGL2 F)) (hA : IsKleinFour A)
    (hAT : A ≤ T) (hAJ : ¬ A ≤ commutator (PGL2 F))
    (hTM : (T : Subgroup (PGL2 F)) ≤ M) (hM : IsCoatom M) :
    ∃ P : Subgroup (PGL2 F), IsEMemberAt 1 (T : Subgroup _) A P ∧ ECaseOdd A P ∧ ¬ P ≤ M := by
  have hodd : IsOddPrimePower (Nat.card F) := ⟨p,1,Fact.out,hpodd,by decide,by simpa using hFcard⟩
  obtain ⟨P,hAP,hS,hlocal,hPM⟩ := outer_kleinFour_escape_of_overgroup_model F hodd
    (by omega) T A M hA hAT hAJ hTM (sylowOvergroupModel_of_prime_card hpodd hpgt hFcard T M hM hTM)
  let : IsKleinFour A := hA
  let : IsElementaryAbelian 2 A := { toIsMulCommutative := IsKleinFour.isMulCommutative, exponent_dvd_p := by rw [hA.exponent_two] }
  have hmodel : Nonempty (PGL2 F ≃* PSL2 F) ∨ Nonempty (PGL2 F ≃* PGL2 F) := Or.inr ⟨MulEquiv.refl _⟩
  have htau := tau_eq_self_of_selfCentralizing T A hAT
    (SquareGeometry.LinearWitnesses.twoCore_eq_bot hodd (by omega) hmodel)
    (SquareGeometry.LinearWitnesses.kleinFour_centralizer_eq_self hodd hmodel A hA)
  have ho := eCaseOdd_of_localModel A P hA hAP hlocal
  have hrank : Group.rank ((A.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P))) = 1 := by
    obtain ⟨r, _, _, _, _, _, hr⟩ := ho
    exact hr
  refine ⟨P, ?_, ho, hPM⟩
  exact ⟨⟨inferInstance,hAT,hAP,(by rw [htau]; exact le_inf hAT hAP),hS,Or.inl ho⟩,
    Or.inl ⟨ho,hrank.le⟩⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.SameActor
