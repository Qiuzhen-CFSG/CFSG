module

public import Theory.GroupTheory.DoubleCoverCentralizer.TwoCentralSylow
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.M12Consequences
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.J2Inner
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.Components
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.StructureTransport

/-!
# Inner marks from the sporadic centralizer rows

A component excludes the solvable M₁₂ row and the self-centralizing-kernel J₂
row. The remaining fixed subgroups cannot contain a Sylow two-subgroup. For
HS, the actual A₆ or A₈ component supplies a subgroup of order divisible by
nine, excluding the kernel row of order 7680. The product row has even index.

Only the literal M₁₂ and HS alternatives of 16.1.5(4),(10) remain explicit;
the J₂ inner calculation is already proved on its concrete carrier.
Source: Aschbacher–Smith, pp.1171–1172 and 16.3.11(3), p.1181.
-/

public section
namespace CFSG.Quasithin.Chapter16.EnlargementSieve.CoverExclusion.InnerMark
open Subgroup Theory.GroupTheory Theory.GroupTheory.DoubleCoverCentralizer
open OtherPreliminaries

/-- The M₁₂ row and an actual component exclude a two-central inner actor. -/
theorem m12_not_twoCentral (r : MulAut Sporadic.Mathieu.M12)
    (ht : Mathieu.M12InvolutionAlternative r)
    (J : Subgroup r.fixedSubgroup) (hJ : IsComponent r.fixedSubgroup J)
    (x : Sporadic.Mathieu.M12) (hx : r = MulAut.conj x) : ¬ TwoCentral x := by
  intro hu
  obtain ⟨S, hS⟩ := hu.exists_sylow_le_centralizer
  have hSfix : (S : Subgroup Sporadic.Mathieu.M12) ≤ r.fixedSubgroup := by
    rwa [hx, MulAut.fixedSubgroup_conj]
  have hi := Mathieu.m12_component_index_of_alternative r ht J hJ S
  rw [relIndex_eq_one.mpr hSfix] at hi
  omega

/-- The proved J₂ inner component calculation gives even centralizer index. -/
theorem j2_not_twoCentral (r : MulAut Sporadic.LeechRelated.J2.Carrier)
    (hr : orderOf r = 2)
    (J : Subgroup r.fixedSubgroup) (hJ : IsComponent r.fixedSubgroup J)
    (x : Sporadic.LeechRelated.J2.Carrier) (hx : r = MulAut.conj x) :
    ¬ TwoCentral x := by
  intro hu
  have hd := JankoTwoHigmanSims.J2Inner.four_dvd_index_of_inner_component
    r hr ⟨x, hx⟩ J hJ
  rw [hx, MulAut.fixedSubgroup_conj] at hd
  exact hu.not_dvd_centralizer_index ((by decide : 2 ∣ 4).trans hd)

/-- In HS the A₆/A₈ order excludes the kernel row without a class-coverage
or self-centralizing-kernel assumption. -/
theorem hs_not_twoCentral (r : MulAut Sporadic.LeechRelated.HS.Carrier)
    (ht : JankoTwoHigmanSims.HSInvolutionAlternative r)
    {J : Type*} [Group J] (f : J →* r.fixedSubgroup) (hf : Function.Injective f)
    (h9 : 9 ∣ Nat.card J)
    (x : Sporadic.LeechRelated.HS.Carrier) (hx : r = MulAut.conj x) :
    ¬ TwoCentral x := by
  rcases ht with ⟨_, hc | hp⟩ | ⟨hout, _⟩
  · have hd := h9.trans (card_dvd_of_injective f hf)
    rw [JankoTwoHigmanSims.HSInner.coreExtension_card hc] at hd
    norm_num at hd
  · intro hu
    obtain ⟨e⟩ := hp
    have hd := JankoTwoHigmanSims.HSInner.four_dvd_fixed_index_of_equiv r e
    rw [hx, MulAut.fixedSubgroup_conj] at hd
    exact hu.not_dvd_centralizer_index ((by decide : 2 ∣ 4).trans hd)
  · exact (hout ⟨x, hx⟩).elim

end CFSG.Quasithin.Chapter16.EnlargementSieve.CoverExclusion.InnerMark
