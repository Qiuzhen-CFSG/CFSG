module
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.ElementaryAbelian.CommutingFamily

/-!
# Elementary orbits of a subgroup of a TI group

Let A lie in an elementary TI subgroup V and in Q. If Q normalizes A
and H normalizes Q, the H-conjugates of A commute: they are normal in
Q, and either their containing V-conjugates coincide or intersect trivially.
Their join is therefore elementary abelian. Normality is relative to H;
no ambient normality of Q or TI hypothesis on A is required.
Source application: Aschbacher--Smith 12.2.22, printed pp.802--803.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G]

theorem elementary_orbit_of_relative_ti {p : ℕ} [Fact p.Prime]
    (A V Q H : Subgroup G) [IsElementaryAbelian p V]
    (hAV : A ≤ V) (hAQ : A ≤ Q)
    (hQA : Q ≤ normalizer (A : Set G))
    (hHQ : H ≤ normalizer (Q : Set G))
    (hTI : ∀ g ∈ H, V.map (MulAut.conj g).toMonoidHom = V ∨
      Disjoint V (V.map (MulAut.conj g).toMonoidHom)) :
    IsElementaryAbelian p (componentOrbit A H) := by
  have hcomm (g : G) (hg : g ∈ H) :
      A.map (MulAut.conj g).toMonoidHom ≤ centralizer (A : Set G) := by
    let f := (MulAut.conj g).toMonoidHom
    have hQg : Q.map f = Q := mem_normalizer_iff_map_conj_eq.mp (hHQ hg)
    have hAgQ : A.map f ≤ Q := hQg ▸ map_mono hAQ
    have hQAg : Q ≤ normalizer (A.map f : Set G) := by
      rw [← hQg]
      exact (map_mono hQA).trans (le_normalizer_map _)
    rcases hTI g hg with he | hd
    · have hAgV : A.map f ≤ V := he ▸ map_mono hAV
      exact hAgV.trans ((le_centralizer V).trans (centralizer_le hAV))
    · apply commutator_eq_bot_iff_le_centralizer.mp
      apply le_bot_iff.mp
      apply le_trans _ (hd.mono hAV (map_mono hAV)).symm.le_bot
      exact le_inf
        (le_normalizer_iff_commutator_le_left.mp (hAQ.trans hQAg))
        (le_normalizer_iff_commutator_le_right.mp (hAgQ.trans hQA))
  have hWA : componentOrbit A H ≤ centralizer (A : Set G) :=
    iSup_le fun g => hcomm g g.property
  have hAW : A ≤ centralizer (componentOrbit A H : Set G) :=
    le_centralizer_iff.mp hWA
  have hWW : componentOrbit A H ≤ centralizer (componentOrbit A H : Set G) :=
    iSup_conjugates_le_centralizer A H _ (le_normalizer_componentOrbit A H)
      (commutator_eq_bot_iff_le_centralizer.mpr hAW)
  let : IsElementaryAbelian p A := IsElementaryAbelian.of_le hAV
  let : ∀ g : H, IsElementaryAbelian p (A.map (MulAut.conj (g : G)).toMonoidHom) :=
    fun g => IsElementaryAbelian.map _
  apply IsElementaryAbelian.iSup_of_le_centralizer
  intro g k
  have hk : A.map (MulAut.conj (k : G)).toMonoidHom ≤ componentOrbit A H :=
    le_iSup (fun k : H => A.map (MulAut.conj (k : G)).toMonoidHom) k
  exact (le_iSup (fun k : H => A.map (MulAut.conj (k : G)).toMonoidHom) g).trans
    (hWW.trans (centralizer_le hk))

end Subgroup
