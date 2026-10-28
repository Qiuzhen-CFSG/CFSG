module
public import CFSG.Quasithin.ChapterE.Section03.WeakClosure
public import Theory.GroupTheory.ConjugateSpanCentralizer

/-!
# Elementary conjugate spans from the zeroth weak closure

If V lies in an H-invariant subgroup Q of X, its H-conjugates are generators
of W₀(Q,V). When W₀(X,V) centralizes V, the resulting H-span centralizes V,
and H-invariance makes that span abelian. Elementary generators then make
it elementary abelian. The weak closures here are the actual conjugate
families of E.3.13.

Source application: Aschbacher--Smith, Lemma 12.5.8(2), printed p.820, with
Q = O₂(G₁), X = T and H = G₁. The source application supplies the core
containment and the centralization proved in 12.5.7.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE
universe u
variable {G : Type u} [Group G]

theorem weakClosure_eq_of_le_of_closure_le (V X Y : Subgroup G) (i : ℕ)
    (hXY : X ≤ Y) (hWX : indexedWeakClosure V Y i ≤ X) :
    indexedWeakClosure V X i = indexedWeakClosure V Y i := by
  apply le_antisymm (weakClosure_mono V i hXY)
  change indexedWeakClosure V Y i ≤ indexedWeakClosure V X i
  rw [weakClosure_eq_sSup_gamma]
  apply sSup_le
  intro A hA
  exact gamma_le_weakClosure ⟨hA.1, (gamma_le_weakClosure hA).trans hWX⟩

theorem conjugateSpanBy_elementary_of_weakClosure_zero
    (V X Q H : Subgroup G) [IsElementaryAbelian 2 V]
    (hVQ : V ≤ Q) (hQX : Q ≤ X) (hHQ : H ≤ normalizer (Q : Set G))
    (hW : indexedWeakClosure V X 0 ≤ centralizer (V : Set G)) :
    IsElementaryAbelian 2 (conjugateSpanBy V H) := by
  have hUW : conjugateSpanBy V H ≤ indexedWeakClosure V Q 0 := by
    apply (closure_le _).mpr
    rintro x ⟨h, hh, v, hv, rfl⟩
    apply gamma_le_weakClosure ((mem_gamma_zero_iff V Q
      (V.map (MulAut.conj h).toMonoidHom)).mpr ⟨h, rfl, ?_⟩)
      (mem_map_of_mem _ hv)
    exact (map_mono hVQ).trans_eq (mem_normalizer_iff_map_conj_eq.mp (hHQ hh))
  have hUC := hUW.trans ((weakClosure_mono V 0 hQX).trans hW)
  let : IsMulCommutative (conjugateSpanBy V H) :=
    (conjugateSpanBy_commutative_iff V H).mpr (le_centralizer_iff.mp hUC)
  exact conjugateSpanBy_elementary_of_commutative V H

end CFSG.Quasithin.ChapterE
