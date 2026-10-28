module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Pair

/-!
# Collapse of the original three-conjugate series

After S≤O₂(G₁), 11.5.5 gives [U,S]≤V₁. Since L normalizes S and V,
the same bound on all three marked conjugates gives [I,S]≤V. Thus
W=U∩S, which contains V, is normal in I. The product S=WWˣWʸ
then reduces to S=W. The literal triple-intersection formula gives S=S₂.

This proves the layer collapse directly from the already established
structural part of G.2.5; no homogeneous-module recognition premise is
needed for this step. Construction of the three generation identities
used for S≤O₂(G₁) remains independent.
Source: Aschbacher--Smith, 11.5.7, printed p.782, first paragraph.
-/

public section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
open ChapterG.Section02.LinearThree
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D) {x y : G}
  (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)

include d

/-- The three-conjugate series collapses under the actual core containment
and the preceding central-quotient commutator bound. -/
theorem threeCore_eq_triple
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hSQ : threeCore E x y ≤ E.G₁.pCoreIn 2)
    (hUQ : ⁅E.W,E.G₁.pCoreIn 2⁆ ≤ E.V₁) :
    threeCore E x y = triple E x y := by
  let I := threeGroup E x y
  let S := threeCore E x y
  let J := W (setup E) x y
  have hLI : L ≤ I := d.L_le_I hUT hf
  have hIV : I ≤ normalizer (V : Set G) := d.I_normalizes hUT
  have hUS : ⁅E.W,S⁆ ≤ V :=
    ((commutator_mono le_rfl hSQ).trans hUQ).trans E.V₁_le
  have hconj (a : G) (ha : a ∈ L) :
      ⁅ChapterG.Section02.Setup.conjugate E.W a,S⁆ ≤ V := by
    let f := (MulAut.conj a⁻¹).toMonoidHom
    have hS : S.map f = S := conjugate_core (setup E) x y a (hLI ha)
    have hV : V.map f = V := mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (V : Set G)).inv_mem (D.normalizes ha))
    have hm := map_mono (f := f) hUS
    rw [map_commutator, hS, hV] at hm
    exact hm
  have hIS : ⁅I,S⁆ ≤ V := by
    have hU : E.W ≤ I := le_sup_left.trans le_sup_left
    have hUx : ChapterG.Section02.Setup.conjugate E.W x ≤ I :=
      le_sup_right.trans le_sup_left
    have hUy : ChapterG.Section02.Setup.conjugate E.W y ≤ I := le_sup_right
    exact commutator_sup_le_of_relative_normal I
      (E.W ⊔ ChapterG.Section02.Setup.conjugate E.W x)
      (ChapterG.Section02.Setup.conjugate E.W y) S V hIV (sup_le hU hUx) hUy
      (commutator_sup_le_of_relative_normal I E.W
        (ChapterG.Section02.Setup.conjugate E.W x) S V hIV hU hUx hUS
        (hconj x d.g_mem)) (hconj y d.h_mem)
  have hVJ : V ≤ J := le_inf (le_conjugateSpanBy V E.G₁)
    ((d.central_first_of_source hUT hf).trans inf_le_left)
  have hIJ : I ≤ normalizer (J : Set G) :=
    le_normalizer_iff_commutator_le_right.mpr
      (((commutator_mono le_rfl (show J ≤ S from inf_le_right)).trans hIS).trans hVJ)
  have hJx : ChapterG.Section02.Setup.conjugate J x = J :=
    mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (J : Set G)).inv_mem (hIJ (hLI d.g_mem)))
  have hJy : ChapterG.Section02.Setup.conjugate J y = J :=
    mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (J : Set G)).inv_mem (hIJ (hLI d.h_mem)))
  have hSJ : S = J := by
    change ChapterG.Section02.LinearThree.S (setup E) x y = J
    rw [d.S_eq_WProduct hUT hf]
    change (J ⊔ ChapterG.Section02.Setup.conjugate J x) ⊔
      ChapterG.Section02.Setup.conjugate J y = J
    simp only [hJx, hJy, sup_idem]
  have htJ : triple E x y = J := by
    change S₂ (setup E) x y = J
    rw [d.S₂_eq_triple_W hUT hf (d.L_le_I hUT hf)]
    change (J ⊓ ChapterG.Section02.Setup.conjugate J x) ⊓
      ChapterG.Section02.Setup.conjugate J y = J
    simp only [hJx, hJy, inf_idem]
  exact hSJ.trans htJ.symm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
