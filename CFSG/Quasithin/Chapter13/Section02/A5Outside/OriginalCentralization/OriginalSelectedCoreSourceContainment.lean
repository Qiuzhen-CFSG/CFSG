module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalSelectedCoreSylow
public import Theory.GroupTheory.SylowKernelCore

/-!
# The original selected pair core lies in the full source core S

The intersection J=N(L)∩H normalizes the residual K and M∩K. Since the
source geometry identifies O₂(M∩K) with T∩K, J preserves the canonical
factor family. It also normalizes L and S. Consequently every J-conjugate
of a selected pair core is the core of another actual selected pair and
lies in T by the preceding original Sylow argument.

The J-conjugate span is therefore a two-subgroup of J normalized by J,
and lies in O₂(J)=S. No normalization by another selected factor is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H R : Subgroup G} {ℛ : Set (Subgroup G)}

private theorem selected_core_le_sylow
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (geom : Global.RightGeometry T L H ℛ) (hR : R ∈ ℛ) :
    (ChapterF.Source.generated ![L,R] (Global.sourceS L H)).pCoreIn 2 ≤ (T : Subgroup G) := by
  by_cases hu : (ChapterF.Source.generated ![L,R] (Global.sourceS L H)).pCoreIn 2 = ⊥
  · exact hu ▸ bot_le
  obtain ⟨he,hi⟩ := original_selected_family_core_normalizer d hH geom hR hu
  rw [he] at hi
  exact (original_selected_pair_core_le_normalizing_sylow d hH (geom.generates R hR)
    hi.le (geom.S_normalizes R hR)).trans inf_le_left

/-- The full source core contains the pair core of every selected member
of the actual canonical family. The source Sylow and right factor are unchanged. -/
theorem original_selected_pair_core_le_sourceS
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (geom : Global.RightGeometry T L H ℛ) (hR : R ∈ ℛ) :
    (ChapterF.Source.generated ![L,R] (Global.sourceS L H)).pCoreIn 2 ≤ Global.sourceS L H := by
  let J := Global.intersection L H
  let K := residual H
  let S := Global.sourceS L H
  let N (Q : Subgroup G) := ChapterF.Source.generated ![L,Q] S
  let U := (N R).pCoreIn 2
  have hJK : J ≤ normalizer (K : Set G) := inf_le_right.trans (le_normalizer_residual H)
  have hJMK : J ≤ normalizer ((normalizer (L : Set G) ⊓ K : Subgroup G) : Set G) :=
    (le_inf (inf_le_left.trans (normalizer (L : Set G)).le_normalizer) hJK).trans
      inf_normalizer_le_normalizer_inf
  have hJTK : J ≤ normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
    have hh := hJMK.trans (normalizer_le_normalizer_characteristic_image
      (normalizer (L : Set G) ⊓ K) (pCore 2 (normalizer (L : Set G) ⊓ K : Subgroup G)))
    change J ≤ normalizer ((normalizer (L : Set G) ⊓ K : Subgroup G).pCoreIn 2 : Set G) at hh
    rw [geom.residual_core d.normalizes_L hH.1.1.2] at hh
    exact hh
  have hJS : J ≤ normalizer (S : Set G) := Global.intersection_normalizes_sourceS L H
  have hconj (g : G) (hg : g ∈ J) :
      U.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) := by
    have hR' := geom.invariant g (hJK hg) (hJTK hg) R hR
    have hL : L.map (MulAut.conj g).toMonoidHom = L :=
      mem_normalizer_iff_map_conj_eq.mp hg.1
    have hS : S.map (MulAut.conj g).toMonoidHom = S :=
      mem_normalizer_iff_map_conj_eq.mp (hJS hg)
    have hN : (N R).map (MulAut.conj g).toMonoidHom =
        N (R.map (MulAut.conj g).toMonoidHom) := by
      change (L ⊔ R ⊔ S).map (MulAut.conj g).toMonoidHom =
        L ⊔ R.map (MulAut.conj g).toMonoidHom ⊔ S
      rw [Subgroup.map_sup,Subgroup.map_sup,hL,hS]
    change ((N R).pCoreIn 2).map (MulAut.conj g).toMonoidHom ≤ _
    rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,hN]
    exact selected_core_le_sylow d hH geom hR'
  let W := conjugateSpanBy U J
  have hWT : W ≤ (T : Subgroup G) := by
    apply (closure_le _).mpr
    rintro x ⟨g,hg,z,hz,rfl⟩
    exact hconj g hg (mem_map_of_mem (MulAut.conj g).toMonoidHom hz)
  have hWJ : W ≤ J := hWT.trans (le_inf d.normalizes_L hH.1.1.2)
  have hWS : W ≤ S := le_pCoreIn_of_normalizes (T.isPGroup'.to_le hWT) hWJ
    (le_normalizer_conjugateSpanBy U J)
  exact (le_conjugateSpanBy U J).trans hWS

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
