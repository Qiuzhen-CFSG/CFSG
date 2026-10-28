module
public import Theory.GroupTheory.UniqueMaximalNormalExtension

/-!
# Unique maximality descends to a quotient

If S contains the kernel of a surjection, subgroup correspondence preserves
the unique maximal overgroup of S. Its image is proper because the kernel
already lies in it, and every proper overgroup of the image pulls back below
the original unique maximal subgroup.

Source application: the actual quotient Sylow subgroup in Niles (1979),
Theorem 7.2, after constructing its central-chief reduction kernel.
-/

public section
open Subgroup
namespace Subgroup
variable {G H : Type*} [Group G] [Group H] [Finite G]

theorem hasUniqueMaximalOver_map_of_surjective
    (f : G →* H) (hf : Function.Surjective f) {S : Subgroup G}
    (hk : f.ker ≤ S) (hu : Order.HasUniqueMaximalOver S ⊤) :
    Order.HasUniqueMaximalOver (S.map f) ⊤ := by
  let : Finite H := Finite.of_surjective f hf
  obtain ⟨M,hM,_⟩ := hu.2
  have hkt : f.ker ≤ M := hk.trans hM.1
  have hMt : M.map f < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    have hh := congrArg (Subgroup.comap f) he
    rw [comap_map_eq_self hkt, comap_top] at hh
    exact hM.2.ne hh
  have hSM : S.map f ≤ M.map f := map_mono hM.1
  have hgreatest (L : Subgroup H) (hSL : S.map f ≤ L) (hLt : L < ⊤) : L ≤ M.map f := by
    have hLC : L.comap f ≤ M := by
      apply hu.le_maximal hM (map_le_iff_le_comap.mp hSL)
      apply lt_top_iff_ne_top.mpr
      intro he
      have hh := congrArg (Subgroup.map f) he
      rw [map_comap_eq_self_of_surjective hf,map_top_of_surjective f hf] at hh
      exact hLt.ne hh
    rw [← map_comap_eq_self_of_surjective hf L]
    exact map_mono hLC
  have hc : M.map f ⋖ ⊤ :=
    ⟨hMt, fun L hmL hLt => (not_lt_of_ge (hgreatest L (hSM.trans hmL.le) hLt)) hmL⟩
  refine ⟨hSM.trans_lt hMt, M.map f, ⟨hSM,hc⟩, ?_⟩
  intro L hL
  exact ((hL.2.eq_or_eq (hgreatest L hL.1 hL.2.lt) hMt.le).resolve_right hMt.ne).symm

end Subgroup
