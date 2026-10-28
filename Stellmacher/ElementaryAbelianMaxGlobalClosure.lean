module

public import Stellmacher.ElementaryAbelianMaxSylowImages

/-!
# The global elementary Thompson subgroup as a Sylow normal closure

The maximum elementary families in a Sylow subgroup and the ambient group
have the same maximum order. Sylow conjugacy therefore puts every global
maximum elementary subgroup in the normal closure of J(S). Conversely J(G)
is characteristic and contains J(S), giving J(G)=⟨J(S)^G⟩.

This is the actual global Thompson subgroup used by Campbell, *Pushing up
in Finite Groups* (1979), II.5.1, printed p.27.
-/

public section
open Subgroup
open scoped Pointwise
namespace Stellmacher
private theorem maxJ_normal {G : Type*} [Group G] :
    (elementaryAbelianMaxJ (⊤ : Subgroup G)).Normal := by
  rw [normal_iff_map_conj_eq]
  intro g
  change (elementaryAbelianMaxJ (⊤ : Subgroup G)).map (MulAut.conj g).toMonoidHom = _
  rw [← elementaryAbelianMaxJ_map_equiv, map_top_of_surjective _ (MulAut.conj g).surjective]

theorem elementaryAbelianMaxJ_top_eq_normalClosure_sylow {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) :
    elementaryAbelianMaxJ (⊤ : Subgroup G) =
      normalClosure (elementaryAbelianMaxJ (S : Subgroup G) : Set G) := by
  let N := normalClosure (elementaryAbelianMaxJ (S : Subgroup G) : Set G)
  let : N.Normal := inferInstanceAs (normalClosure _).Normal
  let : (elementaryAbelianMaxJ (⊤ : Subgroup G)).Normal := maxJ_normal
  apply le_antisymm
  · apply sSup_le
    intro A hA
    obtain ⟨R,hAR⟩ := hA.2.1.isPGroup.exists_le_sylow
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G R S
    have hm : (R : Subgroup G).map (MulAut.conj g).toMonoidHom = S := by
      change ((g • R : Sylow 2 G) : Subgroup G) = _
      rw [hg]
    have hmax : A.map (MulAut.conj g).toMonoidHom ∈ elementaryAbelianMaxSubgroups (S : Subgroup G) := by
      apply (maxFamily_sylow_iff S _).mpr
      refine ⟨(map_mono hAR).trans hm.le,?_⟩
      have hh := (maxFamily_map_injective_iff (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective ⊤ A).mpr hA
      rwa [map_top_of_surjective _ (MulAut.conj g).surjective] at hh
    have hAN : A.map (MulAut.conj g).toMonoidHom ≤ N := (le_sSup hmax).trans le_normalClosure
    intro a ha
    have hc := hAN (mem_map_of_mem (MulAut.conj g).toMonoidHom ha)
    have hh := (inferInstance : N.Normal).conj_mem _ hc g⁻¹
    simpa [MulAut.conj_apply,mul_assoc] using hh
  · apply normalClosure_le_normal
    change elementaryAbelianMaxJ (S : Subgroup G) ≤ elementaryAbelianMaxJ (⊤ : Subgroup G)
    apply sSup_le
    intro A hA
    exact le_sSup ((maxFamily_sylow_iff S A).mp hA).2


end Stellmacher
