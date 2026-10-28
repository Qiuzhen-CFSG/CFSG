module

public import CFSG.Quasithin.ChapterE.Defs
public import CFSG.Quasithin.ChapterE.Section01.Basic

/-!
# Isomorphism transport of tau

The centralizer modulo the two-core commutes with a group isomorphism, since
both the two-core and commutators do. This is the intrinsic transport needed
when comparing the local taus in E-members and when changing Sylow subgroups.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Definition E.1.1 and Lemma E.1.8, printed pp.209--211.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterE
open Subgroup
variable {G Q : Type*} [Group G] [Group Q]

/-- Tau is intrinsic under a group isomorphism, in particular conjugation. -/
theorem map_tau_equiv (e : G ≃* Q) (T A : Subgroup G) :
    (tau T A).map e.toMonoidHom = tau (T.map e.toMonoidHom) (A.map e.toMonoidHom) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxT, hc⟩ := mem_centralizerModulo_iff.mp hx
    apply mem_centralizerModulo_iff.mpr
    refine ⟨mem_map_of_mem _ hxT, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_commutatorElement, ← pCore_map_iso 2 e]
    exact mem_map_of_mem e.toMonoidHom (hc a ha)
  · intro y hy
    obtain ⟨hyT, hc⟩ := mem_centralizerModulo_iff.mp hy
    obtain ⟨x, hx, rfl⟩ := hyT
    refine ⟨x, mem_centralizerModulo_iff.mpr ⟨hx, ?_⟩, rfl⟩
    intro a ha
    have h := hc (e.toMonoidHom a) (mem_map_of_mem e.toMonoidHom ha)
    rw [← map_commutatorElement, ← pCore_map_iso 2 e] at h
    exact (mem_map_iff_mem e.injective).mp h

end CFSG.Quasithin.ChapterE
