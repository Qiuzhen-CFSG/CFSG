module

public import Mathlib.GroupTheory.Sylow
public import Theory.Quasithin.EvenCharacteristic
/-!
# Choosing a subgroup with a maximal local Sylow centralizer

If C_M(W) lies in a specified Sylow overgroup N≤M, conjugate a Sylow
subgroup of C_M(W) into the fixed Sylow subgroup using an element of N.
The conjugate of W then has its fixed-Sylow centralizer maximal among
all two-subgroups of its local M-centralizer. This retains the actual
conjugating element in N, so extra structures preserved by N are preserved.

Source: the Sylow-selection step in Aschbacher--Smith 13.5.6, p.917.
-/

@[expose] public section
open Subgroup
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem maximal_sylow_image (C:Subgroup G)(P:Sylow 2 C)
    (U:Subgroup G)(hU:IsPGroup 2 U)(hPU:(P:Subgroup C).map C.subtype≤U)(hUC:U≤C) :
    U=(P:Subgroup C).map C.subtype := by
  have he:U.subgroupOf C=(P:Subgroup C):=P.is_maximal' hU.comap_subtype (by
    intro x hx;exact hPU (mem_map_of_mem C.subtype hx))
  have hm:=congrArg (map C.subtype) he
  rwa [map_subgroupOf_eq_of_le hUC] at hm

/-- Select a conjugate whose fixed Sylow centralizer is maximal in the
local centralizer; no arbitrary-plane Sylow assertion is used. -/
theorem exists_local_centralizer_alignment (T:Sylow 2 G) (M N W:Subgroup G)
    (hTN:(T:Subgroup G)≤N)(hNM:N≤M)
    (hC:M⊓centralizer (W:Set G)≤N) :
    ∃g:N, ∀U:Subgroup G, IsPGroup 2 U →
      (T:Subgroup G)⊓centralizer (W.map (MulAut.conj g.val).toMonoidHom:Set G)≤U →
      U≤M⊓centralizer (W.map (MulAut.conj g.val).toMonoidHom:Set G) →
      U=(T:Subgroup G)⊓centralizer (W.map (MulAut.conj g.val).toMonoidHom:Set G) := by
  let C:=M⊓centralizer (W:Set G)
  let P:Sylow 2 C:=Classical.choice inferInstance
  let R:Subgroup G:=(P:Subgroup C).map C.subtype
  have hRN:R≤N:=(map_subtype_le _).trans hC
  obtain ⟨S,hRS⟩:=((P.isPGroup'.map C.subtype).comap_subtype (K:=N)).exists_le_sylow
  obtain ⟨g,hg⟩:=MulAction.exists_smul_eq N S (T.subtype hTN)
  let a:=MulAut.conj g.val
  have hcancel:a.symm.toMonoidHom.comp a.toMonoidHom=MonoidHom.id G:=by
    ext x;exact a.symm_apply_apply x
  have hcancel':a.toMonoidHom.comp a.symm.toMonoidHom=MonoidHom.id G:=by
    ext x;exact a.apply_symm_apply x
  have hRT:R.map a.toMonoidHom≤T := by
    rintro _ ⟨r,hr,rfl⟩
    have hh:(MulAut.conj g) ⟨r,hRN hr⟩∈(T.subtype hTN:Subgroup N) := by
      rw [←hg]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hRS hr)
    exact hh
  have hM:M.map a.toMonoidHom=M:=mem_normalizer_iff_map_conj_eq.mp
    (M.le_normalizer (hNM g.property))
  have hCmap:C.map a.toMonoidHom=M⊓centralizer (W.map a.toMonoidHom:Set G) := by
    rw [map_inf _ _ _ a.injective,hM,Theory.Quasithin.map_centralizer]
  let Q:Subgroup G:=(T:Subgroup G)⊓centralizer (W.map a.toMonoidHom:Set G)
  have hRQ:R.map a.toMonoidHom≤Q := le_inf hRT ((map_mono (map_subtype_le (P:Subgroup C))).trans (hCmap.le.trans inf_le_right))
  have hmax (U:Subgroup G)(hp:IsPGroup 2 U)(hRU:R.map a.toMonoidHom≤U)
      (hUC:U≤M⊓centralizer (W.map a.toMonoidHom:Set G)) : U=R.map a.toMonoidHom := by
    have hc:U.map a.symm.toMonoidHom≤C := by
      have ht:=map_mono (hUC.trans hCmap.ge) (f:=a.symm.toMonoidHom)
      simpa only [map_map,hcancel,map_id] using ht
    have hr:R≤U.map a.symm.toMonoidHom := by
      have ht:=map_mono hRU (f:=a.symm.toMonoidHom)
      simpa only [map_map,hcancel,map_id] using ht
    have he:=maximal_sylow_image C P (U.map a.symm.toMonoidHom) (hp.map _) hr hc
    have hh:=congrArg (map a.toMonoidHom) he
    rw [map_map,hcancel',map_id] at hh
    exact hh
  have hQ:Q=R.map a.toMonoidHom := hmax Q (T.isPGroup'.to_le inf_le_left) hRQ
    (le_inf (inf_le_left.trans (hTN.trans hNM)) inf_le_right)
  refine ⟨g,fun U hp hQU hUC=>?_⟩
  exact (hmax U hp (hRQ.trans hQU) hUC).trans hQ.symm
end Subgroup
