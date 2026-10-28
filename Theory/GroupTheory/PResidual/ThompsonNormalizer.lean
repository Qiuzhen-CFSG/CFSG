module

public import Theory.GroupTheory.ElementaryThompsonComponent
public import Theory.GroupTheory.PResidual.CentralizerEscape
public import Theory.GroupTheory.NormalClosureCentralizerCore

/-!
# Residual centralization from Thompson normalizer control

Suppose W is normal, J(T) centralizes W, and the normalizer of J(T)
lies in M. Thompson's Frattini argument gives G = M C_G(W).
If O²(M) centralizes W, the Sylow supplement of M then gives
G = T C_G(W), so the induced action on W is a two-group.
The second theorem retains a literal ambient subgroup C and its maps.

Source application: Aschbacher--Smith 15.1.14(1), printed p.1091.
This reduces its residual conclusion to normalization of the chosen
Thompson fixed subgroup; it does not assert that normalization.
-/

public section
open Subgroup Stellmacher
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Thompson normalizer control transfers residual centralization to the ambient group. -/
theorem pResidual_le_centralizer_of_thompson_normalizer (T : Sylow 2 G) (M W : Subgroup G) [W.Normal]
    (hTM : (T : Subgroup G) ≤ M)
    (hNJ : normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤ M)
    (hJW : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G))
    (hres : (pResidual 2 M).map M.subtype ≤ centralizer (W : Set G)) :
    pResidual 2 G ≤ centralizer (W : Set G) := by
  let D := centralizer (W : Set G)
  have hgen := elementaryAbelianMaxJ_frattini_of_le_normal T D hJW
  have hM : M ≤ D ⊔ (T : Subgroup G) := by
    have he := congrArg (map M.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTM))
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM] at he
    exact he.symm.le.trans (sup_le_sup hres le_rfl)
  have htop : D ⊔ (T : Subgroup G) = ⊤ := by
    apply top_unique
    rw [←hgen]
    exact sup_le (hNJ.trans hM) le_sup_left
  have hh := pResidual_join_le_centralizer 2 D T W le_rfl
    (show (T : Subgroup G) ≤ normalizer (W : Set G) by rw [normalizer_eq_top]; exact le_top) T.isPGroup'
  rw [htop] at hh
  rwa [map_pResidual_of_surjective 2 (⊤ : Subgroup G).subtype
    (fun x => ⟨⟨x,mem_top x⟩,rfl⟩)] at hh

/-- The same argument inside an overgroup of a fixed ambient Sylow subgroup. -/
theorem embedded_pResidual_le_centralizer_of_thompson_normalizer (T : Sylow 2 G) (C M W : Subgroup G)
    (hTC : (T : Subgroup G) ≤ C) (hTM : (T : Subgroup G) ≤ M)
    (hWC : W ≤ C) (hCW : C ≤ normalizer (W : Set G))
    (hNJ : normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤ M)
    (hJW : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G))
    (hres : (pResidual 2 (M ⊓ C : Subgroup G)).map (M ⊓ C).subtype ≤ centralizer (W : Set G)) :
    (pResidual 2 C).map C.subtype ≤ centralizer (W : Set G) := by
  let S := T.subtype hTC
  let I := M.subgroupOf C
  let W' := W.subgroupOf C
  let : W'.Normal := (normal_subgroupOf_iff_le_normalizer hWC).mpr hCW
  have hSmap : (S : Subgroup C).map C.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hTC
  have hJmap : (elementaryAbelianMaxJ (S : Subgroup C)).map C.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective C.subtype C.subtype_injective,hSmap]
  have hDmap : (centralizer (W' : Set C)).map C.subtype = C ⊓ centralizer (W : Set G) := by
    rw [map_centralizer_subtype,map_subgroupOf_eq_of_le hWC]
  have hSI : (S : Subgroup C) ≤ I := fun x hx => hTM hx
  have hNJI : normalizer (elementaryAbelianMaxJ (S : Subgroup C) : Set C) ≤ I := by
    intro x hx
    apply hNJ
    have hh := (elementaryAbelianMaxJ (S : Subgroup C)).le_normalizer_map C.subtype
      (mem_map_of_mem C.subtype hx)
    rwa [hJmap] at hh
  have hJWC : elementaryAbelianMaxJ (S : Subgroup C) ≤ centralizer (W' : Set C) := by
    apply map_subtype_le_map_subtype.mp
    rw [hJmap,hDmap]
    exact le_inf ((sSup_le fun _ hA => hA.1).trans hTC) hJW
  have hIres : (pResidual 2 I).map I.subtype ≤ centralizer (W' : Set C) := by
    apply map_subtype_le_map_subtype.mp
    rw [map_embedded_pResidual,subgroupOf_map_subtype,hDmap]
    exact le_inf ((map_subtype_le _).trans inf_le_right) hres
  exact (map_mono (f := C.subtype)
    (pResidual_le_centralizer_of_thompson_normalizer S I W' hSI hNJI hJWC hIres)).trans
      (hDmap.le.trans inf_le_right)

end Subgroup
