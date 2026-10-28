module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Residual.Frattini
public import Theory.GroupTheory.CComponent.SeedAction
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# A radical supplement in a centralizer normalizer

Let L belong to the local C-component family for a Sylow two-subgroup T.
Suppose T normalizes L, and the nontrivial abelian U ≤ T is normalized
and fully moved by L. Then N_L(C_T(U))^∞ is a member of the same local
family and supplements the solvable radical of L.

Set H=LT and C=C_H(U). The normal subgroup C is solvable, since H has
C-component residual L and L does not centralize U. The Sylow intersection
R=C_T(U) is Sylow in C. Frattini gives H=C N_H(R); solvable residual
transport gives the C-component N_L(R)^∞. The nontrivial normal two-subgroup
R makes N_H(R) local. Restricting the residual cover to L gives the claimed
radical supplement. All normality is relative to these indicated overgroups.

Source: Aschbacher--Smith, proof of 13.1.14, printed pp.875--876, using
A.3.3 and the same Frattini residual construction as 13.1.9 on p.869.
Here the infinity superscript is the solvable residual, not O².
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers
variable {G : Type*} [Group G] [Finite G]

private theorem frattini_intersection (T : Sylow 2 G) (H C : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hCH : C ≤ H)
    (hHC : H ≤ normalizer (C : Set G)) :
    IsSylowIn 2 ((T : Subgroup G) ⊓ C) C ∧
      C ⊔ (H ⊓ normalizer (((T : Subgroup G) ⊓ C : Subgroup G) : Set G)) = H := by
  let C' := C.subgroupOf H
  let : C'.Normal := normal_subgroupOf_of_le_normalizer hHC
  obtain ⟨P,hP⟩ := (T.subtype hTH).exists_subgroupOf_eq_of_normal C'
  have hp : (((P : Subgroup C').map C'.subtype).map H.subtype) =
      (T : Subgroup G) ⊓ C := by
    rw [hP,subgroupOf_map_subtype,Subgroup.map_inf _ _ _ H.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,map_subgroupOf_eq_of_le hCH]
  constructor
  · let e : C' ≃* C := subgroupOfEquivOfLe hCH
    refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
    change ((P : Subgroup C').map e.toMonoidHom).map C.subtype = _
    have hc : C.subtype.comp e.toMonoidHom = H.subtype.comp C'.subtype := by
      ext x
      rfl
    simpa only [map_map, hc] using hp
  · have hf := congrArg (Subgroup.map H.subtype) P.normalizer_sup_eq_top
    rw [Subgroup.map_sup,← MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le hCH] at hf
    apply le_antisymm (sup_le hCH inf_le_left)
    apply hf.symm.le.trans
    apply sup_le _ le_sup_left
    apply le_trans _ le_sup_right
    refine le_inf (map_subtype_le _) ?_
    have hh := ((P : Subgroup C').map C'.subtype).le_normalizer_map H.subtype
    rwa [hp] at hh

/-- The actual normalizer residual is a local C-component and a radical
supplement. The normal Sylow intersection and Frattini cover are constructed. -/
theorem centralizer_normalizerResidual_mem_L_and_supplement
    (T : Sylow 2 G) (L U : Subgroup G)
    (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hLU : L ≤ normalizer (U : Set G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hUT : U ≤ (T : Subgroup G)) (hUC : U ≤ centralizer (U : Set G))
    (hUne : U ≠ ⊥) (hmove : ⁅U,L⁆ = U) :
    normalizerResidual L ((T : Subgroup G) ⊓ centralizer (U : Set G)) ∈
        Chapter1.L G (T : Subgroup G) ∧
      (solvableRadical L).map L.subtype ⊔
        normalizerResidual L ((T : Subgroup G) ⊓ centralizer (U : Set G)) = L := by
  let H := L ⊔ (T : Subgroup G)
  let C := H ⊓ centralizer (U : Set G)
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let N := H ⊓ normalizer (R : Set G)
  let Y := normalizerResidual L R
  have hHC : H ≤ normalizer (C : Set G) := by
    apply (le_inf H.le_normalizer ?_).trans inf_normalizer_le_normalizer_inf
    exact (sup_le hLU hTU).trans
      (le_normalizer_of_normal_subgroupOf (centralizer_le_normalizer (U : Set G)))
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer
      (hTU.trans (le_normalizer_of_normal_subgroupOf
        (centralizer_le_normalizer (U : Set G))))).trans inf_normalizer_le_normalizer_inf
  have hTC : (T : Subgroup G) ⊓ C = R := by
    apply le_antisymm
    · exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
    · exact le_inf inf_le_left (le_inf (inf_le_left.trans le_sup_right) inf_le_right)
  have hCN : C ⊔ N = H := by
    have hf := (frattini_intersection T H C le_sup_right inf_le_left hHC).2
    rwa [hTC] at hf
  let := mem_L_isPerfect hL
  let : Group.IsNilpotent T := T.isPGroup'.isNilpotent
  have hresmap : (solvableResidual H).map H.subtype = L :=
    map_residual_sup_eq_of_perfect_of_solvable L (T : Subgroup G) hTL
  have hres : solvableResidual H = L.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hresmap,map_subgroupOf_eq_of_le (show L ≤ H from le_sup_left)]
  have hrescomp : (solvableResidual H).IsCComponent := hres.symm ▸ hL.1
  let : (C.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHC
  have hLC : ¬ L ≤ C := by
    intro he
    apply hUne
    rw [← hmove,commutator_eq_bot_iff_le_centralizer,le_centralizer_iff]
    exact he.trans inf_le_right
  let : Group.IsSolvable (C.subgroupOf H) :=
    isSolvable_of_normal_not_containing_ccomponent_residual _ hrescomp (by
      intro he
      apply hLC
      have hh := map_mono (f := H.subtype) he
      rwa [hresmap,map_subgroupOf_eq_of_le (show C ≤ H from inf_le_left)] at hh)
  let : Group.IsSolvable C := Group.isSolvable_of_surjective
    (f := (subgroupOfEquivOfLe (show C ≤ H from inf_le_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show C ≤ H from inf_le_left)).surjective
  have hNres : (solvableResidual N).map N.subtype = Y :=
    localNormalizer_residual_eq L T R hL.2.1 hTL
  have hYcomp : (Y.subgroupOf N).IsCComponent := by
    have hh := residual_isCComponent_of_solvable_supplement_in H C N
      inf_le_left inf_le_left hHC hCN hrescomp
    have he : Y.subgroupOf N = solvableResidual N := by
      rw [← hNres]
      exact comap_map_eq_self_of_injective N.subtype_injective _
    exact he.symm ▸ hh
  have hRN : R ≤ N := le_inf (inf_le_left.trans le_sup_right) R.le_normalizer
  have hRne : R ≠ ⊥ := fun he => hUne (bot_unique (he ▸ le_inf hUT hUC))
  have hNcore : N.pCoreIn 2 ≠ ⊥ := by
    intro he
    exact hRne (bot_unique (he ▸ le_pCoreIn_of_normalizes
      (T.isPGroup'.to_le (show R ≤ (T : Subgroup G) from inf_le_left)) hRN inf_le_right))
  have hYN : Y ≤ N := le_inf ((normalizerResidual_le L R).trans le_sup_left)
    (normalizerResidual_le_normalizer L R)
  have hYmem := mem_L_of_cComponent hNcore
    (hL.2.1.restrict (le_inf le_sup_right hTR) inf_le_left) hYN hYcomp
  have hcover : L ≤ C ⊔ Y := by
    have hh := map_solvableResidual_le_sup_residual_of_sup_eq H C N
      inf_le_left inf_le_left hHC hCN
    rwa [hresmap,hNres] at hh
  have hCY : L ≤ (C ⊓ L) ⊔ Y := by
    intro l hl
    have hh : l ∈ ((C ⊔ Y : Subgroup G) : Set G) := hcover hl
    rw [coe_mul_of_right_le_normalizer_left C Y (hYN.trans (inf_le_left.trans hHC))] at hh
    obtain ⟨c,hc,y,hy,he⟩ := hh
    have hcL : c ∈ L := by
      have hh := L.mul_mem hl (L.inv_mem (normalizerResidual_le L R hy))
      simpa only [← he,mul_inv_cancel_right] using hh
    rw [← he]
    exact ((C ⊓ L) ⊔ Y).mul_mem (mem_sup_left ⟨hc,hcL⟩) (mem_sup_right hy)
  have hCrad : C ⊓ L ≤ (solvableRadical L).map L.subtype := by
    let : (C.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer
      ((show L ≤ H from le_sup_left).trans hHC)
    let j : C.subgroupOf L →* C :=
      (L.subtype.comp (C.subgroupOf L).subtype).codRestrict C (fun x => x.property)
    let : Group.IsSolvable (C.subgroupOf L) := Group.isSolvable_of_isSolvable_injective
      (f := j) (by
        intro a b he
        exact Subtype.ext (Subtype.ext (congrArg (fun x : C => (x : G)) he)))
    have hh := map_mono (f := L.subtype) (le_solvableRadical (C.subgroupOf L)
      inferInstance inferInstance)
    rwa [subgroupOf_map_subtype] at hh
  exact ⟨hYmem,le_antisymm (sup_le (map_subtype_le _) (normalizerResidual_le L R))
    (hCY.trans (sup_le_sup_right hCrad Y))⟩


end CFSG.Quasithin.Chapter1.RadicalNormalizers
