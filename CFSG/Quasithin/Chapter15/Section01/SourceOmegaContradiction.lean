module
public import CFSG.Quasithin.Chapter15.Section01.SourceOmegaPointEights
public import CFSG.Quasithin.Chapter15.Section01.SourceElementaryEightObstruction
public import Theory.SpecificGroups.OrthogonalFourBinary.OmegaEightPlaneLift


/-!
# The two-point-eights Omega contradiction

The solvable full-Omega source branch produces two distinct, T-normal elementary
8-subgroups with point images.  If the generated ambient subgroup has the
literal Omega quotient with kernel V, the binary orthogonal geometry selects a
plane image for one of the two eights.  The source elementary-eight obstruction
then gives the contradiction needed by the solvable branch of 15.1.11(1).
The selected quotient is retained throughout.

Source: Aschbacher--Smith 15.1.11(1), printed p.1089.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The literal Omega quotient turns the two actual point eights into a source contradiction. -/
theorem source_two_point_eights_impossible_of_omega_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T=∅)
    (P V L E F : Subgroup G) [IsElementaryAbelian 2 V]
    (hVcard : Nat.card V=16) (hST : P⊔V≤(T : Subgroup G)) (hSL : P⊔V≤L)
    (hne : E≠F)
    (hEF : ∀ U∈({E,F} : Set (Subgroup G)), IsElementaryAbelian 2 U ∧ Nat.card U=8 ∧
      U≤P ∧ (T : Subgroup G)≤normalizer (U : Set G) ∧
      (P⊔V)⊓centralizer (U : Set G)=U ∧ Nonempty (ElementaryEightPointImage U))
    (q : L →* OrthogonalFourBinary.omega) (hq : Function.Surjective q)
    (hk : q.ker=V.subgroupOf L) (e : q.ker ≃ OrthogonalFourBinary.Space)
    (hact : ∀ (g:L) (a:q.ker),e (MulAut.conjNormal g a)=q g • e a) : False := by
  have hVL : V≤L := le_sup_right.trans hSL
  let A := (P⊔V).subgroupOf L
  let U := E.subgroupOf L
  let W := F.subgroupOf L
  have hlocal (D : Subgroup G) (hD : D∈({E,F} : Set (Subgroup G))) :
      D≤L ∧ IsElementaryAbelian 2 (D.subgroupOf L) ∧ Nat.card (D.subgroupOf L)=8 ∧
      A≤normalizer (D.subgroupOf L : Set L) ∧
      A⊓centralizer (D.subgroupOf L : Set L)=D.subgroupOf L := by
    obtain ⟨he,hc,hP,hN,hcent,_⟩ := hEF D hD
    let := he
    have hDL : D≤L := hP.trans (le_sup_left.trans hSL)
    refine ⟨hDL,IsElementaryAbelian.subgroupOf hDL,?_,?_,?_⟩
    · rw [Nat.card_congr (subgroupOfEquivOfLe hDL).toEquiv,hc]
    · rw [←subgroupOf_normalizer_eq hDL]
      exact fun _ ha => hN (hST ha)
    · apply map_injective L.subtype_injective
      rw [←map_inf_centralizer_of_injective L.subtype L.subtype_injective,
        map_subgroupOf_eq_of_le hSL,map_subgroupOf_eq_of_le hDL,hcent]
  obtain ⟨hEL,hU,hUc,hUN,hUC⟩ := hlocal E (Or.inl rfl)
  obtain ⟨hFL,hW,hWc,hWN,hWC⟩ := hlocal F (Or.inr rfl)
  have hUW : U≠W := by
    intro h
    apply hne
    have hh := congrArg (map L.subtype) h
    change (E.subgroupOf L).map L.subtype = (F.subgroupOf L).map L.subtype at hh
    rw [map_subgroupOf_eq_of_le hEL, map_subgroupOf_eq_of_le hFL] at hh
    exact hh
  have hA : IsElementaryAbelian 2 q.ker := hk.symm ▸ IsElementaryAbelian.subgroupOf hVL
  have hAc : Nat.card q.ker=16 := by
    rw [hk,Nat.card_congr (subgroupOfEquivOfLe hVL).toEquiv,hVcard]
  have hkerA : q.ker≤A := by
    rw [hk]
    exact fun _ hv => mem_sup_right hv
  have hout := OrthogonalFourBinary.SylowGeometry.omega_two_elementaryEights_plane_image_map
    q hq e hact hA hAc A U W hU hUc hW hWc hkerA hUN hWN hUC hWC hUW
    L.subtype L.subtype_injective
  change Nonempty (ElementaryEightPlaneImage ((E.subgroupOf L).map L.subtype)) ∨
    Nonempty (ElementaryEightPlaneImage ((F.subgroupOf L).map L.subtype)) at hout
  rw [map_subgroupOf_eq_of_le hEL,map_subgroupOf_eq_of_le hFL] at hout
  have finish (D : Subgroup G) (hD : D∈({E,F} : Set (Subgroup G)))
      (plane : Nonempty (ElementaryEightPlaneImage D)) : False := by
    obtain ⟨he,hc,hDP,hTN,_,point⟩ := hEF D hD
    let := he
    exact source_elementaryEight_plane_point_impossible hG T hempty D hc
      (hDP.trans (le_sup_left.trans hST)) hTN plane.some point.some
  exact hout.elim (finish E (Or.inl rfl)) (finish F (Or.inr rfl))
end CFSG.Quasithin.Chapter15.Section01
