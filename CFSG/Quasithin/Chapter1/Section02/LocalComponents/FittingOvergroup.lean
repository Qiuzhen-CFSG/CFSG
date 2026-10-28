module
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreOvergroup
public import Theory.GroupTheory.CComponent.SolvableImageNormality
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralNormality

/-!
# Nonnormal C-components in an overgroup of the two-core Fitting preimage

Let M contain the preimage of F*(G/O₂(G)). A nonnormal C-component of M
is a C-component of G. The image of M has trivial two-core. Its nonnormal
C-component image is therefore quasisimple by A.3.8(3), hence an ordinary
component. Ordinary component promotion through F* and solvable-quotient
lifting recover an ambient C-component. Kernel containment and minimality
identify this lift with the original local component.

This gives precisely the contrary-normality branch used in
Aschbacher--Smith C.2.13 and C.4.8, printed pp.148,153. It does not assert
promotion of an arbitrary normal C-component through an overgroup of F*.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

/-- A nonnormal local C-component promotes through the two-core Fitting preimage. -/
theorem nonnormal_cComponent_of_twoCore_fitting_overgroup {B M : Subgroup G} (hBM : B ≤ M)
    (hB : (B.subgroupOf M).IsCComponent) (hn : ¬ (B.subgroupOf M).Normal)
    (hQ : IsSQTK κ (G ⧸ pCore 2 G))
    (hF : (generalizedFitting (G ⧸ pCore 2 G)).comap
      (QuotientGroup.mk' (pCore 2 G)) ≤ M) : B.IsCComponent := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let C := M.map q
  let f := q.subgroupMap M
  let D := B.map q
  let : Group.IsNilpotent (pCore 2 G) := pCore_isNilpotent
  let : Group.IsSolvable f.ker := by
    change Group.IsSolvable (q.subgroupMap M).ker
    rw [ker_subgroupMap]
    change Group.IsSolvable ((QuotientGroup.mk' (pCore 2 G)).ker.subgroupOf M)
    rw [QuotientGroup.ker_mk']
    change Group.IsSolvable ((pCore 2 G).comap M.subtype)
    exact Group.isSolvable_of_isSolvable_injective
      (f := M.subtype.subgroupComap (pCore 2 G)) (fun a b he =>
        Subtype.ext (Subtype.ext (congrArg (fun x : pCore 2 G => (x : G)) he)))
  have he : (B.subgroupOf M).map f = D.subgroupOf C := by
    ext x
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact mem_map.mpr ⟨b,hb,rfl⟩
    · rintro ⟨b,hb,hbx⟩
      exact ⟨⟨b,hBM hb⟩,hb,Subtype.ext hbx⟩
  have hD : (D.subgroupOf C).IsCComponent :=
    he ▸ cComponent_map_of_solvable_ker hB f (q.subgroupMap_surjective M)
  have hDn : ¬ (D.subgroupOf C).Normal := by
    intro hh
    exact hn (cComponent_normal_of_solvable_image_normal hB f (q.subgroupMap_surjective M) (he.symm ▸ hh))
  have hFC : generalizedFitting (G ⧸ pCore 2 G) ≤ C := by
    have hh := map_mono (f := q) hF
    rwa [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at hh
  have hDC : D ≤ C := map_mono hBM
  have hDcomp : IsComponent (G ⧸ pCore 2 G) D :=
    IsComponent.of_generalizedFitting_overgroup hDC
      ⟨hD.subnormal, (ChapterA.Section03.NoncentralNormality.normal_or_quasisimple
        (hQ.subgroup C) (twoCore_eq_bot_of_generalizedFitting_le C hFC (pCore_quotient_pCore_eq_bot 2)) hD).resolve_left hDn⟩ hFC
  let := hB.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hBM).toMonoidHom) (subgroupOfEquivOfLe hBM).surjective
  obtain ⟨K,hK,hBK,himage⟩ := exists_cComponent_lift_containing_map
    (B := B) (pCore 2 G) hDcomp.isCComponent le_rfl
  have hKM : K ≤ M := by
    have hh : K ≤ B ⊔ pCore 2 G := by
      simpa only [D,q,comap_map_eq,QuotientGroup.ker_mk'] using
        map_le_iff_le_comap.mp himage.le
    apply hh.trans
    apply sup_le hBM
    have hk : pCore 2 G ≤ (generalizedFitting (G ⧸ pCore 2 G)).comap q := by
      simpa only [q,QuotientGroup.ker_mk'] using
        MonoidHom.ker_le_comap q (generalizedFitting (G ⧸ pCore 2 G))
    exact hk.trans hF
  have hBK' := hB.eq_of_le (hK.subgroupOf hKM) (comap_mono hBK)
  have hBK'' : B = K := by
    have hh := congrArg (map M.subtype) hBK'
    simpa only [map_subgroupOf_eq_of_le hBM,map_subgroupOf_eq_of_le hKM] using hh
  exact hBK''.symm ▸ hK

end CFSG.Quasithin.Chapter1.Section02
