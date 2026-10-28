module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionAmbient
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.ExtendedAffinePlane
public import Theory.Representation.BinaryAlternatingFiveExtension.SylowCommutator.Transport

/-!
# The marked short-root Sylow centralizer in the exceptional source

The literal doubled plane is the affine symmetric-five group. Sylow
conjugacy preserves its translation core; this gives one comparison of the
actual source `T` retaining the original `Q₂`. The already proved identity
`[Q₂,f] = <t>` then selects a dihedral-factor center in its wreath Sylow.
Consequently the exact subgroup `C_T(t)` is `D₈ × D₈`, of order 64.
No exceptional enlargement or ambient fusion assumption is used.

Source: Aschbacher--Smith F.4.37 and F.5.3, printed pp.293, 300--301.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
open BinaryPermutation.AlternatingFiveExtension
open SylowCommutator
local notation "hn" => Nat.le_refl 1
local notation "PE" => Extension.plane 1 hn
local notation "U" => Extension.extendedUpper 1 hn

def extendedPlaneSylow : Sylow 2 PE := extendedUpperSylow.subtype (by
  have h := extendedUpper_le_overlap
  rw [←Extension.exact_overlap] at h
  exact h.trans inf_le_right)

variable {G G0 : Type*} [Group G] [Group G0]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)

theorem source_sylowImage_eq_planeSylow :
    (extendedPlaneSylow : Subgroup PE).map (endpointMap c i true) = Source.sylowImage c i := by
  apply le_antisymm
  · rintro x ⟨a,ha,rfl⟩
    refine ⟨⟨a.val,extendedUpper_le_overlap ha⟩,ha,?_⟩
    exact congrArg i (DFunLike.congr_fun c.compatible ⟨a.val,extendedUpper_le_overlap ha⟩)
  · rintro x ⟨b,hb,rfl⟩
    refine ⟨(Extension.amalgam 1 hn).right b,hb,?_⟩
    exact congrArg i (DFunLike.congr_fun c.compatible b).symm

/-- A marked affine Sylow model preserves the literal plane core. -/
theorem exists_source_marked_sylow_equiv (hi : Function.Injective i) :
    ∃ e : Source.sylowImage c i ≃* SylowModel.PlaneWreath,
      ((Q c i true).subgroupOf (Source.sylowImage c i)).map e.toMonoidHom = baseMap.range := by
  obtain ⟨E,hz,hQ,hB⟩ := UnitaryTwo.ExtendedAffinePlane.exists_marked_plane_equiv
  let j : Model →* G := (i.comp c.right).comp E.toMonoidHom
  have hj : Function.Injective j := (endpointMap_injective c i hi true).comp E.injective
  let S : Sylow 2 Model := extendedPlaneSylow.mapSurjective (f := E.symm.toMonoidHom) E.symm.surjective
  have hT : (S : Subgroup Model).map j = Source.sylowImage c i := by
    change (((extendedPlaneSylow : Subgroup PE).map E.symm.toMonoidHom).map j) = _
    rw [map_map]
    have hcomp : j.comp E.symm.toMonoidHom = i.comp c.right := by
      apply MonoidHom.ext
      intro x
      exact congrArg (i.comp c.right) (E.apply_symm_apply x)
    rw [hcomp]
    exact source_sylowImage_eq_planeSylow c i
  have hcore : translations.map j = Q c i true := by
    calc
      translations.map j =
          (translations.map E.toMonoidHom).map (i.comp c.right) := (map_map _ _ _).symm
      _ = UnitaryTwo.ExtendedAffinePlane.planeCore.map (i.comp c.right) :=
        congrArg (fun K : Subgroup PE => K.map (i.comp c.right)) hQ
      _ = (pCore 2 (planeParabolic 1 hn)).map ((i.comp c.right).comp Source.planeInclusion) := by
        rw [UnitaryTwo.ExtendedAffinePlane.planeCore,map_map]
        rfl
      _ = Q c i true := (Q_eq_map_pCore c i true).symm
  have hex := exists_marked_sylow_embedding_equiv j hj S
  rw [hT,hcore] at hex
  exact hex

variable [Finite G]

/-- The marked short involution has the exact Sylow centralizer D₈ × D₈. -/
theorem source_short_Tcentralizer_iso (hi : Function.Injective i) :
    Nonempty (Tcentralizer c i (sourceMarkedShort c i) ≃* DihedralGroup 4 × DihedralGroup 4) := by
  obtain ⟨e,he⟩ := exists_source_marked_sylow_equiv c i hi
  exact centralizer_of_marked_equiv _ _ (source_Q_plane_le_sylowImage c i) e he
    (Source.graphElement c i) (sourceMarkedShort c i)
    (source_graph_mem_sylowImage c i) (source_short_mem_Q c i)
    (source_short_order c i hi) (source_short_commutator c i hi)

theorem source_short_Tcentralizer_card (hi : Function.Injective i) :
    Nat.card (Tcentralizer c i (sourceMarkedShort c i)) = 64 := by
  obtain ⟨e⟩ := source_short_Tcentralizer_iso c i hi
  rw [Nat.card_congr e.toEquiv,Nat.card_prod,DihedralGroup.nat_card]

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
