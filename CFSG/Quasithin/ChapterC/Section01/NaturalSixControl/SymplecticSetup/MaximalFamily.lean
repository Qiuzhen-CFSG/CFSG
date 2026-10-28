module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.Model.PlaneLattice
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.MaximalOffenders
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.PointFull

/-!
# The maximal family in the original binary symplectic source

In the full point-core branch there are exactly three maximum-order small
movers. Every pair of distinct members generates the original radical;
their intersection is the full preimage of the marked transposition line.
That image has order two, and its fixed subgroup on the natural module has
index two. All statements retain the original projection and kernel.

The last theorem applies this to the literal characteristic replacement.
The existing point-image dichotomy supplies either an alternating block or
this full family, so no extra image or family premise remains in the consumer.
The later geometric contradiction remains a separate source argument.

Source: Meierfrankenfeld--Stellmacher (1993), (5.4), printed p.915;
Aschbacher--Smith C.1.37 and13.7.4(1).
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace SmallImages

theorem plane_injective (g : Model.S) : Function.Injective (plane g) := by
  intro i j he
  exact Model.corePlane_injective ((map_injective (MulAut.conj g).injective) he)

theorem plane_inf_of_ne (g : Model.S) {i j : Fin 3} (hne : i ≠ j) :
    plane g i ⊓ plane g j = last.map (MulAut.conj g).toMonoidHom := by
  rw [plane,plane,←map_inf _ _ _ (MulAut.conj g).injective,Model.corePlane_inf_of_ne hne]

theorem plane_sup_of_ne (g : Model.S) {i j : Fin 3} (hne : i ≠ j) :
    plane g i ⊔ plane g j = Model.E.map (MulAut.conj g).toMonoidHom := by
  rw [plane,plane,←Subgroup.map_sup,Model.corePlane_sup_of_ne hne]

end SmallImages
namespace Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M}
  [L.Normal] [W.Normal] (s : Source L R W)

omit [Finite M] in
private theorem plane_preimage_image (g : Model.S)
    (hR : R.map s.projection = Model.E.map (MulAut.conj g).toMonoidHom) (i : Fin 3) :
    ((SmallImages.plane g i).comap s.projection).map s.projection = SmallImages.plane g i :=
  map_comap_eq_self ((SmallImages.plane_le g i).trans (hR ▸ map_le_range s.projection R))

theorem maximalOffenders_ncard (g : Model.S)
    (hR : R.map s.projection = Model.E.map (MulAut.conj g).toMonoidHom) :
    s.maximalOffenders.ncard = 3 := by
  have he : s.maximalOffenders = Set.range (fun i : Fin 3 =>
      (SmallImages.plane g i).comap s.projection) := by
    ext E
    simpa only [Set.mem_range,eq_comm] using s.mem_maximalOffenders_iff g hR E
  have hinj : Function.Injective (fun i : Fin 3 =>
      (SmallImages.plane g i).comap s.projection) := by
    intro i j hij
    apply SmallImages.plane_injective g
    rw [←plane_preimage_image s g hR i,←plane_preimage_image s g hR j]
    exact congrArg (Subgroup.map s.projection) hij
  rw [he,Set.ncard_range_of_injective hinj]
  simp

theorem maximalOffenders_pair (g : Model.S)
    (hR : R.map s.projection = Model.E.map (MulAut.conj g).toMonoidHom)
    {E F : Subgroup M} (hE : E ∈ s.maximalOffenders) (hF : F ∈ s.maximalOffenders)
    (hne : E ≠ F) :
    E ⊔ F = R ∧ E ⊓ F = (last.map (MulAut.conj g).toMonoidHom).comap s.projection := by
  obtain ⟨i,rfl⟩ := (s.mem_maximalOffenders_iff g hR E).mp hE
  obtain ⟨j,rfl⟩ := (s.mem_maximalOffenders_iff g hR F).mp hF
  have hij : i ≠ j := by rintro rfl; exact hne rfl
  constructor
  · rw [comap_sup_eq_of_le_range _
      ((SmallImages.plane_le g i).trans (hR ▸ map_le_range s.projection R))
      ((SmallImages.plane_le g j).trans (hR ▸ map_le_range s.projection R)),
      SmallImages.plane_sup_of_ne g hij,←hR]
    apply comap_map_eq_self
    rw [s.projection_kernel]
    exact s.core_le
  · rw [←comap_inf,SmallImages.plane_inf_of_ne g hij]

theorem maximalOffenders_intersection (g : Model.S)
    (hR : R.map s.projection = Model.E.map (MulAut.conj g).toMonoidHom)
    {E F : Subgroup M} (hE : E ∈ s.maximalOffenders) (hF : F ∈ s.maximalOffenders)
    (hne : E ≠ F) :
    Nat.card ((E ⊓ F).map s.projection) = 2 ∧
      Nat.card (E ⊓ F : Subgroup M) = Nat.card (pCore 2 M) * 2 ∧
      (centralizer ((E ⊓ F : Subgroup M) : Set M)).relIndex W = 2 := by
  have hp := (s.maximalOffenders_pair g hR hE hF hne).2
  have himage : (E ⊓ F).map s.projection = last.map (MulAut.conj g).toMonoidHom := by
    rw [hp]
    exact map_comap_eq_self ((map_mono last_le_exceptional).trans
      (hR ▸ map_le_range s.projection R))
  have hc : Nat.card ((E ⊓ F).map s.projection) = 2 := by
    rw [himage,card_map_of_injective (MulAut.conj g).injective,card_last]
  refine ⟨hc,?_,?_⟩
  · have hker : s.projection.ker ≤ E ⊓ F := by
      rw [hp]
      exact ker_le_comap _ _
    have hcard := relIndex_mul_relIndex (⊥ : Subgroup M) s.projection.ker (E ⊓ F) bot_le hker
    rw [relIndex_bot_left,relIndex_bot_left,relIndex_ker,hc,s.projection_kernel] at hcard
    exact hcard.symm
  · rw [s.fixed_index,himage,Representation.BinaryOffender.fixedCodim_map_conj]
    rw [fixedCodim_last.2.2.2]
    rfl

end Source

namespace SourceData
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {K : Type*} [Group K] [Finite K] {L W : Subgroup K}
  [L.Normal] [W.Normal] {T : Sylow 2 K} (d : NaturalSixControl.SourceData L W T)

/-- The full point-core branch of source(5.4), on the original characteristic
replacement and its inherited coordinate map. -/
theorem reducedSource_maximalFamily (h : IntrinsicMSPair d)
    (c : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B)))
    (hfull : c.radical.map ((originalSource d h).reduce c).projection =
      Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom) :
    let s := (originalSource d h).reduce c
    s.maximalOffenders.ncard = 3 ∧ s.offenderJoin = c.radical ∧
      ∀ E ∈ s.maximalOffenders, ∀ F ∈ s.maximalOffenders, E ≠ F →
        E ⊔ F = c.radical ∧ Nat.card ((E ⊓ F).map s.projection) = 2 ∧
          Nat.card (E ⊓ F : Subgroup c.overgroup) = Nat.card (pCore 2 c.overgroup) * 2 ∧
          (centralizer ((E ⊓ F : Subgroup c.overgroup) : Set c.overgroup)).relIndex
            ((W.subgroupOf (L ⊔ d.B)).subgroupOf c.overgroup) = 2 := by
  let s := (originalSource d h).reduce c
  refine ⟨s.maximalOffenders_ncard d.relabeler.val⁻¹ hfull,
    s.offenderJoin_eq d.relabeler.val⁻¹ hfull,?_⟩
  intro E hE F hF hne
  exact ⟨(s.maximalOffenders_pair d.relabeler.val⁻¹ hfull hE hF hne).1,
    s.maximalOffenders_intersection d.relabeler.val⁻¹ hfull hE hF hne⟩

/-- The original source supplies either its final block or the full source(5.4)
family, with the point-image branch discharged. -/
theorem reducedSource_alternatingBlock_or_maximalFamily (h : IntrinsicMSPair d)
    (c : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B))) :
    IsAlternatingBlock L 6 ∨
    let s := (originalSource d h).reduce c
    s.maximalOffenders.ncard = 3 ∧ s.offenderJoin = c.radical ∧
      ∀ E ∈ s.maximalOffenders, ∀ F ∈ s.maximalOffenders, E ≠ F →
        E ⊔ F = c.radical ∧ Nat.card ((E ⊓ F).map s.projection) = 2 ∧
          Nat.card (E ⊓ F : Subgroup c.overgroup) = Nat.card (pCore 2 c.overgroup) * 2 ∧
          (centralizer ((E ⊓ F : Subgroup c.overgroup) : Set c.overgroup)).relIndex
            ((W.subgroupOf (L ⊔ d.B)).subgroupOf c.overgroup) = 2 := by
  rcases reducedSource_block_or_full_point_image d h c with hb | hf
  · exact Or.inl hb
  · apply Or.inr
    apply reducedSource_maximalFamily d h c
    simpa only [Model.pointCore_eq_exceptional] using hf

end SourceData
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
