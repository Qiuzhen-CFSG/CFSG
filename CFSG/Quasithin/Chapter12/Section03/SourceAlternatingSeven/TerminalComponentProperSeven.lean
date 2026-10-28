module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentProperEight
public import Theory.SpecificGroups.Alternating.SevenPerfectSylow
public import Theory.SpecificGroups.Alternating.SevenPerfectSylowLift

/-!
# Recognition of the residual in the proper A₇ overcomponent

The original local analysis gives natural coordinates and the weight-six
centralizer bound. The proved 12.3.7 action theorem then makes the full
normalizer act as S₇, with the original Sylow mapping onto a full Sylow.
The literal image of the escaping perfect residual is proper: equality
would lift through the O₂,Z kernel by Sylow normalization.

Minimal parabolicity descends to the image of the original H. The finite
seven-letter theorem identifies its residual image as A₅, and odd central
cover rigidity recovers K/O₂(K) through the same projection. No quotient
marking, cover splitting or residual-recognition callback is assumed.

Source: Aschbacher–Smith 12.2.7(2), printed p.797, and the terminal
application in 12.3.12, p.811. TerminalComponentSource applies this to the
entire original ComponentAnalysis.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V Y W : Subgroup G}
variable {S : Setup T L V} {D : S.LocalAnalysis}
namespace TerminalPoint
variable (P : TerminalPoint S D)

private theorem proper_image_ne_top
    (hlocal : P.K ∈ Chapter1.L G (T : Subgroup G))
    (hKY : P.K < Y) (SY : Setup T Y W) :
    (P.K.subgroupOf Y).map SY.projection ≠ ⊤ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let B := P.K.subgroupOf Y
  let : Group.IsPerfect P.K := Chapter1.mem_L_isPerfect hlocal
  let : Group.IsPerfect Y := Chapter1.mem_L_isPerfect SY.hypothesis.maximal_faithful.1.1
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKY.le).symm.toMonoidHom)
    (subgroupOfEquivOfLe hKY.le).symm.surjective
  obtain ⟨U,hU⟩ := (T.subtype
    (show (T : Subgroup G) ≤ Y ⊔ (T : Subgroup G) from le_sup_right)).exists_map_subtype_eq_inf_of_normalizes
      (show Y ≤ Y ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le Y.le_normalizer SY.chosen.sylow_normalizes_component)
  have hU' : (U : Subgroup Y).map Y.subtype = (T : Subgroup G) ⊓ Y := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using hU
  have hUT : (U : Subgroup Y) ≤ (T : Subgroup G).subgroupOf Y := by
    intro x hx
    exact (show (x : G) ∈ (T : Subgroup G) ⊓ Y from
      hU' ▸ mem_map_of_mem Y.subtype hx).1
  have hUB : (U : Subgroup Y) ≤ normalizer (B : Set Y) :=
    (hUT.trans (comap_mono P.sylow_normalizes_residual)).trans
      (le_normalizer_comap Y.subtype)
  have hk : SY.projection.ker = centralPreimage (pCore 2 Y) := by
    change (SY.quotient.toMonoidHom.comp (QuotientGroup.mk' _)).ker = _
    rw [MonoidHom.ker_comp_of_injective _ _ SY.quotient.injective,QuotientGroup.ker_mk']
    rfl
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isPGroup.isNilpotent
  intro he
  have ht : (⊤ : Subgroup Y) ≤ B :=
    perfect_le_of_map_le_of_kernel_central_mod_solvable SY.projection (pCore 2 Y)
      (hk.symm ▸ le_centralPreimage _)
      (by rw [hk]; exact map_comap_le _ _) ⊤ B
      ((pCore_isPGroup.le_sylow_of_normal U).trans hUB)
      (by rw [he]; exact le_top)
  exact hKY.not_ge (subgroupOf_eq_top.mp (top_unique ht))

/-- Recognition in an actual proper A₇ setup, retaining its central cover. -/
theorem proper_residual_five
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (hKY : P.K < Y) (SY : Setup T Y W) (DY : SY.LocalAnalysis) :
    Nonempty ((P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5)) := by
  let E : SY.NaturalCoordinates :=
    ⟨DY.model.coordinates,fun l v => by
      simpa only [DY.component_action] using
        DY.model.equivariant ⟨l,SY.chosen.normalizes l.property⟩ v⟩
  have hπ := (E.thompson_and_symmetric_of_weight_six structural escape (by
    intro z _ hz
    apply DY.pointCentralizers z ?_ (Or.inr hz)
    intro he
    have hh : weight (E.coordinates (1 : W)).toAdd.val = 0 := by
      simp only [map_one]; rfl
    rw [he] at hz
    omega)).2
  let N := normalizer (W : Set G)
  let π := (E.sourceNormalizerModel structural).permutation
  have hTN : (T : Subgroup G) ≤ N := ((structural G T Y SY.hypothesis).2.2 W SY.chosen).1
  have hKN : P.K ≤ N := hKY.le.trans SY.chosen.normalizes
  have hHN : P.H ≤ N := by
    rw [←P.residual_sup_sylow]
    exact sup_le hKN hTN
  let U := (T.subtype hTN).mapSurjective (f := π) hπ
  let B := P.K.subgroupOf Y
  let F := B.map SY.projection
  let C := F.map (alternatingGroup (Fin 7)).subtype
  let BN := P.K.subgroupOf N
  have hlocal := (P.residual_local_and_quasisimple structural modules hr hw).1
  let : Group.IsPerfect P.K := Chapter1.mem_L_isPerfect hlocal
  let : Group.IsPerfect Y := Chapter1.mem_L_isPerfect SY.hypothesis.maximal_faithful.1.1
  let eB : B ≃* P.K := subgroupOfEquivOfLe hKY.le
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := eB.symm.toMonoidHom) eB.symm.surjective
  let : Group.IsPerfect F := Group.IsPerfect.map _
  have hker : SY.projection.ker = centralPreimage (pCore 2 Y) := by
    change (SY.quotient.toMonoidHom.comp (QuotientGroup.mk' _)).ker = _
    rw [MonoidHom.ker_comp_of_injective _ _ SY.quotient.injective,QuotientGroup.ker_mk']
    rfl
  let : Group.IsSolvable SY.projection.ker := hker ▸ centralPreimage_pCore_isSolvable 2
  have hn : F ≠ ⊥ := by
    intro he
    have hs : Group.IsSolvable F := by rw [he]; infer_instance
    let : Group.IsSolvable B := (Group.isSolvable_map_iff_of_solvable_ker SY.projection B).mp hs
    exact Chapter1.mem_L_not_isSolvable hlocal
      (Group.isSolvable_of_surjective (f := eB.toMonoidHom) eB.surjective)
  have hp : F ≠ ⊤ := P.proper_image_ne_top hlocal hKY SY
  have himage : BN.map π = C := by
    ext a
    constructor
    · rintro ⟨k,hk,rfl⟩
      refine ⟨SY.projection ⟨k,hKY.le hk⟩,mem_map_of_mem SY.projection hk,?_⟩
      exact (E.sourceNormalizerModel_component structural ⟨k,hKY.le hk⟩).symm
    · rintro ⟨a,⟨k,hk,rfl⟩,rfl⟩
      exact ⟨⟨k,hKN hk⟩,hk,E.sourceNormalizerModel_component structural k⟩
  have hUB : (U : Subgroup (Equiv.Perm (Fin 7))) ≤ normalizer (C : Set (Equiv.Perm (Fin 7))) := by
    rw [←himage]
    exact (map_mono ((comap_mono P.sylow_normalizes_residual).trans
      (le_normalizer_comap N.subtype))).trans (le_normalizer_map π)
  let g : P.H →* Equiv.Perm (Fin 7) := π.comp (inclusion hHN)
  have hgr : g.range = C ⊔ (U : Subgroup (Equiv.Perm (Fin 7))) := by
    have hg : g.range = (P.H.subgroupOf N).map π := by
      ext a
      constructor
      · rintro ⟨h,rfl⟩
        exact ⟨⟨h,hHN h.property⟩,h.property,rfl⟩
      · rintro ⟨h,hh,rfl⟩
        exact ⟨⟨h,hh⟩,rfl⟩
    rw [hg,←P.residual_sup_sylow,subgroupOf_sup hKN hTN,Subgroup.map_sup,himage]
    rfl
  have hCg : C ≤ g.range := hgr.symm ▸ le_sup_left
  have hns : ¬ Group.IsSolvable g.range := by
    intro hs
    let := hs
    let j : F →* g.range :=
      ((alternatingGroup (Fin 7)).subtype.comp F.subtype).codRestrict g.range
        (fun a => hCg (mem_map_of_mem _ a.property))
    let : Group.IsSolvable F := Group.isSolvable_of_isSolvable_injective (f := j) (by
      intro a b h
      exact Subtype.ext (Subtype.ext (congrArg (fun x : g.range => x.val) h)))
    let : Nontrivial F := (nontrivial_iff_ne_bot F).mpr hn
    exact Group.IsPerfect.not_isSolvable F inferInstance
  have hu := (ChapterB.minimalParabolic_surjective_of_not_solvable
    (T.subtype P.minimal.1.1.2) (P.minimalParabolic structural hw)
    g.rangeRestrict g.rangeRestrict_surjective hns).1
  let J := C ⊔ (U : Subgroup (Equiv.Perm (Fin 7)))
  let eJ : g.range ≃* J := MulEquiv.subgroupCongr hgr
  let UH := (T.subtype P.minimal.1.1.2).mapSurjective g.rangeRestrict_surjective
  have heU : (UH : Subgroup g.range).map eJ.toMonoidHom =
      (U : Subgroup (Equiv.Perm (Fin 7))).subgroupOf J := by
    ext a
    constructor
    · rintro ⟨b,⟨h,hh,rfl⟩,rfl⟩
      exact mem_map_of_mem π (show (⟨h,hTN hh⟩ : N) ∈ (T : Subgroup G).subgroupOf N from hh)
    · intro ha
      obtain ⟨t,ht,he⟩ := ha
      refine ⟨g.rangeRestrict ⟨t,P.minimal.1.1.2 ht⟩,
        mem_map_of_mem g.rangeRestrict ht,?_⟩
      exact Subtype.ext he
  have hu' : Order.HasUniqueMaximalOver
      ((U : Subgroup (Equiv.Perm (Fin 7))).subgroupOf J) ⊤ := by
    have hh := hu.map eJ.mapSubgroup
    change Order.HasUniqueMaximalOver ((UH : Subgroup g.range).map eJ.toMonoidHom)
      ((⊤ : Subgroup g.range).map eJ.toMonoidHom) at hh
    rwa [heU,map_top_of_surjective _ eJ.surjective] at hh
  obtain ⟨eF⟩ := Theory.SpecificGroups.Alternating.SevenPerfectSylow.five_of_uniqueMaximal
    F hn hp U hUB hu'
  obtain ⟨q⟩ := Theory.SpecificGroups.Alternating.SevenPerfectSylow.core_five_of_image_five
    SY.projection SY.projection_surjective hker B eF
  exact ⟨(QuotientGroup.congr _ _ eB.symm (pCore_map_iso 2 eB.symm)).trans q⟩

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
