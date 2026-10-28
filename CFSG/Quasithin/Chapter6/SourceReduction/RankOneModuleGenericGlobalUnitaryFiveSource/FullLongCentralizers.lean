module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.MarkedCentralizers
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveSource.LongCentralizer

/-!
# Full long-root centralizers on the marked unitary-five extension

The original ambient long-root centralizer lies in the residual normalizer.
The same is true on the full native extension, by the projective matrix
calculation and the middle action. The published marking identifies the
literal endpoint elements, so these two full centralizers have equal order.
The comparison retains the whole overlap action and the same extension carrier.

Both source orientations are admitted; the unreversed branch is excluded by
the existing prepared-row theorem. This supplies the long-root centralizer
comparison used in Aschbacher–Smith F.4.42–43, printed pp.295–296.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem center_image_transport {X : Type*} [Group X]
    {K P : Subgroup G} {R Q : Subgroup X} (hKP : K ≤ P) (e : P ≃* Q)
    (hR : (K.subgroupOf P).map (Q.subtype.comp e.toMonoidHom) = R)
    (z : P) (hz : z.val ∈ (center K).map K.subtype) :
    (e z).val ∈ (center R).map R.subtype := by
  let f := Q.subtype.comp e.toMonoidHom
  obtain ⟨k,hk,hkz⟩ := hz
  have hez : z = ⟨k,hKP k.property⟩ := Subtype.ext hkz.symm
  rw [hez]
  let a : P := ⟨k,hKP k.property⟩
  have haR : f a ∈ R := hR ▸ mem_map_of_mem f k.property
  refine ⟨⟨f a,haR⟩,?_,rfl⟩
  apply mem_center_iff.mpr
  intro r
  obtain ⟨b,hb,he⟩ := (show r.val ∈ (K.subgroupOf P).map f from hR.symm ▸ r.property)
  apply Subtype.ext
  change r.val * f a = f a * r.val
  rw [←he,←map_mul,←map_mul]
  apply congrArg f
  apply Subtype.ext
  exact congrArg K.subtype (mem_center_iff.mp hk ⟨b,hb⟩)

omit [Finite G] in
private theorem nested_centralizer_card (M N : Subgroup G) (hMN : M ≤ N) (x : M)
    (hx : centralizer ({inclusion hMN x} : Set N) ≤ M.subgroupOf N) :
    Nat.card (centralizer ({x} : Set M)) =
      Nat.card (centralizer ({inclusion hMN x} : Set N)) := by
  let e := (subgroupOfEquivOfLe hMN).symm
  exact (Nat.card_congr (CentralizerSmallKernelTransport.centralizerEquiv e x).toEquiv).trans
    (Nat.card_congr (TwoInvolutionClassOrder.centralizerEquiv (M.subgroupOf N) (e x) hx))

variable {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The marked endpoint identifies ambient and full-extension long-root
centralizer orders, with full centralizer containment in the native endpoint. -/
theorem Preparation.unitaryFive_marked_full_long_centralizers
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U) :
    (∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam.reverse,
      ∃ f : UnitaryNativeLift.Five.LiftReverse U a,
      ∃ F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H)) r.extension.amalgam.reverse,
        (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
        (∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
        (∀ z, (F.middle z).val = (f.action z).val) ∧
        r.extension.carrier = inner U.Carrier ⊔
          ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
        r.extension.left = U.leftParabolic.map MulAut.conj ⊔
          ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
        r.extension.right = U.rightParabolic.map MulAut.conj ⊔
          ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
        r.extension.middle =
          ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
        (∀ z : normalizer (residual H : Set G),
          z.val ∈ (center (residual H)).map (residual H).subtype → orderOf z.val = 2 →
          centralizer ({inclusion r.extension.left_le (F.right z)} : Set r.extension.carrier) ≤
            r.extension.left.subgroupOf r.extension.carrier ∧
          Nat.card (centralizer ({z.val} : Set G)) =
            Nat.card (centralizer
              ({inclusion r.extension.left_le (F.right z)} : Set r.extension.carrier)))) := by
  have hs := d.unitaryFive_sourceS_eq h hH.1.1.2 hp U hc
  rcases r.marking with ⟨a,f,F,h0,h1,hD,hE,hleft,hright,hmiddle⟩ |
    ⟨a,f,F,h0,h1,hD,hE,hleft,hright,hmiddle⟩
  · exfalso
    apply d.not_unitaryFive_unreversed h hH.1.1.2 hp U
    rw [hs]
    exact ⟨a.comparison⟩
  · refine ⟨a,f,F,h0,h1,hD,hE,hleft,hright,hmiddle,?_⟩
    intro z hz hz2
    let P := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 1
    have hKP : residual H ≤ P := le_sup_left.trans le_sup_left
    have hzK : z.val ∈ residual H := (map_subtype_le _) hz
    let zP : P := ⟨z.val,hKP hzK⟩
    have hR : ((residual H).subgroupOf P).map
        (U.leftParabolic.subtype.comp a.comparison.right.toMonoidHom) = U.leftLocalImage := by
      have hres : (residual H).subgroupOf P = solvableResidual P := by
        have he : (solvableResidual P).map P.subtype = residual H :=
          d.reduced_parabolic_residuals h hH.1.1.2 hp (.unitaryFive U hc) 1
        rw [←he]
        exact comap_map_eq_self_of_injective P.subtype_injective _
      rw [hres,←map_map,map_solvableResidual_eq a.comparison.right.toMonoidHom
        a.comparison.right.surjective]
      rfl
    have hzn := center_image_transport hKP a.comparison.right hR zP hz
    have hzne : (a.comparison.right zP).val ≠ 1 := by
      intro hh
      have he : a.comparison.right zP = 1 := Subtype.ext hh
      have hzp : zP = 1 := a.comparison.right.map_eq_one_iff.mp he
      have hez : z.val = 1 := congrArg Subtype.val hzp
      simp [hez] at hz2
    have hmark : (F.right z).val = MulAut.conj (a.comparison.right zP).val := h1 zP
    have hbase : inclusion r.extension.left_le (F.right z) =
        r.extension.baseHom (a.comparison.right zP).val := Subtype.ext hmark
    have hfull : centralizer ({inclusion r.extension.left_le (F.right z)} :
        Set r.extension.carrier) ≤ r.extension.left.subgroupOf r.extension.carrier := by
      rw [hbase]
      exact FiveExtension.long_root_centralizer_le U r.extension _ hzn hzne
    refine ⟨hfull,?_⟩
    have hamb := d.unitaryFive_central_involution_centralizers h hH hp U hc 1 z hz hz2
    calc
      Nat.card (centralizer ({z.val} : Set G)) =
          Nat.card (centralizer ({z} : Set (normalizer (residual H : Set G)))) :=
        (Nat.card_congr (TwoInvolutionClassOrder.centralizerEquiv _ z hamb)).symm
      _ = Nat.card (centralizer ({F.right z} : Set r.extension.left)) :=
        Nat.card_congr (CentralizerSmallKernelTransport.centralizerEquiv F.right z).toEquiv
      _ = Nat.card (centralizer
          ({inclusion r.extension.left_le (F.right z)} : Set r.extension.carrier)) :=
        nested_centralizer_card _ _ r.extension.left_le (F.right z) hfull

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
