module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.MovingSection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.NaturalLayerModel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.NaturalLayerMS
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.FrattiniCore
public import Theory.GroupTheory.GeneralizedFitting.InternalModuleResidual

/-!
# Recognition from the whole intrinsic Sp4(4) core

When the intrinsic commutator core of the actual component equals the moving
part of Ω₁(Z(O₂(H))), its original conjugation action and fixed subgroup give
the required short-group and natural Sp4(4) block structure. The final theorem
establishes every clause in the Frattini-small branch of MS93 (3.6).

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two,
(3.2), (3.6); Aschbacher--Smith C.1.32.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H : Type*} [Group H] [Finite H]

private theorem perfect_twoPerfect {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] : IsPPerfect 2 E := by
  intro N hn hp
  let := hn
  by_contra hne
  let : Nontrivial (E ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (E ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  exact Group.IsPerfect.not_isNilpotent (E ⧸ N) hp.isNilpotent

theorem block_of_intrinsic_core_eq
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hfit : generalizedFitting H = pCore 2 H)
    (hker : (QuotientGroup.mk' (pCore 2 H)).ker =
      centralizer (omegaCenterIn (pCore 2 H) : Set H))
    [(K.map (QuotientGroup.mk' (pCore 2 H))).Normal]
    [IsQuasisimple (K.map (QuotientGroup.mk' (pCore 2 H)))]
    (he : (blockU K).map K.subtype = ⁅omegaCenterIn (pCore 2 H),K⁆)
    (hi : IsIrrPlus (NormalElementaryQuotient.representation
      (omegaCenterIn (pCore 2 H)) (QuotientGroup.mk' (pCore 2 H))
      (QuotientGroup.mk'_surjective _) hker)
      (K.map (QuotientGroup.mk' (pCore 2 H)))
      (subspaceCommutator (NormalElementaryQuotient.representation
        (omegaCenterIn (pCore 2 H)) (QuotientGroup.mk' (pCore 2 H))
        (QuotientGroup.mk'_surjective _) hker) ⊤
        (K.map (QuotientGroup.mk' (pCore 2 H)))))
    (hnat : HasNaturalMovingSection (NormalElementaryQuotient.representation
      (omegaCenterIn (pCore 2 H)) (QuotientGroup.mk' (pCore 2 H))
      (QuotientGroup.mk'_surjective _) hker)
      (K.map (QuotientGroup.mk' (pCore 2 H)))) : IsSp4FourBlock K := by
  let X := omegaCenterIn (pCore 2 H)
  let q := QuotientGroup.mk' (pCore 2 H)
  let ρ := NormalElementaryQuotient.representation X q (QuotientGroup.mk'_surjective _) hker
  let C := K.map q
  have hUX : (blockU K).map K.subtype ≤ X := by
    rw [he]
    exact commutator_le_left _ _
  have helem : IsElementaryAbelian 2 (blockU K) := by
    let i : blockU K →* X := {
      toFun x := ⟨x.val.val,hUX (mem_map_of_mem K.subtype x.property)⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    exact IsElementaryAbelian.of_injective i (fun _ _ h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : X => (z : H)) h)))
  have hcentral : blockU K ≤ centralizer (pCore 2 K : Set K) := by
    have hQKQ : (pCore 2 K).map K.subtype ≤ pCore 2 H :=
      le_sSup ⟨inferInstance,pCore_isPGroup.map K.subtype⟩
    intro u hu y hy
    have hx := (mem_omegaCenterIn_iff _ _).mp
      (hUX (mem_map_of_mem K.subtype hu))
    apply Subtype.ext
    exact hx.2.1 y (hQKQ (mem_map_of_mem K.subtype hy))
  let := hK.perfect
  have hfitK : generalizedFitting K = pCore 2 K := by
    apply le_antisymm _ ((pCore_le_fitting K 2).trans (fitting_le_generalizedFitting K))
    rw [pCore_subnormal_eq_comap 2 hK.subnormal]
    apply map_le_iff_le_comap.mp
    rw [← hfit]
    exact generalizedFitting_map_subtype_le_of_isSubnormal K hK.subnormal
  have hshort : IsShort K := ⟨inferInstance,perfect_twoPerfect,hfitK,helem,hcentral,
    Or.inl (IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK).symm),
    BlockMovingSection.irreducible_of_moving X K q (QuotientGroup.mk'_surjective _) hker he hi⟩
  obtain ⟨F,hF,⟨E⟩⟩ := hnat
  have hm : IsLinearBlockModel K (binarySymplectic F) :=
    BlockMovingSection.model_of_moving X K q (QuotientGroup.mk'_surjective _) hker he
      (cComponentTwoCoreQuotientEquiv hK) (fun _ => rfl) _ E
  obtain ⟨r,hr,ha⟩ := hm
  refine ⟨hshort,F.Carrier,inferInstance,inferInstance,?_,r,hr,?_⟩
  · simpa only [F.card_eq,hF] using (show 2 ^ 2 = 4 by decide)
  · exact ha

/-- Every short-group and natural-model clause follows in the Frattini-small
source branch, from the actual MS characteristic condition. -/
theorem block_of_frattini_small_ms
    (K R : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hfit : generalizedFitting H = pCore 2 H)
    (hms : MSCharacteristicCondition R)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hQR : pCore 2 H ≤ R)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H)
    [(K.map (QuotientGroup.mk' (pCore 2 H))).Normal]
    [IsSimpleGroup (K.map (QuotientGroup.mk' (pCore 2 H)))]
    [IsQuasisimple (K.map (QuotientGroup.mk' (pCore 2 H)))]
    (hc : Nat.card (K.map (QuotientGroup.mk' (pCore 2 H))) = 979200)
    (hC : centralizer (K.map (QuotientGroup.mk' (pCore 2 H)) :
      Set (H ⧸ pCore 2 H)) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple
      (K.map (QuotientGroup.mk' (pCore 2 H))))
    (hsmall : ⁅pCore 2 H,K⁆ ≤
      (frattini (pCore 2 H)).map (pCore 2 H).subtype ⊔
        omegaCenterIn (pCore 2 H)) : IsSp4FourBlock K := by
  let := hK.perfect
  obtain ⟨he,_,_⟩ := intrinsic_core_of_frattini_small K perfect_twoPerfect hsmall
  obtain ⟨hi,hnat⟩ := centralOmega_moved_natural R hms hp hne hQR hself hfaith
    (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) (K.map (QuotientGroup.mk' (pCore 2 H))) hc hC hsq
  exact block_of_intrinsic_core_eq K hK hfit
    ((QuotientGroup.ker_mk' _).trans
      (centralOmega_centralizer R hQR hself hfaith).symm) he hi hnat

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
