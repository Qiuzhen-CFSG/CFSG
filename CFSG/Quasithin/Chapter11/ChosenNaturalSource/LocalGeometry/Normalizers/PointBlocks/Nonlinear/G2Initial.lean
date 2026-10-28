module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear.G2Recognition
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Conditions
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.Restriction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedCover
public import Theory.Representation.NormalElementaryQuotient.IrrPlusCommutator
public import Theory.AtlasPort.LinearGroups.G2.Simplicity
public import Theory.Quasithin.CoprimeRank

/-!
# The initial exceptional MS action on the literal point pair

For J=LR₁, the source odd-index witness supplies O₂(J)≤R₁ and the original
escape supplies MS3 relative to J. Simplicity of the marked nonbinary G₂
quotient makes its central omega action faithful. The full FF theorem then
recognizes the canonical moved/fixed section over the original field degree.
The omega orbit has that same commutator, so this is the actual initial layer
of the MS amalgam. The canonical projection is a cover; its fixed kernel is
retained, including at field four.

The later reciprocal-action exclusion remains with this point-normalizer
owner. No hypothesis that T is contained in LR₁ is used.
Source: Aschbacher--Smith C.1.31 and 11.1.5, pp.135,765; MS93 (3.2).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear
open ChapterC ChapterC.MSCentralOrbit ChapterC.RankTwo.NonbinarySymplectic
variable {H : Type*} [Group H]

/-- The genuine exceptional specialization of C.1.31, on its intrinsic group.
No natural-layer, field-four or exclusion conclusion is a field. -/
structure G2Input (K R : Subgroup H) (F : BinaryField) where
  nonbinary : 1 < F.degree
  sqtk : IsSQTK KnownSimple.IsKnownSimple H
  fitting : generalizedFitting H = pCore 2 H
  component : K.IsCComponent
  product : ∀ g : H, ∃ k ∈ K, ∃ r ∈ R, k*r=g
  radical : MSOddIndexRadical R
  characteristic : MSCharacteristicCondition R
  quotientEquiv : (K ⧸ pCore 2 K) ≃* Atlas.G2.Model F.Carrier

variable {K R : Subgroup H} {F : BinaryField} (h : G2Input K R F)
include h

private theorem point_simple : IsSimpleGroup (K ⧸ pCore 2 K) := by
  let : IsSimpleGroup (Atlas.G2.Model F.Carrier) := Atlas.G2.isSimple
    (by
      rw [F.card_eq]
      exact (show (2:ℕ)^1 < 2^F.degree from
        Nat.pow_lt_pow_right (by decide) h.nonbinary))
  exact (h.quotientEquiv).isSimpleGroup


private theorem point_radical : MSOddIndexRadical R := h.radical
private theorem point_characteristic : MSCharacteristicCondition R := h.characteristic
private theorem point_product : ∀ g : H, ∃ k ∈ K, ∃ r ∈ R, k*r=g := h.product

variable [Finite H]

/-- The original component is exactly the two-residual inside LR₁. -/
theorem G2Input.residual_eq : pResidual 2 H = K :=
  component_eq_residual K R h.component (point_radical h).isPGroup
    (point_product h)

private theorem point_selfCentralizing : centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  simpa only [h.fitting] using centralizer_generalizedFitting_le H

private theorem point_radical_ne_bot : R ≠ ⊥ := by
  intro hr
  have hq : pCore 2 H = ⊥ := le_bot_iff.mp (hr ▸ (point_radical h).twoCore_le)
  have ht : (⊤ : Subgroup H) ≤ ⊥ := by
    intro x _
    have hc : x ∈ centralizer (pCore 2 H : Set H) := by
      rw [hq]
      intro y hy
      have hy' : y = 1 := hy
      simp only [hy',one_mul,mul_one]
    exact hq ▸ point_selfCentralizing h hc
  exact h.component.ne_bot (le_bot_iff.mp (le_top.trans ht))

/-- MS3 makes the actual omega-center orbit faithful modulo O₂(LR₁). -/
theorem G2Input.omegaOrbit_centralizer :
    centralizer (omegaOrbit R : Set H) = pCore 2 H := by
  let : (K).Normal := by rw [←h.residual_eq]; infer_instance
  let := point_simple h
  exact MSCentralOrbit.omegaOrbit_centralizer K R (point_radical h).isPGroup
    (point_radical_ne_bot h) (point_radical h).twoCore_le
    (point_selfCentralizing h) (point_product h)
    (point_characteristic h)

/-- Positive even critical geometry is constructed for the original point radical. -/
theorem G2Input.critical_geometry :
    (∃ g : BinaryMS.MS93.Geometry R, 0 < g.b R ∧ Even (g.b R)) ∧
      BinaryMS.MS93.EdgeCentralizerCondition R := by
  have hp := (point_radical h).isPGroup
  have hQR := (point_radical h).twoCore_le
  have hf := h.omegaOrbit_centralizer
  exact ⟨exists_positive_even_geometry R hp (point_radical_ne_bot h)
    (point_characteristic h) hQR (point_selfCentralizing h) hf,
    edgeCentralizerCondition R hp hQR hf⟩

/-- The original component image has its exact normal simple structure. -/
theorem G2Input.image_structure :
    let B := (K).map (QuotientGroup.mk' (pCore 2 H))
    (K).Normal ∧ B.Normal ∧ IsSimpleGroup B ∧ IsQuasisimple B ∧
      centralizer (B : Set (H ⧸ pCore 2 H)) = ⊥ := by
  let := point_simple h
  exact component_image_structure K R h.component
    (point_radical h).isPGroup (point_product h)

private theorem point_image_card :
    Nat.card ((K).map (QuotientGroup.mk' (pCore 2 H))) = Nat.card (Atlas.G2.Model F.Carrier) :=
  (Nat.card_congr (cComponentTwoCoreQuotientEquiv h.component).symm.toEquiv).trans
    (Nat.card_congr (h.quotientEquiv).toEquiv)

private theorem point_image_sqtk :
    IsSQTK KnownSimple.IsKnownSimple ((K).map (QuotientGroup.mk' (pCore 2 H))) := by
  have hk := h.sqtk.subgroup K
  have hq : IsSQTK KnownSimple.IsKnownSimple (K ⧸ pCore 2 K) := by
    refine ⟨?_,hk.isKGroup.quotient (pCore 2 K)⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    rw [primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 K) pCore_isPGroup]
    exact hk.stronglyQuasithin p hp ho
  exact (IsSQTK.equiv (cComponentTwoCoreQuotientEquiv h.component)).mp hq

/-- The genuine FF input recognizes the original point's moved/fixed quotient,
with the degree of the supplied marking and no field-four assumption. -/
theorem G2Input.initial_module :
    let q := QuotientGroup.mk' (pCore 2 H)
    let B := (K).map q
    let X := omegaCenterIn (pCore 2 H)
    ∃ hker : q.ker = centralizer (X : Set H), ∃ hn : B.Normal,
      let := hn
      let ρ := NormalElementaryQuotient.representation X q
        (QuotientGroup.mk'_surjective _) hker
      IsIrrPlus ρ B (subspaceCommutator ρ ⊤ B) ∧
        ∃ E : BinaryField, E.degree = F.degree ∧
          Nonempty (ActionEquiv ((MovedSection.ofNormal ρ B).action.comp B.subtype)
            (binaryG2 E)) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := (K).map q
  let X := omegaCenterIn (pCore 2 H)
  obtain ⟨hK,hB,hs,hqs,hC⟩ := h.image_structure
  let := hK
  let := hB
  let := hs
  let := hqs
  have hp := (point_radical h).isPGroup
  have hQR := (point_radical h).twoCore_le
  have hf := h.omegaOrbit_centralizer
  have hX := centralOmega_centralizer R hQR (point_selfCentralizing h) hf
  let hker : q.ker = centralizer (X : Set H) := (QuotientGroup.ker_mk' _).trans hX.symm
  refine ⟨hker,hB,?_⟩
  apply ff_card_g2_moved_natural _ B F h.nonbinary (point_image_card h)
    hC (point_image_sqtk h)
  · exact NormalElementaryQuotient.representation_injective _ _ _ _
  · exact centralOmega_isFFModule R (point_characteristic h) hp
      (point_radical_ne_bot h) hQR (point_selfCentralizing h) hf
      q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)

/-- This is the literal initial commutator in the point-pair amalgam. -/
theorem G2Input.initial_commutator :
    ⁅omegaOrbit R,K⁆ = ⁅omegaCenterIn (pCore 2 H),K⁆ := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := (K).map q
  let : Group.IsPerfect K := h.component.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (q.subgroupMap_surjective K)
  have hQR := (point_radical h).twoCore_le
  have hself := point_selfCentralizing h
  let : IsElementaryAbelian 2 (omegaOrbit R) := omegaOrbit_elementary R hQR hself
  obtain ⟨hker,hn,hi,_⟩ := h.initial_module
  let := hn
  have hne : B ≠ ⊥ := by
    have hc := point_image_card h
    have hlo := card_g2_ge F.Carrier F.card_eq h.nonbinary
    intro hz
    change Nat.card B = _ at hc
    rw [hz,card_bot] at hc
    omega
  exact NormalElementaryQuotient.commutator_eq_of_irrPlus (omegaOrbit R)
    (omegaCenterIn (pCore 2 H)) (omegaOrbit_le_centralOmega R hQR hself)
    q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.omegaOrbit_centralizer).symm)
    hker K B rfl hne hi

open Representation.OneCohomology in
/-- The original moved/fixed projection is a genuine natural cover. -/
theorem G2Input.initial_cover :
    let q := QuotientGroup.mk' (pCore 2 H)
    let B := (K).map q
    let X := omegaCenterIn (pCore 2 H)
    ∃ hker : q.ker = centralizer (X : Set H), ∃ hn : B.Normal,
      let := hn
      let ρ := NormalElementaryQuotient.representation X q (QuotientGroup.mk'_surjective _) hker
      let s := MovedSection.ofNormal ρ B
      ∃ E : BinaryField, E.degree = F.degree ∧
        ∃ e : ActionEquiv (s.action.comp B.subtype) (binaryG2 E),
          IsCover (MovedSection.coverProjection s e) := by
  obtain ⟨hker,hn,hi,F,hF,⟨e⟩⟩ := h.initial_module
  let := hn
  exact ⟨hker,hn,F,hF,e,MovedSection.coverProjection_isCover _ hi e⟩

omit h

section Point
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction
    (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
  (f : InvariantFlag (.g2 m))

/-- All intrinsic hypotheses are constructed on the original point pair LR₁. -/
def point_g2_input (hm : NonbinaryMSPair S.field L (f.Ri 0)) :
    G2Input (L.subgroupOf (L ⊔ f.Ri 0)) ((f.Ri 0).subgroupOf (L ⊔ f.Ri 0)) S.field where
  nonbinary := S.nonbinary
  sqtk := hm.sqtk
  fitting := hm.fitting
  component := hm.component
  radical := msOddIndexRadical_subgroupOf hm.radical
  characteristic := msCharacteristic_subgroupOf le_sup_right hm.characteristic
  quotientEquiv := (subgroupOfCoreQuotientEquiv le_sup_left).trans m.groupEquiv
  product g := by
    obtain ⟨k,hk,r,hr,he⟩ := hm.product g g.property
    exact ⟨⟨k,mem_sup_left hk⟩,hk,⟨r,mem_sup_right hr⟩,hr,Subtype.ext he⟩

/-- The intrinsic marking preserves the actual source quotient map. -/
theorem point_g2_input_mk (hm : NonbinaryMSPair S.field L (f.Ri 0))
    (l : L.subgroupOf (L ⊔ f.Ri 0)) :
    (point_g2_input D S m f hm).quotientEquiv (QuotientGroup.mk' _ l) =
      m.groupEquiv (QuotientGroup.mk' (pCore 2 L) (subgroupOfEquivOfLe le_sup_left l)) := rfl
end Point

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear
