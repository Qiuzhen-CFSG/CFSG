module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.AbelianSource
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryAbelian.SourceAlternatives.Double.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryAbelian.SourceAlternatives.Double.OmegaCenter

/-!
# The common-axis obstruction in the doubled-natural MS branch

The concrete point-parabolic cubic fixes the doubled Sylow fixed space and
moves the common-axis offender. On a literal marked MS action, equality of R
with the omega-center centralizer's two-core would make that cubic normalize
R. Uniqueness of the offender inside the same Sylow then forces it to normalize
the common axis, a contradiction. Every map below uses the original join L ∨ R.

The order-64 source branch supplies injective doubled coordinates and a
trivial component-fixed subgroup. Odd-index averaging on the literal join
then supplies the omega-center splitting, with no extra geometric hypothesis.
The action-and-offender record is the remaining explicit intermediate input;
constructing it is required before the unconditional source inequality.
The final theorem supplies the radical inequality from that record alone,
under the original small MS hypotheses.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.34(2),
printed p.137, especially the common-axis versus common-center argument.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] {κ : GroupClass.{u}} {L R S : Subgroup G}

open BinaryLinearThree
open BinaryLinearThree.DoubledOffenders

/-- Actual coordinates, conjugation and a simultaneously marked component
Sylow and unique offender. This is proof data to be constructed from MS3;
it does not include the radical inequality or a centralizer conclusion. -/
structure DoubledSourceAction (L R S : Subgroup G) where
  marking : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL
  coordinates : msQ L R ≃* Multiplicative (Vector × Vector)
  normalized : L ⊔ R ≤ normalizer (msQ L R)
  actor : (L ⊔ R : Subgroup G) →* D
  equivariant : ∀ (j : (L ⊔ R : Subgroup G)) (x y : msQ L R),
    (y : G) = (j : G) * (x : G) * (j : G)⁻¹ →
      (coordinates y).toAdd = τ (actor j) (coordinates x).toAdd
  component : ∀ l : L, actor ⟨l, (show L ≤ L ⊔ R from le_sup_left) l.property⟩ =
    δ (marking (QuotientGroup.mk' (pCore 2 L) l))
  frame : Matrix.PSL3Two.SL
  componentSylow : ((S ⊓ L).subgroupOf (L ⊔ R)).map actor =
    (Matrix.PSL3Two.borelSL.map (MulAut.conj frame).toMonoidHom).map δ
  offender_le : ((BinaryLinearThree.R.map (MulAut.conj frame).toMonoidHom).map δ) ≤
    (R.subgroupOf (L ⊔ R)).map actor
  unique_offender : ∀ E : Subgroup D,
    E ≤ (S.subgroupOf (L ⊔ R)).map actor → IsOffender τ E →
      E = (BinaryLinearThree.R.map (MulAut.conj frame).toMonoidHom).map δ

namespace DoubledSourceAction
variable (a : DoubledSourceAction L R S)

include a in
/-- The common-axis contradiction once the actual action and the lifting of
its fixed-space centralizer to the Sylow omega-center are supplied. -/
theorem not_centralizer_core (hRS : R ≤ S)
    (hlift : L ⊓ centralizer ((msQ L R ⊓ centralizer (S : Set G) : Subgroup G) : Set G) ≤
      centralizer (omegaCenterIn S : Set G)) :
    MSNotCentralizerCore L R S := by
  intro heq
  obtain ⟨c, hcfix, hcmove⟩ := exists_point_fixer_moving_axis a.frame
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (a.marking.symm c)
  have hlc : a.marking (QuotientGroup.mk' (pCore 2 L) l) = c := by
    rw [hl, MulEquiv.apply_symm_apply]
  let j : (L ⊔ R : Subgroup G) := ⟨l, (show L ≤ L ⊔ R from le_sup_left) l.property⟩
  have hj : a.actor j = δ c := (a.component l).trans (congrArg δ hlc)
  have hlfix : (l : G) ∈ centralizer
      ((msQ L R ⊓ centralizer (S : Set G) : Subgroup G) : Set G) := by
    intro x hx
    let xQ : msQ L R := ⟨x, hx.1⟩
    have hfixed : (a.coordinates xQ).toAdd ∈ fixedSpace τ
        ((Matrix.PSL3Two.borelSL.map (MulAut.conj a.frame).toMonoidHom).map δ) := by
      rw [← a.componentSylow]
      rintro ⟨_, s, hs, rfl⟩
      exact (a.equivariant s xQ xQ (by
        change x = (s : G) * x * (s : G)⁻¹
        rw [hx.2 s hs.1, mul_inv_cancel_right])).symm
    let y : msQ L R := ⟨(l : G) * x * (l : G)⁻¹,
      (mem_normalizer_iff.mp (a.normalized j.property) x).mp hx.1⟩
    have hy : y = xQ := a.coordinates.injective (Multiplicative.toAdd.injective (by
      rw [a.equivariant j xQ y rfl, hj]
      exact hcfix _ hfixed))
    have hv := congrArg (fun z : msQ L R => (z : G)) hy
    exact (mul_inv_eq_iff_eq_mul.mp hv).symm
  have hlZ := hlift ⟨l.property, hlfix⟩
  let C := (L ⊔ R) ⊓ centralizer (omegaCenterIn S : Set G)
  have hlC : (l : G) ∈ C := ⟨j.property, hlZ⟩
  have hlN : (l : G) ∈ normalizer R := by
    rw [heq]
    exact normalizer_le_normalizer_characteristic_image C (pCore 2 C)
      (C.le_normalizer hlC)
  have hjN : j ∈ normalizer (R.subgroupOf (L ⊔ R) : Set (L ⊔ R : Subgroup G)) :=
    (Subgroup.le_normalizer_comap (L ⊔ R).subtype) hlN
  have himage : a.actor j ∈ normalizer ((R.subgroupOf (L ⊔ R)).map a.actor : Set D) :=
    (R.subgroupOf (L ⊔ R)).le_normalizer_map a.actor (mem_map_of_mem a.actor hjN)
  have hnorm := normalizes_unique_offender τ
    (normalizer ((R.subgroupOf (L ⊔ R)).map a.actor : Set D))
    ((R.subgroupOf (L ⊔ R)).map a.actor) ((S.subgroupOf (L ⊔ R)).map a.actor)
    ((BinaryLinearThree.R.map (MulAut.conj a.frame).toMonoidHom).map δ)
    le_rfl a.offender_le (map_mono (comap_mono hRS)) (axis_isOffender a.frame)
    a.unique_offender
  exact hcmove (hj ▸ hnorm himage)

end DoubledSourceAction

/-- A literal central correction for every omega-center element supplies the
centralizer containment consumed by the common-axis argument. -/
theorem centralizer_omega_le_of_double_split
    (hsplit : ∀ z ∈ omegaCenterIn S,
      ∃ q ∈ msQ L R ⊓ centralizer (S : Set G),
        q⁻¹ * z ∈ centralizer (L : Set G)) :
    L ⊓ centralizer ((msQ L R ⊓ centralizer (S : Set G) : Subgroup G) : Set G) ≤
      centralizer (omegaCenterIn S : Set G) := by
  intro l hl z hz
  obtain ⟨q, hq, hc⟩ := hsplit z hz
  have he : q * (q⁻¹ * z) = z := mul_inv_cancel_left q z
  calc
    z * l = (q * (q⁻¹ * z)) * l := by rw [he]
    _ = q * ((q⁻¹ * z) * l) := mul_assoc _ _ _
    _ = q * (l * (q⁻¹ * z)) := by rw [(hc l hl.1).symm]
    _ = (q * l) * (q⁻¹ * z) := (mul_assoc _ _ _).symm
    _ = (l * q) * (q⁻¹ * z) := by rw [hl.2 q hq]
    _ = l * z := by rw [mul_assoc, he]

/-- The source inequality from marked offenders and actual central corrections. -/
theorem DoubledSourceAction.not_centralizer_core_of_split
    (a : DoubledSourceAction L R S) (hRS : R ≤ S)
    (hsplit : ∀ z ∈ omegaCenterIn S,
      ∃ q ∈ msQ L R ⊓ centralizer (S : Set G),
        q⁻¹ * z ∈ centralizer (L : Set G)) :
    MSNotCentralizerCore L R S :=
  a.not_centralizer_core hRS (centralizer_omega_le_of_double_split hsplit)

variable [Finite G]

/-- Order 64 forces two natural copies, with no component-fixed kernel. -/
theorem SmallMSPair.abelian_source_double_quotient (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : IsMulCommutative (msQ L R)) (hcard : Nat.card (msQ L R) = 64) :
    ∃ q : AbelianSourceQuotient L R 2,
      Function.Injective q.projection ∧ msQ L R ⊓ centralizer (L : Set G) = ⊥ := by
  obtain ⟨m, q, hm, _, hbound, hdouble, hsize, _⟩ := h.abelian_source_quotient e hc
  rcases hm with rfl | rfl
  · rw [hcard] at hsize
    norm_num only [Nat.mul_one, Nat.reducePow] at hsize
    omega
  · have hz : msQ L R ⊓ centralizer (L : Set G) = ⊥ :=
      Subgroup.card_eq_one.mp (hdouble rfl)
    refine ⟨q, ?_, hz⟩
    apply (MonoidHom.ker_eq_bot_iff q.projection).mp
    rw [q.kernel, hz, bot_subgroupOf]

/-- Application of the marked common-axis argument to the literal alternative.
The fixed-space lifting input is discharged below; constructing the marked
action remains required for the unconditional theorem. -/
theorem SmallMSPair.abelian_source_double_of_geometry (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : IsMulCommutative (msQ L R)) (hcard : Nat.card (msQ L R) = 64)
    (hRS : R ≤ S) (a : DoubledSourceAction L R S)
    (hlift : L ⊓ centralizer ((msQ L R ⊓ centralizer (S : Set G) : Subgroup G) : Set G) ≤
      centralizer (omegaCenterIn S : Set G)) :
    ∃ e', MSModuleAlternatives L R S 1 (ZMod 2) e' := by
  obtain ⟨e', h8 | h64 | h16⟩ := h.abelian_source_sections e hc
  · omega
  · exact ⟨e', Or.inr (Or.inl ⟨h64.2, a.not_centralizer_core hRS hlift⟩)⟩
  · omega

/-- Every element of the original Sylow omega-center has a unique component-
central correction in the Sylow-fixed part of the actual commutator core. -/
theorem SmallMSPair.abelian_source_double_split (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : IsMulCommutative (msQ L R)) (hcard : Nat.card (msQ L R) = 64)
    (hS : Chapter1.IsSylowIn 2 S (L ⊔ R)) :
    ∀ z ∈ omegaCenterIn S,
      ∃ q ∈ msQ L R ⊓ centralizer (S : Set G),
        q⁻¹ * z ∈ centralizer (L : Set G) := by
  obtain ⟨_,_,_,hD,_,_,_,_⟩ := h.abelian_source_quotient e hc
  obtain ⟨_,_,hfixed⟩ := h.abelian_source_double_quotient e hc hcard
  let := hD
  let J := L ⊔ R
  let K := L.subgroupOf J
  have hDb : IsElementaryAbelian 2 (BinaryMS.commutatorCore K) :=
    IsElementaryAbelian.of_surjective (binaryCoreEquiv L R).symm.toMonoidHom
      (binaryCoreEquiv L R).symm.surjective
  have hfb : BinaryMS.coreFixed K = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    apply Subtype.ext
    apply Subtype.ext
    have hxx : ((x : J) : G) ∈ msQ L R ⊓ centralizer (L : Set G) := by
      refine ⟨?_,?_⟩
      · rw [← binaryCore_map L R]
        exact mem_map_of_mem J.subtype x.property
      · intro l hl
        exact congrArg Subtype.val (hx ⟨l,(show L ≤ J from le_sup_left) hl⟩ hl)
    exact (show ((x : J) : G) ∈ (⊥ : Subgroup G) from hfixed ▸ hxx)
  obtain ⟨P,hP⟩ := hS
  have hSJ : S ≤ J := hP ▸ map_subtype_le (P : Subgroup J)
  intro z hz
  have hzS : z ∈ S := map_subtype_le _ hz
  have hzC : z ∈ centralizer (S : Set G) := by
    obtain ⟨a,⟨b,hb,rfl⟩,rfl⟩ := hz
    intro s hs
    exact congrArg S.subtype (mem_center_iff.mp b.property ⟨s,hs⟩)
  let zJ : J := ⟨z,hSJ hzS⟩
  have hzP : zJ ∈ centralizer (P : Set J) := by
    intro p hp
    exact Subtype.ext (hzC p (hP ▸ mem_map_of_mem J.subtype hp))
  obtain ⟨q,hq,hqc⟩ := (h.binaryInput e).core_sylow_fixed_correction hDb hfb P zJ hzP
  refine ⟨q,⟨?_,?_⟩,?_⟩
  · rw [← binaryCore_map L R]
    exact mem_map_of_mem J.subtype hq.1
  · intro s hs
    obtain ⟨p,hp,hps⟩ := (show s ∈ (P : Subgroup J).map J.subtype from hP.symm ▸ hs)
    rw [← hps]
    exact congrArg Subtype.val (hq.2 p hp)
  · intro l hl
    exact congrArg Subtype.val (hqc ⟨l,(show L ≤ J from le_sup_left) hl⟩ hl)

/-- The source radical inequality now requires only the marked action and
its offender geometry; the omega-center lifting is proved from the MS pair. -/
theorem SmallMSPair.abelian_source_double_of_action (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : IsMulCommutative (msQ L R)) (hcard : Nat.card (msQ L R) = 64)
    (hS : Chapter1.IsSylowIn 2 S (L ⊔ R)) (hRS : R ≤ S)
    (a : DoubledSourceAction L R S) : MSNotCentralizerCore L R S :=
  a.not_centralizer_core_of_split hRS (h.abelian_source_double_split e hc hcard hS)


end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
