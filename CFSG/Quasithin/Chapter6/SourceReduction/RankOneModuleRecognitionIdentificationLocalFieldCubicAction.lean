module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFieldCubic
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFieldReduced
public import Theory.GroupTheory.ConjugateSpanNormalizer
public import Theory.Representation.BinaryConjugationSection.NormalizingActors
public import Theory.Representation.BinaryConjugationSection.ActionKernel
public import Theory.ThreeSubgroups

/-!
# Cubic action on the original field-plane quotient

Conjugation by O²(N_L(U)) extends the existing section coordinates on
J/U, where J is the C_G(U)-closure of the natural layer. The actual cubic
constructed in LocalFieldCubic fully moves that layer and has order three
on this same quotient. The extended action restricts to the original
faithful action, without changing its marking.

For any K in C_G(U) containing the noncommuting conjugate layer, relative
three-subgroups proves the noncentrality claim in paragraph two of 6.2.7.
If K and the cubic commute modulo the action kernel, the cubic moves the
K-commutator space. Otherwise K would normalize the original layer, and
the already proved mutual-normalization result would force commutation.
Both the ambient-kernel and marked-quotient statements are supplied.

The companion Chapter12 module constructs all these witnesses on the
whole reduced commutator layer. The component restrictions of 6.2.4(6)
and subsequent exclusions of 6.2.7 remain separate local obligations.

Source: Aschbacher--Smith, 6.2.7, printed p.682, first two paragraphs.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {L M B U R : Subgroup G} {n : ℕ} {T : Sylow 2 G}

omit [Finite G] in
private theorem section_extension
    {H J U P : Subgroup G} [IsElementaryAbelian 2 J]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) H W} (c : BinaryConjugationSection H J U ρ)
    (hHP : H ≤ P) (hPJ : P ≤ normalizer (J : Set G))
    (hPU : P ≤ normalizer (U : Set G)) :
    ∃ (η : Representation (ZMod 2) P W) (c' : BinaryConjugationSection P J U η),
      c'.coordinates = c.coordinates ∧ ∀ a : H, η (inclusion hHP a) = ρ a := by
  obtain ⟨η,hη⟩ := c.exists_original_quotient_action hPJ hPU
  let c' : BinaryConjugationSection P J U η := {
    section_le := c.section_le.trans hHP
    kernel_le := c.kernel_le
    normalized := hPJ
    coordinates := c.coordinates
    onto := c.onto
    kernel_eq := c.kernel_eq
    equivariant := fun p w => (hη p w).symm }
  refine ⟨η,c',rfl,?_⟩
  intro a
  ext w
  obtain ⟨j,hj⟩ := c.onto (Multiplicative.ofAdd w)
  have hw : (c.coordinates j).toAdd = w := congrArg Multiplicative.toAdd hj
  rw [←hw,hη,←c.equivariant]
  rfl

/-- Extend any marking of the literal field-plane quotient to its actual
normalizer residual. The cubic has order three on these same coordinates. -/
theorem field_plane_cubic_section_action
    [IsElementaryAbelian 2 (conjugateSpanBy B (centralizer (U : Set G)))]
    (hnat : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUc : Nat.card U = 4)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) (centralizer (U : Set G)) W}
    (c : BinaryConjugationSection (centralizer (U : Set G))
      (conjugateSpanBy B (centralizer (U : Set G))) U ρ) :
    let P := centralizer (U : Set G) ⊔ fieldLocalResidual L U
    ∃ d ∈ fieldLocalResidual L U, orderOf d = 3 ∧ ⁅B,zpowers d⁆ = B ∧
      ∃ (η : Representation (ZMod 2) P W)
        (c' : BinaryConjugationSection P (conjugateSpanBy B (centralizer (U : Set G))) U η),
        c'.coordinates = c.coordinates ∧
        (∀ a : centralizer (U : Set G), η (inclusion le_sup_left a) = ρ a) ∧
        ∃ hd : d ∈ P, orderOf (η.asGroupHom ⟨d,hd⟩) = 3 := by
  let H := centralizer (U : Set G)
  let J := conjugateSpanBy B H
  let D := fieldLocalResidual L U
  let P := H ⊔ D
  have hDU : D ≤ normalizer (U : Set G) := (map_subtype_le _).trans inf_le_right
  have hDB : D ≤ normalizer (B : Set G) := by
    obtain ⟨_, _, _, _, _, hm⟩ := hnat
    exact (map_subtype_le _).trans (inf_le_left.trans hm.normalizes)
  have hDJ : D ≤ normalizer (J : Set G) := normalizes_conjugateSpanBy B H D hDB
    (hDU.trans (normalizer_le_normalizer_centralizer U))
  have hPJ : P ≤ normalizer (J : Set G) := sup_le (le_normalizer_conjugateSpanBy B H) hDJ
  have hPU : P ≤ normalizer (U : Set G) := sup_le (Subgroup.centralizer_le_normalizer _) hDU
  obtain ⟨η,c',hcoords,hrestrict⟩ := section_extension c (show H ≤ P from le_sup_left) hPJ hPU
  obtain ⟨d,hd,ho,hBD,_⟩ := field_plane_cubic_movement hnat hfield hUc
  have hdP : d ∈ P := (show D ≤ P from le_sup_right) hd
  have hUne : U ≠ ⊥ := by intro he; rw [he,card_bot] at hUc; contradiction
  have hnot : ¬ B ≤ U := by
    intro hBU
    obtain ⟨δ,hδ,hδker,_⟩ := field_fixedSpace_displacement hnat hfield hUne
    obtain ⟨u,hu⟩ := ne_bot_iff_exists_ne_one.mp hUne
    obtain ⟨b,hb⟩ := hδ u
    have hbker : b ∈ δ.ker := by rw [hδker]; exact hBU b.property
    exact hu (hb.symm.trans hbker)
  have hηne : η ⟨d,hdP⟩ ≠ 1 := by
    intro hzero
    have hpre : d ∈ commutatorPreimage P J U := by
      rw [←c'.action_kernel_map hPU]
      exact ⟨⟨d,hdP⟩,hzero,rfl⟩
    have hDJU : ⁅zpowers d,J⁆ ≤ U :=
      (commutator_mono (zpowers_le.mpr hpre) le_rfl).trans
        (commutator_commutatorPreimage_le _ _ _ hPU)
    apply hnot
    rw [←hBD,commutator_comm]
    exact (commutator_mono le_rfl (le_conjugateSpanBy B H)).trans hDJU
  have hηorder : orderOf (η.asGroupHom ⟨d,hdP⟩) = 3 := by
    have hdorder : orderOf (⟨d,hdP⟩ : P) = 3 := (Subgroup.orderOf_coe _).symm.trans ho
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp
      (hdorder ▸ orderOf_map_dvd η.asGroupHom ⟨d,hdP⟩) with he | he
    · exact (hηne (congrArg Units.val (orderOf_eq_one_iff.mp he))).elim
    · exact he
  exact ⟨d,hd,ho,hBD,η,c',hcoords,hrestrict,hdP,hηorder⟩

/-- The cubic noncentrality claim in paragraph two of 6.2.7, on the
literal closure and kernel. The actor K may be any subgroup of C_G(U)
containing the original conjugate layer; no component is selected here. -/
theorem local_one_sided_cubic_noncentral
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (g : G)
    (hBA : layer L R ≤ normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (layer L R).map (MulAut.conj g).toMonoidHom ≤ centralizer (layer L R : Set G)) :
    let B := layer L R
    let A := B.map (MulAut.conj g).toMonoidHom
    let U := B ⊓ centralizer (A : Set G)
    let H := centralizer (U : Set G)
    let J := conjugateSpanBy B H
    ∀ d ∈ fieldLocalResidual L U, ⁅B,zpowers d⁆ = B →
      ∀ K : Subgroup G, A ≤ K → K ≤ H →
        ⁅K,zpowers d⁆ ≤ commutatorPreimage (normalizer (U : Set G)) J U →
        ¬ ⁅⁅J,K⁆,zpowers d⁆ ≤ U := by
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let U := B ⊓ centralizer (A : Set G)
  let H := centralizer (U : Set G)
  let J := conjugateSpanBy B H
  change ∀ d ∈ fieldLocalResidual L U, ⁅B,zpowers d⁆ = B →
    ∀ K : Subgroup G, A ≤ K → K ≤ H →
      ⁅K,zpowers d⁆ ≤ commutatorPreimage (normalizer (U : Set G)) J U →
      ¬ ⁅⁅J,K⁆,zpowers d⁆ ≤ U
  intro d hd hBD K hAK hKH hKD htriple
  have hDU : zpowers d ≤ normalizer (U : Set G) :=
    zpowers_le.mpr (map_subtype_le _ hd).2
  have hKU : K ≤ normalizer (U : Set G) := hKH.trans (Subgroup.centralizer_le_normalizer _)
  let := h.layer_elementary
  have hBH : B ≤ H := B.le_centralizer.trans (centralizer_le inf_le_left)
  have hJH : J ≤ H := conjugateSpanBy_le_self hBH
  have hJU : J ≤ normalizer (U : Set G) := hJH.trans (Subgroup.centralizer_le_normalizer _)
  have hrot : ⁅⁅zpowers d,J⁆,K⁆ ≤ U :=
    commutator_commutator_le_of_rotate_of_le_normalizer hDU hJU hKU htriple
      ((commutator_mono hKD le_rfl).trans
        (commutator_commutatorPreimage_le _ _ _ le_rfl))
  have hBK : ⁅B,K⁆ ≤ U := by
    calc
      ⁅B,K⁆ = ⁅⁅B,zpowers d⁆,K⁆ := by rw [hBD]
      _ ≤ ⁅⁅J,zpowers d⁆,K⁆ := commutator_mono (commutator_mono (le_conjugateSpanBy B H) le_rfl) le_rfl
      _ = ⁅⁅zpowers d,J⁆,K⁆ := by rw [commutator_comm J (zpowers d)]
      _ ≤ U := hrot
  have hAN : A ≤ normalizer (B : Set G) := hAK.trans
    (le_normalizer_iff_commutator_le_left.mpr (hBK.trans inf_le_left))
  have hc := local_commuting_normalized h hnatural hE hfactor g hBA hAN
  exact hnon (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc))

/-- Paragraph two of 6.2.7 on the same marked quotient: commuting actor
images force a nonzero cubic displacement of the K-moved space. -/
theorem local_one_sided_cubic_section_noncentral
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (g : G)
    (hBA : layer L R ≤ normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (layer L R).map (MulAut.conj g).toMonoidHom ≤ centralizer (layer L R : Set G))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] :
    let B := layer L R
    let A := B.map (MulAut.conj g).toMonoidHom
    let U := B ⊓ centralizer (A : Set G)
    let H := centralizer (U : Set G)
    let J := conjugateSpanBy B H
    let P := H ⊔ fieldLocalResidual L U
    ∀ (η : Representation (ZMod 2) P W) (c : BinaryConjugationSection P J U η)
      (d : G), d ∈ fieldLocalResidual L U → ⁅B,zpowers d⁆ = B →
      ∀ K : Subgroup G, A ≤ K → K ≤ H →
        (⁅K,zpowers d⁆.subgroupOf P).map η.asGroupHom = ⊥ →
        c.imageSpace ⁅⁅J,K⁆,zpowers d⁆ ≠ ⊥ := by
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let U := B ⊓ centralizer (A : Set G)
  let H := centralizer (U : Set G)
  let J := conjugateSpanBy B H
  let P := H ⊔ fieldLocalResidual L U
  change ∀ (η : Representation (ZMod 2) P W) (c : BinaryConjugationSection P J U η)
    (d : G), d ∈ fieldLocalResidual L U → ⁅B,zpowers d⁆ = B →
    ∀ K : Subgroup G, A ≤ K → K ≤ H →
      (⁅K,zpowers d⁆.subgroupOf P).map η.asGroupHom = ⊥ →
      c.imageSpace ⁅⁅J,K⁆,zpowers d⁆ ≠ ⊥
  intro η c d hd hBD K hAK hKH hcomm hzero
  have hDP : zpowers d ≤ P := zpowers_le.mpr
    ((show fieldLocalResidual L U ≤ P from le_sup_right) hd)
  have hKP : K ≤ P := hKH.trans le_sup_left
  have hPU : P ≤ normalizer (U : Set G) := sup_le (Subgroup.centralizer_le_normalizer _)
    ((map_subtype_le _).trans inf_le_right)
  have hKDP : ⁅K,zpowers d⁆ ≤ P := commutator_le.mpr (fun k hk d hd =>
    P.mul_mem (P.mul_mem (P.mul_mem (hKP hk) (hDP hd)) (P.inv_mem (hKP hk))) (P.inv_mem (hDP hd)))
  have hker : ⁅K,zpowers d⁆ ≤ η.ker.map P.subtype := by
    intro x hx
    let a : P := ⟨x,hKDP hx⟩
    have hqa : η.asGroupHom a = 1 :=
      ((Subgroup.map_eq_bot_iff _).mp hcomm) (show a ∈ ⁅K,zpowers d⁆.subgroupOf P from hx)
    exact ⟨a,congrArg Units.val hqa,rfl⟩
  rw [c.action_kernel_map hPU] at hker
  have hKD : ⁅K,zpowers d⁆ ≤ commutatorPreimage (normalizer (U : Set G)) J U :=
    le_commutatorPreimage (hKDP.trans hPU)
      ((commutator_mono hker le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hPU))
  apply local_one_sided_cubic_noncentral h hnatural hE hfactor g hBA hnon d hd hBD K hAK hKH hKD
  have hJK : ⁅J,K⁆ ≤ J := le_normalizer_iff_commutator_le_left.mp (hKP.trans c.normalized)
  have htriple : ⁅⁅J,K⁆,zpowers d⁆ ≤ J := (commutator_mono hJK le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp (hDP.trans c.normalized))
  intro x hx
  let j : J := ⟨x,htriple hx⟩
  have hj : (c.coordinates j).toAdd ∈ c.imageSpace ⁅⁅J,K⁆,zpowers d⁆ :=
    (c.mem_imageSpace_iff _ _).mpr ⟨j,hx,rfl⟩
  rw [hzero,Submodule.mem_bot] at hj
  exact (c.coordinates_eq_one_iff j).mp hj


namespace LocalFieldQuotientAction
/-- A cubic extension of the original faithful quotient marking, together
with the literal nonzero displacement assertion of source 6.2.7. -/
@[expose] def CubicSection (L B A U : Subgroup G) [IsElementaryAbelian 2 (space B U)] : Prop :=
    let H := LocalFieldQuotientAction.Centralizer U
    let J := conjugateSpanBy B H
    let P := H ⊔ fieldLocalResidual L U
    let W := Additive (LocalFieldQuotientAction.space B U)
    let π := (LocalFieldQuotientAction.action B U).rangeRestrict
    let I := (A.subgroupOf H).map π
    ∃ (ρ : Representation (ZMod 2) (LocalFieldQuotientAction.action B U).range W)
      (c : BinaryConjugationSection H J U (ρ.comp π)),
      Function.Injective ρ ∧ IsOffender ρ I ∧ Nat.card I = 4 ∧
      ∃ d ∈ fieldLocalResidual L U, orderOf d = 3 ∧ ⁅B,zpowers d⁆ = B ∧
        ∃ (η : Representation (ZMod 2) P W) (c' : BinaryConjugationSection P J U η),
          c'.coordinates = c.coordinates ∧
          (∀ a : H, η (inclusion le_sup_left a) = ρ (π a)) ∧
          (∃ hd : d ∈ P, orderOf (η.asGroupHom ⟨d,hd⟩) = 3) ∧
          (∀ K : Subgroup G, A ≤ K → K ≤ H →
            (⁅K,zpowers d⁆.subgroupOf P).map η.asGroupHom = ⊥ →
            c'.imageSpace ⁅⁅J,K⁆,zpowers d⁆ ≠ ⊥) ∧
          ∀ j : J, ∃ hj : (j : G) ∈ H, LocalFieldQuotientAction.projection U ⟨j,hj⟩ =
            ((c'.coordinates j).toAdd.toMul : LocalFieldQuotientAction.Ambient U)
end LocalFieldQuotientAction

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
