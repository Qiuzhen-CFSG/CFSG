module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryReciprocal
public import Theory.Representation.BinaryConjugationSection.NormalizingActors
public import Theory.Representation.BinaryConjugationSection.FixedSplitting

/-!
# Cross-core movement of the actual reciprocal plane

The orthogonal chief quotient and whole literal section have the same
binary dimension, so the chief kernel is zero. Irreducibility transfers
between any two markings of U/V₁. The nonzero reciprocal-intersection
commutator then shows that O₂(H) does not centralize U, and irreducibility
identifies its fixed subgroup in U with V₁.

The reciprocal point lies in U and is disjoint from V₁, so its commutator
with O₂(H) is exactly V₁. Reversing the same critical path proves the
opposite equality [V₁,Qα] = Zα. The final application constructs both
movements on the original selected order-four plane, discharging every
local irreducibility and movement premise.

Source: Aschbacher–Smith, proof of 14.7.32, printed pp.1057–1058,
refs/quasithin.pdf. These are the two transvection centers used to construct
Y₀; the plane-centralizer bound, construction of Y, and weak-closure
contradiction remain separate obligations.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.Components Swapped Swapped.LinearTwo ModuleAlternatives
open Chapter15.Section03.AbelianAmalgam
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) F.H W}

/-- Every marking of the literal original section is irreducible in the exchanged branch. -/
theorem local_nonnormal_component_section_irreducible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) : IsIrreducible ρ := by
  obtain ⟨hU,a,A,hA,hirr,hfaith,hmQ,hrest⟩ :=
    local_nonnormal_component_orthogonal_chief d h hab structural previous faithful earlier
      I K hI hKI hK hnormal
  let := hU
  obtain ⟨hU',b,hm,hrest'⟩ := local_nonnormal_component_whole_orthogonal d h hab structural
    previous faithful earlier I K hI hKI hK hnormal
  obtain ⟨f,e,he⟩ := hm
  obtain ⟨fQ,eQ,heQ⟩ := hmQ
  let M := Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U)
  let : Finite M := inferInstance
  let : FiniteDimensional (ZMod 2) M := Module.Finite.of_finite
  have hz : A = ⊥ := by
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.finrank_eq_zero.mp
    have hd := A.toSubmodule.finrank_quotient_add_finrank
    have hdim : Module.finrank (ZMod 2) (M ⧸ A.toSubmodule) =
        Module.finrank (ZMod 2) M := eQ.finrank_eq.trans e.finrank_eq.symm
    rw [hdim] at hd
    exact Nat.add_left_cancel (hd.trans (Nat.add_zero _).symm)
  let q : M ≃ₗ[ZMod 2] (M ⧸ A.toSubmodule) := LinearEquiv.ofBijective A.toSubmodule.mkQ
    ⟨by
      rw [←LinearMap.ker_eq_bot,Submodule.ker_mkQ]
      exact congrArg Subrepresentation.toSubmodule hz,
      A.toSubmodule.mkQ_surjective⟩
  let eqv : a.representation.Equiv A.quotientRepresentation :=
    Representation.Equiv.mk q (fun g => LinearMap.ext (fun v => (A.quotientRepresentation_mk g v).symm))
  have hi : IsIrreducible a.representation :=
    (RepEquiv.ofRepresentationEquiv eqv).irreducible_of_euqiv hirr
  have hic : IsIrreducible (a.representation.comp (starMap F)) :=
    (irreducible_comp_surjective_iff (starMap F) (QuotientGroup.mk'_surjective _) _).mpr hi
  let s₀ := ModuleBound.OriginalF916.conjugationSection a
    (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide)))
  let c : BinaryConjugationSection F.H F.U (F.Vi 1)
      (a.representation.comp (starMap F)) := {
    section_le := s₀.le
    kernel_le := s₀.line_le
    normalized := s₀.normalizes
    coordinates := s₀.quotient
    onto := s₀.surjective
    kernel_eq := s₀.kernel
    equivariant := fun x v => (s₀.conjugates x v).symm }
  exact c.irreducible_of_same_section s hic

/-- The two-core has precisely the original central point as its fixed subgroup in U. -/
theorem critical_core_centralizer_of_irreducible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hkernel : ρ.ker = pCore 2 F.H)
    (hno : ∀ a : F.H, fixedCodim ρ (zpowers a) ≠ 1)
    [IsIrreducible ρ]
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) :
    F.U ⊓ centralizer (F.H.pCoreIn 2 : Set G) = F.Vi 1 := by
  have hnormal : F.H ≤ normalizer (F.H.pCoreIn 2 : Set G) :=
    F.H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H))
  have hp : F.Vi 1 ≤ centralizer (F.H : Set G) :=
    le_centralizer_iff.mp
      (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide)))
  have hZ : F.Vi 1 ≤ F.U ⊓ centralizer (F.H.pCoreIn 2 : Set G) :=
    le_inf s.kernel_le (hp.trans (centralizer_le (pCoreIn_le 2 F.H)))
  apply (s.eq_kernel_or_section _ hZ inf_le_left
    ((le_inf s.normalized (hnormal.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf)).resolve_right
  intro he
  have hUC : F.U ≤ centralizer (F.H.pCoreIn 2 : Set G) := he ▸ inf_le_right
  have hz : ⁅c.Uα ⊓ F.H.pCoreIn 2,F.U⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (inf_le_right.trans (le_centralizer_iff.mp hUC))
  rw [critical_reverse_intersection_commutator_of_no_transvections h hab structural
    hkernel hno s c hs ha] at hz
  have hc := F.card 1 (by decide)
  rw [hz] at hc
  simp at hc

/-- The reciprocal central point is moved by the entire original core onto V₁. -/
theorem critical_cross_core_commutator_of_irreducible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hkernel : ρ.ker = pCore 2 F.H)
    (hno : ∀ a : F.H, fixedCodim ρ (zpowers a) ≠ 1)
    [IsIrreducible ρ]
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) :
    ⁅c.Zα,F.H.pCoreIn 2⁆ = F.Vi 1 := by
  have hZU : c.Zα ≤ F.U := by
    rw [←critical_intersection_commutator_of_no_transvections h hab structural hkernel hno s c hs ha]
    apply (commutator_mono inf_le_left le_rfl).trans
    exact le_normalizer_iff_commutator_le_left.mp
      (((critical_le_Q h structural c).trans (Q_le_H F)).trans s.normalized)
  have hle : ⁅c.Zα,F.H.pCoreIn 2⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl hZU).trans (section_core_commutator_le_point h s)
  apply eq_of_le_of_card_ge hle
  rw [show Nat.card (F.Vi 1) = 2 from by simpa using F.card 1 (by decide)]
  apply (one_lt_card_iff_ne_bot _).mpr
  intro hz
  have hZ : c.Zα ≤ F.Vi 1 := by
    rw [←critical_core_centralizer_of_irreducible h hab structural hkernel hno s c hs ha]
    exact le_inf hZU (commutator_eq_bot_iff_le_centralizer.mp hz)
  have hbot : c.Zα = ⊥ := (critical_points_disjoint_of_no_transvections h hab structural
    hkernel hno s c hs ha).symm.eq_bot_of_le hZ
  have hc : Nat.card c.Zα = 2 := by
    rw [CriticalPath.Zα,conjugate,card_map_of_injective (MulAut.conj c.conjugator⁻¹).injective]
    simpa using F.card 1 (by decide)
  rw [hbot] at hc
  simp at hc

/-- Reversal gives the opposite cross-core movement on the same selected pair. -/
theorem critical_reverse_cross_core_commutator_of_irreducible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hkernel : ρ.ker = pCore 2 F.H)
    (hno : ∀ a : F.H, fixedCodim ρ (zpowers a) ≠ 1)
    [IsIrreducible ρ]
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) :
    ⁅F.Vi 1,c.Qα⁆ = c.Zα := by
  have hAH := (critical_le_Q h structural c).trans (Q_le_H F)
  obtain ⟨r⟩ := exists_reversal_of_star_ne_bot h structural c hAH (c.star_ne_bot hs)
  have hrCard : Nat.card (star F r.path.Uα) = 2 := by
    rw [r.reverse_star_of_placement ((critical_le_Q h structural r.path).trans (Q_le_H F))]
    exact selected_critical_indices_of_card_two h hab c hs ha
  have hrSel : r.path.RankSelection :=
    ⟨critical_index_positive r.path,by
      rw [r.reverse_index_of_placement hAH,ha,hrCard]⟩
  have he := congrArg (fun B : Subgroup G => conjugate B r.conjugator)
    (critical_cross_core_commutator_of_irreducible h hab structural hkernel hno s r.path hrSel hrCard)
  have hm (A B : Subgroup G) : conjugate ⁅A,B⁆ r.conjugator =
      ⁅conjugate A r.conjugator,conjugate B r.conjugator⁆ := map_commutator _ _ _
  rwa [hm,r.tip_point,r.base_core,r.base_point] at he

/-- The original exchanged component supplies both cross-core movements on
its actual selected plane, without an irreducibility or movement premise. -/
theorem local_nonnormal_component_cross_core_plane
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal) :
    F.U ⊓ centralizer (F.H.pCoreIn 2 : Set G) = F.Vi 1 ∧
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
      Nat.card (star F c.Uα) = 2 ∧ (F.U ⊓ c.Qα).relIndex F.U = 2 ∧
      ⁅c.Zα,F.H.pCoreIn 2⁆ = F.Vi 1 ∧ ⁅F.Vi 1,c.Qα⁆ = c.Zα ∧
      Disjoint (F.Vi 1) c.Zα ∧
      (F.Vi 1 ⊔ c.Zα : Subgroup G) ≤ ⁅F.U,c.Uα⁆ ∧
      ⁅F.U,c.Uα⁆ ≤ F.U ⊓ c.Uα ∧
      IsElementaryAbelian 2 (F.Vi 1 ⊔ c.Zα : Subgroup G) ∧
      Nat.card (F.Vi 1 ⊔ c.Zα : Subgroup G) = 4 ∧
      Nat.card (⁅F.U,c.Uα⁆ : Subgroup G) = 8 := by
  obtain ⟨hU,a,hm,c,hs,hR,hV,hA,hquad,hr,hi,hcod,hcard,hindex,hl,hb,hno,hd⟩ :=
    local_nonnormal_component_selected_critical_rank_one d h hab structural previous
      faithful earlier I K hI hKI hK hnormal
  let := hU
  let s₀ := ModuleBound.OriginalF916.conjugationSection a
    (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide)))
  let s : BinaryConjugationSection F.H F.U (F.Vi 1)
      (a.representation.comp (starMap F)) := {
    section_le := s₀.le
    kernel_le := s₀.line_le
    normalized := s₀.normalizes
    coordinates := s₀.quotient
    onto := s₀.surjective
    kernel_eq := s₀.kernel
    equivariant := fun x v => (s₀.conjugates x v).symm }
  let := local_nonnormal_component_section_irreducible d h hab structural previous faithful earlier
    I K hI hKI hK hnormal s
  have hk : (a.representation.comp (starMap F)).ker = pCore 2 F.H := by
    ext x
    change a.representation (starMap F x) = 1 ↔ x ∈ pCore 2 F.H
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff _).mp (a.faithful (hx.trans a.representation.map_one.symm))
    · intro hx
      have he : starMap F x = 1 := (QuotientGroup.eq_one_iff _).mpr hx
      rw [he,map_one]
  have hn (x : F.H) : fixedCodim (a.representation.comp (starMap F)) (zpowers x) ≠ 1 := by
    change Module.finrank (ZMod 2) (_ ⧸ fixedSpace (a.representation.comp (starMap F)) _) ≠ 1
    rw [fixedSpace_comp_map,MonoidHom.map_zpowers]
    exact hno (starMap F x)
  have he := critical_intersection_commutator_of_no_transvections h hab structural hk hn s c hs hcard
  have her := critical_reverse_intersection_commutator_of_no_transvections h hab structural hk hn s c hs hcard
  have hz := critical_points_disjoint_of_no_transvections h hab structural hk hn s c hs hcard
  have hP : F.Vi 1 ≤ ⁅F.U,c.Uα⁆ := by
    rw [←her,commutator_comm]
    exact commutator_mono le_rfl inf_le_left
  have hZ : c.Zα ≤ ⁅F.U,c.Uα⁆ := by
    rw [←he]
    exact commutator_mono inf_le_left le_rfl
  have hCU : ⁅F.U,c.Uα⁆ ≤ F.U := le_normalizer_iff_commutator_le_left.mp
    (((critical_le_Q h structural c).trans (Q_le_H F)).trans s.normalized)
  have hCA : ⁅F.U,c.Uα⁆ ≤ c.Uα :=
    le_normalizer_iff_commutator_le_right.mp (G2Source.normalizes_partner h c)
  have hplane := sup_le hP hZ
  have hfour : Nat.card (F.Vi 1 ⊔ c.Zα : Subgroup G) = 4 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
      ((hZ.trans hCU).trans s.section_le) hz]
    have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    have hzc : Nat.card c.Zα = 2 := by
      rw [CriticalPath.Zα,conjugate,card_map_of_injective (MulAut.conj c.conjugator⁻¹).injective]
      exact hp
    rw [hp,hzc]
  exact ⟨critical_core_centralizer_of_irreducible h hab structural hk hn s c hs hcard,
    c,hs,hR,hcard,hindex,
    critical_cross_core_commutator_of_irreducible h hab structural hk hn s c hs hcard,
    critical_reverse_cross_core_commutator_of_irreducible h hab structural hk hn s c hs hcard,
    hz,hplane,le_inf hCU hCA,
    IsElementaryAbelian.of_injective (inclusion (hplane.trans hCU)) (inclusion_injective _),
    hfour,critical_commutator_card_of_no_transvections h hab structural hk hn s c hs hcard⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
