module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalCartan
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalCartan
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.LinearThree
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.DiagramHall.LinearCovered
public import Theory.SpecificGroups.PSL3.CartanActions.FullTorusFixer
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# The supplied right Cartan in the PSL₃(4) residual branch

Normality identifies the intrinsic quotient of K = O²(H) with its image
in H/O₂(H). This image is centerless, so the center identity of E.2.2
identifies the full core of the unique maximal subgroup with O₂(H).
The original diagram theorem then marks its overlap with K as the actual
PSL₃(4) Borel. Every supplied odd Hall subgroup lies in K, embeds through
the two-group kernel, and maps onto an odd Hall subgroup of this Borel.
Its order is therefore three.

The last theorem applies this calculation to the literal subgroup B of
N_G(L) ∩ H in a compatible Cartan pair. The calculation precedes parity
and both cubic branches, and uses no equality between the generation
parameter and a model exponent.

The internal imports reuse the Chapter B core convention and the existing
H-star overlap identification within this source development.

Source: Aschbacher--Smith, E.2.2, printed pp.215--216; Notation 5.1.9,
5.1.10, and the opening of 5.1.14, printed pp.634,638 (`refs/quasithin.pdf`).
-/

open Subgroup Theory.GroupTheory
open CFSG.Quasithin CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open scoped MatrixGroups
public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.RightCartan
variable {X : Type*} [Group X] [Finite X]

private theorem hall_card_of_two_kernel {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 4) (f : X →* Matrix.PSL3.LinearThree.borel F)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (Y : Subgroup X) (hY : IsHallSubgroup OddHall.oddPrimes Y) : Nat.card Y = 3 := by
  have ho := OddHall.odd_hall_odd hY
  obtain ⟨k, hkcard⟩ := hk.exists_card_eq
  have hd : Disjoint Y f.ker := disjoint_of_coprime_natCard (by
    rw [hkcard]
    exact ho.coprime_two_right.pow_right k)
  have hi : Function.Injective (f.subgroupMap Y) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro y hy
    apply Subtype.ext
    apply mem_bot.mp
    apply disjoint_iff_inf_le.mp hd
    exact ⟨y.property, congrArg Subtype.val (MonoidHom.mem_ker.mp hy)⟩
  let e := MulEquiv.ofBijective (f.subgroupMap Y) ⟨hi, f.subgroupMap_surjective Y⟩
  have hmap : IsHallSubgroup OddHall.oddPrimes (Y.map f) :=
    ⟨fun p hp => hY.p_in_pi_of_p_dvd_card p (hp.trans (card_map_dvd Y f)),
      fun p hp => hY.p_in_pi_of_p_dvd_index p (hp.trans (index_map_dvd Y hf))⟩
  exact (Nat.card_congr e.toEquiv).trans
    (Matrix.PSL3.CartanActions.FullTorusFixer.hall_card_and_inf_pointResidual_of_card_four
      hF (Y.map f) hmap).1

private theorem marked_linear_borel (S : Sylow 2 X)
    (hP : ChapterB.IsMinimalParabolicOver S ⊤) (hs : ¬ Group.IsSolvable X)
    (K : Subgroup X) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (S : Subgroup X) = ⊤)
    (hm : ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax S hP) K) 3 4) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      ∃ e : sourceImage (ChapterB.minimalParabolicMax S hP) K ≃* PSL(3,F),
        (componentOverlap (ChapterB.minimalParabolicMax S hP) K).map e.toMonoidHom =
          Matrix.PSL3.LinearThree.borel F := by
  let M := ChapterB.minimalParabolicMax S hP
  let J := sourceKernel M
  let q := QuotientGroup.mk' J
  let T := S.mapSurjective (QuotientGroup.mk'_surjective J)
  let D := sourceImage M K
  have hi := Structure.source_normal_simple_image S hP hs K hK hgen
  let : D.Normal := hi.2.2.1
  have hmin := (Structure.source_star_minimal_core_free S hP).1
  have hmax : ChapterB.minimalParabolicMax T hmin = M.map q :=
    (ChapterB.minimalParabolicMax_map_core S hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk']; exact le_rfl)).symm
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  obtain ⟨g,_,_,hB⟩ := Structure.LinearThree.exists_diagram_and_borel
    F (n := 2) (by decide) (by norm_num; exact hcard) D e T hi.2.2.2 hmin
  let e' := e.trans (MulAut.conj g)
  refine ⟨F,hF,hfin,hcard,e',?_⟩
  rw [source_overlap_coordinate]
  change ((M.map q).subgroupOf D).map e'.toMonoidHom = _
  rw [← hB,hmax]
  exact (comap_equiv_eq_map_symm e'.symm _).symm

/-- The original maximal-core kernel is the two-core in the centerless linear branch. -/
theorem residual_source_kernel (S : Sylow 2 X)
    (hP : ChapterB.IsMinimalParabolicOver S ⊤) (hs : ¬ Group.IsSolvable X)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 X) ⧸ pCore 2 (pResidual 2 X)) 3 4) :
    sourceKernel (ChapterB.minimalParabolicMax S hP) = pCore 2 X := by
  let K := pResidual 2 X
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv e.symm
  have hK : K.IsCComponent := isCComponent_of_isPPerfect_of_quasisimple_core_quotient
    (inferInstance : K.Normal).isSubnormal (isPPerfect_pResidual 2)
  have hc := source_single_clauses S hP hs K hK inferInstance (pResidual_sup_sylow_eq_top S)
  let ea : actorImage K ≃* PSL(3,F) := (coreQuotientEquivImage 2 K).symm.trans e
  have hz : center (actorImage K) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    apply ea.injective
    rw [map_one]
    have hcent : ea x ∈ center PSL(3,F) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨z,rfl⟩ := ea.surjective y
      simpa only [map_mul] using congrArg ea (mem_center_iff.mp hx z)
    simpa only [Group.IsPerfect.center_quotient_center_eq_bot SL(3,F), mem_bot] using hcent
  apply le_antisymm _ (twoCore_le_sourceKernel S hP)
  have he := hc.kernel_center
  rw [hz, Subgroup.map_bot] at he
  simpa only [QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp he

/-- Every supplied odd Hall subgroup of the original unique maximal has order three. -/
theorem oddHall_card_three_of_linear_residual (S : Sylow 2 X)
    (hP : ChapterB.IsMinimalParabolicOver S ⊤) (hs : ¬ Group.IsSolvable X)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 X) ⧸ pCore 2 (pResidual 2 X)) 3 4)
    (Y : Subgroup (ChapterB.minimalParabolicMax S hP))
    (hY : IsHallSubgroup OddHall.oddPrimes Y) : Nat.card Y = 3 := by
  let K := pResidual 2 X
  let M := ChapterB.minimalParabolicMax S hP
  have hj := residual_source_kernel S hP hs hm
  have hmodel : ClassicalGroup.IsPSL (actorImage K) 3 4 :=
    hm.of_mulEquiv (coreQuotientEquivImage 2 K).symm
  change sourceKernel M = pCore 2 X at hj
  let c := DiagramHall.linearSourceComparison S hP K
  have hc : Function.Injective c := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    rintro ⟨x,hxK⟩ hx
    obtain ⟨k,hk,rfl⟩ := hxK
    apply Subtype.ext
    have hh := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    change QuotientGroup.mk' (sourceKernel M) k = 1 at hh
    apply (QuotientGroup.eq_one_iff _).mpr
    have hkJ := (QuotientGroup.eq_one_iff _).mp hh
    exact hj ▸ hkJ
  let ec := MulEquiv.ofBijective c
    ⟨hc, DiagramHall.linearSourceComparison_surjective S hP K⟩
  have hmJ : ClassicalGroup.IsPSL (sourceImage M K) 3 4 := hmodel.of_mulEquiv ec.symm
  obtain ⟨F,hF,hfin,hcard,⟨e₀⟩⟩ := hm
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv e₀.symm
  have hK : K.IsCComponent := isCComponent_of_isPPerfect_of_quasisimple_core_quotient
    (inferInstance : K.Normal).isSubnormal (isPPerfect_pResidual 2)
  obtain ⟨E,hE,hEfin,hEcard,e,he⟩ := marked_linear_borel S hP hs K hK
    (pResidual_sup_sylow_eq_top S) hmJ
  let f := e.toMonoidHom.comp c
  have hf : Function.Bijective f :=
    ⟨e.injective.comp hc, e.surjective.comp (DiagramHall.linearSourceComparison_surjective S hP K)⟩
  let fe := MulEquiv.ofBijective f hf
  let C := (Matrix.PSL3.LinearThree.borel E).comap f
  have hC : C.map fe.toMonoidHom = Matrix.PSL3.LinearThree.borel E :=
    map_comap_eq_self_of_surjective hf.2 _
  let ce : C ≃* Matrix.PSL3.LinearThree.borel E :=
    (fe.subgroupMap C).trans (MulEquiv.subgroupCongr hC)
  let q := ce.toMonoidHom.comp (DiagramHall.linearCoveredProjection S hP K e he)
  have hq : Function.Surjective q := ce.surjective.comp
    (DiagramHall.linearCoveredProjection_surjective S hP K e he)
  have hqker : q.ker = (DiagramHall.linearCoveredProjection S hP K e he).ker := by
    ext x
    exact ce.map_eq_one_iff
  have hq2 : IsPGroup 2 q.ker := by
    rw [hqker]
    exact DiagramHall.linearCoveredProjection_kernel_two S hP K e he
  have hYK : Y ≤ K.subgroupOf M := by
    have hle := OddHall.odd_subgroup_le K (Y.map M.subtype)
      (isPGroup_quotient_pResidual 2)
      ((OddHall.odd_hall_odd hY).of_dvd_nat (card_map_dvd Y M.subtype))
    exact map_le_iff_le_comap.mp hle
  have hcardY := hall_card_of_two_kernel hEcard q hq hq2
    (Y.subgroupOf (K.subgroupOf M)) (hY.subgroupOf hYK)
  rwa [Nat.card_congr (subgroupOfEquivOfLe hYK).toEquiv] at hcardY

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.RightCartan

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
open ChapterB

/-- The supplied right Hall subgroup in Notation 5.1.9 is cubic in the literal
PSL₃(4) residual branch, before the parity and cubic-normalization arguments. -/
theorem CartanPair.right_card_of_linear_residual {T : Sylow 2 G}
    {L H A B : Subgroup G} (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    Nat.card B = 3 := by
  let S := T.subtype hH.1.1.2
  have hP := hstar_minimalParabolic_of_generation_gt_one hTL hH hgen
  have hs : ¬ Group.IsSolvable H := by
    intro hs
    let := hs
    exact (Nat.not_le_of_gt hgen) ChapterE.generationParameter_le_one_of_solvable
  let M := normalizer (L : Set G)
  let N := M.subgroupOf H
  let e : minimalParabolicMax S hP ≃* (M ⊓ H : Subgroup G) :=
    (MulEquiv.subgroupCongr (hstar_maximal_eq_overlap hH hP)).trans
      ((N.equivMapOfInjective H.subtype H.subtype_injective).trans
        (MulEquiv.subgroupCongr (subgroupOf_map_subtype M H)))
  have hB := RightCartan.oddHall_card_three_of_linear_residual S hP hs hm
    ((B.subgroupOf (M ⊓ H)).map e.symm.toMonoidHom)
    ⟨fun p hp => c.right_hall.p_in_pi_of_p_dvd_card p
        (hp.trans (card_map_dvd _ e.symm.toMonoidHom)),
      fun p hp => c.right_hall.p_in_pi_of_p_dvd_index p
        (hp.trans (index_map_dvd _ e.symm.surjective))⟩
  rwa [card_map_of_injective e.symm.injective,
    Nat.card_congr (subgroupOfEquivOfLe c.right_le).toEquiv] at hB

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
