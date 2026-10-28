module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.HStarSource.ComponentLocalClass
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.HStarSource.SingleExclusion
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedLinearCartan
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.HallAlpha
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.QuasisimpleLinearLocalClass
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedLinearLocalClass
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.LocalAmbient
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.FiveSeedObstruction
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.CompleteSource
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.ActionSource
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.Solvable
/-!
# The actual selected H* component and its prescribed Hall cubic

The actual paired source at field order four selects its canonical component
and a cubic in its Baumann normalizer. The global Baumann-normalizer bound
places that cubic in the solvable maximal overlap. Hall conjugacy by a Sylow
element puts it in the prescribed Hall subgroup while preserving nonzero
alpha fixed points. The same component, localV, quotient, residual cover and
literal conjugator are retained; an ambient wrapper feeds axis alignment.
Source: Aschbacher--Smith E.2.3 and 10.2.3(4), pp.216--217 and746--747.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB ChapterE ChapterE.ThompsonAction
open ChapterB.SourceInduction ChapterB.QuasisimpleSource
open ChapterC.RankOne.ChiProduct.SelectedRankOne
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)


variable {F : Type*} [Field F] [CharP F 2]
local instance hstarPairedHallFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
variable
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (hF : Nat.card F = 4) (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
include e hn hH hZH hF f n



set_option backward.isDefEq.respectTransparency false in
theorem source_hstar_paired_component_and_hall_cubic
    (hlarge : 1 < generationParameter H)
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype hH.1.1.2 : Subgroup H))
    (BH : Subgroup H)
    (hHall : IsHallSubgroup Subgroup.OddHall.oddPrimes (BH.subgroupOf (D.maximalLocal.subgroupOf H))) :
    let S := T.subtype hH.1.1.2
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    letI := (source_hstar_omega_orbit_reduced D hH).normal
    letI := (source_hstar_omega_orbit_reduced D hH).elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let hq := QuotientGroup.mk'_surjective C
    let hk := QuotientGroup.ker_mk' C
    let α := NormalElementaryQuotient.representation U q hq hk
    let Y := offenderSubgroup α
    let B := baumann (S : Subgroup H)
    letI := offenderSubgroup_normal α
    ∀ (d : SourceTwoFactorCase (α.comp Y.subtype)) (E : BinaryField)
      (_hE : Nat.card E.Carrier = 4) (_c : d.MarkedProduct (linearNatural E 2))
      (_hexchange : ∃ t : S.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.first),
    ∃ K : Subgroup H, K.IsCComponent ∧ K.map q = d.first.map Y.subtype ∧
      (solvableResidual (ChapterB.RankOneBaumann.PairedFactorOrbit.factorPreimage q Y d.first)).map
        (ChapterB.RankOneBaumann.PairedFactorOrbit.factorPreimage q Y d.first).subtype = K ∧
      U ≤ normalizer (K : Set H) ∧ B ≤ normalizer (K : Set H) ∧
      ChapterC.GlaubermanNiles.InLocalClass (inclusion (show B ≤ K ⊔ B from le_sup_right)) ∧
      (ChapterC.GlaubermanNiles.localV (inclusion (show B ≤ K ⊔ B from le_sup_right))).map
        (K ⊔ B).subtype = (⁅U,K⁆ : Subgroup H) ⊔
          (thompsonAlpha (S : Subgroup H) ⊓ centralizer (K : Set H)) ∧
      thompsonAlpha (S : Subgroup H) ⊓ centralizer (K : Set H) ≠ ⊥ ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* SL(2,E.Carrier)) ∧ K ⊔ (S : Subgroup H) = ⊤ ∧
      (∃ t ∈ (S : Subgroup H), pResidual 2 H = K ⊔ K.map (MulAut.conj t).toMonoidHom) ∧
      ∃ A : Subgroup H, A ≤ K ∧ Nat.card A = 3 ∧ A ≤ normalizer (B : Set H) ∧
        ∃ t ∈ (S : Subgroup H), A.map (MulAut.conj t).toMonoidHom ≤ BH ∧
          Nat.card (A.map (MulAut.conj t).toMonoidHom) = 3 ∧
          thompsonAlpha (S : Subgroup H) ⊓
            centralizer (A.map (MulAut.conj t).toMonoidHom : Set H) ≠ ⊥ := by
  let S := T.subtype hH.1.1.2
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  have hU := source_hstar_omega_orbit_reduced D hH
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let B := baumann (S : Subgroup H)
  let := offenderSubgroup_normal α
  have hP := source_a5_hstar_minimal_parabolic D e hn hH
  have hJ := source_hstar_thompson_moves_omega_orbit_of_natural_four D e hn hH hZH hF f n
  have hfit := source_hstar_fitting_eq_core D hH
  have hsq := Chapter3.sqtk_of_mem_H D.simpleQTKE hH.1.1.1
  have hs : ¬ Group.IsSolvable H := by
    intro hs
    let := hs
    exact (not_lt_of_ge (generationParameter_le_one_of_solvable (G := H))) hlarge
  have h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple :=
    ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hkc : q.ker = pCore 2 H := hk.trans
    (source_hstar_action_kernel_eq_core_of_seed_centralizer D hH hCZ)
  dsimp only
  intro d E hE c hexchange
  obtain ⟨K,hK,hi,hcan,hUK,hBK,hlocal,hv,hfixed,heq,hgen,hcover,A,hAK,hA,hAB⟩ :=
    first_component_localClass_with_cubic h36 hsq S hP U hU hJ q hq hk hkc
      hs hfit d E hE c hexchange
  have hBm : B.map H.subtype = baumann (T : Subgroup G) := by
    change (baumann (S : Subgroup H)).map H.subtype = _
    have hh := baumann_map_injective H.subtype H.subtype_injective (S : Subgroup H)
    change (baumann (S : Subgroup H)).map H.subtype = baumann ((S : Subgroup H).map H.subtype) at hh
    rw [show (S : Subgroup H).map H.subtype = (T : Subgroup G) from map_subgroupOf_eq_of_le hH.1.1.2] at hh
    exact hh
  have hAM : A ≤ D.maximalLocal.subgroupOf H := by
    intro a ha
    apply source_natural_four_baumann_normalizer_le D e hn hF f n
    have hm := B.le_normalizer_map H.subtype (mem_map_of_mem H.subtype (hAB ha))
    rwa [hBm] at hm
  have hAF : thompsonAlpha (S : Subgroup H) ⊓ centralizer (A : Set H) ≠ ⊥ := by
    intro he
    exact hfixed (bot_unique ((inf_le_inf_left _ (centralizer_le hAK)).trans he.le))
  obtain ⟨_,_,_,data,hmax,_⟩ := source_a5_hstar_cartan_data D e hn hH hlarge
  have hsolv : Group.IsSolvable (D.maximalLocal.subgroupOf H) := hmax ▸ data.maximal_solvable
  have hSM : (S : Subgroup H) ≤ D.maximalLocal.subgroupOf H := by
    intro s hs
    exact (le_normalizer_componentOrbit L T) hs
  exact ⟨K,hK,hi,hcan,hUK,hBK,hlocal,hv,hfixed,heq,hgen,hcover,A,hAK,hA,hAB,
    exists_hall_cubic_with_alpha_fixed S (D.maximalLocal.subgroupOf H) A BH
      hSM hAM hsolv hHall hA hAF⟩

set_option backward.isDefEq.respectTransparency false in
theorem source_hstar_paired_hall_cubic_with_ambient_fixed
    (hlarge : 1 < generationParameter H)
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype hH.1.1.2 : Subgroup H))
    (BH : Subgroup H)
    (hHall : IsHallSubgroup Subgroup.OddHall.oddPrimes (BH.subgroupOf (D.maximalLocal.subgroupOf H))) :
    let S := T.subtype hH.1.1.2
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    letI := (source_hstar_omega_orbit_reduced D hH).normal
    letI := (source_hstar_omega_orbit_reduced D hH).elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let hq := QuotientGroup.mk'_surjective C
    let hk := QuotientGroup.ker_mk' C
    let α := NormalElementaryQuotient.representation U q hq hk
    let Y := offenderSubgroup α
    letI := offenderSubgroup_normal α
    ∀ (d : SourceTwoFactorCase (α.comp Y.subtype)) (E : BinaryField)
      (_hE : Nat.card E.Carrier = 4) (_c : d.MarkedProduct (linearNatural E 2))
      (_hexchange : ∃ t : S.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.first),
    ∃ P : Subgroup G, P ≤ BH.map H.subtype ∧ Nat.card P = 3 ∧
      thompsonAlpha (T : Subgroup G) ⊓ centralizer (P : Set G) ≠ ⊥ := by
  dsimp only
  intro d E hE c hexchange
  obtain ⟨K,hK,hi,hcan,hUK,hBK,hlocal,hv,hfixed,heq,hgen,hcover,A,hAK,hA,hAB,t,ht,hAH,hc,hfix⟩ :=
    source_hstar_paired_component_and_hall_cubic D e hn hH hZH hF f n hlarge hCZ BH hHall
      d E hE c hexchange
  let P := (A.map (MulAut.conj t).toMonoidHom).map H.subtype
  refine ⟨P,map_mono hAH,?_,?_⟩
  · rw [show P=(A.map (MulAut.conj t).toMonoidHom).map H.subtype from rfl,
      card_map_of_injective H.subtype_injective,hc]
  · exact alpha_fixed_subtype_nontrivial T H hH.1.1.2 _ hfix

/-- The actual three-Hall source supplies the cubic required for original axis recognition. -/
theorem source_hstar_paired_hall_cubic_of_three_hall
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hzH : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥)
    (BH : Subgroup H) (hBM : BH ≤ D.maximalLocal.subgroupOf H)
    (hHall : IsHallSubgroup {p : Nat.Primes | p.val ≠ 2}
      (BH.subgroupOf (D.maximalLocal.subgroupOf H)))
    (hB : IsPGroup 3 BH)
    (hlarge : 1 < generationParameter H)
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype hH.1.1.2 : Subgroup H)) :
    ∃ P : Subgroup G, P ≤ BH.map H.subtype ∧ Nat.card P = 3 ∧
      thompsonAlpha (T : Subgroup G) ⊓ centralizer (P : Set G) ≠ ⊥ := by
  obtain ⟨d,E,hE,⟨c⟩,hexchange⟩ := source_hstar_paired_four_of_three_hall D e hn hH hZH hF f n
    hz hzH BH hBM hHall hB hlarge hCZ
  exact source_hstar_paired_hall_cubic_with_ambient_fixed D e hn hH hZH hF f n
    hlarge hCZ BH hHall d E hE c hexchange
end CFSG.Quasithin.Chapter10
