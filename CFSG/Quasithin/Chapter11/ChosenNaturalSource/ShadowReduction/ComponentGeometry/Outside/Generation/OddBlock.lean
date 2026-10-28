module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.SymplecticDerived
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Witness.OddExtension
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.SL3Core
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.Reduction
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.SpecificGroups.SL2.BinaryPointHom

/-!
# Generation one in the original odd-extension configuration

In the exceptional block from 11.1.5, C_T(L)=1. The original Cartan Y
normalizes R₁ and has no fixed points on V, so V=[V,Y]. The proved
odd-extension radical bound puts this commutator in O₂(KT). Shortness
also puts O₂(L) inside V, retaining the original covering kernel.

Restrict the actual quotient K → K/O₂(K) → SL₂(p) to L₁. Its kernel
is solvable, being contained in O₂,F(K), and contains the kernel of
L₁ → L/O₂(L). Hence it factors through the marked binary point-local
model. The model has no nontrivial odd-characteristic SL₂ image, which
would make L₁ solvable. This contradicts its original local membership.

Together with the completed equality and prime-PSL₂ rows this proves
n(H)=1 for every original outside H and for the source-selected H, with
both alternatives expressed using O²(H). It adds no outer-group,
selected-subgroup, generation-bound or Sylow premise.

Earlier geometry, the survivor list, Kz=K, full 11.3.2 and 11.1.5 remain
with qt-d-1222-natural-local-geometry, qt-d-1222-shadow-linear-geometry,
qt-d-1222-shadow-component-triangle and qt-d-1222-shadow-component-comparison,
with final discharge by qt-d-1222-shadow-components. The exact
OddKernelNormalizer remains with qt-d-1222-natural-odd-kernel-normalizer;
this conditional assembly does not discharge that independent source input.
The original marked G₂ R₁-Sylow construction and E.3.19 application are
already supplied by Outside.Witness.G2Source.

Source: Aschbacher–Smith 11.1.5 and 11.4.3–11.5.1,
refs/quasithin.pdf, printed pp.765–766,778–779.
-/


public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
open LocalGeometry LocalGeometry.Normalizers LocalGeometry.Normalizers.PointCohomology
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)

/-- The original seed lies in O₂(KT), using the source Cartan and its fixed space. -/
theorem ofFlag_odd_block_seed_le_core
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hb : ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L)
    (hC : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hm : Source.IsSL (Source.TwoOddQuotient (ofFlag S f X z H).K) 2 p) :
    V ≤ ((ofFlag S f X z H).K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let : IsElementaryAbelian 2 V := D.elementary
  let : Group.IsSolvable V := Group.isSolvable_of_comm
    (fun x y => IsMulCommutative.is_comm.comm x y)
  let E := ofFlag S f X z H
  have hprod : f.Ri 0 = (f.Li 0).pCoreIn 2 ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    cases c with
    | sl3 m => exact PointGeometry.SL3Core.core_product D S m f
    | sp4 m => exact PointGeometry.Sp4Core.core_product D S m f
    | g2 m => exact (PointGeometry.no_g2_block_marking D S m hb).elim
  obtain ⟨Y,hY⟩ := exists_cartan D
  have hYR := PointGeometry.cartan_normalizes_point_radical_of_core_product D S f
    (PointGeometry.block_flag_inner_unique D S f hb) hprod hY
  have hYV := (hY.1.trans inf_le_left).trans D.normalizes
  have hfixed : V ⊓ centralizer (Y : Set G) = ⊥ := by
    apply bot_unique
    have hh := PointGeometry.block_cartan_fixed_le D S c hb hY
    exact (le_inf (inf_le_left.trans D.le_sylow) hh).trans_eq hC
  have hcop : Nat.Coprime (Nat.card Y) (Nat.card V) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hn]
    exact hY.odd.coprime_two_right.pow_right n
  have hgen : V = ⁅V,Y⁆ := by
    simpa only [hfixed,sup_bot_eq] using
      eq_commutator_sup_centralizer_of_solvable_coprime V Y hYV inferInstance hcop
  have hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) E.K :=
    ⟨h.line_component,normal_subgroupOf_of_le_normalizer E.G₁_normalizes_K⟩
  have hbound := Radical.ofFlag_commutator_le_core_of_twoOdd_sl2 S f Y z H E.K hK
    (le_conjugateSpanBy _ _)
    (f.cartan_normalizes (PointGeometry.block_flag_inner_unique D S f hb) hY 0) hYR hp hm
  exact hgen.le.trans ((commutator_mono (f.seed_le_Ri S 0) le_rfl).trans hbound)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
public noncomputable section
open Subgroup Theory.GroupTheory Representation Matrix
open scoped MatrixGroups
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
open LocalGeometry LocalGeometry.Normalizers LocalGeometry.Normalizers.PointCohomology

private theorem hom_trivial_of_model
    {A B J E : Type*} [Group A] [Group B] [Group J] [Field E]
    (r : A →* B) (e : r.range ≃* J) (a : A →* SL(2,E))
    (hk : r.ker ≤ a.ker) (hm : ∀ b : J →* SL(2,E), ∀ j, b j = 1)
    (x : A) : a x = 1 := by
  let d := r.rangeRestrict.liftOfSurjective r.rangeRestrict_surjective
    ⟨a,by simpa only [MonoidHom.ker_rangeRestrict] using hk⟩
  have hh := hm (d.comp e.symm.toMonoidHom) (e (r.rangeRestrict x))
  simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply,d,
    MonoidHom.liftOfRightInverse_comp_apply] using hh

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)

/-- The original short block cannot occur in the surviving odd-by-SL₂ row.
The full covering kernels are retained throughout the restriction to L₁. -/
theorem ofFlag_odd_block_impossible
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hb : ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L)
    (hC : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥)
    {p : ℕ} (hp : p = 5 ∨ (p.Prime ∧ 11 ≤ p))
    (hm : Source.IsSL (Source.TwoOddQuotient (ofFlag S f X z H).K) 2 p) : False := by
  let K := (ofFlag S f X z H).K
  let A := f.Li 0
  have hAK : A ≤ K := le_conjugateSpanBy _ _
  have hAL : A ≤ L := (localResidual_le _).trans inf_le_left
  have hprime : p.Prime ∧ 3 < p := by
    rcases hp with rfl | ⟨hp,hl⟩
    · exact ⟨by decide,by decide⟩
    · exact ⟨hp,by omega⟩
  let : Fact p.Prime := ⟨hprime.1⟩
  have hVQ := ofFlag_odd_block_seed_le_core S f X z H h hb hC hprime.2 hm
  have hshort : ChapterC.IsShort L := hb.elim (fun b => b.2.1) (fun b => b.1)
  have hcore : L.pCoreIn 2 ≤ V := by
    cases c with
    | sl3 m =>
      have hh := sl3_core_eq_denominator D S m hshort
      rw [cohomologyDenominator,hC,sup_bot_eq] at hh
      exact (pCoreIn_mono_of_normalizes le_sup_left
        (sup_le L.le_normalizer D.sylow_normalizes_component)).trans_eq hh
    | sp4 m => exact (SylowNormalizer.Sp4Terminal.intrinsic_core_eq_seed D S m hshort).le
    | g2 m => exact (PointGeometry.no_g2_block_marking D S m hb).elim
  obtain ⟨E,_,_,hE,⟨e⟩⟩ := hm
  have hodd : Odd (Nat.card E) := hE ▸ hprime.1.odd_of_ne_two (by omega)
  have hE2 := GorensteinWalter.two_ne_zero_of_odd_card E hodd
  let q₂ := QuotientGroup.mk' (pCore 2 K)
  let qₒ := QuotientGroup.mk' (pPrimeCore 2 (K ⧸ pCore 2 K))
  let a : A →* SL(2,E) := e.toMonoidHom.comp (qₒ.comp (q₂.comp (inclusion hAK)))
  have hk : a.ker = (twoFittingCore K).comap (inclusion hAK) := by
    rw [ofFlag_twoFittingCore_eq_twoOddCore S f X z H h hp (by exact ⟨E,inferInstance,inferInstance,hE,⟨e⟩⟩)]
    ext x
    change e (qₒ (q₂ (inclusion hAK x))) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective]
    exact QuotientGroup.eq_one_iff _
  let j : a.ker →* twoFittingCore K :=
    ((inclusion hAK).comp a.ker.subtype).codRestrict _ (by
      intro x
      exact hk.le x.property)
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext ((inclusion_injective hAK) (congrArg Subtype.val he))
  let : Group.IsSolvable (twoFittingCore K) := twoFittingCore_solvable
  let : Group.IsSolvable a.ker := Group.isSolvable_of_isSolvable_injective hj
  let r := c.quotientMap.comp (inclusion hAL)
  have hkr : r.ker ≤ a.ker := by
    intro x hx
    have hxL : inclusion hAL x ∈ pCore 2 L := by
      apply (QuotientGroup.eq_one_iff _).mp
      apply c.groupEquiv.injective
      rw [map_one]
      exact hx
    have hxV : (x : G) ∈ V := hcore (mem_map_of_mem L.subtype hxL)
    have hxK : (x : G) ∈ K.pCoreIn 2 :=
      inf_pCoreIn_le_of_le 2 (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)
        ⟨hAK x.property,hVQ hxV⟩
    have hx₂ : inclusion hAK x ∈ pCore 2 K :=
      (mem_map_iff_mem K.subtype_injective).mp hxK
    change e (qₒ (q₂ (inclusion hAK x))) = 1
    rw [show q₂ (inclusion hAK x) = 1 from (QuotientGroup.eq_one_iff _).mpr hx₂,
      map_one,map_one]
  have hzero : ∀ x, a x = 1 := by
    have hrange : r.range = (A.subgroupOf L).map c.quotientMap := by
      rw [MonoidHom.range_comp]
      congr 1
      ext x
      exact ⟨fun ⟨a,ha⟩ => ha ▸ a.property,fun hx => ⟨⟨x,hx⟩,rfl⟩⟩
    cases c with
    | sl3 m =>
      obtain ⟨g,hg⟩ := Matrix.PSL3.PointRadicalGeneration.exists_standardPoint_conjugator
        (f.space 0) (f.dimension 0)
      have hm' := PointGeometry.SL3Core.componentImage_residual_conjugate D S m f g hg
      have heq : r.range = (PSL3.LinearThree.pointLocalSL S.field.Carrier).map
          (MulAut.conj g⁻¹).toMonoidHom := hrange.trans hm'
      let em : r.range ≃* PSL3.LinearThree.pointLocalSL S.field.Carrier :=
        by
          have e₁ : r.range ≃* ((PSL3.LinearThree.pointLocalSL S.field.Carrier).map
              (MulAut.conj g⁻¹).toMonoidHom) := MulEquiv.subgroupCongr heq
          exact e₁.trans ((MulAut.conj g⁻¹).subgroupMap _).symm
      exact hom_trivial_of_model r em a hkr
        (Theory.SpecificGroups.BinaryPointHom.linear_point_hom_trivial S.field.card_eq S.nonbinary hE2)
    | sp4 m =>
      have hm' := PointGeometry.Sp4Core.modelImage_point D S m f
      have heq : r.range = (Theory.SpecificGroups.SymplecticFour.pointLocal
          (F := S.field.Carrier)).map (MulAut.conj (Sp4.alignment m)).toMonoidHom :=
        hrange.trans hm'
      let em : r.range ≃* Theory.SpecificGroups.SymplecticFour.pointLocal
          (F := S.field.Carrier) :=
        by
          have e₁ : r.range ≃* ((Theory.SpecificGroups.SymplecticFour.pointLocal
              (F := S.field.Carrier)).map (MulAut.conj (Sp4.alignment m)).toMonoidHom) :=
            MulEquiv.subgroupCongr heq
          exact e₁.trans ((MulAut.conj (Sp4.alignment m)).subgroupMap _).symm
      exact hom_trivial_of_model r em a hkr
        (Theory.SpecificGroups.BinaryPointHom.symplectic_point_hom_trivial S.field.card_eq S.nonbinary hE2)
    | g2 m => exact (PointGeometry.no_g2_block_marking D S m hb).elim
  have hs : Group.IsSolvable A := by
    have he : a.ker = ⊤ := top_unique (fun x _ => hzero x)
    let : Group.IsSolvable (⊤ : Subgroup A) := he ▸ inferInstanceAs (Group.IsSolvable a.ker)
    exact Group.isSolvable_of_surjective
      (f := (topEquiv : (⊤ : Subgroup A) ≃* A).toMonoidHom) topEquiv.surjective
  exact Chapter1.mem_L_not_isSolvable (Triangle.Reselection.flag_residual_mem_local D S f 0) hs
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)

/-- Original 11.4.4 for every outside H on the chosen flag. All surviving
component rows are discharged; the registered earlier-source inputs remain. -/
theorem ofFlag_surviving_generation_eq_one
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H))
    (h1115 : Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree) :
    ChapterE.generationParameter H = 1 := by
  rcases ofFlag_generation_one_or_odd_extension D S f X z H h hcase he hlinear h1132
    hcontrol hH hHz h1115 with hone | ⟨hn,p,hp,hm⟩
  · exact hone
  rcases ofFlag_generation_one_or_exceptional_block S f X z H h hcase he hlinear h1132
    hcontrol hH hHz h1115 with hone | ⟨_,_,_,hb,hC,_⟩
  · exact hone
  exact (ofFlag_odd_block_impossible S f X z H h (by simpa only [hn] using hb) hC hp hm).elim

/-- Select the source H, retaining its literal O² alternative and the
universal generation-one statement for all original outside subgroups. -/
theorem ofFlag_selected_and_universal_generation_one
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (h1115 : Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree) :
    (∀ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      J ≤ Gz (ofFlag S f X z J) → ChapterE.generationParameter J = 1) ∧
    ∃ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      J ≤ Gz (ofFlag S f X z J) ∧ SelectedResidualAlternative (ofFlag S f X z J) ∧
      ChapterE.generationParameter J = 1 := by
  have hall (J : Subgroup G)
      (hJ : J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
      (hJz : J ≤ Gz (ofFlag S f X z J)) : ChapterE.generationParameter J = 1 :=
    ofFlag_surviving_generation_eq_one S f X z J
      ⟨h.point_mem,h.point_fixed,h.point_ne_one,h.seed_centralizes,
        h.line_component,h.point_component,h.normalizer_split⟩
      hcase he hlinear h1132 hcontrol hJ hJz h1115
  obtain ⟨J,hJ,hJz,hsel⟩ := Models.ofFlag_surviving_selected_H S f X z H h hcase he hNT h1132
  exact ⟨hall,J,hJ,hJz,hsel,hall J hJ hJz⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
