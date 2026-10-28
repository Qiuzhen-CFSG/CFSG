module
public import CFSG.Quasithin.Chapter14.Section06.SourceSingletonCompatibility.NinePointControl
public import Theory.GroupTheory.PrimitiveAbelianResidual
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The original elementary-nine point-centralizer image

Minimal normality of the abelian odd residual, triviality of the two-core,
and cyclic Sylow two-subgroups force every subgroup with a nontrivial
two-core to be a two-group. The original critical span has nontrivial
quotient image and lies in the actual opposite-point centralizer's two-core.
Its centralizer image is therefore cyclic of order two or four; lifting
through the original two-core also makes the actual centralizer a two-group.

At the selected strict endpoint, the opposite point belongs to [U,J] and
lies outside Z. The proved lifting theorem identifies its quotient
stabilizer with the image of its actual centralizer. The four-dimensional
moved quotient bounds the stabilizer index by sixteen. Since the quotient
has order36, an image of order two is impossible, leaving cyclic order four.

Every map uses the original J, U, Z and critical representative. The full
proper-K hypothesis is retained. These restrictions do not exclude the
remaining cyclic-four stabilizer configuration or prove original14.6.12.

Source: Aschbacher--Smith 14.6.12--13, printed pp.1031--1032, and
F.9.13--17, printed pp.322--324 of refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open OddNormalizer OddCriticalPair.OrthogonalSource
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab


/-- The literal quotient image of a noncentral moved-point centralizer has
index at most the size of the moved quotient. -/
theorem source_solvable_moved_point_image_index
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (u : conjugateSpanBy (localModule T M) J)
    (huW : (u : G) ∈ ⁅conjugateSpanBy (localModule T M) J,J⁆)
    (huZ : (u : G) ∉ centralInvolutions T) :
    (((J ⊓ centralizer ({(u : G)} : Set G)).subgroupOf J).map
      (QuotientGroup.mk' (pCore 2 J))).index ≤ 2 ^ Module.finrank (ZMod 2) (movedSpace a) := by
  let U := conjugateSpanBy (localModule T M) J
  let Z := centralInvolutions T
  let q := QuotientGroup.mk' (pCore 2 J)
  let C := J ⊓ centralizer ({(u : G)} : Set G)
  let B := (C.subgroupOf J).map q
  let v : Multiplicative (movedSpace a) := movedMap a ⟨u,huW⟩
  let := movedAction a
  have he : B = MulAction.stabilizer (J ⧸ pCore 2 J) v := by
    ext t
    constructor
    · rintro ⟨x,hx,rfl⟩
      change movedRepresentation a (q x) v.toAdd = v.toAdd
      apply Subtype.ext
      change a.representation (q x) (Additive.ofMul
        (QuotientGroup.mk' (Z.subgroupOf U) u)) = Additive.ofMul
        (QuotientGroup.mk' (Z.subgroupOf U) u)
      rw [a.conjugation]
      congr 2
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hx.2)
    · intro ht
      have ht' : a.representation t (Additive.ofMul
          (QuotientGroup.mk' (Z.subgroupOf U) u)) = Additive.ofMul
          (QuotientGroup.mk' (Z.subgroupOf U) u) :=
        congrArg (fun w : Multiplicative (movedSpace a) => w.toAdd.val) ht
      obtain ⟨k,hk,hkc⟩ := source_solvable_moved_point_centralizer_lifts
        hG T hempty hM hu hmany hcard e hab J hJ hs a u huW huZ t ht'
      exact ⟨k,⟨k.property,hkc⟩,hk⟩
  change B.index ≤ _
  rw [he,MulAction.index_stabilizer,←Nat.card_coe_set_eq]
  have hb := Nat.card_le_card_of_injective
    (Subtype.val : MulAction.orbit (J ⧸ pCore 2 J) v → Multiplicative (movedSpace a))
    Subtype.val_injective
  have hc : Nat.card (Multiplicative (movedSpace a)) =
      2 ^ Module.finrank (ZMod 2) (movedSpace a) := by
    change Nat.card (movedSpace a) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  exact hc ▸ hb

/-- Every original critical point centralizer is a two-group; its quotient
image is cyclic of order two or four. Relative core maps remain literal. -/
theorem source_singleton_nine_point_centralizers
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
    ∀ i : h.CriticalEndpoint,
      IsPGroup 2 (J ⊓ centralizer (i.conjugate D.V₁ : Set G) : Subgroup G) ∧
      IsCyclic (((J ⊓ centralizer (i.conjugate D.V₁ : Set G)).subgroupOf J).map
        (QuotientGroup.mk' (pCore 2 J))) ∧
      (Nat.card (((J ⊓ centralizer (i.conjugate D.V₁ : Set G)).subgroupOf J).map
          (QuotientGroup.mk' (pCore 2 J))) = 2 ∨
        Nat.card (((J ⊓ centralizer (i.conjugate D.V₁ : Set G)).subgroupOf J).map
          (QuotientGroup.mk' (pCore 2 J))) = 4) := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  let P := pResidual 2 (J ⧸ pCore 2 J)
  obtain ⟨p,hp,hE,_,_,hmin⟩ := source_solvable_minimal_elementary_residual
    hG T hempty hM hu hmany hcard e hab J hJ hs
  let := hE
  obtain ⟨horder,hSyl⟩ := source_singleton_nine_quotient_structure
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine
  have hSylAb (S : Sylow 2 (J ⧸ pCore 2 J)) : IsMulCommutative S := by
    let := (hSyl S).1
    infer_instance
  have hodd : Odd (Nat.card P) := hnine ▸ (by decide : Odd 9)
  change ∀ i : h.CriticalEndpoint, _
  intro i
  let C := J ⊓ centralizer (i.conjugate D.V₁ : Set G)
  let C₀ := C.subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  let B := C₀.map q
  let A := (i.conjugate D.UH).subgroupOf J
  have hcoreC := source_critical_span_le_point_core hG T hempty hM hu hmany hcard e hab J hJ.1 i
  have hAcore : A.map q ≤ B.pCoreIn 2 := by
    have hh := map_mono (f := q) (subgroupOf_mono J hcoreC)
    rw [←pCoreIn_subgroupOf 2 C J inf_le_left,
      map_pCoreIn_of_ker_isPGroup q (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)] at hh
    exact hh
  have hAc : Nat.card (A.map q) = 2 :=
    (source_singleton_nine_critical_image hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d hd hone hnine i).1
  have hBcore : pCore 2 B ≠ ⊥ := by
    intro hz
    have hb : B.pCoreIn 2 = ⊥ := by simp only [pCoreIn,hz,Subgroup.map_bot]
    have ha : A.map q = ⊥ := bot_unique (hb ▸ hAcore)
    rw [ha,card_bot] at hAc
    omega
  have hB : IsPGroup 2 B := isPGroup_of_nontrivial_core_of_primitive_odd_residual
    (pCore_quotient_pCore_eq_bot 2) hodd hmin hSylAb B hBcore
  have hC₀ : IsPGroup 2 C₀ :=
    (hB.comap_of_ker_isPGroup q (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)).to_le
      (le_comap_map q C₀)
  have hC : IsPGroup 2 C := hC₀.of_equiv (subgroupOfEquivOfLe (show C ≤ J from inf_le_left))
  obtain ⟨S,hBS⟩ := IsPGroup.exists_le_sylow (G := J ⧸ pCore 2 J) (p := 2) (P := B) hB
  let := (hSyl S).1
  have hcyc : IsCyclic B := isCyclic_of_injective (G := B) (G' := S) (inclusion hBS) (inclusion_injective hBS)
  have hdiv := card_dvd_of_le hBS
  rw [(hSyl S).2] at hdiv
  have htwo := card_dvd_of_le (hAcore.trans (pCoreIn_le 2 B))
  rw [hAc] at htwo
  change IsPGroup 2 C ∧ IsCyclic B ∧ _
  refine ⟨hC,hcyc,?_⟩
  have hnum (n : ℕ) (h2 : 2 ∣ n) (h4 : n ∣ 4) : n = 2 ∨ n = 4 := by
    obtain ⟨k,hk,rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show n ∣ 2^2 from h4)
    interval_cases k
    · norm_num at h2
    · exact Or.inl rfl
    · exact Or.inr rfl
  exact hnum (Nat.card B) htwo hdiv

/-- The original elementary-nine singleton has a four-dimensional moved quotient. -/
theorem source_singleton_nine_moved_finrank
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9) : Module.finrank (ZMod 2) (movedSpace a) = 4 := by
  obtain ⟨i,hi⟩ := Nat.card_eq_one_iff_exists.mp hone
  have hc := source_singleton_factor_star_cyclic hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d hd hone i
  have halt := source_ratio_singleton_cyclicStar_alternatives
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd i hi hc
  rw [movedSpace,source_rankTwo_whole_moved_eq_residual hG T hempty hM hu hmany hcard e hab J hJ.1 a]
  rcases halt with hcyc | ⟨_,_,hdim⟩
  · let := hcyc
    obtain ⟨p,hp,hE,_,_,_⟩ := source_solvable_minimal_elementary_residual
      hG T hempty hM hu hmany hcard e hab J hJ hs
    let := hE
    have hv := IsElementaryAbelian.exponent_dvd_p (p := p)
      (G := pResidual 2 (J ⧸ pCore 2 J))
    rw [IsCyclic.exponent_eq_card,hnine] at hv
    rcases hp with rfl | rfl <;> norm_num at hv
  · exact hdim

open OddCriticalPair.Selection in
/-- At the selected elementary-nine endpoint the actual point centralizer is
a two-group and its image in the original quotient is cyclic of order four. -/
theorem source_singleton_nine_selected_point_sylow
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    letI : IsElementaryAbelian 2 D.UH :=
      ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)›
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
    ∃ c : SelectedQuadraticEndpoint h a,
      c.endpoint.representative ∉ Mc ∧
      IsPGroup 2 (J ⊓ centralizer (c.endpoint.conjugate D.V₁ : Set G) : Subgroup G) ∧
      IsCyclic (((J ⊓ centralizer (c.endpoint.conjugate D.V₁ : Set G)).subgroupOf J).map
        (QuotientGroup.mk' (pCore 2 J))) ∧
      Nat.card (((J ⊓ centralizer (c.endpoint.conjugate D.V₁ : Set G)).subgroupOf J).map
        (QuotientGroup.mk' (pCore 2 J))) = 4 := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)›
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  change ∃ c : SelectedQuadraticEndpoint h a, _
  obtain ⟨c,hout,_,_,_,hmove,hpoint⟩ := source_singleton_nine_selected_geometry
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine
  have hpCard : Nat.card (c.endpoint.conjugate D.V₁) = 2 :=
    (card_map_of_injective (MulAut.conj c.endpoint.representative).injective).trans h.point_card
  obtain ⟨z,hz,hzne⟩ := (c.endpoint.conjugate D.V₁).bot_or_exists_ne_one.resolve_left (by
    intro hz
    rw [hz,card_bot] at hpCard
    omega)
  have hzZ : z ∉ D.V₁ := by
    intro hzz
    have he : D.V₁ = c.endpoint.conjugate D.V₁ := by
      have hi := inf_eq_bot_of_card_two_of_ne D.V₁ (c.endpoint.conjugate D.V₁)
        h.point_card hpCard
      by_contra hn
      exact hzne ((hi hn).le ⟨hzz,hz⟩)
    apply hout
    have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
      (source_lemma_14_1_18 hG T hempty hM hu hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
    apply hMc.ge
    exact normalizer_le_centralizer_of_card_two D.V₁ h.point_card
      (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  let u : D.UH := ⟨z,hpoint hz⟩
  have huW : (u : G) ∈ ⁅D.UH,J⁆ := by
    have hb := (source_rankTwo_critical_track_bounds hG T hempty hM hu hmany hcard e hab J hJ.1).1
    have hp : c.endpoint.conjugate D.V₁ ≤ ⁅D.UH,J⁆ := by
      rw [←hmove]
      exact commutator_mono (commutatorPreimage_le _ _ _) (c.endpoint.large_le hb)
    exact hp hz
  have hline : zpowers (u : G) = c.endpoint.conjugate D.V₁ := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr hz)
    rw [hpCard]
    exact Nat.succ_le_of_lt ((zpowers (u : G)).one_lt_card_iff_ne_bot.mpr
      (fun hb => hzne (Subgroup.zpowers_eq_bot.mp hb)))
  have he : centralizer ({(u : G)} : Set G) = centralizer (c.endpoint.conjugate D.V₁ : Set G) := by
    rw [←centralizer_closure,←zpowers_eq_closure,hline]
  have hbound := source_solvable_moved_point_image_index
    hG T hempty hM hu hmany hcard e hab J hJ hs a u huW hzZ
  rw [he,source_singleton_nine_moved_finrank hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d hd hone hnine] at hbound
  obtain ⟨hC,hcyc,hcases⟩ := source_singleton_nine_point_centralizers
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine c.endpoint
  refine ⟨c,hout,hC,hcyc,?_⟩
  rcases hcases with htwo | hfour
  · have hh := (((J ⊓ centralizer (c.endpoint.conjugate D.V₁ : Set G)).subgroupOf J).map
      (QuotientGroup.mk' (pCore 2 J))).card_mul_index
    rw [htwo,(source_singleton_nine_quotient_structure hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d hd hone hnine).1] at hh
    omega
  · exact hfour

end CFSG.Quasithin.Chapter14.Section06
