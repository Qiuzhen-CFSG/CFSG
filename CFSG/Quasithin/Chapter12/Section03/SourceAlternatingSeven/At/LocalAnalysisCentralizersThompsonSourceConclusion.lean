module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersThompsonSourceConclusion
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisCentralizersThompsonSourceSubgroups
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowReduction

/-!
# LocalAnalysisCentralizersThompsonSourceConclusion at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisCentralizersThompsonSourceConclusion`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory Stellmacher

open scoped IsMulCommutative Pointwise commutatorElement

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

namespace SylowNormalizer.Points

variable {E : S.NaturalCoordinates} (P : Points E)

theorem five_join_normalizes_module_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    P.five ⊔ (T : Subgroup G) ≤ normalizer (V : Set G) :=
  sup_le (((pointResidual_le L (P.two : G)).trans inf_le_left).trans S.chosen.normalizes)
    (((structural L S.hypothesis).2.2 V S.chosen).1)

def fiveJoinPermutation_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    (P.five ⊔ (T : Subgroup G) : Subgroup G) →*
      WeightTwoGeometry.symmetricStabilizer (E.coordinates P.two).toAdd :=
  ((E.sourceNormalizerModel_at structural).permutation.comp
    (inclusion (P.five_join_normalizes_module_at structural))).codRestrict _ (fun h => by
      rw [WeightTwoGeometry.mem_symmetricStabilizer]
      have hc : P.five ⊔ (T : Subgroup G) ≤ centralizer ({(P.two : G)} : Set G) :=
        sup_le ((pointResidual_le L (P.two : G)).trans inf_le_right)
          (fun t ht => mem_centralizer_singleton_iff.mpr (P.two_central t ht))
      change evenRepresentation ((E.sourceNormalizerModel_at structural).permutation
        (inclusion (P.five_join_normalizes_module_at structural) h))
        ((E.sourceNormalizerModel_at structural).coordinates P.two).toAdd =
        ((E.sourceNormalizerModel_at structural).coordinates P.two).toAdd
      rw [← (E.sourceNormalizerModel_at structural).equivariant]
      congr 2
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (hc h.property)))

theorem fiveJoinPermutation_contains_five_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (a : WeightTwoGeometry.five (E.coordinates P.two).toAdd) :
    ∃ h : (P.five ⊔ (T : Subgroup G) : Subgroup G), (P.fiveJoinPermutation_at structural h).val = a.val.val := by
  obtain ⟨k,hk⟩ := E.pointResidualProjection_surjective P.two P.two_weight a
  refine ⟨⟨k,mem_sup_left k.property⟩,?_⟩
  have he := E.sourceNormalizerModel_component_at structural
    ⟨k,((pointResidual_le L (P.two : G)).trans inf_le_left) k.property⟩
  exact he.trans (congrArg (fun b : WeightTwoGeometry.five (E.coordinates P.two).toAdd => b.val.val) hk)

theorem five_core_fixes_complement_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (q : pCore 2 (P.five ⊔ (T : Subgroup G) : Subgroup G))
    (i : WeightTwoGeometry.Complement (E.coordinates P.two).toAdd) :
    (P.fiveJoinPermutation_at structural q).val i = i :=
  WeightTwoGeometry.twoCore_fixes_complement _ P.two_weight
    (P.fiveJoinPermutation_at structural) (P.fiveJoinPermutation_contains_five_at structural) q i

theorem five_moved_le_core_omega_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    ⁅V,P.five⁆ ≤ omegaCenterIn ((P.five ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2) := by
  have hWV : ⁅V,P.five⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp
    (((pointResidual_le L (P.two : G)).trans inf_le_left).trans S.chosen.normalizes)
  intro x hx
  let x' : V := ⟨x,hWV hx⟩
  refine (mem_omegaCenterIn_iff _ _).mpr ⟨?_,?_,?_⟩
  · exact Setup.NaturalCoordinates.core_le_subjoin_core P.five
      ((pointResidual_le L (P.two : G)).trans inf_le_left) (S.chosen.le_core (hWV hx))
  · rintro q ⟨q,hq,rfl⟩
    have he := (E.sourceNormalizerModel_at structural).equivariant
      ⟨q,P.five_join_normalizes_module_at structural q.property⟩ x'
    have hf := WeightTwoGeometry.fixes_word_of_complement_fixed
      (E.coordinates P.two).toAdd (E.coordinates x').toAdd
      (P.fiveJoinPermutation_at structural q) (P.five_core_fixes_complement_at structural ⟨q,hq⟩)
      (E.point_residual_commutator_support_zero P.two P.two_weight x' hx)
    have hh : V.normalizerMonoidHom
        ⟨q,P.five_join_normalizes_module_at structural q.property⟩ x' = x' :=
      E.coordinates.injective (Multiplicative.toAdd.injective (he.trans hf))
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hh)
  · exact ((mem_omegaCenterIn_iff _ _).mp
      (Setup.NaturalCoordinates.chosen_le_core_omega (S := S) (hWV hx))).2.2

theorem fiveJoinPermutation_kernel_isTwoGroup_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    IsPGroup 2 (P.fiveJoinPermutation_at structural).ker := by
  let H := P.five ⊔ (T : Subgroup G)
  let B := P.five.subgroupOf H
  let R := (T : Subgroup G).subgroupOf H
  let f := P.fiveJoinPermutation_at structural
  let : B.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le P.five.le_normalizer
      (pointResidual_normalized S.chosen.sylow_normalizes_component P.two_central))
  have hgen : B ⊔ R = ⊤ := by
    rw [← subgroupOf_sup (show P.five ≤ H from le_sup_left)
      (show (T : Subgroup G) ≤ H from le_sup_right),subgroupOf_self]
  apply f.kernel_isPGroup_of_normal_supplement B R T.isPGroup'.comap_subtype hgen
  let j : (f.comp B.subtype).ker →* (E.pointResidualProjection P.two P.two_weight).ker :=
    { toFun x := ⟨⟨x.val.val.val,x.val.property⟩,by
        apply Subtype.ext
        apply Subtype.ext
        have he := E.sourceNormalizerModel_component_at structural
          ⟨x.val.val.val,((pointResidual_le L (P.two : G)).trans inf_le_left) x.val.property⟩
        exact he.symm.trans (congrArg Subtype.val x.property)⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  exact (E.pointResidualProjection_kernel_isTwoGroup P.two P.two_weight).of_injective j
    (fun x y h => Subtype.ext (Subtype.ext (Subtype.ext
      (congrArg (fun z : (E.pointResidualProjection P.two P.two_weight).ker =>
        ((z.val : P.five) : G)) h))))

theorem exists_five_core_support_swap_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hsurj : Function.Surjective (E.sourceNormalizerModel_at structural).permutation)
    (i j : Fin 7) (hij : i ≠ j)
    (hpair : WeightTwoGeometry.support (E.coordinates P.two).toAdd = {i,j}) :
    ∃ q : pCore 2 (P.five ⊔ (T : Subgroup G) : Subgroup G),
      (P.fiveJoinPermutation_at structural q).val = Equiv.swap i j := by
  let D := E.sourceNormalizerModel_at structural
  let hTV := ((structural L S.hypothesis).2.2 V S.chosen).1
  let R := T.subtype hTV
  let Q := R.mapSurjective hsurj
  let C := WeightTwoGeometry.symmetricStabilizer (E.coordinates P.two).toAdd
  have hQC : (Q : Subgroup (Equiv.Perm (Fin 7))) ≤ C := by
    rintro g ⟨t,ht,rfl⟩
    rw [WeightTwoGeometry.mem_symmetricStabilizer]
    change evenRepresentation (D.permutation t) (D.coordinates P.two).toAdd =
      (D.coordinates P.two).toAdd
    rw [← D.equivariant]
    congr 2
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (P.two_central t ht)
  let s : C := ⟨Equiv.swap i j,WeightTwoGeometry.support_swap_mem _ i j hij hpair⟩
  have hs : s ∈ pCore 2 C := WeightTwoGeometry.support_swap_mem_twoCore _ i j hij hpair
  have hsQ := (pCore_isPGroup.le_sylow_of_normal (Q.subtype hQC)) hs
  obtain ⟨t,ht,hts⟩ := hsQ
  let tH : (P.five ⊔ (T : Subgroup G) : Subgroup G) := ⟨t,mem_sup_right ht⟩
  have hf : (P.fiveJoinPermutation_at structural tH) = s := Subtype.ext hts
  have hp := pCore_isPGroup.comap_of_ker_isPGroup (P.fiveJoinPermutation_at structural)
    (P.fiveJoinPermutation_kernel_isTwoGroup_at structural)
  have hle : (pCore 2 C).comap (P.fiveJoinPermutation_at structural) ≤
      pCore 2 (P.five ⊔ (T : Subgroup G) : Subgroup G) := le_sSup ⟨inferInstance,hp⟩
  have htcore := hle (show tH ∈ (pCore 2 C).comap (P.fiveJoinPermutation_at structural) from by
    change P.fiveJoinPermutation_at structural tH ∈ pCore 2 C
    rw [hf]
    exact hs)
  exact ⟨⟨tH,htcore⟩,hts⟩

theorem five_core_omega_decomposition_of_weight_six_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (hsix : ∀ z : V, (z : G) ∈ centralizer (T : Set G) →
      weight (E.coordinates z).toAdd.val = 6 →
      centralizer ({(z : G)} : Set G) ≤ normalizer (L : Set G)) :
    omegaCenterIn ((P.five ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2) =
      ⁅V,P.five⁆ ⊔ (omegaCenterIn (T : Subgroup G) ⊓ centralizer (P.five : Set G)) ∧
    Disjoint ⁅V,P.five⁆
      (omegaCenterIn (T : Subgroup G) ⊓ centralizer (P.five : Set G)) := by
  let F := omegaCenterIn (T : Subgroup G) ⊓ centralizer (P.five : Set G)
  refine ⟨le_antisymm ?_ (sup_le (P.five_moved_le_core_omega_at structural)
    P.five_sylow_fixed_le_core_omega),P.five_core_omega_factors_disjoint⟩
  rw [(P.five_core_omega_reduction_of_weight_six_at structural escape hsix).1]
  apply sup_le ?_ (le_sup_of_le_right (inf_le_inf_left _
    (centralizer_le ((pointResidual_le L (P.two : G)).trans inf_le_left))))
  obtain ⟨i,j,hij,hpair⟩ := Finset.card_eq_two.mp
    (show (WeightTwoGeometry.support (E.coordinates P.two).toAdd).card = 2 from P.two_weight)
  obtain ⟨q,hq⟩ := P.exists_five_core_support_swap_at structural
    (E.thompson_and_symmetric_of_weight_six_at structural escape hsix).2 i j hij hpair
  intro x hx
  let x' : V := ⟨x,hx.1⟩
  have hqG : ((q.val : (P.five ⊔ (T : Subgroup G) : Subgroup G)) : G) ∈
      (P.five ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 := mem_map_of_mem _ q.property
  have he := (E.sourceNormalizerModel_at structural).equivariant
    ⟨q.val,P.five_join_normalizes_module_at structural q.val.property⟩ x'
  have hc : V.normalizerMonoidHom
      ⟨q.val,P.five_join_normalizes_module_at structural q.val.property⟩ x' = x' :=
    Subtype.ext (mul_inv_eq_iff_eq_mul.mpr (hx.2 _ hqG))
  have hfix : evenRepresentation (Equiv.swap i j) (E.coordinates x').toAdd =
      (E.coordinates x').toAdd := by
    rw [← hq]
    exact he.symm.trans (congrArg (fun v : V => (E.coordinates v).toAdd) hc)
  obtain ⟨y,hy,c,hc⟩ := WeightTwoGeometry.support_swap_fixed_split
    (E.coordinates P.two).toAdd (E.coordinates x').toAdd i j hij hpair hfix
  let v : V := E.coordinates.symm (Multiplicative.ofAdd y)
  have hv : (E.coordinates v).toAdd = y := congrArg Multiplicative.toAdd
    (E.coordinates.apply_symm_apply (Multiplicative.ofAdd y))
  have hvW : (v : G) ∈ ⁅V,P.five⁆ := P.support_zero_mem_five_moved v (hv.symm ▸ hy)
  have htwo : (P.two : G) ∈ F := ⟨P.two_mem_omega,by
    intro k hk
    exact (mem_centralizer_singleton_iff.mp (pointResidual_le L (P.two : G) hk).2)⟩
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · simp only [zero_smul,add_zero] at hc
    have hxx : x' = v := E.coordinates.injective
      (Multiplicative.toAdd.injective (hc.trans hv.symm))
    have hg : x = (v : G) := congrArg Subtype.val hxx
    rw [hg]
    exact mem_sup_left hvW
  · simp only [one_smul] at hc
    have hxx : x' = v * P.two := E.coordinates.injective (Multiplicative.toAdd.injective (by
      rw [map_mul,toAdd_mul,hv]
      exact hc))
    have hg := congrArg Subtype.val hxx
    change x = (v : G) * (P.two : G) at hg
    rw [hg]
    exact mul_mem_sup hvW htwo

theorem thompson_not_le_five_core_of_weight_six_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (hsix : ∀ z : V, (z : G) ∈ centralizer (T : Set G) →
      weight (E.coordinates z).toAdd.val = 6 →
      centralizer ({(z : G)} : Set G) ≤ normalizer (L : Set G)) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      (P.five ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 := by
  classical
  intro hJ
  let N := normalizer (V : Set G)
  let D := E.sourceNormalizerModel_at structural
  let π := D.permutation
  let hTV := ((structural L S.hypothesis).2.2 V S.chosen).1
  let R := T.subtype hTV
  have hπ := (E.thompson_and_symmetric_of_weight_six_at structural escape hsix).2
  let Q := R.mapSurjective hπ
  have hQC : (Q : Subgroup (Equiv.Perm (Fin 7))) ≤
      WeightTwoGeometry.symmetricStabilizer (E.coordinates P.two).toAdd := by
    rintro g ⟨t,ht,rfl⟩
    rw [WeightTwoGeometry.mem_symmetricStabilizer]
    change evenRepresentation (D.permutation t) (D.coordinates P.two).toAdd =
      (D.coordinates P.two).toAdd
    rw [← D.equivariant]
    congr 2
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (P.two_central t ht)
  obtain ⟨i,j,hij,hpair⟩ := Finset.card_eq_two.mp
    (show (WeightTwoGeometry.support (E.coordinates P.two).toAdd).card = 2 from P.two_weight)
  have hmax (B : Subgroup N) (hB : B ∈ elementaryAbelianMaxSubgroups (R : Subgroup N)) :
      B.map π ≤ zpowers (Equiv.swap i j) := by
    have hBG : B.map N.subtype ∈ elementaryAbelianMaxSubgroups (T : Subgroup G) := by
      have hh := (maxFamily_map_injective_iff N.subtype N.subtype_injective _ _).mpr hB
      rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTV] at hh
    rintro g ⟨b,hb,rfl⟩
    have hbJ : (b : G) ∈ elementaryAbelianMaxJ (T : Subgroup G) :=
      le_sSup hBG (mem_map_of_mem N.subtype hb)
    obtain ⟨q,hq,hqb⟩ := hJ hbJ
    have he : π b = (P.fiveJoinPermutation_at structural q).val := by
      have hn : b = ⟨q,P.five_join_normalizes_module_at structural q.property⟩ := Subtype.ext hqb.symm
      rw [hn]
      rfl
    rw [he]
    rcases WeightTwoGeometry.support_swap_image_le (E.coordinates P.two).toAdd i j hij hpair
      (P.fiveJoinPermutation_at structural q)
      (P.five_core_fixes_complement_at structural ⟨q,hq⟩) with hz | hs
    · rw [hz]; exact one_mem _
    · rw [hs]; exact mem_zpowers _
  obtain ⟨A,hA,hne,_⟩ := E.core_omega_maxElementary_splitting_of_weight_six_at structural escape hsix
  let A' := A.subgroupOf N
  have hA' : A' ∈ elementaryAbelianMaxSubgroups (R : Subgroup N) := by
    apply (maxFamily_map_injective_iff N.subtype N.subtype_injective _ _).mp
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTV,
      map_subgroupOf_eq_of_le (hA.1.trans hTV)]
  have hAimage : A'.map π = zpowers (Equiv.swap i j) := by
    apply le_antisymm (hmax A' hA')
    obtain ⟨a,ha,hane⟩ := ((A'.map π).bot_or_exists_ne_one).resolve_left hne
    have ha' := hmax A' hA' ha
    have hcard : Nat.card (zpowers (Equiv.swap i j)) = 2 := by
      rw [Nat.card_zpowers]
      apply orderOf_eq_prime
      · simp [pow_two]
      · intro h
        have hh := congrArg (fun a : Equiv.Perm (Fin 7) => a i) h
        exact hij (by simpa using hh.symm)
    have haeq : a = Equiv.swap i j := by
      have htwo : ∀ b : zpowers (Equiv.swap i j), b ≠ 1 →
          b = ⟨Equiv.swap i j,mem_zpowers _⟩ := by
        have hnon : (⟨Equiv.swap i j,mem_zpowers _⟩ : zpowers (Equiv.swap i j)) ≠ 1 :=
          fun h => hij (by
            have hh := congrArg (fun a : zpowers (Equiv.swap i j) => a.val i) h
            simpa using hh.symm)
        intro b hb
        obtain ⟨c,_,hc⟩ := (Nat.card_eq_two_iff' (1 : zpowers (Equiv.swap i j))).mp hcard
        exact (hc b hb).trans (hc _ hnon).symm
      exact congrArg Subtype.val (htwo ⟨a,ha'⟩ (fun h => hane (congrArg Subtype.val h)))
    exact zpowers_le.mpr (haeq ▸ ha)
  obtain ⟨r,t,hrt,hrtQ⟩ := WeightTwoGeometry.sylow_contains_complement_swap
    (E.coordinates P.two).toAdd P.two_weight Q hQC
  have hrt' : r.val ≠ t.val := fun h => hrt (Subtype.ext h)
  obtain ⟨g,hg⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap hij hrt')
  obtain ⟨n,hn⟩ := hπ g
  let B := A'.map (MulAut.conj n).toMonoidHom
  have hBg : B ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup N) := by
    have hh := (maxFamily_map_injective_iff (MulAut.conj n).toMonoidHom
      (MulAut.conj n).injective ⊤ A').mpr ((maxFamily_sylow_iff R A').mp hA').2
    rwa [map_top_of_surjective _ (MulAut.conj n).surjective] at hh
  have hBi : B.map π = zpowers (Equiv.swap r.val t.val) := by
    have he : π.comp (MulAut.conj n).toMonoidHom = (MulAut.conj g).toMonoidHom.comp π := by
      apply MonoidHom.ext
      intro a
      change π (n*a*n⁻¹) = g * π a * g⁻¹
      rw [map_mul,map_mul,map_inv,hn]
    change (A'.map _).map π = _
    rw [map_map,he,←map_map,hAimage,MonoidHom.map_zpowers]
    congr 1
  obtain ⟨C,hC,hCi⟩ := exists_maxFamily_sylow_same_image R π B hBg (by
    rw [hBi]
    exact zpowers_le.mpr hrtQ)
  have htar : Equiv.swap r.val t.val ∈ C.map π := by rw [hCi,hBi]; exact mem_zpowers _
  have hle := hmax C hC htar
  have hfix : ∀ a ∈ zpowers (Equiv.swap i j), a r.val = r.val := by
    intro a ha
    have hri : r.val ≠ i := by
      intro he
      apply Finset.mem_compl.mp r.property
      have hi : i ∈ WeightTwoGeometry.support (E.coordinates P.two).toAdd := by rw [hpair]; simp
      exact he.symm ▸ hi
    have hrj : r.val ≠ j := by
      intro he
      apply Finset.mem_compl.mp r.property
      have hj : j ∈ WeightTwoGeometry.support (E.coordinates P.two).toAdd := by rw [hpair]; simp
      exact he.symm ▸ hj
    have hs : zpowers (Equiv.swap i j) ≤ MulAction.stabilizer (Equiv.Perm (Fin 7)) r.val :=
      zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff]; exact Equiv.swap_apply_of_ne_of_ne hri hrj)
    exact MulAction.mem_stabilizer_iff.mp (hs ha)
  have hh := hfix _ hle
  rw [Equiv.swap_apply_left] at hh
  exact hrt' hh.symm

private theorem perfect_normal_full_image_at
    {A B : Type*} [Group A] [Group B] [Group.IsPerfect A]
    (f : A →* B) [Group.IsSolvable f.ker]
    (N : Subgroup A) [N.Normal] (himage : N.map f = ⊤) : N = ⊤ := by
  have hgen : N ⊔ f.ker = ⊤ := by
    have hh := congrArg (Subgroup.comap f) himage
    simpa only [comap_map_eq,comap_top] using hh
  let q := QuotientGroup.mk' N
  have hq : Function.Surjective (q.comp f.ker.subtype) := by
    intro x
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective N x
    have hg : g ∈ N ⊔ f.ker := hgen ▸ mem_top g
    obtain ⟨n,hn,k,hk,rfl⟩ := mem_sup_of_normal_left.mp hg
    refine ⟨⟨k,hk⟩,?_⟩
    change q k = q (n*k)
    rw [map_mul,show q n = 1 from (QuotientGroup.eq_one_iff n).mpr hn,one_mul]
  let : Group.IsSolvable (A ⧸ N) := Group.isSolvable_of_surjective hq
  let : Group.IsPerfect (A ⧸ N) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hs : Subsingleton (A ⧸ N) := by
    by_contra! hnt
    exact Group.IsPerfect.not_isSolvable (A ⧸ N) inferInstance
  apply top_unique
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (hs.elim (q g) 1)

theorem five_thompson_generation_of_weight_six_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (hsix : ∀ z : V, (z : G) ∈ centralizer (T : Set G) →
      weight (E.coordinates z).toAdd.val = 6 →
      centralizer ({(z : G)} : Set G) ≤ normalizer (L : Set G)) :
    P.five = ⁅P.five,elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  let K := P.five
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  let C := ⁅K,J⁆
  have hJT : J ≤ (T : Subgroup G) := sSup_le (fun _ h => h.1)
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    pointResidual_normalized S.chosen.sylow_normalizes_component P.two_central
  have hCK : C ≤ K := le_normalizer_iff_commutator_le_left.mp (hJT.trans hTK)
  let N := C.subgroupOf K
  let : N.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left K J)
  let e := P.fiveCoreEquiv
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent f.ker := (hk ▸ pCore_isPGroup).isNilpotent
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : (N.map f).Normal := (inferInstance : N.Normal).map f hf
  rcases (inferInstance : (N.map f).Normal).eq_bot_or_eq_top with hn | hn
  · exfalso
    have hN := (Subgroup.map_eq_bot_iff N).mp hn
    rw [hk] at hN
    have hcenter : center (K ⧸ pCore 2 K) = ⊥ := by
      apply bot_unique
      intro x hx
      have he : e x ∈ center (alternatingGroup (Fin 5)) := by
        rw [mem_center_iff]
        intro y
        obtain ⟨a,rfl⟩ := e.surjective y
        simpa only [map_mul] using congrArg e (mem_center_iff.mp hx a)
      rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at he
      exact e.injective (he.trans e.map_one.symm)
    apply P.thompson_not_le_five_core_of_weight_six_at structural escape hsix
    intro j hj
    let jH : (K ⊔ (T : Subgroup G) : Subgroup G) := ⟨j,mem_sup_right (hJT hj)⟩
    have hjker : jH ∈ (pCoreJoinAction 2 hTK).ker := by
      apply MulEquiv.ext
      intro x
      obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) x
      rw [pCoreJoinAction_mk]
      let b : K := K.normalizerMonoidHom (inclusion (sup_le K.le_normalizer hTK) jH) k
      have hb : b*k⁻¹ ∈ pCore 2 K := by
        apply hN
        change ⁅j,(k : G)⁆ ∈ C
        change ⁅j,(k : G)⁆ ∈ ⁅K,J⁆
        rw [commutator_comm]
        exact commutator_mem_commutator hj k.property
      have he := (QuotientGroup.eq_one_iff (b*k⁻¹)).mpr hb
      change QuotientGroup.mk' (pCore 2 K) (b*k⁻¹) = 1 at he
      rw [map_mul,map_inv] at he
      exact mul_inv_eq_one.mp he
    have hcore := (pCoreJoinAction_kernel 2 hTK T.isPGroup' hcenter) ▸ hjker
    exact mem_map_of_mem (K ⊔ (T : Subgroup G)).subtype hcore
  · have ht := perfect_normal_full_image_at f N hn
    apply le_antisymm ?_ hCK
    intro k hk
    have hh : (⟨k,hk⟩ : K) ∈ N := ht ▸ mem_top _
    exact hh

theorem source_1237_two_of_weight_six_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (hsix : ∀ z : V, (z : G) ∈ centralizer (T : Set G) →
      weight (E.coordinates z).toAdd.val = 6 →
      centralizer ({(z : G)} : Set G) ≤ normalizer (L : Set G)) :
    P.five = ⁅P.five,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
    omegaCenterIn ((P.five ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2) =
      ⁅V,P.five⁆ ⊔ (omegaCenterIn (T : Subgroup G) ⊓ centralizer (P.five : Set G)) ∧
    Disjoint ⁅V,P.five⁆
      (omegaCenterIn (T : Subgroup G) ⊓ centralizer (P.five : Set G)) :=
  ⟨P.five_thompson_generation_of_weight_six_at structural escape hsix,
    P.five_core_omega_decomposition_of_weight_six_at structural escape hsix⟩

theorem source_1237_of_weight_six_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (hsix : ∀ z : V, (z : G) ∈ centralizer (T : Set G) →
      weight (E.coordinates z).toAdd.val = 6 →
      centralizer ({(z : G)} : Set G) ≤ normalizer (L : Set G)) :
    L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
    Function.Surjective (E.sourceNormalizerModel_at structural).permutation ∧
    omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) =
      V ⊔ (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) ∧
    Disjoint V (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) ∧
    P.five = ⁅P.five,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
    omegaCenterIn ((P.five ⊔ (T : Subgroup G)).pCoreIn 2) =
      ⁅V,P.five⁆ ⊔ (omegaCenterIn (T : Subgroup G) ⊓ centralizer (P.five : Set G)) ∧
    Disjoint ⁅V,P.five⁆
      (omegaCenterIn (T : Subgroup G) ⊓ centralizer (P.five : Set G)) := by
  obtain ⟨hL,hperm,hOmega,hdisjoint⟩ := E.source_1237_one_of_weight_six_at structural escape hsix
  exact ⟨hL,hperm,hOmega,hdisjoint,P.source_1237_two_of_weight_six_at structural escape hsix⟩

end SylowNormalizer.Points

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

