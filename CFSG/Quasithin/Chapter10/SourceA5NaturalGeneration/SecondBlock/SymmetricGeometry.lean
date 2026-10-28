module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SecondBlock.SymmetricCore
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.Rank
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SylowTwoStep
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.CommutingSylow
public import Theory.GroupTheory.CentralElementaryCommutatorProduct
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.Marking
/-!
# Common Baumann geometry from either residual orientation

A block covering the residual alone, or with a Sylow conjugate, has trivial
center and its entire two-core equals the distinguished block module once
the ambient core is moved. Its natural Sylow subgroup has central elementary
commutators under a cubic normalizer. In the paired row the conjugator carries
this bound to the other commuting Sylow factor; the two bounds combine in
the original Baumann subgroup.
Source: Aschbacher--Smith 10.2.3(4), printed p.747, using C.1.9 and C.1.17.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open ChapterB ChapterC ChapterC.RankOne.ChiProduct
variable {G : Type*} [Group G] [Finite G]

/-- Residual block coverage and whole-core movement recover the intrinsic core. -/
theorem source_block_center_and_core_of_residual_cover
    (hfit : generalizedFitting G = pCore 2 G)
    (K : Subgroup G) (hb : IsBlock K)
    (hR : pResidual 2 G = K ∨
      ∃ t : G, pResidual 2 G = K ⊔ K.map (MulAut.conj t).toMonoidHom)
    (hz : pCore 2 G ⊓ centralizer (pResidual 2 G : Set G) = ⊥)
    (hm : pCore 2 G = ⁅pCore 2 G,pResidual 2 G⁆) :
    center K = ⊥ ∧ pCore 2 K = blockU K := by
  have single (he : pResidual 2 G = K) : center K = ⊥ ∧ pCore 2 K = blockU K := by
    have hfix : pCore 2 G ⊓ centralizer ((K ⊔ (⊥ : Subgroup G) : Subgroup G) : Set G) = ⊥ := by
      simpa only [sup_bot_eq,←he] using hz
    exact ⟨hb.center_eq_bot_of_pair_core_centralizer (by simp) hfix,
      hb.core_eq_blockU_of_residual_core_generated he hm⟩
  rcases hR with he | ⟨t,he⟩
  · exact single he
  let J := K.map (MulAut.conj t).toMonoidHom
  have hbJ : IsBlock J := hb.map_equiv (MulAut.conj t)
  by_cases hne : K = J
  · apply single
    change pResidual 2 G = K ⊔ J at he
    simpa only [←hne,sup_idem] using he
  have hc : ⁅K,J⁆ = ⊥ := blocks_commute (blockCommutationHypothesis_of_fitting hfit) hb hbJ hne
  have hfix : pCore 2 G ⊓ centralizer ((K ⊔ J : Subgroup G) : Set G) = ⊥ := he ▸ hz
  have hzK := hb.center_eq_bot_of_pair_core_centralizer hc hfix
  have hzJ : center J = ⊥ := by
    apply hbJ.center_eq_bot_of_pair_core_centralizer
    · rwa [commutator_comm]
    · simpa only [sup_comm] using hfix
  exact ⟨hzK,hb.core_eq_blockU_of_pair_core_generated hbJ hc hzJ (he ▸ hm)⟩

/-- Central elementary commutators from either source residual orientation. -/
theorem source_baumann_commutator_of_natural_residual_cover
    (T : Sylow 2 G) (hfit : generalizedFitting G = pCore 2 G)
    (K : Subgroup G) (hb : IsBlock K) {n : ℕ} (hnat : IsL2EvenBlock K n)
    (hR : pResidual 2 G = K ∨
      ∃ t : G, t ∈ (T : Subgroup G) ∧
        pResidual 2 G = K ⊔ K.map (MulAut.conj t).toMonoidHom)
    (hz : omegaCenterIn (T : Subgroup G) ⊓ center G = ⊥)
    (hm : pCore 2 G = ⁅pCore 2 G,pResidual 2 G⁆)
    (hS : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G)) (pResidual 2 G))
    (A : Subgroup G) (hAK : A ≤ K) (hA : Nat.card A = 3)
    (hAS : A ≤ normalizer (baumann (T : Subgroup G) : Set G)) :
    commutator (baumann (T : Subgroup G)) ≤
      GlaubermanNiles.omegaCenter (baumann (T : Subgroup G)) := by
  let S := baumann (T : Subgroup G)
  let P := S ⊓ K
  have hR' : pResidual 2 G = K ∨ ∃ t : G,
      pResidual 2 G = K ⊔ K.map (MulAut.conj t).toMonoidHom := by
    rcases hR with h | ⟨t,_,h⟩
    · exact Or.inl h
    · exact Or.inr ⟨t,h⟩
  obtain ⟨hzK,hcore⟩ := source_block_center_and_core_of_residual_cover hfit K hb hR'
    (core_residual_fixed_eq_bot_of_omega_center T hz) hm
  have hKR : K ≤ pResidual 2 G := by
    rcases hR with he | ⟨_,_,he⟩
    · exact he.ge
    · exact he ▸ le_sup_left
  have hSP : Chapter1.IsSylowIn 2 P K :=
    Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hS hKR hb.subnormal.subgroupOf
  have hAP : A ≤ normalizer (P : Set G) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    rw [commutator_comm]
    exact le_inf ((commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hAS))
      ((commutator_mono inf_le_right le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp (hAK.trans K.le_normalizer)))
  have hP := hnat.ambient_sylow_commutator_le_omegaCenterIn K P A hcore hzK hSP hAK hA hAP
  have hcomm : ⁅S,S⁆ ≤ omegaCenterIn S := by
    rcases hR with he | ⟨t,ht,he⟩
    · have hSK : S ≤ K := he ▸ (Chapter1.isSylowIn_iff.mp hS).2.1
      simpa only [show P=S from inf_eq_left.mpr hSK] using hP
    · let f := (MulAut.conj t).toMonoidHom
      let J := K.map f
      by_cases hne : K=J
      · have hSK : S ≤ K := by
          have h := (Chapter1.isSylowIn_iff.mp hS).2.1
          change pResidual 2 G = K ⊔ J at he
          simpa only [he,←hne,sup_idem] using h
        simpa only [show P=S from inf_eq_left.mpr hSK] using hP
      have hc : K ≤ centralizer (J : Set G) := commutator_eq_bot_iff_le_centralizer.mp
        (blocks_commute (blockCommutationHypothesis_of_fitting hfit) hb
          (hb.map_equiv (MulAut.conj t)) hne)
      have hSm : S.map f=S := mem_normalizer_iff_map_conj_eq.mp
        (normalizer_le_normalizer_baumann _ ((T : Subgroup G).le_normalizer ht))
      have hPm : P.map f=S ⊓ J := by
        rw [show P=S ⊓ K from rfl,map_inf _ _ _ (MulAut.conj t).injective,hSm]
      have hJP : Chapter1.IsSylowIn 2 (S ⊓ J) J := by
        have h := Chapter1.Section02.IndexTwo.isSylowIn_map hSP f
        rwa [hPm] at h
      have hJ : ⁅S ⊓ J,S ⊓ J⁆ ≤ omegaCenterIn (S ⊓ J) := by
        have h := map_mono (f := f) hP
        change (⁅P,P⁆).map f ≤ (omegaOneCenterAmbient P).map f at h
        rw [map_commutator,←omegaOneCenterAmbient_map_injective f (MulAut.conj t).injective,hPm] at h
        exact h
      have hsplit : S=P ⊔ (S ⊓ J) := eq_sup_sylow_intersections_of_commuting S K J
        (Chapter1.isSylowIn_iff.mp hS).1 (he ▸ (Chapter1.isSylowIn_iff.mp hS).2.1) hc hSP hJP
      have hh := commutator_le_omegaCenterIn_join_of_commuting P (S ⊓ J)
        (inf_le_right.trans (hc.trans (centralizer_le inf_le_right))) hP hJ
      rwa [←hsplit] at hh
  intro x hx
  have hm' : (commutator S).map S.subtype=⁅S,S⁆ := by
    rw [_root_.commutator_def,map_commutator,←MonoidHom.range_eq_map,range_subtype]
  obtain ⟨_,hxc,hx2⟩ := (mem_omegaCenterIn_iff S (x:G)).mp
    (hcomm (hm' ▸ mem_map_of_mem S.subtype hx))
  exact (GlaubermanNiles.mem_omegaCenter_iff x).mpr
    ⟨Subtype.ext hx2,fun y => Subtype.ext (hxc y y.property)⟩
end CFSG.Quasithin.Chapter10
