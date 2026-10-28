module
public import Theory.GroupTheory.NormalCubicSylowProduct
public import Theory.GroupTheory.QuotientIntersection
public import Theory.Quasithin.CoprimeRank
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaResidualStructure

/-!
# The Sylow-three structure in the cubic Omega branch

The original Y has a faithful star image of order three. It commutes with
C_M(V)* by 15.2.3(5), and their intersection is trivial. Additivity of
three-rank and quasithinness give m₃(C_M(V))≤1 directly in this branch.

The normal cubic star image is detected by M-bar ≃ S₃ × S₃. Its coordinate
projection splits a Sylow three-subgroup of M* into that cubic and a cyclic
complement. The full order-nine quotient makes the complement nontrivial.
A two-group kernel preserves Sylow three-subgroups, giving the original
Sylow subgroups of M the required C₃ × C₃ⁿ structure.

Source: Aschbacher--Smith15.2.3(1)(iii), printed p.1105. All subgroups,
actions and quotient maps are the original chosen-module constructions.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem omega_core_le_kernel {M V : Subgroup G}
    [IsElementaryAbelian 2 V] (hn : M ≤ normalizer (V : Set G))
    (ho : SourceCases.Omega (imageRepresentation M V hn)) :
    pCore 2 M ≤ (actionHom M V hn).ker := by
  let f := (actionHom M V hn).rangeRestrict
  let e := ho.2.2.2.1.some
  have hnormal : ((pCore 2 M).map (e.toMonoidHom.comp f)).Normal :=
    Normal.map inferInstance _ (e.surjective.comp (actionHom M V hn).rangeRestrict_surjective)
  have hp : (pCore 2 M).map (e.toMonoidHom.comp f) ≤
      pCore 2 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
    le_sSup ⟨hnormal,pCore_isPGroup.map _⟩
  rw [SymmetricThreeProduct.twoCore_eq_bot] at hp
  intro x hx
  have hh : f x = 1 := e.injective
    ((Subgroup.mem_bot.mp (hp (mem_map_of_mem _ hx))).trans e.map_one.symm)
  exact congrArg Subtype.val hh

/-- The cubic source branch has cyclic centralizer Sylow three-subgroups and
all Sylow three-subgroups of M are C₃ × C₃ⁿ for a positive n. -/
theorem source_omega_cubic_sylow_structure
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hcard : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (actionHom M V hV.normalized).rangeRestrict) = 3) :
    primeRank 3 (M ⊓ centralizer (V : Set G) : Subgroup G) ≤ 1 ∧
      ∀ P : Sylow 3 M, ∃ n : ℕ, 1 ≤ n ∧ Nonempty
        (P ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod (3 ^ n))) := by
  let f := (actionHom M V hV.normalized).rangeRestrict
  let q := QuotientGroup.mk' (pCore 2 M)
  let Y := (caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M
  let A := Y.map q
  let C := f.ker.map q
  have hcore : pCore 2 M ≤ f.ker := by
    simpa only [f,MonoidHom.ker_rangeRestrict] using omega_core_le_kernel hV.normalized ho
  let g := QuotientGroup.lift (pCore 2 M) f hcore
  have hgs : Function.Surjective g :=
    QuotientGroup.lift_surjective_of_surjective _ f (actionHom M V hV.normalized).rangeRestrict_surjective hcore
  have hgk : g.ker = C := QuotientGroup.ker_lift _ _ _
  have hbound : Y ⊓ f.ker ≤ pCore 2 M := by
    simpa only [f,MonoidHom.ker_rangeRestrict] using
      source_omega_cyclic_kernel_le_core T hM.2 hu hV ho hcard
  have hd : Disjoint A C := by
    rw [disjoint_iff]
    change Y.map q ⊓ f.ker.map q = ⊥
    rw [← map_inf_of_ker_le q Y f.ker (by rwa [QuotientGroup.ker_mk'])]
    rw [Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
    exact hbound
  have hac : A ≤ centralizer (C : Set (M ⧸ pCore 2 M)) := by
    have hCeq : (M ⊓ centralizer (V : Set G)).subgroupOf M = f.ker := by
      rw [show f = (actionHom M V hV.normalized).rangeRestrict from rfl,
        MonoidHom.ker_rangeRestrict,actionHom_ker]
      ext x
      exact ⟨fun hx => hx.2,fun hx => ⟨x.property,hx⟩⟩
    have hh := source_omega_lemma_15_2_3_5 T hM.2 hu hV ho
    rw [hCeq] at hh
    exact le_sup_right.trans hh
  have hc : Nat.card A = 3 := source_omega_cyclic_star_card T hM.2 hu hV ho hcard
  have hrank : primeRank 3 (M ⧸ pCore 2 M) ≤ 2 := by
    rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 M) pCore_isPGroup]
    exact (hG.twoLocal_sqtk hM.1.1).stronglyQuasithin 3 Nat.prime_three (by decide)
  have hCr : primeRank 3 C ≤ 1 := by
    have hAr : 1 ≤ primeRank 3 A := by
      by_contra h
      have hz : primeRank 3 A = 0 := by omega
      exact (PrimeRank.eq_zero_iff_not_dvd_card.mp hz) (hc ▸ dvd_rfl)
    have he := primeRank_sup_eq_add_of_disjoint_commuting A C hd hac 3
    have hr := (Theory.GroupTheory.primeRank_le_of_injective 3 (A ⊔ C).subtype (A ⊔ C).subtype_injective).trans hrank
    omega
  have hcop : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := M)).exists_card_eq
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  constructor
  · have hqk : IsPGroup 2 (q.subgroupMap f.ker).ker := by
      rw [ker_subgroupMap,QuotientGroup.ker_mk']
      exact pCore_isPGroup.comap_subtype
    obtain ⟨k,hk⟩ := hqk.exists_card_eq
    have hCp : Nat.Coprime 3 (Nat.card (q.subgroupMap f.ker).ker) := by
      rw [hk]
      exact (by decide : Nat.Coprime 3 2).pow_right k
    have he := primeRank_eq_of_surjective_of_coprime 3 (q.subgroupMap f.ker)
      (q.subgroupMap_surjective f.ker) hCp
    have hCmap : f.ker.map M.subtype = M ⊓ centralizer (V : Set G) := by
      rw [show f = (actionHom M V hV.normalized).rangeRestrict from rfl,
        MonoidHom.ker_rangeRestrict,actionHom_ker,subgroupOf_map_subtype,inf_comm]
    have he2 := primeRank_equiv 3
      ((f.ker.equivMapOfInjective M.subtype M.subtype_injective).trans (MulEquiv.subgroupCongr hCmap))
    change primeRank 3 f.ker = primeRank 3 C at he
    omega
  · intro P
    let : Y.Normal := source_omega_lemma_15_2_3_2 T hM.2 hV.normalized ho
    let : A.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
    let e := ho.2.2.2.1.some
    have hi : Function.Injective ((e.toMonoidHom.comp g).comp A.subtype) := by
      apply (injective_iff_map_eq_one _).mpr
      intro x hx
      have hxg : g (x : M ⧸ pCore 2 M) = 1 := e.injective (hx.trans e.map_one.symm)
      exact Subtype.ext (disjoint_def.mp hd x.property (hgk ▸ hxg))
    let Ps := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 M))
    obtain ⟨n,hn,⟨en⟩⟩ := normal_cubic_sylow_three_product hrank A hc
      (e.toMonoidHom.comp g) (e.surjective.comp hgs) hi Ps
    refine ⟨n,hn,⟨?_⟩⟩
    exact (Sylow.equivOfSurjectiveCoprime q (QuotientGroup.mk'_surjective _) hcop P Ps).trans en
end CFSG.Quasithin.Chapter15.Section02
