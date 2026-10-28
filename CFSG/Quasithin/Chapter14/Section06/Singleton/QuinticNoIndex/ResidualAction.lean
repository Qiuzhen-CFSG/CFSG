module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairCompatibility.QuinticGeometryParallel.ResidualPlane
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ModuleGeometry.ResidualIndex
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer

/-!
# The intrinsic quintic residual action before the factor-join index

Transport the literal action of Mc on O²(J)/O₂(O²(J)) to the primitive
residual in J/O₂(J). Self-centralization identifies the kernel on J, and
coprimality identifies its restriction to the original Sylow T. Consequently
|J/O₂(J)| is twenty-five times the order of that Sylow action image.

In the unresolved outer alternative, the actual permutation kernel properly
contains the D10 factor product of order one hundred. Its proved index two
therefore forces |J/O₂(J)| > 200 and makes the intrinsic Sylow image divisible
by sixteen. In particular the signed image of order eight used after 14.6.12
cannot supply a no-index argument here. All quotient maps and the original
outer witness are retained. These are conditional source calculations;
the Mc-normalizer bound and the outer contradiction are not proved here.

Source: Aschbacher--Smith, 14.6.12 and 14.6.15, printed pp.1031,1034.
The literal nonsingleton application is in `QuinticNoIndex.Source`.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open OddNormalizer
namespace Singleton.QuinticNoIndex
open SourcePairCompatibility.QuinticGeometryParallel
open OddNormalizer.Quintic.ModuleGeometry (residualPartnerAction residual_partner_normalizes)
variable {G : Type*} [Group G] [Finite G]

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
variable (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation)
    (π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index)
    (w : SourcePairCompatibility.QuinticOuterAction a f d π)
include hG hempty hM hu hmany hcard e hJ

omit [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)] in
private theorem original_partner_contains : J ≤ Mc := by
  have he := (Section02.source_lemma_14_2_3 hG T hempty hM hu
    hmany hcard e J hJ.1.1 hJ.1.2).1
  exact (show Mc ∈ maximalTwoLocalOvergroups J from he ▸ Set.mem_singleton Mc).2

include hab hs w

/-- On J, the literal intrinsic residual action is trivial precisely over
its starred residual. This is a quotient-kernel statement. -/
theorem source_quintic_action_eq_one_iff
    (hc : residualClosure J Mc = residual J) (x : Mc) (hx : (x : G) ∈ J) :
    residualPartnerAction Mc J hc x = 1 ↔
      QuotientGroup.mk' (pCore 2 J) ⟨x,hx⟩ ∈ pResidual 2 (J ⧸ pCore 2 J) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let := (source_quintic_primitive_residual hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π w).elementary
  let R := pResidual 2 (J ⧸ pCore 2 J)
  let q := QuotientGroup.mk' (pCore 2 J)
  obtain ⟨c,hcmap⟩ := residual_quotient_equiv (by decide : Odd 5) J
    (IsElementaryAbelian.isPGroup 5 R)
  have hcompat (v : residual J ⧸ pCore 2 (residual J)) :
      (c (residualPartnerAction Mc J hc x v) : J ⧸ pCore 2 J) =
        q ⟨x,hx⟩ * (c v : J ⧸ pCore 2 J) * (q ⟨x,hx⟩)⁻¹ := by
    obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (residual J)) v
    change (c (pCoreNormalizerAction 2 (residual J)
      (inclusion (residual_partner_normalizes Mc J hc) x)
        (QuotientGroup.mk' (pCore 2 (residual J)) v)) : J ⧸ pCore 2 J) = _
    rw [pCoreNormalizerAction_mk,hcmap,hcmap]
    change q _ = q ⟨x,hx⟩ * q _ * (q ⟨x,hx⟩)⁻¹
    rw [←map_inv,←map_mul,←map_mul]
    rfl
  constructor
  · intro hact
    apply centralizer_pResidual_le_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot 2)
    intro r hr
    have hh := hcompat (c.symm ⟨r,hr⟩)
    simp only [hact, MulAut.one_apply, c.apply_symm_apply] at hh
    change r = q ⟨x,hx⟩ * r * (q ⟨x,hx⟩)⁻¹ at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  · intro hr
    apply MulEquiv.ext
    intro v
    apply c.injective
    apply Subtype.ext
    rw [hcompat]
    change q ⟨x,hx⟩ * (c v : J ⧸ pCore 2 J) * (q ⟨x,hx⟩)⁻¹ = (c v : J ⧸ pCore 2 J)
    have hh : q ⟨x,hx⟩ * (c v : J ⧸ pCore 2 J) = (c v : J ⧸ pCore 2 J) * q ⟨x,hx⟩ :=
      congrArg Subtype.val (mul_comm (⟨q ⟨x,hx⟩,hr⟩ : R) (c v))
    rw [hh,mul_inv_cancel_right]

/-- The original Sylow's intrinsic residual-action kernel is exactly its
kernel in J/O₂(J). No signed coordinates are assumed. -/
theorem source_quintic_sylow_action_kernel
    (hc : residualClosure J Mc = residual J) :
    ((residualPartnerAction Mc J hc).comp
      (inclusion (AlternatingThree.sylow_le_partner T hu))).ker =
    ((QuotientGroup.mk' (pCore 2 J)).comp (inclusion hJ.1.1.2)).ker := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let := (source_quintic_primitive_residual hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π w).elementary
  let q := QuotientGroup.mk' (pCore 2 J)
  let S := (T.subtype hJ.1.1.2).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
  have hd : Disjoint (S : Subgroup (J ⧸ pCore 2 J)) (pResidual 2 (J ⧸ pCore 2 J)) :=
    IsPGroup.disjoint_of_coprime S.isPGroup' (IsElementaryAbelian.isPGroup 5 _) (by decide)
  ext x
  change residualPartnerAction Mc J hc ⟨x,hJ.1.1.2.trans (original_partner_contains hG T hempty hM hu hmany hcard e J hJ) x.property⟩ = 1 ↔
    q ⟨x,hJ.1.1.2 x.property⟩ = 1
  rw [source_quintic_action_eq_one_iff hG T hempty hM hu hmany hcard e hab J hJ hs a f d π w hc _ (hJ.1.1.2 x.property)]
  constructor
  · intro hx
    exact Subgroup.disjoint_def.mp hd
      (mem_map_of_mem q (show (⟨x,hJ.1.1.2 x.property⟩ : J) ∈
        (T : Subgroup G).subgroupOf J from x.property)) hx
  · intro hx
    rw [hx]
    exact one_mem _

/-- The literal J-action is already supplied by T, since the residual acts
internally on an abelian quotient. -/
theorem source_quintic_action_image
    (hc : residualClosure J Mc = residual J) :
    (J.subgroupOf Mc).map (residualPartnerAction Mc J hc) =
      ((T : Subgroup G).subgroupOf Mc).map (residualPartnerAction Mc J hc) := by
  let φ := residualPartnerAction Mc J hc
  have hHM := original_partner_contains hG T hempty hM hu hmany hcard e J hJ
  have hKM : residual J ≤ Mc := (residual_le J).trans hHM
  have hTM := hJ.1.1.2.trans (original_partner_contains hG T hempty hM hu hmany hcard e J hJ)
  have hKker : (residual J).subgroupOf Mc ≤ φ.ker := by
    intro x hx
    apply (source_quintic_action_eq_one_iff hG T hempty hM hu hmany hcard e hab J hJ hs a f d π w hc x (residual_le J hx)).mpr
    have hxH : (x : G) ∈ J := residual_le J hx
    obtain ⟨y,hy,he⟩ := hx
    have hmap := mem_map_of_mem (QuotientGroup.mk' (pCore 2 J)) hy
    rw [map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)] at hmap
    have hxy : (⟨(x : G),hxH⟩ : J) = y := Subtype.ext he.symm
    rw [hxy]
    exact hmap
  have hj : residual J ⊔ (T : Subgroup G) = J := by
    have hh := congrArg (map J.subtype) (pResidual_sup_sylow_eq_top (T.subtype hJ.1.1.2))
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
    change residual J ⊔ (((T : Subgroup G).subgroupOf J).map J.subtype) = J at hh
    rwa [map_subgroupOf_eq_of_le hJ.1.1.2] at hh
  change (J.subgroupOf Mc).map φ = ((T : Subgroup G).subgroupOf Mc).map φ
  have hjM : J.subgroupOf Mc = (residual J).subgroupOf Mc ⊔ (T : Subgroup G).subgroupOf Mc := by
    rw [←subgroupOf_sup hKM hTM,hj]
  have hz : ((residual J).subgroupOf Mc).map φ = ⊥ := by
    apply bot_unique
    rintro y ⟨x,hx,rfl⟩
    exact hKker hx
  rw [hjM,Subgroup.map_sup,hz,bot_sup_eq]


/-- The actual residual action retains the whole two-part of J/O₂(J).
Its odd part is the primitive plane of order twenty-five. -/
theorem source_quintic_action_card_formula
    (hc : residualClosure J Mc = residual J) :
    Nat.card (J ⧸ pCore 2 J) = 25 *
      Nat.card (((T : Subgroup G).subgroupOf Mc).map (residualPartnerAction Mc J hc)) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let := (source_quintic_primitive_residual hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π w).elementary
  have hTM := hJ.1.1.2.trans (original_partner_contains hG T hempty hM hu hmany hcard e J hJ)
  let φ := (residualPartnerAction Mc J hc).comp (inclusion hTM)
  let q := QuotientGroup.mk' (pCore 2 J)
  let qT := q.comp (inclusion hJ.1.1.2)
  let S := (T.subtype hJ.1.1.2).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
  let R := pResidual 2 (J ⧸ pCore 2 J)
  have hf : ((T : Subgroup G).subgroupOf Mc).map (residualPartnerAction Mc J hc) = φ.range := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
    · rintro ⟨x,rfl⟩
      exact ⟨⟨x,hTM x.property⟩,x.property,rfl⟩
  have hq : (S : Subgroup (J ⧸ pCore 2 J)) = qT.range := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
    · rintro ⟨x,rfl⟩
      exact ⟨⟨x,hJ.1.1.2 x.property⟩,x.property,rfl⟩
  have hk : φ.ker = qT.ker :=
    source_quintic_sylow_action_kernel hG T hempty hM hu hmany hcard e hab J hJ hs a f d π w hc
  have hsizes : Nat.card (((T : Subgroup G).subgroupOf Mc).map
      (residualPartnerAction Mc J hc)) = Nat.card S := by
    rw [hf,←index_ker,hk,index_ker,←hq]
  have hdis : Disjoint R (S : Subgroup (J ⧸ pCore 2 J)) :=
    IsPGroup.disjoint_of_coprime (IsElementaryAbelian.isPGroup 5 _) S.isPGroup' (by decide)
  have hnorm : (S : Subgroup (J ⧸ pCore 2 J)) ≤ normalizer (R : Set _) := by
    rw [normalizer_eq_top]; exact le_top
  have hjoin : R ⊔ (S : Subgroup (J ⧸ pCore 2 J)) = ⊤ := pResidual_sup_sylow_eq_top S
  have hprod := card_sup_eq_mul_of_normalizes_of_disjoint R (S : Subgroup (J ⧸ pCore 2 J)) hnorm hdis
  rw [hjoin,Nat.card_congr (topEquiv : (⊤ : Subgroup (J ⧸ pCore 2 J)) ≃* _).toEquiv] at hprod
  rw [source_quintic_residual_plane_card hG T hempty hM hu hmany hcard e hab J hJ hs a f d π w] at hprod
  rw [hsizes]
  exact hprod

/-- A genuine outer element in the preserving kernel forces the starred
group to have order greater than two hundred. In particular the index-two
permutation kernel cannot be replaced by the dihedral actor join. -/
theorem source_quintic_outer_quotient_card
    (hker : ChapterD.Jhat a.representation ≤ π.ker)
    (hp : ∀ g i, (f.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (f.ambientFactor d (π g i)).actor) :
    200 < Nat.card (J ⧸ pCore 2 J) := by
  obtain ⟨i,j,_,_,hjoin,hdis,hcom,_,_⟩ := f.two_factor_moved_decomposition d w.two_factors
  obtain ⟨em,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (f.ambientFactor d i).actor (f.ambientFactor d j).actor hdis
    (fun x hx y hy => (hcom x hx y hy).symm)
  have hsize : Nat.card (ChapterD.Jhat a.representation) = 100 := by
    rw [←hjoin,←Nat.card_congr em.toEquiv,Nat.card_prod,
      Nat.card_congr (w.dihedral i).some.toEquiv,
      Nat.card_congr (w.dihedral j).some.toEquiv,DihedralGroup.nat_card]
  have hlt : 100 < Nat.card π.ker := by
    by_contra! hh
    have he : ChapterD.Jhat a.representation = π.ker :=
      eq_of_le_of_card_ge hker (hsize.symm ▸ hh)
    exact w.outside_join (he ▸ w.fixes_factors)
  have hi := (source_quintic_preserving_preimage hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π hp w).1
  change (((π.ker.comap (QuotientGroup.mk' (pCore 2 J))).map J.subtype).comap J.subtype).index = 2 at hi
  rw [comap_map_eq_self_of_injective J.subtype_injective,
    index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)] at hi
  have htotal := π.ker.card_mul_index
  rw [hi] at htotal
  omega

/-- In the actual unresolved outer branch the intrinsic Sylow action has
order divisible by sixteen. The signed group of order eight used after
14.6.12 therefore cannot provide a no-index marking for this branch. -/
theorem source_quintic_outer_sylow_action_card
    (hker : ChapterD.Jhat a.representation ≤ π.ker)
    (hp : ∀ g i, (f.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (f.ambientFactor d (π g i)).actor)
    (hc : residualClosure J Mc = residual J) :
    16 ∣ Nat.card (((T : Subgroup G).subgroupOf Mc).map (residualPartnerAction Mc J hc)) := by
  have hlarge := source_quintic_outer_quotient_card hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π w hker hp
  rw [source_quintic_action_card_formula hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π w hc] at hlarge
  have hpg := T.isPGroup'.comap_subtype.map (residualPartnerAction Mc J hc)
  obtain ⟨n,hn⟩ := hpg.exists_card_eq
  change Nat.card (((T : Subgroup G).subgroupOf Mc).map (residualPartnerAction Mc J hc)) = 2 ^ n at hn
  have hfour : 4 ≤ n := by
    rw [hn] at hlarge
    by_contra! hh
    interval_cases n <;> norm_num at hlarge
  rw [hn]
  exact Nat.pow_dvd_pow 2 hfour

/-- An injective coordinate map cannot identify the original Sylow action
with the signed matrices in the outer branch. This rules out importing the
later index-bearing signed-action argument into the no-index reduction. -/
theorem source_quintic_outer_no_signed_coordinates
    (hker : ChapterD.Jhat a.representation ≤ π.ker)
    (hp : ∀ g i, (f.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (f.ambientFactor d (π g i)).actor)
    (hc : residualClosure J Mc = residual J)
    (c : MulAut (residual J ⧸ pCore 2 (residual J)) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod 5)) (hinj : Function.Injective c) :
    ((T : Subgroup G).subgroupOf Mc).map (c.comp (residualPartnerAction Mc J hc)) ≠
      Matrix.GeneralLinearGroup.SignedFive.signedSubgroup := by
  intro hm
  have hd := source_quintic_outer_sylow_action_card hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π w hker hp hc
  have hsize : Nat.card (((T : Subgroup G).subgroupOf Mc).map
      (residualPartnerAction Mc J hc)) = 8 := by
    have heq := congrArg (fun A : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod 5)) => Nat.card A) hm
    rw [←Subgroup.map_map,card_map_of_injective hinj] at heq
    rw [heq]
    change Nat.card (Matrix.GeneralLinearGroup.diagonalSwapSubgroup (ZMod 5) (-1)) = 8
    rw [Matrix.GeneralLinearGroup.diagonalSwapSubgroup_card]
    have ho : orderOf (-1 : (ZMod 5)ˣ) = 2 :=
      orderOf_eq_prime (p := 2) (by decide) (by decide)
    norm_num [ho]
  rw [hsize] at hd
  norm_num at hd

end Singleton.QuinticNoIndex
end CFSG.Quasithin.Chapter14.Section06
