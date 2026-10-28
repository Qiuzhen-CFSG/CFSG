module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceNaturalSevenReconstruction
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesPreparation
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.NaturalPermutation
public import Theory.Representation.BinaryPermutation.SevenAmbientAction
public import Theory.Representation.NormalElementaryQuotient.OriginalAction

/-!
# Reconstructing a source block from its original natural S₇ star row

The initial moved subgroup is retained literally. The component--Sylow join
normalizes KR and its characteristic omega-center, hence also the moved
subgroup. Its original natural action extends from the marked A₇ component
to the whole join; the original star S₇ image proves surjectivity. C.1.24
and the crossing Baumann argument then give a block without assuming shortness.

Source: Aschbacher--Smith C.1.24, C.2.7 and original4.3.7,
pp.130--131,145--147 and615--616.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open ChapterC ChapterC.C27Source ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem star_row_coordinates {H K R M : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple H R M K)
    [IsElementaryAbelian 2 (⁅starV K R,K.subgroupOf (K ⊔ R)⁆ : Subgroup (K ⊔ R : Subgroup G))]
    (hCO : starImage K R K ≤ offenderSubgroup (starRepresentation K R))
    (s : MovedSection ((starRepresentation K R).comp (offenderSubgroup (starRepresentation K R)).subtype)
      ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R))))
    (a : MarkedActionEquiv s.action (offenderSubgroup s.action)
      ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R)))
      (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7)))
    (hr : quadraticRatio s.action = 1)
    (hsplit : IsCompl s.space.toSubmodule (fixedSpace
      ((starRepresentation K R).comp (offenderSubgroup (starRepresentation K R)).subtype)
      ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R))))) :
    ∃ e : StarQuotient K R ≃* Equiv.Perm (Fin 7),
    ∃ E : Additive (⁅starV K R,K.subgroupOf (K ⊔ R)⁆ : Subgroup (K ⊔ R : Subgroup G)) ≃ₗ[ZMod 2]
        BinaryPermutation.natural (Fin 7),
      (∀ x : starImage K R K, e x =
        (a.subgroupEquiv ((subgroupOfEquivOfLe hCO).symm x)).val) ∧
      ∀ (g : (K ⊔ R : Subgroup G)) (u v : (⁅starV K R,K.subgroupOf (K ⊔ R)⁆ : Subgroup (K ⊔ R : Subgroup G))),
        (v : (K ⊔ R : Subgroup G)) = g * u * g⁻¹ →
        E (Additive.ofMul v) = BinaryPermutation.naturalRepresentation (Fin 7)
          (e (QuotientGroup.mk' (starKernel K R) g)) (E (Additive.ofMul u)) := by
  let J := K ⊔ R
  let O := offenderSubgroup (starRepresentation K R)
  let C := starImage K R K
  let B := K.subgroupOf J
  let W := ⁅starV K R,B⁆
  have hs : s.space.toSubmodule = NormalElementaryQuotient.commutatorSpace (starV K R) B := by
    rw [NormalElementaryQuotient.commutatorSpace_eq (starV K R)
      (QuotientGroup.mk' (starKernel K R)) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _),s.space_eq]
    change subspaceCommutator ((starRepresentation K R).comp O.subtype) ⊤ (C.subgroupOf O) = _
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hCO]
    rfl
  let m : Additive W ≃ₗ[ZMod 2] s.space.toSubmodule :=
    (NormalElementaryQuotient.commutatorSpaceEquiv (starV K R) B).trans
      (LinearEquiv.ofEq _ _ hs.symm)
  have hz : s.central.toSubmodule = ⊥ := by
    rw [s.central_eq]
    apply bot_unique
    intro v hv
    apply Subtype.ext
    exact (disjoint_iff.mp hsplit.disjoint).le
      ⟨v.property,fun g => congrArg Subtype.val (hv g)⟩
  let qE := s.central.toSubmodule.quotEquivOfEqBot hz
  let E := m.trans (qE.symm.trans a.action.linearEquiv)
  obtain ⟨e,he,ha⟩ := natural_permutation_star_coordinates h hCO s (Or.inr rfl) a hr
  have htop : O = ⊤ := natural_permutation_offender_eq_top h hCO s (Or.inr rfl) a hr
  refine ⟨e,E,he,?_⟩
  intro g u v hv
  let b : O := ⟨QuotientGroup.mk' (starKernel K R) g,htop ▸ mem_top _⟩
  have hm : s.space.toRepresentation b (m (Additive.ofMul u)) = m (Additive.ofMul v) := by
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    change (starRepresentation K R (QuotientGroup.mk' (starKernel K R) g)
      (Additive.ofMul ⟨u,(commutator_le_left (starV K R) B) u.property⟩)).toMul.val = v.val
    rw [starRepresentation_apply]
    exact hv.symm
  have hq : qE.symm (m (Additive.ofMul v)) =
      s.central.quotientRepresentation b (qE.symm (m (Additive.ofMul u))) := by
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    exact congrArg s.central.toSubmodule.mkQ hm.symm
  exact (congrArg a.action.linearEquiv hq).trans (ha b _)

/-- The marked whole star row, with its actual splitting and ratio, suffices
for block reconstruction on the original selected component. -/
theorem SourceConfiguration.block_of_natural_seven_star_row
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K)
    (hCO : starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≤
      offenderSubgroup (starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2)))
    (s : MovedSection
      ((starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2))).subtype)
      ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype)).subgroupOf
        (offenderSubgroup (starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2)))))
    (a : MarkedActionEquiv s.action (offenderSubgroup s.action)
      ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype)).subgroupOf
        (offenderSubgroup (starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2))))
      (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7)))
    (hr : quadraticRatio s.action = 1)
    (hsplit : IsCompl s.space.toSubmodule
      (fixedSpace
        ((starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2)).comp
          (offenderSubgroup (starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2))).subtype)
        ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype)).subgroupOf
          (offenderSubgroup (starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2)))))) :
    IsBlock c.K := by
  let K := c.K.map c.H.subtype
  let R := c.I.pCoreIn 2
  let S := (T : Subgroup G) ⊓ c.H
  let J := K ⊔ S
  let J₀ := K ⊔ R
  let O := offenderSubgroup (starRepresentation K R)
  let C := starImage K R K
  let B := K.subgroupOf J₀
  let W := ⁅starV K R,B⁆
  let A := W.map J₀.subtype
  have hRJ : R ≤ S := c.core_sylow.le.trans inf_le_left
  have hJ₀J : J₀ ≤ J := sup_le le_sup_left (hRJ.trans le_sup_right)
  have hAJ : A ≤ J := (map_subtype_le W).trans hJ₀J
  have hKnorm : J ≤ normalizer (K : Set G) :=
    (sup_le (map_subtype_le _) inf_le_right).trans c.normalizer_component.le
  have hRnorm : S ≤ normalizer (R : Set G) := by
    change S ≤ normalizer (c.I.pCoreIn 2 : Set G)
    rw [c.core_join]
    exact le_sup_right.trans ((c.I ⊔ S).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (c.I ⊔ S) (pCore 2 (c.I ⊔ S : Subgroup G))))
  have hnJ₀ : J ≤ normalizer (J₀ : Set G) := by
    apply sup_le (le_sup_left.trans J₀.le_normalizer)
    exact (le_inf ((le_sup_right : S ≤ J).trans hKnorm) hRnorm).trans
      (normalizer_inf_normalizer_le_normalizer_sup K R)
  have hnV : J ≤ normalizer ((starV K R).map J₀.subtype : Set G) :=
    hnJ₀.trans (normalizer_le_normalizer_characteristic_image J₀ (starV K R))
  have hAeq : A = ⁅(starV K R).map J₀.subtype,K⁆ := by
    change (⁅starV K R,B⁆ : Subgroup J₀).map J₀.subtype = _
    rw [map_commutator,map_subgroupOf_eq_of_le (show K ≤ J₀ from le_sup_left)]
  have hnA : J ≤ normalizer (A : Set G) := by
    rw [hAeq]
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hnV hg),
      mem_normalizer_iff_map_conj_eq.mp (hKnorm hg)]
  let U := A.subgroupOf J
  let : U.Normal := normal_subgroupOf_of_le_normalizer hnA
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left (starV K R) B)
  let jU : U ≃* W := (subgroupOfEquivOfLe hAJ).trans
    (W.equivMapOfInjective J₀.subtype J₀.subtype_injective).symm
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective jU.toMonoidHom jU.injective
  have hjU (u : U) : (((jU u : W) : J₀) : G) = ((u : J) : G) :=
    congrArg Subtype.val ((W.equivMapOfInjective J₀.subtype J₀.subtype_injective).apply_symm_apply
      (subgroupOfEquivOfLe hAJ u))
  obtain ⟨e,E₀,he,hE₀raw⟩ := star_row_coordinates (c.block_source_input hf) hCO s a hr hsplit
  let E : Additive U ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 7) :=
    (jU.toAdditive.toLinearEquiv (ZMod.map_smul _)).trans E₀
  let q₀ := e.toMonoidHom.comp (QuotientGroup.mk' (starKernel K R))
  have hq₀ : Function.Surjective q₀ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let α := NormalElementaryQuotient.originalAction U
  have hE₀ (g : J₀) (u : Additive U) :
      E (α (inclusion hJ₀J g) u) =
        BinaryPermutation.naturalRepresentation (Fin 7) (q₀ g) (E u) := by
    apply hE₀raw g (jU u.toMul) (jU (α (inclusion hJ₀J g) u).toMul)
    apply Subtype.ext
    change (((jU (α (inclusion hJ₀J g) u).toMul : W) : J₀) : G) =
      (g : G) * (((jU u.toMul : W) : J₀) : G) * (g : G)⁻¹
    rw [hjU,hjU]
    exact congrArg Subtype.val
      (NormalElementaryQuotient.originalAction_apply U (inclusion hJ₀J g) u)
  let KJ := K.subgroupOf J
  let : KJ.Normal := normal_subgroupOf_of_le_normalizer hKnorm
  let ek : KJ ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let eC : C ≃* alternatingGroup (Fin 7) := (subgroupOfEquivOfLe hCO).symm.trans a.subgroupEquiv
  let kmark : KJ →* alternatingGroup (Fin 7) :=
    eC.toMonoidHom.comp ((toStarImage K R).comp ek.toMonoidHom)
  have hkmark : Function.Surjective kmark :=
    eC.surjective.comp ((toStarImage_surjective K R).comp ek.surjective)
  let EC := E.trans (BinaryPermutation.coreEquivNatural (Fin 7) (by decide)).symm
  have hEC (k : KJ) (u : Additive U) :
      EC (α k u) = BinaryPermutation.alternatingCoreRepresentation (Fin 7) (kmark k) (EC u) := by
    apply (BinaryPermutation.coreEquivNatural (Fin 7) (by decide)).injective
    change BinaryPermutation.coreEquivNatural (Fin 7) (by decide)
      ((BinaryPermutation.coreEquivNatural (Fin 7) (by decide)).symm (E (α k u))) =
      BinaryPermutation.coreEquivNatural (Fin 7) (by decide)
        (BinaryPermutation.coreRepresentation (Fin 7) (kmark k).val
          ((BinaryPermutation.coreEquivNatural (Fin 7) (by decide)).symm (E u)))
    rw [LinearEquiv.apply_symm_apply,BinaryPermutation.coreEquivNatural_equivariant,
      LinearEquiv.apply_symm_apply]
    have hh := hE₀ (inclusion (show K ≤ J₀ from le_sup_left) (ek k)) u
    change E (α k u) = BinaryPermutation.naturalRepresentation (Fin 7)
      (e (toStarImage K R (ek k))) (E u) at hh
    rw [he] at hh
    exact hh
  obtain ⟨q,hqK,hqE,hker⟩ := BinaryPermutation.SevenAmbientAction.exists_ambient_hom
    α KJ kmark hkmark EC hEC
  have hqE' (g : J) (u : Additive U) : E (α g u) =
      BinaryPermutation.naturalRepresentation (Fin 7) (q g) (E u) := by
    have hh := congrArg (BinaryPermutation.coreEquivNatural (Fin 7) (by decide)) (hqE g u)
    simpa only [EC,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,
      BinaryPermutation.coreEquivNatural_equivariant] using hh
  have hqq (g : J₀) : q (inclusion hJ₀J g) = q₀ g := by
    apply BinaryPermutation.naturalRepresentation_injective (Fin 7) (by decide)
    apply LinearMap.ext
    intro v
    obtain ⟨u,rfl⟩ := E.surjective v
    exact (hqE' _ u).symm.trans (hE₀ g u)
  have hq : Function.Surjective q := by
    intro g
    obtain ⟨j,rfl⟩ := hq₀ g
    exact ⟨inclusion hJ₀J j,hqq j⟩
  have hk : q.ker = centralizer (U : Set J) := hker.trans
    (NormalElementaryQuotient.originalAction_kernel U)
  have hKq : KJ.map q = alternatingGroup (Fin 7) := by
    apply le_antisymm
    · rintro _ ⟨k,hk,rfl⟩
      rw [hqK ⟨k,hk⟩]
      exact (kmark ⟨k,hk⟩).property
    · intro g hg
      obtain ⟨k,hk⟩ := hkmark ⟨g,hg⟩
      exact ⟨k,k.property,(hqK k).trans (congrArg Subtype.val hk)⟩
  have hact (g : Equiv.Perm (Fin 7)) (u : Additive U) :
      E (NormalElementaryQuotient.representation U q hq hk g u) =
        BinaryPermutation.naturalRepresentation (Fin 7) g (E u) := by
    obtain ⟨j,rfl⟩ := hq g
    have heq : NormalElementaryQuotient.representation U q hq hk (q j) u = α j u := by
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [NormalElementaryQuotient.representation_apply,NormalElementaryQuotient.originalAction_apply]
    rw [heq]
    exact hqE' j u
  have hm : ⁅U,KJ⁆ ≠ ⊥ := by
    intro hz
    have hle : KJ ≤ centralizer (U : Set J) := by
      rw [commutator_comm] at hz
      exact commutator_eq_bot_iff_le_centralizer.mp hz
    have hb : KJ.map q = ⊥ := by
      apply bot_unique
      rintro _ ⟨k,hkk,rfl⟩
      have hmem : k ∈ q.ker := by rw [hk]; exact hle hkk
      exact mem_bot.mpr hmem
    have heq : alternatingGroup (Fin 7) = ⊥ := hKq.symm.trans hb
    have hc := congrArg (fun X : Subgroup (Equiv.Perm (Fin 7)) => Nat.card X) heq
    rw [nat_card_alternatingGroup] at hc
    norm_num at hc
  exact c.block_of_natural_seven_join_action hf U q hq hk hKq E hact hm

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
