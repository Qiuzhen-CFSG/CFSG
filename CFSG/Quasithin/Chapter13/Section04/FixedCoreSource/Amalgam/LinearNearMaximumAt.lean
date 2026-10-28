module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearNearMaximum
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearWholeModuleAt

/-!
# Guarded near-maximum replacement in the linear amalgam

The whole six-dimensional action is non-FF under the same component
marking. A near-maximum actor moving the second residual then gives a
maximum centralizing replacement through the actual full two-core.
Source: Aschbacher--Smith 13.4.7(2), printed p.902.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open BinaryLinearThree.FanoDecomposition Representation.BinaryOffender NoncentralChiefRefinement
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- The whole original faithful quotient action is non-FF. -/
theorem original_pair_linear_action_nonFF_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL) :
    let X := A ⊔ B
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
    let E := U.subgroupOf X
    ∃ hN : E.Normal, ∃ he : IsElementaryAbelian 2 E,
      let := hN
      let := he
      let N := centralizer (E : Set X)
      ¬ IsFFModule (Representation.NormalElementaryQuotient.representation E
        (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) (QuotientGroup.ker_mk' N)) := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z X
  let E := U.subgroupOf X
  have hTX : (T : Subgroup G) ≤ X := hTA.trans le_sup_left
  have hUX : U ≤ X := conjugateSpanBy_le (fun z hz =>
    hTX ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) X.le_normalizer
  have hred := (original_pair_action_kernel h₀ D m hTA hTB eA eB hne hindexA hindexB).1
  let : E.Normal := hred.normal
  let : IsElementaryAbelian 2 E := hred.elementary
  obtain ⟨heU,e,hA,hB,hS,hm,_⟩ := original_pair_linear_whole_module_at h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK
  let := heU
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  let j : K ≃* C := K.equivMapOfInjective X.subtype X.subtype_injective
  let fK := f.comp j.toMonoidHom
  have hfK : Function.Surjective fK := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp j.surjective)
  have hns : ¬ Group.IsSolvable X := by
    intro hh
    let := hh
    exact hK.not_isSolvable inferInstance
  have hfull := original_pair_full_action_kernel h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB hres hns
  have hcent : centralizer (E : Set X) = pCore 2 X := by
    apply map_injective X.subtype_injective
    have hh := map_inf_centralizer_of_injective X.subtype X.subtype_injective
      (⊤ : Subgroup X) E
    have heq : (centralizer (E : Set X)).map X.subtype = X ⊓ centralizer (U : Set G) := by
      simpa only [top_inf_eq,←MonoidHom.range_eq_map,range_subtype,
        E,map_subgroupOf_eq_of_le hUX] using hh.symm
    exact heq.trans hfull
  have hgen : K ⊔ centralizer (E : Set X) = ⊤ := by
    rw [hcent]
    apply map_injective X.subtype_injective
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype]
    exact (original_pair_linear_core_supplement h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK eK).2
  have hk : fK.ker = (centralizer (E : Set X)).subgroupOf K := by
    have hqker := (original_pair_component_twoCore_image h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK).1
    have hp : (pCore 2 X).subgroupOf K = pCore 2 K := by
      have hh : ((QuotientGroup.mk' (pCore 2 X)).subgroupMap K).ker =
          (pCore 2 X).subgroupOf K := by
        ext k
        change ((QuotientGroup.mk' (pCore 2 X)).subgroupMap K) k = 1 ↔ k.val ∈ pCore 2 X
        rw [Subtype.ext_iff]
        exact QuotientGroup.eq_one_iff k.val
      exact hh.symm.trans hqker
    rw [hcent,hp]
    change (f.comp j.toMonoidHom).ker = _
    rw [←MonoidHom.comap_ker,MonoidHom.ker_comp_of_injective _ _ e.injective,
      QuotientGroup.ker_mk',←pCore_map_iso 2 j,comap_map_eq_self_of_injective j.injective]
  let N := centralizer (E : Set X)
  let τ := Representation.NormalElementaryQuotient.representation E (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) (QuotientGroup.ker_mk' N)
  refine ⟨inferInstance,inferInstance,?_⟩
  have step {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
      (σ : Representation (ZMod 2) BinaryLinearThree.Group M)
      (eU : Representation.Equiv (σ.comp f)
        (Representation.elementaryRepresentation (p := 2)
          (U.normalizerMonoidHom.comp (inclusion
            ((map_subtype_le K).trans (le_normalizer_conjugateSpanBy Z X))))))
      (hn : ¬ IsFFModule σ) : ¬ IsFFModule τ := by
    let a : Additive U ≃ₗ[ZMod 2] Additive E :=
      LinearEquiv.ofBijective
        ((subgroupOfEquivOfLe hUX).symm.toMonoidHom.toAdditive.toZModLinearMap 2)
        (subgroupOfEquivOfLe hUX).symm.bijective
    apply Representation.NormalElementaryQuotient.nonFF_of_component_model
      E K hgen fK hfK hk σ
      (eU.toLinearEquiv.trans a) _ hn
    intro k v
    have he := LinearMap.congr_fun (eU.isIntertwining' (j k)) v
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : Additive U => w.toMul.val) he
  rcases hm with hm | hm | hm
  · obtain ⟨em⟩ := hm
    exact step _ em BinaryLinearThree.FanoNonFF.sum_not_ff
  · obtain ⟨em⟩ := hm
    exact step _ em BinaryLinearThree.FanoNonFF.point_not_ff
  · obtain ⟨em⟩ := hm
    exact step _ em BinaryLinearThree.FanoNonFF.line_not_ff

private theorem near_maximum_replacement_of_nonFF
    {H Q : Type*} [Group H] [Finite H] [Group Q]
    (S U E : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (hUS : U ≤ S) (hE : E ∈ ChapterB.thompsonFamily S 1)
    (q : H →* Q) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set H)) (hne : E.map q ≠ ⊥)
    (hn : ¬ IsFFModule (Representation.NormalElementaryQuotient.representation U q hq hk)) :
    U ⊔ (E ⊓ centralizer (U : Set H)) ∈ elementaryAbelianMaxSubgroups S := by
  let := hE.2.1
  let τ := Representation.NormalElementaryQuotient.representation U q hq hk
  have hb := ChapterB.near_maximum_action_codimension S U hUS q hq hk hE hne
  change ¬ IsFFModule τ at hn
  change fixedCodim τ (E.map q) ≤ rank (E.map q) + 1 at hb
  have hl : rank (E.map q) < fixedCodim τ (E.map q) := by
    by_contra hh
    exact hn ⟨E.map q,⟨hne,IsElementaryAbelian.map q⟩,by omega⟩
  have hc := fixedCodim_map_equivariant (normalRepresentation U) τ q
    (LinearEquiv.refl (ZMod 2) (Additive U))
    (by
      intro g v
      apply Additive.toMul.injective
      apply Subtype.ext
      exact (Representation.NormalElementaryQuotient.representation_apply U q hq hk g v).symm) E
  rw [normalRepresentation_fixedCodim_eq_rank_difference] at hc
  have hr := (ChapterB.mem_thompsonFamily_iff_rank S E 1).mp hE |>.2.2
  apply ChapterB.lemma_B_2_4_2 S U E hUS hE.1 1 (by
    change Nat.log 2 (Nat.card E) = ChapterB.twoRank S - 1
    omega) q hk hne
  change Nat.log 2 (Nat.card (E.map q)) < _ at hl
  change _ ≤ Nat.log 2 (Nat.card (E.map q)) + 1 at hb
  omega

/-- Every near-maximum actor escaping the actual action kernel has a maximum
elementary replacement in the original Sylow subgroup. -/
theorem original_pair_linear_near_maximum_replacement_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL)
    (E : Subgroup G) (hE : E ∈ ChapterB.thompsonFamily (T : Subgroup G) 1)
    (hneE : ¬ E ≤ centralizer
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) : Set G)) :
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)
    ⁅K.map (A ⊔ B).subtype,E⁆ = K.map (A ⊔ B).subtype ∧
      U ⊔ (E ⊓ centralizer (U : Set G)) ∈ elementaryAbelianMaxSubgroups (T : Subgroup G) := by
  let X := A ⊔ B
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
  let W := U.subgroupOf X
  have hTX : (T : Subgroup G) ≤ X := hTA.trans le_sup_left
  have hEX : E ≤ X := hE.1.trans hTX
  have hUX : U ≤ X := conjugateSpanBy_le (fun z hz =>
    hTX ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) X.le_normalizer
  let S := T.subtype hTX
  let Ei := E.subgroupOf X
  obtain ⟨hN,he,hn⟩ := original_pair_linear_action_nonFF_at h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK
  let := hN
  let := he
  let N := centralizer (W : Set X)
  let q := QuotientGroup.mk' N
  have hmS : (S : Subgroup X).map X.subtype = (T : Subgroup G) := by
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTX]
  have hmE : Ei.map X.subtype = E := map_subgroupOf_eq_of_le hEX
  have hEi : Ei ∈ ChapterB.thompsonFamily (S : Subgroup X) 1 := by
    apply (ChapterB.thompsonFamily_map_iff_of_injective X.subtype X.subtype_injective
      (S : Subgroup X) Ei 1).mp
    rwa [hmS,hmE]
  have hneI : Ei.map q ≠ ⊥ := by
    intro hz
    have hc : Ei ≤ N := by simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff Ei).mp hz
    apply hneE
    intro e he u hu
    exact congrArg Subtype.val (hc (show (⟨e,hEX he⟩ : X) ∈ Ei from he)
      ⟨u,hUX hu⟩ hu)
  have hWS : W ≤ (S : Subgroup X) :=
    (IsElementaryAbelian.isPGroup 2 W).le_sylow_of_normal S
  have hm := near_maximum_replacement_of_nonFF (S : Subgroup X) W Ei hWS hEi q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hneI hn
  have hmapped := (maxFamily_map_injective_iff X.subtype
    X.subtype_injective (S : Subgroup X) (W ⊔ (Ei ⊓ N))).mpr hm
  rw [hmS,Subgroup.map_sup,map_subgroupOf_eq_of_le hUX] at hmapped
  have hc := map_inf_centralizer_of_injective X.subtype X.subtype_injective Ei W
  rw [hmE,map_subgroupOf_eq_of_le hUX] at hc
  rw [←hc] at hmapped
  refine ⟨?_,hmapped⟩
  let q₂ := QuotientGroup.mk' (pCore 2 X)
  have hns : ¬ Group.IsSolvable X := by
    intro hh
    let := hh
    exact hK.not_isSolvable inferInstance
  have hfull := original_pair_full_action_kernel h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB hres hns
  have hnot : ¬ Ei ≤ pCore 2 X := by
    intro hh
    apply hneE
    intro e he
    have heQ : e ∈ X.pCoreIn 2 := mem_map_of_mem X.subtype
      (hh (show (⟨e,hEX he⟩ : X) ∈ Ei from he))
    exact (hfull.symm ▸ heQ).2
  obtain ⟨eqX⟩ := original_pair_linear_full_quotient h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK eK
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.Comparisons.Exceptional.psl3Two_simple
  let : IsSimpleGroup (X ⧸ pCore 2 X) := eqX.isSimpleGroup
  have hcenter : center (X ⧸ pCore 2 X) = ⊥ := by
    apply bot_unique
    intro x hx
    have hh := (centerCongr eqX) ⟨x,hx⟩ |>.property
    exact mem_bot.mpr (eqX.map_eq_one_iff.mp
      (mem_bot.mp (Matrix.PSL3Two.Automorphisms.center_psl_eq_bot.le hh)))
  have hnon : ⁅(⊤ : Subgroup (X ⧸ pCore 2 X)),Ei.map q₂⁆ ≠ ⊥ := by
    intro hh
    rw [commutator_comm] at hh
    have hc : Ei.map q₂ ≤ center (X ⧸ pCore 2 X) := by
      simpa only [coe_top,centralizer_univ] using commutator_eq_bot_iff_le_centralizer.mp hh
    rw [hcenter] at hc
    exact hnot (by simpa only [q₂,QuotientGroup.ker_mk'] using (map_eq_bot_iff Ei).mp (le_bot_iff.mp hc))
  let : (⁅(⊤ : Subgroup (X ⧸ pCore 2 X)),Ei.map q₂⁆).Normal :=
    normalizer_eq_top_iff.mp (top_unique (normalizer_commutator_ge_left ⊤ (Ei.map q₂)))
  have ht : ⁅(⊤ : Subgroup (X ⧸ pCore 2 X)),Ei.map q₂⁆ = ⊤ :=
    (inferInstance : (⁅(⊤ : Subgroup (X ⧸ pCore 2 X)),Ei.map q₂⁆).Normal).eq_bot_or_eq_top.resolve_left hnon
  have hr := (original_pair_component_is_residual h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK).1
  have hk := (original_pair_linear_core_supplement h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK eK).1
  have hh := pResidual_eq_commutator_of_quotient (p := 2) Ei (by
    rw [hr,hk]
    exact ht.symm)
  rw [hr] at hh
  have hm := congrArg (Subgroup.map X.subtype) hh.symm
  rwa [map_commutator,hmE] at hm

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
