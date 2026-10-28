module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.PointFamily
public import Theory.Representation.BinaryOffender.CubicConjugateBound
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.EasyCases

/-!
# B.2.19 for the actual S6 point-radical family

The two full plane preimages supply all four structural hypotheses of the
Baumann argument. Every maximum elementary image is covered by equal-weight
subgroups lying in even conjugates of the first plane. Transporting that
cover through the literal action quotient proves B.2.19 on the original
group. In particular the kernel of the original Baumann action is Sylow in
the kernel of the component--Baumann product, the step needed for C.1.37's
MS reduction. No MS recognition conclusion is assumed here.

Source: Aschbacher--Smith B.2.19, printed pp.81--82, and C.1.37, p.143.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.NaturalSixControl
open Subgroup Stellmacher
open scoped IsMulCommutative
open ChapterB ChapterB.BaumannArgument
open Representation.BinaryOffender
open ChapterB.Offenders.Six
variable {K : Type*} [Group K] {V : Subgroup K} [V.Normal] [IsElementaryAbelian 2 V]
private theorem alternating_codim : fixedCodim Model.rho (alternatingGroup (Fin 6)) = 4 := by
  have hz := fixedSpace_eq_bot_of_faithful_irreducible_on
    Model.rho (alternatingGroup (Fin 6))
    (BinaryPermutation.naturalRepresentation_injective _ (by decide))
    (BinaryPermutation.alternatingNatural_isIrreducible (by decide))
  have hd := fixedCodim_add_finrank Model.rho (alternatingGroup (Fin 6))
  rw [hz,finrank_bot,BinaryPermutation.finrank_natural_even (Fin 6) (by decide)] at hd
  simpa using hd


namespace NaturalAction
variable (d : NaturalAction V) [Finite K]

omit [Finite K] in
private theorem map_conjugate {H : Type*} [Group H] (q : K →* H)
    (A : Subgroup K) (g : K) :
    (A.map (MulAut.conj g).toMonoidHom).map q =
      (A.map q).map (MulAut.conj (q g)).toMonoidHom := by
  rw [map_map,map_map]
  congr 1
  ext x
  simp

private theorem thompson_self (S : Subgroup K) :
    elementaryAbelianMaxJ (elementaryAbelianMaxJ S) = elementaryAbelianMaxJ S := by
  have hle : elementaryAbelianMaxJ S ≤ S := sSup_le fun _ hA => hA.1
  have h := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le S
    (elementaryAbelianMaxJ S) le_rfl
  have he : elementaryAbelianMaxOrder S = elementaryAbelianMaxOrder (elementaryAbelianMaxJ S) :=
    le_antisymm h.1 (elementaryAbelianMaxOrder_le_and_j_le_of_eq _ _ hle).1
  exact le_antisymm (sSup_le fun _ hA => hA.1) (h.2 he)

omit [IsElementaryAbelian 2 V] in
private theorem structural :
    (pCore 2 (pResidual 2 K)).map (pResidual 2 K).subtype ≤
      d.R ⊓ centralizer (V : Set K) ∧
    pResidual 2 K ≤ normalizer (d.R ⊓ centralizer (V : Set K) : Set K) ∧
    pResidual 2 K ⊓ centralizer (V : Set K) ≤ coreFrattini (pResidual 2 K) := by
  have hcore : pCore 2 (pResidual 2 K) = (pCore 2 K).comap (pResidual 2 K).subtype :=
    pCore_subnormal_eq_comap 2 (inferInstance : (pResidual 2 K).Normal).isSubnormal
  have he : d.R ⊓ centralizer (V : Set K) = pCore 2 K := by
    rw [← d.kernel_centralizer, inf_eq_right.mpr d.kernel_le_R, d.kernel]
  refine ⟨?_, ?_, ?_⟩
  · rw [he,hcore,map_comap_eq,range_subtype]
    exact inf_le_right
  · change pResidual 2 K ≤ normalizer ((d.R ⊓ centralizer (V : Set K) : Subgroup K) : Set K)
    rw [he,normalizer_eq_top]
    exact le_top
  · rintro x ⟨hxL,hxC⟩
    refine ⟨⟨x,hxL⟩,?_,rfl⟩
    have hx : (⟨x,hxL⟩ : pResidual 2 K) ∈ pCore 2 (pResidual 2 K) := by
      rw [hcore, ← d.kernel]
      exact d.kernel_centralizer.symm ▸ hxC
    change QuotientGroup.mk' (pCore 2 (pResidual 2 K)) _ ∈ frattini _
    have hx1 : QuotientGroup.mk' (pCore 2 (pResidual 2 K)) (⟨x,hxL⟩ : pResidual 2 K) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hx
    rw [hx1]
    exact one_mem _

theorem family_AD (hne : ¬ (elementaryAbelianMaxJ d.R).map d.q ≤ last) :
    HypothesesAD V d.R (fun i : Fin 2 => elementaryAbelianMaxJ (d.D i)) := by
  obtain ⟨hcore,hnorm,hfrat⟩ := d.structural
  refine ⟨d.R_two,d.module_le_R,hcore,hnorm,hfrat,d.noStrongOffenders,
    ?_,(fun i => thompson_self (d.D i)),?_,?_,?_⟩
  · intro i
    obtain ⟨l,hl,hD⟩ := d.D_conjugate i
    refine ⟨l⁻¹,inv_mem hl,?_⟩
    apply (map_mono (show elementaryAbelianMaxJ (d.D i) ≤ d.D i from
      sSup_le fun _ hA => hA.1)).trans
    rw [← hD]
    have hc : (MulAut.conj l⁻¹).toMonoidHom.comp (MulAut.conj l).toMonoidHom =
        MonoidHom.id K := by ext x; simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.id_apply]; group
    rw [map_map,hc,map_id]
    exact d.D_zero_le_R
  · intro i
    exact (twoRank_eq_of_intermediate (d.D i) _ le_rfl
      (sSup_le fun _ hA => hA.1)).trans (d.D_rank i)
  · apply (map_le_map_iff_of_injective (f := d.actionEquiv.toMonoidHom)
      d.actionEquiv.injective).mp
    rw [Subgroup.map_iSup]
    simp_rw [d.image_eq, d.thompson_D_image hne]
    rw [Model.root_generation]
    exact le_top
  · have hc (i : Fin 2) : ChapterB.BaumannArgument.fixedCodim V
        (elementaryAbelianMaxJ (d.D i)) = 2 := by
      rw [d.fixedCodim_eq_model,d.thompson_D_image hne,Model.root_codim]
    have hr : ChapterB.BaumannArgument.fixedCodim V (pResidual 2 K) = 4 := by
      rw [d.fixedCodim_eq_model,d.residual_image,alternating_codim]
    simp_rw [hc]
    rw [hr]
    decide



omit [Finite K] in
theorem action_representation :
    Representation.NormalElementaryQuotient.representation V (actionMap V)
      (QuotientGroup.mk'_surjective _) (actionMap_ker V) =
      d.ρ.comp d.actionEquiv.toMonoidHom := by
  apply MonoidHom.ext
  intro h
  apply LinearMap.ext
  intro v
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (centralizer (V : Set K)) h
  apply Additive.toMul.injective
  apply Subtype.ext
  change ((Representation.NormalElementaryQuotient.representation V (actionMap V)
    (QuotientGroup.mk'_surjective _) (actionMap_ker V) (actionMap V g) v).toMul : K) =
    ((d.ρ (d.q g) v).toMul : K)
  exact (Representation.NormalElementaryQuotient.representation_apply V (actionMap V)
    (QuotientGroup.mk'_surjective _) (actionMap_ker V) g v).trans
    (Representation.NormalElementaryQuotient.representation_apply
      V d.q d.onto d.kernel_centralizer g v).symm

omit [Finite K] in
theorem action_weight (E : Subgroup (K ⧸ centralizer (V : Set K))) :
    Representation.BinaryOffender.weight
      (Representation.NormalElementaryQuotient.representation V (actionMap V)
        (QuotientGroup.mk'_surjective _) (actionMap_ker V)) E =
      Representation.BinaryOffender.weight d.ρ (E.map d.actionEquiv.toMonoidHom) := by
  rw [d.action_representation]
  exact Representation.BinaryOffender.weight_comp_map d.ρ d.actionEquiv.toMonoidHom
    d.actionEquiv.injective E

theorem equal_weight_cover (A : Subgroup K)
    (hA : A ∈ elementaryAbelianMaxSubgroups d.R) (hne : A.map (actionMap V) ≠ ⊥) :
    ∃ E : Set (Subgroup (K ⧸ centralizer (V : Set K))),
      sSup E = A.map (actionMap V) ∧
      ∀ B ∈ E, IsElementaryTwo B ∧
        EqualWeightLE
          (Representation.NormalElementaryQuotient.representation V (actionMap V)
            (QuotientGroup.mk'_surjective _) (actionMap_ker V)) B (A.map (actionMap V)) ∧
        ∃ i : Fin 2, ∃ g ∈ pResidual 2 K,
          B ≤ ((d.D i).map (MulAut.conj g).toMonoidHom).map (actionMap V) := by
  have ha : A.map d.q ≤ Model.E := map_le_iff_le_comap.mpr hA.1
  have han : A.map d.q ≠ ⊥ := by
    rw [← d.image_eq]
    exact (map_eq_bot_iff_of_injective _ d.actionEquiv.injective).not.mpr hne
  have hb : IsBestOffender Model.rho (A.map d.q) := (d.bestOffender_iff _).mp
    (Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
      V d.q d.onto d.kernel_centralizer d.R A d.module_le_R hA han)
  obtain ⟨F,hF,hparts⟩ := Model.equal_weight_cover ha hb
  let E : Set (Subgroup (K ⧸ centralizer (V : Set K))) :=
    (fun C : Subgroup Model.S => C.map d.actionEquiv.symm.toMonoidHom) '' F
  have he (C : Subgroup Model.S) :
      (C.map d.actionEquiv.symm.toMonoidHom).map d.actionEquiv.toMonoidHom = C := by
    rw [map_map]
    have hh : d.actionEquiv.toMonoidHom.comp d.actionEquiv.symm.toMonoidHom =
        MonoidHom.id Model.S := MonoidHom.ext (fun x => d.actionEquiv.apply_symm_apply x)
    rw [hh,map_id]
  refine ⟨E,?_,?_⟩
  · apply (map_injective (f := d.actionEquiv.toMonoidHom) d.actionEquiv.injective)
    rw [d.image_eq,← hF]
    apply le_antisymm
    · apply map_le_iff_le_comap.mpr
      apply sSup_le
      rintro _ ⟨C,hC,rfl⟩
      apply map_le_iff_le_comap.mp
      rw [he]
      exact le_sSup hC
    · apply sSup_le
      intro C hC
      rw [← he C]
      exact map_mono (le_sSup (show C.map d.actionEquiv.symm.toMonoidHom ∈ E from ⟨C,hC,rfl⟩))
  · rintro B ⟨C,hC,rfl⟩
    obtain ⟨hc,hw,g,hg,hcg⟩ := hparts C hC
    have hBA : C.map d.actionEquiv.symm.toMonoidHom ≤ A.map (actionMap V) := by
      apply (map_le_map_iff_of_injective (f := d.actionEquiv.toMonoidHom) d.actionEquiv.injective).mp
      rw [he,d.image_eq]
      exact hw.1
    have hBe : IsElementaryTwo (C.map d.actionEquiv.symm.toMonoidHom) := by
      let := hc.2
      exact ⟨(map_eq_bot_iff_of_injective C d.actionEquiv.symm.injective).not.mpr hc.1,
        IsElementaryAbelian.map _⟩
    refine ⟨hBe,⟨hBA,?_⟩,?_⟩
    · rw [d.action_weight,d.action_weight,he,d.image_eq]
      simpa only [weight,d.fixed_finrank] using hw.2
    · obtain ⟨l,hl,hq⟩ := d.residual_lift ⟨g,hg⟩
      refine ⟨0,l,hl,?_⟩
      apply (map_le_map_iff_of_injective (f := d.actionEquiv.toMonoidHom) d.actionEquiv.injective).mp
      rw [he,d.image_eq,map_conjugate,d.D_image,hq]
      exact hcg

theorem baumann_conclusions
    (hne : ¬ (elementaryAbelianMaxJ d.R).map d.q ≤ last) :
    (pCore 2 (pResidual 2 K)).map (pResidual 2 K).subtype ≤ baumann d.R ∧
      thompsonAlpha d.R = (thompsonAlpha d.R ⊓ centralizer (pResidual 2 K : Set K)) ⊔
        (V ⊓ centralizer (elementaryAbelianMaxJ d.R : Set K)) ∧
      IsSylowSubgroupIn (baumann d.R ⊓ centralizer (V : Set K))
        ((pResidual 2 K ⊔ baumann d.R) ⊓ centralizer (V : Set K)) ∧
      (IsSylowSubgroupIn ((baumann d.R).map (actionMap V))
          ((pResidual 2 K).map (actionMap V) ⊔ (baumann d.R).map (actionMap V)) →
        IsSylowSubgroupIn (baumann d.R) (pResidual 2 K ⊔ baumann d.R)) := by
  apply baumann_of_preimage_cover V d.R d.D (d.family_AD hne) ?_ d.D_rank
    (fun A hA hn => d.equal_weight_cover A hA hn) ?_
  · intro i
    apply comap_map_eq_self
    rw [actionMap_ker,← d.kernel_centralizer]
    exact d.D_kernel i
  · have hR : d.R ⊓ centralizer (V : Set K) = d.q.ker := by
      rw [← d.kernel_centralizer,inf_eq_right.mpr d.kernel_le_R]
    have hL : (pResidual 2 K ⊔ d.R) ⊓ centralizer (V : Set K) = d.q.ker := by
      rw [← d.kernel_centralizer,inf_eq_right.mpr (d.kernel_le_R.trans le_sup_right)]
    rw [hR,hL]
    have hp : IsPGroup 2 d.q.ker := d.kernel.symm ▸ pCore_isPGroup
    let S : Sylow 2 d.q.ker := Sylow.nonempty.some
    have hS : (S : Subgroup d.q.ker) = ⊤ := (S.is_maximal' (hp.to_subgroup ⊤) le_top).symm
    refine ⟨S,?_⟩
    rw [hS,← MonoidHom.range_eq_map,range_subtype]

end NaturalAction

namespace SourceData
variable {L : Subgroup K} [L.Normal] {T : Sylow 2 K} (d : SourceData L V T) [Finite K]
include d

omit [IsElementaryAbelian 2 V] in
/-- The actual perfect component is the two-residual of its Sylow product. -/
theorem component_eq_residual : pResidual 2 K = L := by
  let : Group.IsPerfect L := d.component.perfect
  have hp : IsPPerfect 2 L := by
    intro N hn hq
    let : N.Normal := hn
    by_contra hne
    let : Nontrivial (L ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (L ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (L ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (L ⧸ N) inferInstance
  exact pResidual_eq_of_subnormal_product L (T : Subgroup K) d.component.subnormal
    hp T.isPGroup' d.product

/-- The original component core lies in the original point Baumann subgroup. -/
theorem component_core_le_baumann
    (hne : ¬ (elementaryAbelianMaxJ d.R).map d.q0 ≤ last) : L.pCoreIn 2 ≤ d.B := by
  have hr : d.canonicalAction.R = d.R := d.R_eq_comap.symm
  have hn : ¬ (elementaryAbelianMaxJ d.canonicalAction.R).map d.canonicalAction.q ≤ last := by
    change ¬ (elementaryAbelianMaxJ d.canonicalAction.R).map d.q0 ≤ last
    rw [hr]
    exact hne
  have h := (d.canonicalAction.baumann_conclusions hn).1
  change (pResidual 2 K).pCoreIn 2 ≤ baumann d.canonicalAction.R at h
  rw [hr,d.component_eq_residual] at h
  exact h

/-- The literal kernel-Sylow conclusion used by the original MS-pair step. -/
theorem baumann_kernel_sylow
    (hne : ¬ (elementaryAbelianMaxJ d.R).map d.q0 ≤ last) :
    IsSylowSubgroupIn (d.B ⊓ centralizer (V : Set K))
      ((L ⊔ d.B) ⊓ centralizer (V : Set K)) := by
  have hr : d.canonicalAction.R = d.R := d.R_eq_comap.symm
  have hn : ¬ (elementaryAbelianMaxJ d.canonicalAction.R).map d.canonicalAction.q ≤ last := by
    change ¬ (elementaryAbelianMaxJ d.canonicalAction.R).map d.q0 ≤ last
    rw [hr]
    exact hne
  have h := (d.canonicalAction.baumann_conclusions hn).2.2.1
  simpa only [hr,d.component_eq_residual] using h

end SourceData
end CFSG.Quasithin.ChapterC.NaturalSixControl
