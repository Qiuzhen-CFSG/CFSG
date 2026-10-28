module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSFixedBounds
public import Theory.Representation.SL3.NaturalNormalizerRank

/-!
# The outside-image bound in the original larger-core argument

The literal KS-action on K/O₂(K), marked by the original full SL₃
isomorphism, is intertwined with its action on U. On every elementary
two-subgroup E its kernel is E ∩ O₂(KS): an involution centralizing SL₃
is scalar on U, and hence trivial. The checked projective automorphism
rank bound gives |E : E ∩ O₂(KS)| ≤ 2^(2n), including field actors.

The source maximum-elementary-subgroup argument then has two proved
branches. An outside image of order at most 2^n forces a deficit of at
least n inside the larger core, so E ∩ O₂(KS) is not contained in its
centralizer factor C. If E ∩ A ≤ U, the original fixed-center bound
instead gives |A : A ∩ E| ≥ 2^(4n), and the image bound forces an
inside-core deficit of at least 2n. These are the low-image part of (**)
and the lower-bound part of (!)–(!!) in C.1.35.

The paired natural/dual 3n estimate for larger images and the equality
argument are still required to prove O₂(KS)=Q. MSData remains explicit;
its construction, the original A₅ application, secondary geometry and
terminal exclusions remain with qt-d-1222-rankone-uniqueness-nonblock.
Source: Aschbacher–Smith C.1.35, printed pp.138–139, applied in original
4.3.11, printed p.617.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

/-- The original quotient action, retaining the full SL₃ marking. -/
def joinLinearThreeAction (d : MSData c n) :
    (K c ⊔ S c : Subgroup G) →* MulAut (Matrix.SpecialLinearGroup (Fin 3) d.field.Carrier) :=
  (MulAut.congr d.model).toMonoidHom.comp
    (pCoreJoinAction 2 (inf_le_right.trans c.normalizer_component.le))

/-- Natural coordinates intertwine the original KS-actions on U and K/O₂(K). -/
theorem MSData.exists_join_center_coordinates (d : MSData c n) :
    ∃ u : U c ≃* Multiplicative (Fin 3 → d.field.Carrier),
      let β := (MulAut.congr u).toMonoidHom.comp (joinCenterAction c)
      β.ker = pCore 2 (K c ⊔ S c : Subgroup G) ∧
      ∀ x g v, (β x (Multiplicative.ofAdd (Representation.specialLinearNatural 3 g v))).toAdd =
        Representation.specialLinearNatural 3 (joinLinearThreeAction d x g)
          (β x (Multiplicative.ofAdd v)).toAdd := by
  have hm := d.natural
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,hbot,e,he⟩ := hm
  let := hbot
  let u : U c ≃* Multiplicative (Fin 3 → d.field.Carrier) :=
    QuotientGroup.quotientBot.symm.trans e
  have hu (k : K c) (a : U c) :
      (u (joinCenterAction c (inclusion le_sup_left k) a)).toAdd =
        Representation.specialLinearNatural 3 (linearThreeActor d.model k) (u a).toAdd :=
    he k a _ rfl
  let β := (MulAut.congr u).toMonoidHom.comp (joinCenterAction c)
  have hnat (k : K c) (v : Fin 3 → d.field.Carrier) :
      (β (inclusion le_sup_left k) (Multiplicative.ofAdd v)).toAdd =
        Representation.specialLinearNatural 3 (linearThreeActor d.model k) v := by
    change (u (joinCenterAction c (inclusion le_sup_left k)
      (u.symm (Multiplicative.ofAdd v)))).toAdd = _
    rw [hu,u.apply_symm_apply]
    rfl
  refine ⟨u,?_,?_⟩
  · exact (MonoidHom.ker_comp_of_injective _ _ (MulAut.congr u).injective).trans
      d.joinCenterAction_ker
  intro x g v
  obtain ⟨k,rfl⟩ := d.model.surjective.comp (QuotientGroup.mk'_surjective _) g
  have hSK : S c ≤ normalizer (K c : Set G) := inf_le_right.trans c.normalizer_component.le
  let k' : K c := (K c).normalizerMonoidHom
    (inclusion (sup_le (K c).le_normalizer hSK) x) k
  have hα : joinLinearThreeAction d x (linearThreeActor d.model k) =
      linearThreeActor d.model k' := by
    change d.model (pCoreJoinAction 2 hSK x
      (d.model.symm (d.model (QuotientGroup.mk' _ k)))) = _
    rw [d.model.symm_apply_apply,pCoreJoinAction_mk]
    rfl
  have hinc : inclusion le_sup_left k' = x * inclusion le_sup_left k * x⁻¹ := Subtype.ext rfl
  have hβ : β (inclusion le_sup_left k') (β x (Multiplicative.ofAdd v)) =
      β x (β (inclusion le_sup_left k) (Multiplicative.ofAdd v)) := by
    rw [hinc,map_mul,map_mul,map_inv]
    exact congrArg (β x) (congrArg (β (inclusion le_sup_left k))
      ((β x).symm_apply_apply _))
  change (β x (Multiplicative.ofAdd
    (Representation.specialLinearNatural 3 (linearThreeActor d.model k) v))).toAdd = _
  rw [←hnat k v]
  change (β x (β (inclusion le_sup_left k) (Multiplicative.ofAdd v))).toAdd = _
  rw [←hβ]
  change (β (inclusion le_sup_left k') (β x (Multiplicative.ofAdd v))).toAdd =
    Representation.specialLinearNatural 3 (joinLinearThreeAction d x (linearThreeActor d.model k))
      (β x (Multiplicative.ofAdd v)).toAdd
  rw [hα]
  exact hnat k' (β x (Multiplicative.ofAdd v)).toAdd

private theorem centerAction_restrict_kernel (d : MSData c n)
    (u : U c ≃* Multiplicative (Fin 3 → d.field.Carrier))
    (E : Subgroup G) (hE : E ≤ K c ⊔ S c) :
    (((MulAut.congr u).toMonoidHom.comp (joinCenterAction c)).comp (inclusion hE)).ker =
      ((K c ⊔ S c).pCoreIn 2).subgroupOf E := by
  rw [←MonoidHom.comap_ker,MonoidHom.ker_comp_of_injective _ _ (MulAut.congr u).injective,
    d.joinCenterAction_ker]
  ext x
  change inclusion hE x ∈ pCore 2 (K c ⊔ S c : Subgroup G) ↔
    (x : G) ∈ (pCore 2 (K c ⊔ S c : Subgroup G)).map (K c ⊔ S c : Subgroup G).subtype
  constructor
  · exact fun hx => mem_map_of_mem _ hx
  · rintro ⟨y,hy,hxy⟩
    have he : y = inclusion hE x := Subtype.ext hxy
    exact he ▸ hy

/-- The induced full SL₃ action detects exactly E ∩ O₂(KS) on elementary E. -/
theorem MSData.elementary_joinLinearThreeAction_ker (d : MSData c n)
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : E ≤ K c ⊔ S c) :
    ((joinLinearThreeAction d).comp (inclusion hE)).ker =
      ((K c ⊔ S c).pCoreIn 2).subgroupOf E := by
  obtain ⟨u,hker,hi⟩ := d.exists_join_center_coordinates
  let β := ((MulAut.congr u).toMonoidHom.comp (joinCenterAction c)).comp (inclusion hE)
  have hk := Representation.SL3NaturalFixed.natural_actor_ker_eq β
    ((joinLinearThreeAction d).comp (inclusion hE))
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 E))
    (fun x g v => hi (inclusion hE x) g v)
  exact hk.symm.trans (centerAction_restrict_kernel d u E hE)

/-- The original outside image has order at most 2^(2n). -/
theorem MSData.elementary_joinCore_index_le (d : MSData c n)
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : E ≤ K c ⊔ S c) :
    ((K c ⊔ S c).pCoreIn 2).relIndex E ≤ 2^(2*n) := by
  obtain ⟨u,hker,hi⟩ := d.exists_join_center_coordinates
  let β := ((MulAut.congr u).toMonoidHom.comp (joinCenterAction c)).comp (inclusion hE)
  have hb := Representation.SL3NaturalFixed.natural_actor_card_le
    (show 0<n from d.pair.positive) (d.field.card_eq.trans (congrArg (2^·) d.degree_eq))
    β ((joinLinearThreeAction d).comp (inclusion hE)) (fun x g v => hi (inclusion hE x) g v)
  rw [←index_ker,centerAction_restrict_kernel d u E hE] at hb
  exact hb

/-- The low-image case of source (**), in literal relative-index form. -/
theorem MSData.maxElementary_smallImage_core_deficit (d : MSData c n)
    (A : invariantCoreLifts c) (hA : K c ⊔ S c ≤ normalizer (A.val : Set G))
    (E : Subgroup G) (hE : E ∈ elementaryAbelianMaxSubgroups (S c))
    (hout : ¬ E ≤ (K c ⊔ S c).pCoreIn 2)
    (hsmall : ((K c ⊔ S c).pCoreIn 2).relIndex E ≤ 2^n) :
    let P := (K c ⊔ S c).pCoreIn 2
    let C := P ⊓ Subgroup.centralizer (A.val : Set G)
    2^n ≤ C.relIndex (P ⊓ E) := by
  dsimp only
  have h := d.maxElementary_fixed_deficit A hA E hE hout
  dsimp only at h
  have hm := h.1.trans h.2
  have hb := hm.trans (Nat.mul_le_mul_left _ hsmall)
  rw [show 2*n=n+n from by omega,pow_add] at hb
  exact Nat.le_of_mul_le_mul_right hb (by positivity)

private theorem invariantLift_le_joinCore (A : invariantCoreLifts c) :
    A.val ≤ (K c ⊔ S c).pCoreIn 2 := by
  apply A.property.2.1.le.trans
  rw [←sylow_join_commutator_eq c]
  exact le_normalizer_iff_commutator_le_left.mp ((le_sup_left : K c ≤ K c ⊔ S c).trans
    ((K c ⊔ S c).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (K c ⊔ S c)
        (pCore 2 (K c ⊔ S c : Subgroup G)))))

/-- A small outside image forces a genuine core element outside C. -/
theorem MSData.maxElementary_smallImage_not_le_liftCentralizer (d : MSData c n)
    (A : invariantCoreLifts c) (hA : K c ⊔ S c ≤ normalizer (A.val : Set G))
    (E : Subgroup G) (hE : E ∈ elementaryAbelianMaxSubgroups (S c))
    (hout : ¬ E ≤ (K c ⊔ S c).pCoreIn 2)
    (hsmall : ((K c ⊔ S c).pCoreIn 2).relIndex E ≤ 2^n) :
    ¬ (K c ⊔ S c).pCoreIn 2 ⊓ E ≤
      (K c ⊔ S c).pCoreIn 2 ⊓ Subgroup.centralizer (A.val : Set G) := by
  intro hle
  have hb := d.maxElementary_smallImage_core_deficit A hA E hE hout hsmall
  dsimp only at hb
  rw [relIndex_eq_one.mpr hle] at hb
  exact (not_le_of_gt (one_lt_pow₀ (by decide : 1 < (2:ℕ))
    (show n ≠ 0 from by have := d.pair.positive; omega))) hb

/-- If E ∩ A lies in U, the original lift has fixed index at least 2^(4n);
the bounded outside image leaves an inside-core deficit of at least 2n. -/
theorem MSData.maxElementary_centerIntersection_deficit (d : MSData c n)
    (A : invariantCoreLifts c) (E : Subgroup G)
    (hE : E ∈ elementaryAbelianMaxSubgroups (S c))
    (hout : ¬ E ≤ (K c ⊔ S c).pCoreIn 2)
    (hintersection : A.val ⊓ E ≤ U c) :
    let P := (K c ⊔ S c).pCoreIn 2
    let C := P ⊓ Subgroup.centralizer (A.val : Set G)
    2^(4*n) ≤ E.relIndex A.val ∧
      2^(4*n) ≤ E.relIndex C ∧ 2^(2*n) ≤ C.relIndex (P ⊓ E) := by
  dsimp only
  let P := (K c ⊔ S c).pCoreIn 2
  let C := P ⊓ Subgroup.centralizer (A.val : Set G)
  let := hE.2.1
  have hb : Nat.card (A.val ⊓ E : Subgroup G) ≤ 2^(2*n) :=
    (card_le_of_le (le_inf hintersection
      (inf_le_right.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)))).trans
      (d.center_fixed_card_le E (hE.1.trans le_sup_right) hout)
  have he := relIndex_mul_relIndex (⊥ : Subgroup G) (E ⊓ A.val) A.val bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_right,
    (d.invariantCoreLifts_elementary A).2,inf_comm E A.val] at he
  have hindex : 2^(4*n) ≤ E.relIndex A.val := by
    apply Nat.le_of_mul_le_mul_left (c := 2^(2*n)) _ (by positivity)
    calc
      2^(2*n)*2^(4*n) = 2^(6*n) := by rw [←pow_add]; congr 1; omega
      _ = Nat.card (A.val ⊓ E : Subgroup G) * E.relIndex A.val := he.symm
      _ ≤ _ := Nat.mul_le_mul_right _ hb
  let := (d.invariantCoreLifts_elementary A).1
  have hAC : A.val ≤ C := le_inf (invariantLift_le_joinCore A) (le_centralizer A.val)
  have hC : 2^(4*n) ≤ E.relIndex C := hindex.trans
    (relIndex_le_of_le_right hAC (E.subgroupOf C).index_ne_zero_of_finite)
  have hdef := (d.maxElementary_joinCore_deficit A E hE).2
  have houtbound := d.elementary_joinCore_index_le E (hE.1.trans le_sup_right)
  refine ⟨hindex,hC,?_⟩
  have hh := (hC.trans hdef).trans (Nat.mul_le_mul_left _ houtbound)
  rw [show 4*n=2*n+2*n from by omega,pow_add] at hh
  exact Nat.le_of_mul_le_mul_right hh (by positivity)


end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
end
