module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalFixedCore
public import Theory.Representation.FirstCohomologyAutomorphism.CentralKernelBound
public import Theory.Representation.BinaryPermutation.EightNaturalCocycles

/-!
# The original core bound and the nontrivial fixed-space branch

Commutator cocycles project through the original L/O2(L) and V/C_V(L)
coordinates. The three-subgroups lemma puts [Q,O2(L)] in the original
fixed line, so the cocycles descend. Perfectness of L identifies their
kernel with C_Q(L). The natural A8 cocycle space has order128, while the
proved Sylow-centralizer bound is two; hence |Q|<=256. The already
constructed elementary subgroup of order256 is therefore all of Q.

At the same preferred escaping point, R_v is the actual two-core of
K_v T_v and Q has index two in it. Since C_LT(V)=Q and Q<R_v, this R_v
cannot be elementary. Two-perfectness of K_v then forces it to normalize
Q, contrary to the original normalizer uniqueness. This proves nonsingular
centralizer control when the original C_V(L) is nontrivial, with no extra
block, cohomology, splitting or extension-action premise.

The C_V(L)=1 branch, its HS/J4 exclusions and general12.6.13(3), and the
later fixed-space elimination12.6.23 remain. Earlier T-invariance/TI
retain their existing producer, and full source discharge remains with
the Section06 assembly. Neither full12.6.2 nor12.6.23 is asserted here.
Source: Aschbacher--Smith C.1.13(b), I.1.6(1), and the conclusion of12.6.2,
printed pp.124--125,408,828, combined manuscript of1 March2004.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original core has order at most256 once the original Sylow
centralizer has order at most two. Both quotient maps are those of D. -/
theorem SourceHypothesis.original_core_card_le_of_short_centralizer
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hs : ChapterC.IsShort L)
    (hc : Nat.card ((T : Subgroup G) ⊓ centralizer (L : Set G) : Subgroup G) ≤ 2) :
    Nat.card (Q T L) ≤ 256 := by
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect H.source.maximal_faithful.1.1
  let ρ := BinaryPermutation.alternatingNaturalRepresentation (Fin 8)
  let f := (D.coreQuotientEquiv H.chosen H.source.quasisimple).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f :=
    (D.coreQuotientEquiv H.chosen H.source.quasisimple).surjective.comp
      (QuotientGroup.mk'_surjective _)
  let m : V →* Multiplicative (BinaryPermutation.natural (Fin 8)) := {
    toFun := fun x => Multiplicative.ofAdd (D.coordinates
      (Submodule.Quotient.mk (Additive.ofMul x)))
    map_one' := by change D.coordinates 0 = 0; exact map_zero _
    map_mul' := by
      intro x y
      change D.coordinates (Submodule.Quotient.mk (Additive.ofMul x + Additive.ofMul y)) = _
      rw [Submodule.Quotient.mk_add,map_add]
      rfl }
  have hm (x : V) : m x = 1 ↔ (x : G) ∈ ZV L V := by
    change D.coordinates (Submodule.Quotient.mk (Additive.ofMul x)) = 0 ↔ _
    rw [D.coordinates.map_eq_zero_iff,Submodule.Quotient.mk_eq_zero]
    exact mem_fixedSeed_iff L V H.chosen.normalizes x
  have he (l : L) (x : V) :
      m (V.normalizerMonoidHom ⟨l,H.chosen.normalizes l.property⟩ x) =
        Multiplicative.ofAdd (ρ (f l) (m x).toAdd) := by
    apply Multiplicative.toAdd.injective
    change D.coordinates (Submodule.Quotient.mk (Additive.ofMul (conjugation L V H.chosen.normalizes l x))) = _
    change D.coordinates (Submodule.Quotient.mk
      (Additive.ofMul (conjugation L V H.chosen.normalizes l x))) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 8)
        (D.coreQuotientEquiv H.chosen H.source.quasisimple (QuotientGroup.mk' (pCore 2 L) l))
        (D.coordinates (Submodule.Quotient.mk (Additive.ofMul x)))
    rw [D.coreQuotientEquiv_mk H.chosen H.source.quasisimple]
    exact D.equivariant l (Submodule.Quotient.mk (Additive.ofMul x))
  have hcomm := H.original_core_commutator_of_short hs
  have hQC := H.chosen.core_centralizes
  have hQQL : ⁅Q T L,Q T L⁆ ≤ centralizer (L : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply commutator_commutator_eq_bot_of_rotate
    · rw [hcomm]
      exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hQC)
    · rw [commutator_comm L (Q T L),hcomm]
      exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hQC)
  have hCQ : L.pCoreIn 2 ≤ Q T L := pCoreIn_mono_of_normalizes le_sup_left
    (sup_le L.le_normalizer H.chosen.sylow_normalizes_component)
  have hd (p : Q T L) (l : L) (hl : f l = 1) :
      m ⟨⁅(p : G),(l : G)⁆,hcomm.le (commutator_mem_commutator p.property l.property)⟩ = 1 := by
    apply (hm _).mpr
    refine ⟨hcomm.le (commutator_mem_commutator p.property l.property),?_⟩
    have hlq : l ∈ pCore 2 L := by
      apply (QuotientGroup.eq_one_iff l).mp
      apply (D.coreQuotientEquiv H.chosen H.source.quasisimple).injective
      exact hl.trans (map_one _).symm
    exact hQQL (commutator_mem_commutator p.property (hCQ (mem_map_of_mem L.subtype hlq)))
  have hb := card_le_cocycles_mul_centralizer (Q T L) L V H.chosen.normalizes
    hQC hcomm.le f hf m ρ he (fun x hx => ((hm x).mp hx).2) hd
  rw [BinaryPermutation.EightNaturalCocycles.cocycles_card] at hb
  have hQ : Q T L ≤ (T : Subgroup G) := (Q_le_Tv H.chosen (1 : V)).trans inf_le_left
  have hcent : Nat.card ((centralizer (L : Set G)).subgroupOf (Q T L)) ≤ 2 := by
    rw [←inf_subgroupOf_left (centralizer (L : Set G)) (Q T L)]
    rw [Nat.card_congr (subgroupOfEquivOfLe
      (show (Q T L ⊓ centralizer (L : Set G) : Subgroup G) ≤ Q T L from inf_le_left)).toEquiv]
    exact (card_le_of_le (inf_le_inf_right _ hQ)).trans hc
  exact hb.trans (by omega)

/-- The cohomological upper bound for the original Q, with its centralizer
premise discharged at the preferred escaping nonsingular point. -/
theorem SourceHypothesis.core_card_le_of_nonsingular_escape
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hz : ZV L V ≠ ⊥)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    Nat.card (Q T L) ≤ 256 := by
  obtain ⟨_,hc⟩ := H.sylow_centralizer_eq_fixed_of_nonsingular_escape D hTV hTI hz v hv he
  obtain ⟨_,hL,_⟩ := H.exists_preferred_nonsingular_original_blocks_of_fixed D hTV hTI hz v hv he
  exact H.original_core_card_le_of_short_centralizer D hL.2.1 hc.le

/-- Both bounds concern the same original Q: it is elementary of order256. -/
theorem SourceHypothesis.core_elementary_of_nonsingular_escape
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hz : ZV L V ≠ ⊥)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    IsElementaryAbelian 2 (Q T L) ∧ Nat.card (Q T L) = 256 :=
  H.core_elementary_of_nonsingular_escape_of_card_le D hTV hTI hz v hv he
    (H.core_card_le_of_nonsingular_escape D hTV hTI hz v hv he)

/-- The entire nontrivial-original-fixed-space branch of12.6.2. The cocycle
bound and original elementary subgroup supply Q, and the preferred A7 core
supplies its actual normalizing component. No extension/action premise remains. -/
theorem SourceHypothesis.nonsingular_centralizer_le_of_fixed
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hz : ZV L V ≠ ⊥)
    (v : V) (hv : D.Nonsingular v) : Gv (v : G) ≤ M L := by
  by_contra he
  have hQ := (H.core_elementary_of_nonsingular_escape D hTV hTI hz v hv he).1
  obtain ⟨w,hw,hew,hs,hi,hlt,hnot,hL,hA,hK,hjoin,hcommon,hidx,hR,hcore,htail⟩ :=
    H.exists_preferred_nonsingular_seven_core_of_fixed D hTV hTI hz v hv he
  have hnR : Kv (w : G) ≤ normalizer (Rv T L (w : G) : Set G) := by
    rw [hcore]
    exact (show Kv (w : G) ≤ Kv (w : G) ⊔ Tv T (w : G) from le_sup_left).trans
      ((Kv (w : G) ⊔ Tv T (w : G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hQR : Q T L < Rv T L (w : G) := lt_of_le_of_ne (Q_le_Rv H.chosen w)
    (fun heq => hnot ((show Kv (w : G) ≤ normalizer (Q T L : Set G) by
      rwa [←heq] at hnR).trans H.core_normalizer_le))
  have hnon : ¬ IsElementaryAbelian 2 (Rv T L (w : G)) := by
    intro hE
    have hVR := H.chosen.le_core.trans hQR.le
    have hRV : Rv T L (w : G) ≤ centralizer (V : Set G) :=
      (commutator_eq_bot_iff_le_centralizer.mp
        (commutator_self_eq_bot_iff.mpr hE.toIsMulCommutative)).trans (centralizer_le hVR)
    have hRQ : Rv T L (w : G) ≤ Q T L := by
      rw [←H.join_centralizer_eq_core hTV]
      exact le_inf ((pCoreIn_le 2 _).trans inf_le_left) hRV
    exact hQR.not_ge hRQ
  exact hnot ((twoPerfect_le_normalizer_elementary_index_two (Kv (w : G))
    (Rv T L (w : G)) (Q T L) (Kv_isPPerfect (w : G)) hnR hQR.le hQ
    (H.nonsingular_original_core_index D w hw hQR) hnon).trans H.core_normalizer_le)

/-- Escaping nonsingular centralizers can now occur only in the original
fixed-free branch. This retains the literal V and C_V(L). -/
theorem SourceHypothesis.fixed_eq_bot_of_nonsingular_escape
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) : ZV L V = ⊥ := by
  by_contra hz
  exact he (H.nonsingular_centralizer_le_of_fixed D hTV hTI hz v hv)

end CFSG.Quasithin.Chapter12.Section06
