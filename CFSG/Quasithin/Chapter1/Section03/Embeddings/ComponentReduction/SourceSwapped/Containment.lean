module
public import Theory.GroupAction.TwoOrbitInnerAction
public import Theory.GroupAction.IrreducibleElementaryContainment
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.SourceCommutator

/-!
# Containment in the exchanged detected-component orbit

The original Frattini commutator identity descends through H/O₂(H), using the
same normalizer and quotient maps. Its image acts by inner automorphisms on
each factor of the detected two-component orbit when the factor's outer
group is abelian or a two-group. The perfect normal orbit and the ambient
odd-rank bound then force the odd complement into it. Coprime absorption
through O₂(H) gives P ≤ K; the original conjugate-generation equation gives
X ≤ K for K = ⟨Lᵀ⟩.

The sole model input in this intermediate leaf is the actual outer-group
alternative. The source nonnormal-component inspection supplies it in the
final SourceSwapped module; no stronger full A.3.8 classification is assumed.
Source: Aschbacher--Smith, proof of Proposition 1.3.4, printed p.510.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem quotientImage_componentOrbit_source (H L T : Subgroup G) (hL : L ≤ H) (hT : T ≤ H) :
    quotientImage H (componentOrbit L T) = componentOrbit (quotientImage H L) (quotientImage H T) := by
  have hKH : componentOrbit L T ≤ H := (componentOrbit_le_sup L T).trans (sup_le hL hT)
  have he : (componentOrbit L T).subgroupOf H = componentOrbit (L.subgroupOf H) (T.subgroupOf H) := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hKH,map_componentOrbit,
      map_subgroupOf_eq_of_le hL,map_subgroupOf_eq_of_le hT]
  unfold quotientImage
  rw [he,map_componentOrbit]

omit [Finite G] in
theorem LocalInput.quotient_frattini_commutator_source
    {p : ℕ} {T X P H : Subgroup G} (h : LocalInput p T X P H) :
    let S := T ⊓ normalizer P
    let f : S →* XiQuotient H := (QuotientGroup.mk' (pCore 2 H)).comp
      (inclusion (inf_le_left.trans (le_sup_right.trans h.overgroup)))
    quotientImage H P = ⁅quotientImage H P,(frattini S).map f⁆ := by
  dsimp only
  let S := T ⊓ normalizer P
  have hSH : S ≤ H := inf_le_left.trans (le_sup_right.trans h.overgroup)
  let D := (frattini S).map S.subtype
  have hDH : D ≤ H := (map_subtype_le _).trans hSH
  have he : D.subgroupOf H = (frattini S).map (inclusion hSH) := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hDH,map_map]
    rfl
  have hi : P.subgroupOf H = ⁅P.subgroupOf H,D.subgroupOf H⁆ := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le h.complement_le_overgroup,
      map_subgroupOf_eq_of_le hDH]
    exact h.frattini_commutator
  have hh := congrArg (map (QuotientGroup.mk' (pCore 2 H))) hi
  rw [map_commutator,he,map_map] at hh
  exact hh


theorem LocalInput.quotient_orbit_inner_of_outer_alternative
    {p : ℕ} {T X P H L : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hT : IsSylowIn 2 T H)
    (hL : ComponentDetection P H L) (hn : ¬ (quotientImage H L).Normal)
    (hout : IsMulCommutative (MulAut.Outer (quotientImage H L)) ∨
      IsPGroup 2 (MulAut.Outer (quotientImage H L))) :
    quotientImage H P ≤ quotientImage H (componentOrbit L T) ⊔
      centralizer (quotientImage H (componentOrbit L T) : Set (XiQuotient H)) := by
  let : Fact p.Prime := ⟨h.prime⟩
  let B := quotientImage H L
  let A := quotientImage H T
  have hsq : IsSQTK KnownSimple.IsKnownSimple (XiQuotient H) :=
    ⟨quotient_stronglyQuasithin hH.stronglyQuasithin, hH.isKGroup.quotient _⟩
  have hi : (normalizer (B : Set (XiQuotient H))).index = 2 := by
    exact (ChapterA.Section03.ComponentOrbitBound.normal_or_index_two_of_noncentral_structure
      (ChapterA.Section03.CComponentCommutation.noncentralStructureInput KnownSimple.IsKnownSimple)
      hsq (pCore_quotient_pCore_eq_bot 2) (component_isCComponent hL.component)).resolve_left hn
  have hnK := h.detected_component_orbit_normal hH hT hL
  have hnKb : (quotientImage H (componentOrbit L T)).Normal :=
    Subgroup.Normal.map hnK _ (QuotientGroup.mk'_surjective _)
  have he := quotientImage_componentOrbit_source H L T hL.mem.1 (le_sup_right.trans h.overgroup)
  have : (componentOrbit B A).Normal := he ▸ hnKb
  let S := T ⊓ normalizer P
  let f : S →* XiQuotient H := (QuotientGroup.mk' (pCore 2 H)).comp
    (inclusion (inf_le_left.trans (le_sup_right.trans h.overgroup)))
  rw [he]
  exact frattini_commutator_inner_on_orbit_of_outer_tame_source f B (quotientImage H P) A
    h.quotient_odd_complement.isPGroup h.odd hL.component hi hout
    h.quotient_frattini_commutator_source

theorem LocalInput.quotient_complement_le_orbit_of_outer_alternative
    {p : ℕ} {T X P H L : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hT : IsSylowIn 2 T H)
    (hL : ComponentDetection P H L) (hn : ¬ (quotientImage H L).Normal)
    (hout : IsMulCommutative (MulAut.Outer (quotientImage H L)) ∨
      IsPGroup 2 (MulAut.Outer (quotientImage H L))) :
    quotientImage H P ≤ quotientImage H (componentOrbit L T) := by
  let : Fact p.Prime := ⟨h.prime⟩
  have hnK := h.detected_component_orbit_normal hH hT hL
  have : (quotientImage H (componentOrbit L T)).Normal :=
    Subgroup.Normal.map hnK _ (QuotientGroup.mk'_surjective _)
  have he := quotientImage_componentOrbit_source H L T hL.mem.1 (le_sup_right.trans h.overgroup)
  have : Group.IsPerfect (quotientImage H (componentOrbit L T)) := by
    rw [he]
    exact hL.component.orbit_isPerfect _
  have hi : IsNormalizerFrattiniIrreducible (quotientImage H P) := h.quotient_normalizer_irreducible
  apply hi.le_normal_of_inner_of_exponent_p h.quotient_odd_complement.isPGroup h.odd
    h.quotient_complement_not_cyclic ?_
    (quotient_stronglyQuasithin hH.stronglyQuasithin p h.prime h.odd) _
    (h.quotient_orbit_inner_of_outer_alternative hH hT hL hn hout) ?_
  · intro a
    rcases h.quotient_odd_complement with ⟨he,_⟩ | ⟨_,_,hexp⟩
    · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp he.exponent_dvd_p a
    · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (dvd_of_eq hexp) a
  · intro hzero
    apply hL.quotient_commutator_ne_bot h.complement_le_overgroup
    apply bot_unique
    apply (commutator_mono ?_ le_rfl).trans_eq hzero
    exact map_mono (subgroupOf_mono H (le_componentOrbit L T))

theorem LocalInput.complement_and_X_le_orbit_of_outer_alternative
    {p : ℕ} {T X P H L : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hT : IsSylowIn 2 T H)
    (hL : ComponentDetection P H L) (hn : ¬ (quotientImage H L).Normal)
    (hout : IsMulCommutative (MulAut.Outer (quotientImage H L)) ∨
      IsPGroup 2 (MulAut.Outer (quotientImage H L))) :
    P ≤ componentOrbit L T ∧ X ≤ componentOrbit L T := by
  let : Fact p.Prime := ⟨h.prime⟩
  let K := componentOrbit L T
  have hKH : K ≤ H := (componentOrbit_le_sup L T).trans
    (sup_le hL.mem.1 (le_sup_right.trans h.overgroup))
  have : (K.subgroupOf H).Normal := h.detected_component_orbit_normal hH hT hL
  have hinc := h.quotient_complement_le_orbit_of_outer_alternative hH hT hL hn hout
  have hsup : P.subgroupOf H ≤ K.subgroupOf H ⊔ pCore 2 H := by
    have hh := map_le_iff_le_comap.mp hinc
    change P.subgroupOf H ≤ ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).comap
      (QuotientGroup.mk' (pCore 2 H)) at hh
    rw [comap_map_eq,QuotientGroup.ker_mk'] at hh
    exact hh
  have hsub : P.subgroupOf H ≤ K.subgroupOf H :=
    le_normal_of_le_sup_coprime_pGroup _ _ _
      h.odd_complement.isPGroup.comap_subtype pCore_isPGroup
      (Nat.coprime_two_right.mpr h.odd) hsup
  have hPK : P ≤ K := by
    have hm := map_mono (f := H.subtype) hsub
    simpa only [map_subgroupOf_eq_of_le h.complement_le_overgroup,
      map_subgroupOf_eq_of_le hKH] using hm
  exact ⟨hPK,h.le_componentOrbit_of_complement_le hH hT hL hPK⟩

end CFSG.Quasithin.Chapter1.XiEmbedding
