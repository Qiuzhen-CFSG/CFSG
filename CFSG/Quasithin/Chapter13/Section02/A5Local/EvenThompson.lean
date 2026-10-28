module

public import CFSG.Quasithin.Chapter13.Section02.A5Local.FullAction
public import Theory.GroupTheory.ElementaryThompsonFrattini
public import Theory.GroupTheory.ElementaryThompsonRelative
public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalUniqueness

/-!
# Thompson and Baumann subgroups in the even part of the A₅ local action

A maximum elementary subgroup of R≥V that moves V maps to an offender on
its original five-point core. Every such offender contains an odd permutation.
Thus an even local action forces J(R) to centralize V. Between O₂(LT) and T,
the known Sylow-centralizer identity and Thompson/Baumann heredity identify
both subgroups with those of O₂(LT).

Source: Aschbacher–Smith 13.2.4(1), printed p.879, specialized to the original
chosen module, as used in 13.2.9. No uniform reduced-module classification is
assumed.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

/-- An intermediate subgroup acting by even permutations has J(R)≤C(V). -/
theorem thompson_centralizes_of_even_action (R : Subgroup G)
    (hVR : V ≤ R) (hRK : R ≤ L ⊔ (T : Subgroup G))
    (heven : (R.subgroupOf (L ⊔ (T : Subgroup G))).map d.localActor ≤ alternatingGroup (Fin 5)) :
    elementaryAbelianMaxJ R ≤ centralizer (V : Set G) := by
  let K := L ⊔ (T : Subgroup G)
  let U := V.subgroupOf K
  let := d.reduced.normal
  let := d.reduced.elementary
  let q := d.localActor.rangeRestrict
  have hk : q.ker = centralizer (U : Set K) :=
    d.localActor.ker_rangeRestrict.trans d.localActor_kernel
  let ρ := NormalElementaryQuotient.representation U q d.localActor.rangeRestrict_surjective hk
  have he : ∀ g v, d.localModuleCoordinates.symm (ρ g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g.val (d.localModuleCoordinates.symm v) := by
    intro g v
    obtain ⟨g,rfl⟩ := d.localActor.rangeRestrict_surjective g
    apply d.localModuleCoordinates.injective
    rw [LinearEquiv.apply_symm_apply]
    have hh := d.localModuleCoordinates_equivariant g (d.localModuleCoordinates.symm v)
    rw [LinearEquiv.apply_symm_apply] at hh
    exact hh
  have hj : elementaryAbelianMaxJ (R.subgroupOf K) ≤ q.ker := by
    by_contra hn
    have hb := (ChapterB.lemma_B_2_7_local U q d.localActor.rangeRestrict_surjective hk
      (R.subgroupOf K) (fun _ hv => hVR hv) hn).2
    apply hn
    refine sSup_le fun A hA => ?_
    apply (map_eq_bot_iff A).mp
    by_contra hne
    have ha := (hb (A.map q) ⟨A,hA,rfl,hne⟩).isOffender ρ
    have ha' := ha.map_equivariant ρ (BinaryPermutation.coreRepresentation (Fin 5))
      d.localActor.range.subtype d.localActor.range.subtype_injective d.localModuleCoordinates.symm he
    have hnot := ChapterB.Offenders.core_offender_not_le_alternating (Or.inl rfl) ha'
    apply hnot
    rintro a ⟨a,⟨x,hx,rfl⟩,rfl⟩
    exact heven (mem_map_of_mem d.localActor (hA.1 hx))
  have hm : (elementaryAbelianMaxJ (R.subgroupOf K)).map K.subtype =
      elementaryAbelianMaxJ R := by
    rw [← elementaryAbelianMaxJ_map_injective K.subtype K.subtype_injective,
      map_subgroupOf_eq_of_le hRK]
  rw [← hm]
  rintro x ⟨x,hx,rfl⟩ v hv
  have hc := hk ▸ hj hx
  exact congrArg K.subtype (hc ⟨v,hRK (hVR hv)⟩ hv)

/-- The source J/Baumann identities on any even subgroup between O₂(LT) and T. -/
theorem thompson_baumann_eq_core_of_even_action (R : Subgroup G)
    (hQR : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R) (hRT : R ≤ (T : Subgroup G))
    (heven : (R.subgroupOf (L ⊔ (T : Subgroup G))).map d.localActor ≤ alternatingGroup (Fin 5)) :
    elementaryAbelianMaxJ R = elementaryAbelianMaxJ ((L ⊔ (T : Subgroup G)).pCoreIn 2) ∧
      ChapterB.baumann R = ChapterB.baumann ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let := d.elementary
  have hVR := d.chosen.le_core.trans hQR
  have hJ := d.thompson_centralizes_of_even_action R hVR (hRT.trans le_sup_right) heven
  have hc : R ⊓ centralizer (V : Set G) = (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    apply le_antisymm
    · exact (inf_le_inf_right _ hRT).trans_eq (d.sylow_centralizer d.normalizes_L)
    · exact le_inf hQR d.chosen.core_centralizes
  have hJQ : elementaryAbelianMaxJ R ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    rw [← hc]
    exact le_inf (sSup_le fun _ hA => hA.1) hJ
  exact ⟨(elementaryAbelianMaxJ_eq_of_intermediate R _ hJQ hQR).symm,
    (ChapterB.lemma_B_2_3_5 R V hVR hJ).trans (congrArg ChapterB.baumann hc)⟩

/-- The original even Sylow subgroup R₁=(T∩L)O₂(LT) has the two source identities. -/
theorem even_sylow_thompson_baumann :
    let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
    let R₁ := ((T : Subgroup G) ⊓ L) ⊔ Q
    elementaryAbelianMaxJ R₁ = elementaryAbelianMaxJ Q ∧
      ChapterB.baumann R₁ = ChapterB.baumann Q := by
  let K := L ⊔ (T : Subgroup G)
  let Q := K.pCoreIn 2
  have hQT : Q ≤ (T : Subgroup G) := by
    exact (d.sylow_centralizer d.normalizes_L).ge.trans inf_le_left
  apply d.thompson_baumann_eq_core_of_even_action _ le_sup_right (sup_le inf_le_left hQT)
  rw [subgroupOf_sup (inf_le_left.trans le_sup_right) (hQT.trans le_sup_right),Subgroup.map_sup]
  refine sup_le ?_ ?_
  · exact (map_mono (show (((T : Subgroup G) ⊓ L).subgroupOf K) ≤ L.subgroupOf K from
      fun _ hx => hx.2)).trans_eq d.localActor_component_image
  · rintro a ⟨x,hx,rfl⟩
    have hc := d.chosen.core_centralizes hx
    have hk : x ∈ d.localActor.ker := by
      rw [d.localActor_kernel]
      intro v hv
      exact Subtype.ext (hc v hv)
    change d.localActor x = 1 at hk
    rw [hk]
    exact one_mem _

private theorem core_thompson_normalizer :
    normalizer (elementaryAbelianMaxJ ((L ⊔ (T : Subgroup G)).pCoreIn 2) : Set G) ≤
      normalizer (L : Set G) := by
  let K := L ⊔ (T : Subgroup G)
  let Q := K.pCoreIn 2
  have hQ : IsPGroup 2 Q := pCore_isPGroup.map K.subtype
  have hJQ : elementaryAbelianMaxJ Q ≤ Q := sSup_le fun _ hA => hA.1
  have hne : Q ≠ ⊥ := fun h => d.chosen.ne_bot (bot_unique (h ▸ d.chosen.le_core))
  apply normalizer_le_of_unique_maximalTwoLocal d.unique_maximal_overgroup
    (hQ.to_le hJQ) (elementaryAbelianMaxJ_ne_bot_of_finite_pGroup Q hQ hne)
  exact (K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K))).trans
    (normalizer_le_normalizer_elementaryAbelianMaxJ Q)

/-- The normalizer of J(R) lies in N(L) for every even source intermediate R. -/
theorem thompson_normalizer_of_even_action (R : Subgroup G)
    (hQR : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R) (hRT : R ≤ (T : Subgroup G))
    (heven : (R.subgroupOf (L ⊔ (T : Subgroup G))).map d.localActor ≤ alternatingGroup (Fin 5)) :
    normalizer (elementaryAbelianMaxJ R : Set G) ≤ normalizer (L : Set G) := by
  rw [(d.thompson_baumann_eq_core_of_even_action R hQR hRT heven).1]
  exact d.core_thompson_normalizer

/-- Literal normalizer bound for the source R₁=(T∩L)O₂(LT). -/
theorem even_sylow_thompson_normalizer :
    normalizer (elementaryAbelianMaxJ
      (((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2) : Set G) ≤
        normalizer (L : Set G) := by
  rw [d.even_sylow_thompson_baumann.1]
  exact d.core_thompson_normalizer

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
