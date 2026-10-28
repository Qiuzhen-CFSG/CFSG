module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryGeneration
public import Theory.SpecificGroups.PSL3.LinearThreeAdditiveRadical
public import Theory.GroupTheory.PResidual.NormalSubgroup
/-!
# Coverage and generation of the whole secondary radical

The original marked natural module gives one additive action of KS on U=Z(Q).
Its restriction to K has kernel O₂(K). The full kernel is a two-group, since
its image in KS/K and its intersection with K are two-groups. Source 4.3.11,
Q=O₂(KS), therefore identifies C_{KS}(U) with Q.

The actual R₂--K₂ commutators lie in O₂(K₂). Under the original root marking,
the additive transvection calculation forces every element of the R₂ image
into the full root plane, which is the image of O₂(K₂). Lifting through the
kernel proves R₂≤Q O₂(K₂), hence Q[R₂,K₂]=R₂ and R₂≤K. Generation is then
transported through the same normalQuotientAction used by the source sieve.

Only the original natural/root marking and the source core identity remain
as inputs. Neither coverage, generation nor R₂≤K is assumed as a record field.
Their construction and the terminal nonblock contradiction remain with
`qt-d-1222-rankone-uniqueness-nonblock`.
Source: Aschbacher--Smith, original 4.3.10--16, printed pp.617--618.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
open Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} {d : MSData c n}

private theorem join_le_original_normalizer : K c ⊔ S c ≤ normalizer (K c : Set G) :=
  sup_le (K c).le_normalizer (inf_le_right.trans c.normalizer_component.le)

private theorem join_le_center_normalizer : K c ⊔ S c ≤ normalizer (U c : Set G) :=
  ((sup_le (map_subtype_le _) inf_le_right).trans (core_normalized c)).trans
    (normalizer_le_normalizer_characteristic_image (Q c) (center (Q c)))

namespace RootCoordinates
variable (m : RootCoordinates d)
/-- Conjugation on the original center, transported through its root coordinates. -/
noncomputable def naturalAction : (K c ⊔ S c : Subgroup G) →*
    MulAut (Multiplicative (Fin 3 → d.field.Carrier)) :=
  (MulAut.congr m.coordinates).toMonoidHom.comp
    ((U c).normalizerMonoidHom.comp (inclusion (by exact join_le_center_normalizer)))

private theorem naturalAction_original (k : K c) :
    m.naturalAction ⟨k,mem_sup_left k.property⟩ = naturalAut (linearThreeActor d.model k) := by
  apply MulEquiv.ext
  intro v
  apply Multiplicative.toAdd.injective
  let u := m.coordinates.symm v
  let u' := (U c).normalizerMonoidHom ⟨k,join_le_center_normalizer (mem_sup_left k.property)⟩ u
  have hh := m.compatible k u u' (normalizerMonoidHom_apply_apply_coe _ _ _)
  rw [show m.coordinates u = v from m.coordinates.apply_symm_apply v] at hh
  exact hh

/-- Faithfulness of the original natural marking identifies its actual kernel. -/
theorem naturalAction_kernel_inter_original :
    (m.naturalAction.comp (inclusion (show K c ≤ K c ⊔ S c from le_sup_left))).ker =
      pCore 2 (K c) := by
  have he : m.naturalAction.comp (inclusion (show K c ≤ K c ⊔ S c from le_sup_left)) =
      naturalAut.comp (linearThreeActor d.model) := by
    apply MonoidHom.ext
    intro k
    exact m.naturalAction_original k
  rw [he,MonoidHom.ker_comp_of_injective _ _ naturalAut_injective]
  change (d.model.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (K c)))).ker = _
  rw [MonoidHom.ker_comp_of_injective _ _ d.model.injective,QuotientGroup.ker_mk']

/-- The full kernel is a two-group: modulo K it embeds in KS/K, and its
intersection with K is the already identified two-core. -/
theorem naturalAction_kernel_isPGroup : IsPGroup 2 m.naturalAction.ker := by
  let H := K c ⊔ S c
  let N := (K c).subgroupOf H
  let : N.Normal := normal_subgroupOf_of_le_normalizer join_le_original_normalizer
  let q := (QuotientGroup.mk' N).comp m.naturalAction.ker.subtype
  have hquot : IsPGroup 2 (H ⧸ N) := by
    apply isPGroup_quotient_of_sup_eq_top N ((S c).subgroupOf H)
      (T.isPGroup'.to_le (show S c ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
    rw [←subgroupOf_sup (show K c ≤ H from le_sup_left) (show S c ≤ H from le_sup_right)]
    exact subgroupOf_self H
  have hk : IsPGroup 2 q.ker := by
    let i : q.ker →* pCore 2 (K c) := {
      toFun := fun x => ⟨⟨x.val.val.val, by
        have hx : (x.val.val : H) ∈ N := (QuotientGroup.eq_one_iff _).mp x.property
        exact hx⟩, by
        rw [←m.naturalAction_kernel_inter_original]
        exact x.val.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    apply (pCore_isPGroup (p := 2) (G := K c)).of_injective i
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : pCore 2 (K c) => ((z : K c) : G)) he
  have hh := (hquot.to_subgroup (⊤ : Subgroup (H ⧸ N))).comap_of_ker_isPGroup q hk
  rw [comap_top] at hh
  exact hh.of_surjective (⊤ : Subgroup m.naturalAction.ker).subtype (by
    intro x; exact ⟨⟨x,mem_top x⟩,rfl⟩)

/-- The action kernel is exactly the centralizer of the original U in KS. -/
theorem naturalAction_kernel_centralizer : m.naturalAction.ker =
    (centralizer (U c : Set G)).subgroupOf (K c ⊔ S c) := by
  rw [naturalAction,MonoidHom.ker_comp_of_injective _ _ (MulAut.congr m.coordinates).injective,
    ←MonoidHom.comap_ker,normalizerMonoidHom_ker]
  rfl

variable [Finite G]

/-- Source 4.3.11 removes every extra element from the full natural-action kernel. -/
theorem naturalAction_kernel_eq (hcore : (K c ⊔ S c).pCoreIn 2 = Q c) :
    m.naturalAction.ker.map (K c ⊔ S c).subtype = Q c := by
  apply le_antisymm
  · rw [←hcore]
    exact map_mono (le_sSup ⟨inferInstance,m.naturalAction_kernel_isPGroup⟩)
  · intro q hq
    refine ⟨⟨q,mem_sup_right (core_le_sylow c hq)⟩,?_,rfl⟩
    rw [m.naturalAction_kernel_centralizer]
    change q ∈ centralizer (U c : Set G)
    intro z hz
    obtain ⟨u,hu,rfl⟩ := hz
    exact (congrArg Subtype.val (mem_center_iff.mp hu ⟨q,hq⟩)).symm

include m in
/-- The original natural-module centralizer in the full Sylow join is Q. -/
theorem join_centralizer_center (hcore : (K c ⊔ S c).pCoreIn 2 = Q c) :
    (K c ⊔ S c) ⊓ centralizer (U c : Set G) = Q c := by
  rw [←m.naturalAction_kernel_eq hcore,m.naturalAction_kernel_centralizer]
  ext x
  constructor
  · rintro ⟨hx,hz⟩
    exact ⟨⟨x,hx⟩,hz,rfl⟩
  · rintro ⟨x,hz,rfl⟩
    exact ⟨x.property,hz⟩

omit [Finite G] in
private theorem secondary_le_join : secondary c ≤ K c ⊔ S c :=
  secondary_le_original.trans le_sup_left

omit [Finite G] in
private theorem secondaryNatural_eq :
    m.naturalAction.comp (inclusion (secondary_le_join (c := c))) =
      naturalAut.comp ((pointLocalSL d.field.Carrier).subtype.comp m.secondaryProjection) := by
  apply MonoidHom.ext
  intro x
  exact m.naturalAction_original ⟨x,secondary_le_original x.property⟩

/-- The root plane is the image of the literal secondary two-core, with the
same action on U used for all of R₂. -/
theorem naturalAction_secondary_core (hn : 1 < n) :
    (((secondary c).pCoreIn 2).subgroupOf (K c ⊔ S c)).map m.naturalAction =
      ((pointRadicalSL d.field.Carrier).map (pointLocalSL d.field.Carrier).subtype).map
        naturalAut := by
  have he : ((secondary c).pCoreIn 2).subgroupOf (K c ⊔ S c) =
      (pCore 2 (secondary c)).map (inclusion (secondary_le_join (c := c))) := by
    apply map_injective (K c ⊔ S c).subtype_injective
    rw [map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans secondary_le_join),map_map]
    rfl
  rw [he,map_map,m.secondaryNatural_eq,←map_map,←map_map,m.secondary_core_image hn,
    pointLocalSL_twoCore_eq]

/-- The whole secondary radical has image in the root plane. The commutator
premise is proved on the actual radical and actual secondary subgroup. -/
theorem naturalAction_radical_le_rootPlane (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    ((R₂ c).subgroupOf (K c ⊔ S c)).map m.naturalAction ≤
      ((pointRadicalSL d.field.Carrier).map (pointLocalSL d.field.Carrier).subtype).map
        naturalAut := by
  intro b hb
  obtain ⟨r,hr,rfl⟩ := hb
  apply twoElement_of_root_commutators
  · obtain ⟨j,hj⟩ := (isPGroup_pCoreIn 2 (secondary c ⊔ S c)).exists_pow_pow_eq_one ⟨r,hr⟩
    refine ⟨j,?_⟩
    rw [←map_pow]
    have hh : r ^ (2^j) = 1 := Subtype.ext (congrArg (fun x : R₂ c => (x : G)) hj)
    rw [hh,map_one]
  · intro g hg
    obtain ⟨k,hk⟩ := m.secondaryProjection_surjective hn ⟨g,hg⟩
    let kH : (K c ⊔ S c : Subgroup G) := ⟨k,secondary_le_join k.property⟩
    have hki : m.naturalAction kH = naturalAut g := by
      have hh := m.naturalAction_original ⟨k,secondary_le_original k.property⟩
      rw [←m.secondaryProjection_apply,congrArg Subtype.val hk] at hh
      exact hh
    rw [←hki,←map_commutatorElement,←m.naturalAction_secondary_core hn]
    apply mem_map_of_mem
    exact radical_secondary_commutator_le_core D
      (commutator_mem_commutator hr k.property)

include m in
/-- The faithful-kernel lift controls every element of R₂, including its
possible part outside K. Source 4.3.11 is the only core identity assumed. -/
theorem radical_coverage (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hcore : (K c ⊔ S c).pCoreIn 2 = Q c) :
    R₂ c ≤ Q c ⊔ (secondary c).pCoreIn 2 := by
  have hi := m.naturalAction_radical_le_rootPlane hn D
  rw [←m.naturalAction_secondary_core hn] at hi
  have hh := comap_mono (f := m.naturalAction) hi
  rw [comap_map_eq,comap_map_eq] at hh
  have hm := map_mono ((le_sup_left : (R₂ c).subgroupOf (K c ⊔ S c) ≤ _).trans hh)
    (f := (K c ⊔ S c).subtype)
  rw [map_subgroupOf_eq_of_le ((radical_le_sylow c).trans le_sup_right),Subgroup.map_sup,
    map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans secondary_le_join),
    m.naturalAction_kernel_eq hcore,sup_comm] at hm
  exact hm

include m in
/-- Whole-radical generation in the original ambient group, with no generation
or containment field added to the source record. -/
theorem radical_generation (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hcore : (K c ⊔ S c).pCoreIn 2 = Q c) :
    Q c ⊔ ⁅R₂ c, secondary c⁆ = R₂ c := by
  have hQ : Q c = (K c).pCoreIn 2 := by
    apply le_antisymm
    · exact le_normalizer_iff_commutator_le_left.mp ((K c).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (K c) (pCore 2 (K c))))
    · exact (pCoreIn_mono_of_normalizes le_sup_left join_le_original_normalizer).trans_eq hcore
  exact (m.radical_generation_iff_coverage hn D hQ).mpr (m.radical_coverage hn D hcore)

include m in
/-- The desired containment follows from generation; it is not a source premise. -/
theorem radical_le_original (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hcore : (K c ⊔ S c).pCoreIn 2 = Q c) : R₂ c ≤ K c :=
  radical_le_original_of_secondary_generation D (m.radical_generation hn D hcore)

include m in
/-- The same literal normalQuotientAction now satisfies the generation input
of the corrected source sieve. -/
theorem source_action_generation (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V) (s : SecondarySourceData c n) :
    ((Q c).subgroupOf (rootNormalizer c)).map s.action ⊔
      ⁅((R₂ c).subgroupOf (rootNormalizer c)).map s.action,
        ((secondary c).subgroupOf (rootNormalizer c)).map s.action⁆ =
      ((R₂ c).subgroupOf (rootNormalizer c)).map s.action :=
  s.action_generation_of_generation (m.radical_generation hn D s.core_eq)

end RootCoordinates
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
