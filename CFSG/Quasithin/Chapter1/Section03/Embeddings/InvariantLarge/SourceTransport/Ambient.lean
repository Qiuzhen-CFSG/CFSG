module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.SourceModels
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.SourceTransport.Action
public import Theory.GroupTheory.GeneralizedFitting.NormalQuasisimpleImage

/-!
# The actual almost-simple section for the invariant large-prime case

Restrict to LT, quotient by its two-core, and then quotient by the centralizer
of the component image. The resulting group has the simple marked component
as its generalized Fitting subgroup and the original T-image as a Sylow
two-subgroup. The maps preserve P and all its normalizer and Frattini data.
A/C and A.3.6 make the component center coprime to p > 3, so P embeds.

Strong quasithinness is not assumed to descend through arbitrary quotients.
Theorem A gives it for the simple component section. The quotient by that
component is a two-group, so every odd subgroup of the new ambient group lies
inside the component. This proves precisely the SQTK input needed by A.3.15.
The source component's central quotient and every original inclusion remain
marked by the displayed equivalences and commuting homomorphisms.

Source: Aschbacher–Smith A.3.15 and Proposition 1.3.4, printed pp.510–511.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.SourceTransport
universe u
variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} {T X P H L : Subgroup G}
variable (h : SylowInput KnownSimple.IsKnownSimple p T X P H L)

abbrev joined (_h : SylowInput KnownSimple.IsKnownSimple p T X P H L) := L ⊔ T

local instance joined_component_normal : (L.subgroupOf (joined h)).Normal :=
  (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le L.le_normalizer h.component_invariant)

abbrev originalComponent (_h : SylowInput KnownSimple.IsKnownSimple p T X P H L) :
    Subgroup (XiQuotient (joined _h)) := quotientImage (joined _h) L

local instance image_normal : (originalComponent h).Normal :=
  Subgroup.Normal.map (joined_component_normal h) _ (QuotientGroup.mk'_surjective _)

/-- The component's own two-core quotient, with the actual ambient quotient map. -/
def componentImageEquiv : XiQuotient L ≃* originalComponent h := by
  let B := L.subgroupOf (joined h)
  let f := (QuotientGroup.mk' (pCore 2 (joined h))).subgroupMap B
  have he : f.ker = pCore 2 B := by
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2
      (inferInstance : B.Normal).isSubnormal).symm
  exact (QuotientGroup.congr _ _ (subgroupOfEquivOfLe (show L ≤ joined h from le_sup_left)).symm
    (pCore_map_iso 2 (subgroupOfEquivOfLe (show L ≤ joined h from le_sup_left)).symm)).trans
      ((QuotientGroup.quotientMulEquivOfEq he.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective f
          ((QuotientGroup.mk' (pCore 2 (joined h))).subgroupMap_surjective B)))

local instance image_quasisimple : IsQuasisimple (originalComponent h) := by
  let : IsQuasisimple (XiQuotient L) := h.component_quasisimple
  exact IsQuasisimple.of_mulEquiv (componentImageEquiv h)

abbrev Ambient := CentralizerQuotient (originalComponent h)

/-- The canonical quotient group structure, exposed at the source boundary. -/
@[reducible] instance ambientGroup : Group (Ambient h) := inferInstance
abbrev component : Subgroup (Ambient h) := centralizerQuotientComponent (originalComponent h)

def ambientMap : joined h →* Ambient h :=
  (centralizerQuotientMap (originalComponent h)).comp (QuotientGroup.mk' (pCore 2 (joined h)))

omit [Finite G] in
theorem ambientMap_surjective : Function.Surjective (ambientMap h) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

def simpleComponentEquiv : (XiQuotient L ⧸ center (XiQuotient L)) ≃* component h :=
  (QuotientGroup.congr _ _ (componentImageEquiv h)
    (by
      let e := componentImageEquiv h
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact (centerCongr e ⟨x, hx⟩).property
      · intro x hx
        exact ⟨e.symm x, (centerCongr e).symm ⟨x, hx⟩ |>.property, e.apply_symm_apply x⟩)).trans
      (centralizerQuotientComponentEquiv (originalComponent h))

theorem component_simple : IsSimpleGroup (component h) :=
  centralizerQuotientComponent_simple (originalComponent h)

theorem component_fitting : generalizedFitting (Ambient h) = component h :=
  centralizerQuotient_generalizedFitting_unrestricted (originalComponent h)

theorem component_centralizer : centralizer (component h : Set (Ambient h)) = ⊥ :=
  centralizerQuotientComponent_centralizer (originalComponent h)

theorem joined_sqtk : IsSQTK KnownSimple.IsKnownSimple (joined h) := by
  have hle : joined h ≤ H := sup_le h.component.1 (le_sup_right.trans h.overgroup)
  exact (IsSQTK.equiv (subgroupOfEquivOfLe hle)).mp (h.sqtk.subgroup _)

omit [Finite G] in
theorem joined_two_sylow : IsSylowIn 2 T (joined h) :=
  component_join_sylow_of_sylow h.toLocalInput h.two_sylow h.component.1

def sylow : Sylow 2 (Ambient h) :=
  (joined_two_sylow h).choose.mapSurjective (f := ambientMap h) (ambientMap_surjective h)

theorem sylow_eq_image : (sylow h : Subgroup (Ambient h)) =
    imageTwoGroup (T := T) (ambientMap h) := by
  have hs : ((joined_two_sylow h).choose : Subgroup (joined h)) = T.subgroupOf (joined h) := by
    apply map_injective (joined h).subtype_injective
    rw [(joined_two_sylow h).choose_spec, map_subgroupOf_eq_of_le (show T ≤ joined h from le_sup_right)]
  change ((joined_two_sylow h).choose : Subgroup (joined h)).map (ambientMap h) = _
  rw [hs]

abbrev complement : Subgroup (Ambient h) := imageComplement (P := P) (ambientMap h)

omit [Finite G] in
theorem complement_le_component : complement h ≤ component h := by
  change (P.subgroupOf (joined h)).map ((centralizerQuotientMap (originalComponent h)).comp
    (QuotientGroup.mk' (pCore 2 (joined h)))) ≤ _
  rw [← map_map]
  exact map_mono (map_mono (subgroupOf_mono (joined h) h.complement_le_component))

local instance component_normal : (component h).Normal :=
  Subgroup.Normal.map (image_normal h) (centralizerQuotientMap (originalComponent h))
    (QuotientGroup.mk'_surjective _)

local instance component_quasisimple : IsQuasisimple (component h) := by
  let : IsSimpleGroup (component h) := component_simple h
  exact IsQuasisimple.of_surjective
    ((centralizerQuotientMap (originalComponent h)).subgroupMap (originalComponent h))
    ((centralizerQuotientMap (originalComponent h)).subgroupMap_surjective _)

omit [Finite G] in
theorem component_eq_map : component h = (L.subgroupOf (joined h)).map (ambientMap h) := by
  change ((L.subgroupOf (joined h)).map (QuotientGroup.mk' _)).map _ = _
  rw [map_map]
  rfl

theorem component_sup_sylow : component h ⊔ (sylow h : Subgroup (Ambient h)) = ⊤ := by
  rw [component_eq_map, sylow_eq_image]
  change (L.subgroupOf (joined h)).map (ambientMap h) ⊔
    (T.subgroupOf (joined h)).map (ambientMap h) = _
  rw [← Subgroup.map_sup]
  have he : L.subgroupOf (joined h) ⊔ T.subgroupOf (joined h) = ⊤ := by
    apply map_injective (joined h).subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show L ≤ joined h from le_sup_left),
      map_subgroupOf_eq_of_le (show T ≤ joined h from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
  rw [he, map_top_of_surjective _ (ambientMap_surjective h)]

theorem ambient_quotient_two : IsPGroup 2 (Ambient h ⧸ component h) :=
  isPGroup_quotient_of_sup_eq_top (component h) (sylow h : Subgroup (Ambient h))
    (sylow h).isPGroup' (component_sup_sylow h)

theorem ambient_sqtk
    (hA : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple Y) :
    IsSQTK KnownSimple.IsKnownSimple (Ambient h) := by
  have hQ : IsSQTK KnownSimple.IsKnownSimple (XiQuotient (joined h)) :=
    ⟨quotient_stronglyQuasithin (joined_sqtk h).stronglyQuasithin,
      (joined_sqtk h).isKGroup.quotient _⟩
  have hsem : ChapterA.Section02.IsSemisimple (component h) := by
    apply top_unique
    exact le_sSup (show IsComponent (component h) ⊤ from
      ⟨.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩)
  have hsec : ChapterA.Section02.IsSectionOf (component h) (XiQuotient (joined h)) :=
    (ChapterA.Section02.IsSectionOf.quotient_subgroup (originalComponent h) (center _)).of_mulEquiv
      (centralizerQuotientComponentEquiv (originalComponent h)).symm
  have hD := (hA (XiQuotient (joined h))).stronglyQuasithin_section
    hQ.stronglyQuasithin hQ.isKGroup hsec hsem
  refine ⟨?_, hQ.isKGroup.quotient _⟩
  intro r hr ho
  let : Fact r.Prime := ⟨hr⟩
  apply (primeRank_le_iff r 2).mpr
  intro A hAp hAc
  let q := QuotientGroup.mk' (component h)
  have htwo : IsPGroup 2 (A.map q) := (ambient_quotient_two h).to_subgroup _
  have hz : A.map q = ⊥ := by
    have hd := (hAp.map q).disjoint_of_coprime htwo (Nat.coprime_two_right.mpr ho)
    simpa using hd.eq_bot
  have hAD : A ≤ component h := by
    simpa only [Subgroup.map_eq_bot_iff, q, QuotientGroup.ker_mk'] using hz
  have hh := (primeRank_le_iff r 2).mp (hD r hr ho) (A.subgroupOf (component h))
    hAp.comap_subtype
    (IsMulCommutative.of_comm (fun a b => (subgroupOfEquivOfLe hAD).injective (by
      let _ := hAc
      rw [map_mul, map_mul]
      exact mul_comm _ _)))
  rwa [Group.rank_congr (subgroupOfEquivOfLe hAD)] at hh

@[simp] theorem simpleComponentEquiv_mk (x : L) :
    (simpleComponentEquiv h (QuotientGroup.mk' (center (XiQuotient L))
      (QuotientGroup.mk' (pCore 2 L) x)) : Ambient h) =
      ambientMap h (inclusion (show L ≤ joined h from le_sup_left) x) := rfl

theorem complementMap_factor :
    (ambientMap h).comp (inclusion (h.complement_le_component.trans le_sup_left)) =
      (component h).subtype.comp ((simpleComponentEquiv h).toMonoidHom.comp
        (InvariantLarge.componentSimpleMap h.complement_le_component)) := by
  ext x
  exact (simpleComponentEquiv_mk h (inclusion h.complement_le_component x)).symm

theorem complementMap_injective
    (hA : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple Y)
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple Y)
    (hp : 3 < p) :
    Function.Injective ((ambientMap h).comp
      (inclusion (h.complement_le_component.trans le_sup_left))) := by
  let : Fact p.Prime := ⟨h.prime⟩
  rw [complementMap_factor]
  exact (component h).subtype_injective.comp ((simpleComponentEquiv h).injective.comp
    (componentSimpleMap_injective h.odd_complement.isPGroup h.odd h.complement_le_component
      (h.component_center_coprime hA hC hp)))

theorem complement_pairAction
    (hA : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple Y)
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple Y)
    (hp : 3 < p) : PairAction p (sylow h : Subgroup (Ambient h)) (complement h) := by
  rw [sylow_eq_image]
  exact image_pairAction (ambientMap h) (h.complement_le_component.trans le_sup_left)
    le_sup_right h.toLocalInput (complementMap_injective h hA hC hp)

theorem complement_permute_sylow :
    (complement h : Set (Ambient h)) * (sylow h : Set (Ambient h)) =
      (sylow h : Set (Ambient h)) * (complement h : Set (Ambient h)) := by
  change (complement h : Set (Ambient h)) * ((sylow h : Subgroup (Ambient h)) : Set (Ambient h)) =
    ((sylow h : Subgroup (Ambient h)) : Set (Ambient h)) * (complement h : Set (Ambient h))
  rw [sylow_eq_image]
  exact complement_image_mul_two_image h.toLocalInput
    (h.complement_le_component.trans le_sup_left) le_sup_right (ambientMap h)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.SourceTransport
