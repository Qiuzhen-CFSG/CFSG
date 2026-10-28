module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.Setup
public import CFSG.Quasithin.Chapter13.Section07.OrdinaryQuotient
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.LocalSetup
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers

/-!
# The original point-parabolic input for natural-six Baumann control

The nonabelian V-span supplies the actual surjection LT to S6 and its
literal two-core kernel. The source coordinates on V and any nonidentity
element of V1 therefore give the natural-six point-parabolic data, with
no additional action, characteristic-two or component premise. The
parabolic maps back to the original N_LT(V1), hence its radical is R1.

Source: Aschbacher--Smith 13.2.1--2(7) and 13.7.4(1), pp.877--878,937.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
open Section08.SourceCompletion
open Section05.PlaneGeometry
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

local notation "X" => (L ⊔ (T : Subgroup G) : Subgroup G)
local notation "LX" => L.subgroupOf X
local notation "VX" => V.subgroupOf X

/-- The original component is normal in its Sylow product. -/
theorem component_normal : (LX).Normal :=
  normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer d.normalizes_L)

/-- SQTK is inherited from the actual two-local normalizer of V. -/
theorem local_sqtk : IsSQTK KnownSimple.IsKnownSimple X := by
  let := NaturalAction.elementary d
  have hn : IsTwoLocal (normalizer (V : Set G)) :=
    ⟨V,d.chosen.ne_bot,IsElementaryAbelian.isPGroup 2 V,rfl⟩
  exact (IsSQTK.equiv (subgroupOfEquivOfLe d.normalizes_V)).mp
    ((d.counterexample.qtke.twoLocal_sqtk hn).subgroup
      ((X).subgroupOf (normalizer (V : Set G))))

/-- The literal source group and action instantiate natural-six control. -/
def sourceData
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (v : V₁) (hv : v ≠ 1) :
    let := component_normal d
    let := local_module_normal d
    ChapterC.NaturalSixControl.SourceData LX VX (T.subtype le_sup_right) := by
  let := component_normal d
  let := local_module_normal d
  let w : VX := ⟨⟨v,d.chosen.le_sylow.trans le_sup_right
    (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le) v.property)⟩,
    d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le) v.property⟩
  refine {
    sqtk := local_sqtk d
    component := d.counterexample.local_component.1.1
    fitting := local_characteristic_two d
    component_fitting := local_component_characteristic_two d
    generation := ?_
    elementary := local_module_elementary d
    q := NaturalAction.permutation d
    onto := nonabelian_permutation_surjective d h hU hV
    ker_eq := nonabelian_permutation_kernel d h hU hV
    image_component := permutation_local_image d
    eV := localCoordinate d
    action := localCoordinate_conjugation d
    v := w
    v_ne := ?_
    sylow_fixes := ?_ }
  · rw [Sylow.coe_subtype,←subgroupOf_sup le_sup_left le_sup_right]
    exact subgroupOf_self X
  · intro he
    apply hv
    exact Subtype.ext (congrArg (fun a : VX => a.val.val) he)
  · intro t ht
    apply Subtype.ext
    have hc := normalizer_le_centralizer_of_card_two V₁ d.line_card
      (d.line_stable ht)
    exact (mem_centralizer_iff.mp hc v v.property).symm

variable
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (v : V₁) (hv : v ≠ 1)

private theorem point_centralizer (hv : v ≠ 1) : centralizer ({(v : G)} : Set G) = normalizer (V₁ : Set G) := by
  have hgen : zpowers (v : G) = V₁ := by
    have hh := congrArg (Subgroup.map V₁.subtype)
      (zpowers_eq_top_of_prime_card (p := 2) d.line_card hv)
    simpa only [MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype,subtype_apply] using hh
  calc
    centralizer ({(v : G)} : Set G) = centralizer (V₁ : Set G) := by
      rw [←centralizer_closure,←zpowers_eq_closure,hgen]
    _ = normalizer (V₁ : Set G) := le_antisymm (Subgroup.centralizer_le_normalizer _)
      (normalizer_le_centralizer_of_card_two V₁ d.line_card)

/-- The point parabolic is exactly the original N_LT(V1). -/
theorem sourceData_point_map :
    let := component_normal d
    let := local_module_normal d
    ((sourceData d h hU hV v hv).P).map (X).subtype = X ⊓ normalizer (V₁ : Set G) := by
  let := component_normal d
  let := local_module_normal d
  let s := sourceData d h hU hV v hv
  ext g
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨x.property,?_⟩
    rw [←point_centralizer d v hv]
    apply mem_centralizer_iff.mpr
    intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact congrArg Subtype.val ((mem_centralizer_iff.mp hx) (s.v : X) (Set.mem_singleton _))
  · rintro ⟨hg,hc⟩
    refine ⟨⟨g,hg⟩,?_,rfl⟩
    apply mem_centralizer_iff.mpr
    intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    apply Subtype.ext
    rw [←point_centralizer d v hv] at hc
    exact (mem_centralizer_iff.mp hc) v (Set.mem_singleton _)

/-- The literal source point parabolic is generated by L1 and T. -/
theorem point_parabolic_eq :
    X ⊓ normalizer (V₁ : Set G) = sourceOne L T V₁ ⊔ (T : Subgroup G) := by
  exact (Section08.TransvectionQuotients.FiveSeed.BarMarking.residual_normalizer_sup_sylow
    X V₁ T le_sup_right d.line_stable).symm

/-- The radical maps to the original R1=O2(L1T), with the literal quotient conventions. -/
theorem sourceData_radical_map :
    let := component_normal d
    let := local_module_normal d
    ((sourceData d h hU hV v hv).R).map (X).subtype =
      (sourceOne L T V₁ ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 := by
  let := component_normal d
  let := local_module_normal d
  rw [ChapterC.NaturalSixControl.SourceData.R,map_pCoreIn_of_injective 2 _ _ (X).subtype_injective,
    sourceData_point_map d h hU hV v hv,point_parabolic_eq d]

/-- Baumann control is transported to that same R1, rather than to a conjugate or model. -/
theorem sourceData_baumann_map :
    let := component_normal d
    let := local_module_normal d
    ((sourceData d h hU hV v hv).B).map (X).subtype =
      ChapterB.baumann ((sourceOne L T V₁ ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2) := by
  let := component_normal d
  let := local_module_normal d
  have hm : ((sourceData d h hU hV v hv).B).map (X).subtype =
      ChapterB.baumann (((sourceData d h hU hV v hv).R).map (X).subtype) :=
    Stellmacher.baumann_map_injective (X).subtype (X).subtype_injective _
  exact hm.trans (congrArg ChapterB.baumann (sourceData_radical_map d h hU hV v hv))

/-- The genuine characteristic-subgroup alternative gives the required
ambient normalizer bound under the original maximal local hypothesis. -/
theorem sourceData_characteristic_normalizer_bound
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    letI := component_normal d
    letI := local_module_normal d
    ∀ C : Subgroup (sourceData d h hU hV v hv).B, C.Characteristic → C ≠ ⊥ →
      (C.map (sourceData d h hU hV v hv).B.subtype).Normal →
      normalizer (ChapterB.baumann
        ((sourceOne L T V₁ ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2) : Set G) ≤ M := by
  let := component_normal d
  let := local_module_normal d
  intro C hchar hne hnormal
  let := hchar
  let B := (sourceData d h hU hV v hv).B
  let D := (C.map B.subtype).map (X).subtype
  have hDX : D ≤ X := map_subtype_le _
  have hDne : D ≠ ⊥ := by
    intro he
    exact hne ((C.map_eq_bot_iff_of_injective B.subtype_injective).mp
      (((C.map B.subtype).map_eq_bot_iff_of_injective (X).subtype_injective).mp he))
  have hXD : X ≤ normalizer (D : Set G) := by
    apply le_normalizer_iff.mpr
    intro x hx a ha
    obtain ⟨a,ha,rfl⟩ := ha
    exact mem_map_of_mem (X).subtype (hnormal.conj_mem a ha ⟨x,hx⟩)
  have hcontrol : normalizer (D : Set G) ≤ M := by
    rw [d.local_normalizer]
    exact h1221.normal_subgroup_normalizer_le d.normalizes_L hDX hDne hXD
  rw [←sourceData_baumann_map d h hU hV v hv]
  exact (normalizer_le_normalizer_characteristic_map
    (X).subtype (X).subtype_injective B C).trans hcontrol

end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
