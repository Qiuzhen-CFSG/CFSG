module
public import CFSG.Quasithin.Chapter13.Section07.OrdinaryQuotient
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.LocalSetup
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers

public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.BaumannBudget.Count
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.BaumannBudget.Inputs
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.BaumannBudget.SixAlternative.EvenAction
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.OriginalCoreComplete

/-!
# The ordinary natural-six Baumann block alternative

The actual LT action has image A₆ or S₆. In the first case the even
point-offender calculation makes the point-radical Baumann subgroup normal.
In the second case native C.1.37 gives its characteristic-normal or block
alternative. The maximal-local hypothesis excludes the normal alternatives
when the original Baumann normalizer escapes M. All point and radical maps
are literal; no nonabelian conjugate-span premise is used.

Source: Aschbacher--Smith 13.2.2(7), 13.3.10(2), pp.878,887.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinarySix
open Section08.SourceCompletion
open Section07.NaturalAction
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

private theorem local_sqtk : IsSQTK KnownSimple.IsKnownSimple X := by
  let := Section07.NaturalAction.elementary d
  have hn : IsTwoLocal (normalizer (V : Set G)) :=
    ⟨V,d.chosen.ne_bot,IsElementaryAbelian.isPGroup 2 V,rfl⟩
  exact (IsSQTK.equiv (subgroupOfEquivOfLe d.normalizes_V)).mp
    ((d.counterexample.qtke.twoLocal_sqtk hn).subgroup
      ((X).subgroupOf (normalizer (V : Set G))))

private def pointElement (v : V₁) : VX :=
  ⟨⟨v,d.chosen.le_sylow.trans le_sup_right
    (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le) v.property)⟩,
    d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le) v.property⟩

/-- The literal source group and action instantiate natural-six control. -/
def sourceData
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (honto : Function.Surjective (Section07.NaturalAction.permutation d))
    (v : V₁) (hv : v ≠ 1) :
    let := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer d.normalizes_L)
    let := local_module_normal d
    ChapterC.NaturalSixControl.SourceData LX VX (T.subtype le_sup_right) := by
  let := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer d.normalizes_L)
  let := local_module_normal d
  let w := pointElement d v
  refine {
    sqtk := local_sqtk d
    component := d.counterexample.local_component.1.1
    fitting := local_characteristic_two d
    component_fitting := local_component_characteristic_two d
    generation := ?_
    elementary := local_module_elementary d
    q := permutation d
    onto := honto
    ker_eq := ordinary_natural_permutation_kernel d eL
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
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (honto : Function.Surjective (Section07.NaturalAction.permutation d))
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

private theorem point_map (hv : v ≠ 1) :
    (centralizer ({(pointElement d v : X)} : Set X)).map (X).subtype =
      X ⊓ normalizer (V₁ : Set G) := by
  ext g
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨x.property,?_⟩
    rw [←point_centralizer d v hv]
    apply mem_centralizer_iff.mpr
    intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact congrArg Subtype.val ((mem_centralizer_iff.mp hx) (pointElement d v : X) (Set.mem_singleton _))
  · rintro ⟨hg,hc⟩
    refine ⟨⟨g,hg⟩,?_,rfl⟩
    apply mem_centralizer_iff.mpr
    intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    apply Subtype.ext
    rw [←point_centralizer d v hv] at hc
    exact (mem_centralizer_iff.mp hc) v (Set.mem_singleton _)

/-- The point parabolic is exactly the original N_LT(V1). -/
theorem sourceData_point_map :
    let := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer d.normalizes_L)
    let := local_module_normal d
    ((sourceData d eL honto v hv).P).map (X).subtype = X ⊓ normalizer (V₁ : Set G) :=
  point_map d v hv

/-- The literal source point parabolic is generated by L1 and T. -/
theorem point_parabolic_eq :
    X ⊓ normalizer (V₁ : Set G) = sourceOne L T V₁ ⊔ (T : Subgroup G) := by
  exact (Section08.TransvectionQuotients.FiveSeed.BarMarking.residual_normalizer_sup_sylow
    X V₁ T le_sup_right d.line_stable).symm

private theorem point_baumann_map (hv : v ≠ 1) :
    (ChapterB.baumann ((centralizer ({(pointElement d v : X)} : Set X)).pCoreIn 2)).map
      (X).subtype =
      ChapterB.baumann ((sourceOne L T V₁ ⊔ (T : Subgroup G)).pCoreIn 2) := by
  have hm : (ChapterB.baumann
      ((centralizer ({(pointElement d v : X)} : Set X)).pCoreIn 2)).map (X).subtype =
      ChapterB.baumann (((centralizer ({(pointElement d v : X)} : Set X)).pCoreIn 2).map
        (X).subtype) :=
    Stellmacher.baumann_map_injective (X).subtype (X).subtype_injective _
  rw [hm,map_pCoreIn_of_injective 2 _ _ (X).subtype_injective,
    point_map d v hv,point_parabolic_eq d]

/-- The radical maps to the original R1=O2(L1T), with the literal quotient conventions. -/
theorem sourceData_radical_map :
    let := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer d.normalizes_L)
    let := local_module_normal d
    ((sourceData d eL honto v hv).R).map (X).subtype =
      (sourceOne L T V₁ ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 := by
  let := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer d.normalizes_L)
  let := local_module_normal d
  rw [ChapterC.NaturalSixControl.SourceData.R,map_pCoreIn_of_injective 2 _ _ (X).subtype_injective,
    sourceData_point_map d eL honto v hv,point_parabolic_eq d]

/-- Baumann control is transported to that same R1, rather than to a conjugate or model. -/
theorem sourceData_baumann_map :
    let := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer d.normalizes_L)
    let := local_module_normal d
    ((sourceData d eL honto v hv).B).map (X).subtype =
      ChapterB.baumann ((sourceOne L T V₁ ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2) := by
  let := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer d.normalizes_L)
  let := local_module_normal d
  have hm : ((sourceData d eL honto v hv).B).map (X).subtype =
      ChapterB.baumann (((sourceData d eL honto v hv).R).map (X).subtype) :=
    Stellmacher.baumann_map_injective (X).subtype (X).subtype_injective _
  exact hm.trans (congrArg ChapterB.baumann (sourceData_radical_map d eL honto v hv))

/-- The genuine characteristic-subgroup alternative gives the required
ambient normalizer bound under the original maximal local hypothesis. -/
theorem sourceData_characteristic_normalizer_bound
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    letI := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer d.normalizes_L)
    letI := local_module_normal d
    ∀ C : Subgroup (sourceData d eL honto v hv).B, C.Characteristic → C ≠ ⊥ →
      (C.map (sourceData d eL honto v hv).B.subtype).Normal →
      normalizer (ChapterB.baumann
        ((sourceOne L T V₁ ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2) : Set G) ≤ M := by
  let := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer d.normalizes_L)
  let := local_module_normal d
  intro C hchar hne hnormal
  let := hchar
  let B := (sourceData d eL honto v hv).B
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
  rw [←sourceData_baumann_map d eL honto v hv]
  exact (normalizer_le_normalizer_characteristic_map
    (X).subtype (X).subtype_injective B C).trans hcontrol

/-- In the A₆-image case, the literal point Baumann normalizer is controlled. -/
theorem normalizer_le_of_even_image
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (v : V₁) (hv : v ≠ 1)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (heven : (permutation d).range = alternatingGroup (Fin 6)) :
    normalizer (ChapterB.baumann
      ((sourceOne L T V₁ ⊔ (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M := by
  let := local_module_normal d
  let := local_module_elementary d
  let w := pointElement d v
  let R := (centralizer ({(w : X)} : Set X)).pCoreIn 2
  let B := ChapterB.baumann R
  have hw : w ≠ 1 := by
    intro hh
    exact hv (Subtype.ext (congrArg (fun a : VX => a.val.val) hh))
  have hn : B.Normal := baumann_normal_of_even_natural_action VX (permutation d)
    (localCoordinate d) (localCoordinate_conjugation d)
    (ordinary_natural_permutation_kernel d eL) heven w hw
  have hVR : VX ≤ R := by
    apply le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 VX) ?_ le_normalizer_of_normal
    intro a ha
    apply mem_centralizer_iff.mpr
    rintro b rfl
    exact congrArg Subtype.val (mul_comm w (⟨a,ha⟩ : VX))
  have hRne : R ≠ ⊥ := by
    intro hh
    have hmem := hVR w.property
    rw [hh,mem_bot] at hmem
    exact hw (Subtype.ext hmem)
  have hBne : B ≠ ⊥ :=
    ChapterC.RankOne.SymmetricSix.baumann_ne_bot R (isPGroup_pCoreIn 2 _) hRne
  have he : B.map (X).subtype = ChapterB.baumann
      ((sourceOne L T V₁ ⊔ (T : Subgroup G)).pCoreIn 2) := point_baumann_map d v hv
  rw [← he,d.local_normalizer]
  apply h1221.normal_subgroup_normalizer_le d.normalizes_L (map_subtype_le _) ?_ ?_
  · intro hz
    exact hBne ((B.map_eq_bot_iff_of_injective (X).subtype_injective).mp hz)
  · apply le_normalizer_iff.mpr
    intro x hx a ha
    obtain ⟨a,ha,rfl⟩ := ha
    exact mem_map_of_mem (X).subtype (hn.conj_mem a ha ⟨x,hx⟩)

/-- Original 13.3.10(2) in the ordinary A₆ case, with both action images proved. -/
theorem block_of_baumann_escape
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    OrdinaryBaumannBlockAlternative d := by
  intro hescape
  let := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer d.normalizes_L)
  let := local_module_normal d
  have hnV : Nontrivial V₁ := Finite.one_lt_card_iff_nontrivial.mp (by rw [d.line_card]; decide)
  obtain ⟨v,hv⟩ := exists_ne (1 : V₁)
  by_cases honto : Function.Surjective (permutation d)
  · rcases (sourceData d eL honto v hv).characteristic_or_block_source with hc | hb
    · obtain ⟨C,hC,hne,hn⟩ := hc
      exact (hescape (sourceData_characteristic_normalizer_bound d eL honto v hv
        h1221 C hC hne hn)).elim
    · exact hb
  · have hi : (permutation d).range.index ∣ 2 := by
      simpa only [alternatingGroup.index_eq_two] using index_dvd_of_le (alternating_le_range d)
    have heven : (permutation d).range = alternatingGroup (Fin 6) := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hi with hi | hi
      · exact (honto (MonoidHom.range_eq_top.mp (index_eq_one.mp hi))).elim
      · exact Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi
    exact (hescape (normalizer_le_of_even_image d eL v hv h1221 heven)).elim

end CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinarySix
