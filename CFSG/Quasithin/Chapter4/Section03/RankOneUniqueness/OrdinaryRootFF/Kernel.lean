module

public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF.Action
public import Theory.GroupTheory.PCoreCentralKernelTransfer
public import Theory.GroupTheory.PerfectCenterFrattini
public import Theory.GroupTheory.ConjugateIntersectionCore

/-!
# Lifting the ordinary root action comparison

The marked point local acts nontrivially on its own two-core, hence on U.
For the normal secondary subgroup KZ, reducedness kills O₂(KZ) in the
action on U. Quasisimplicity makes the remaining kernel central. If KZ and
the point local have the same actual action image, perfectness of
KZ/O₂(KZ) removes this central supplement. Thus KZ lies in J O₂(KZ),
and consequently in J Q. This retains the original quotient projection;
an abstract isomorphism between the two image groups is insufficient.

The fixed-factor identity also makes Q normalize J before the module
equality is known. Conjugate generation then gives KZ = J, so N normalizes
O₂(J) and U = O₂(J). Only the action image equality remains to classify.

Source: Aschbacher--Smith 4.3.6, printed p.615, final paragraph.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} (m : OrdinarySymplecticMarking c n)

private theorem sup_core_eq_top_of_image_eq_top
    {X Y : Type*} [Group X] [Group Y] [Nontrivial Y]
    [IsQuasisimple (X ⧸ pCore 2 X)]
    (f : X →* Y) (hf : Function.Surjective f)
    (hc : pCore 2 X ≤ f.ker) (J : Subgroup X) (hJ : J.map f = ⊤) :
    J ⊔ pCore 2 X = ⊤ := by
  let q := QuotientGroup.mk' (pCore 2 X)
  have hk : f.ker.map q ≤ center (X ⧸ pCore 2 X) :=
    f.map_ker_central_of_quasisimple_pCore hf hc
  have hgen : J ⊔ f.ker = ⊤ := by
    rw [← comap_map_eq, hJ, comap_top]
  have him : J.map q = ⊤ := by
    apply eq_top_of_sup_center_eq_top
    apply top_unique
    calc
      ⊤ = (J ⊔ f.ker).map q := by
        rw [hgen, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr
          (QuotientGroup.mk'_surjective _)]
      _ = J.map q ⊔ f.ker.map q := map_sup _ _ _
      _ ≤ J.map q ⊔ center (X ⧸ pCore 2 X) := sup_le_sup_left hk _
  have he := congrArg (fun S => S.comap q) him
  simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using he

/-- Nontriviality comes from the embedded point radical's natural quotient. -/
theorem second_image_ne_bot (hn : 1 < n)
    (hUN : m.rootSpan ≤ m.rootNormalizer)
    (hcore : m.second.pCoreIn 2 ≤ m.rootSpan) : image m m.second ≠ ⊥ := by
  intro he
  have hJN : m.second ≤ m.rootNormalizer :=
    (map_subtype_le _).trans inf_le_right
  have hker := (Subgroup.map_eq_bot_iff _).mp he
  rw [projection_kernel m hUN] at hker
  have hc : m.second ≤ centralizer (m.second.pCoreIn 2 : Set G) := by
    intro j hj
    exact (centralizer_le hcore) (hker (show (⟨j, hJN hj⟩ : m.rootNormalizer) ∈
      m.second.subgroupOf m.rootNormalizer from hj))
  have hpc : ((pointLocal (F := m.Field)).pCoreIn 2).map m.modelEmbedding =
      m.second.pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 _ _ m.modelEmbedding_injective, m.pointLocal_image hn]
  have hrad : pointRadical (F := m.Field) ≤ center (pointLocal (F := m.Field)) := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply m.modelEmbedding_injective
    have hy : m.modelEmbedding y.val ∈ m.second :=
      (m.pointLocal_image hn).le (mem_map_of_mem _ y.property)
    have hx' : x.val ∈ (pointLocal (F := m.Field)).pCoreIn 2 :=
      mem_map_of_mem _ ((pointLocal_core_eq m.card hn).ge hx)
    have hh := hc hy (m.modelEmbedding x.val) (hpc.le (mem_map_of_mem _ hx'))
    simpa only [Subgroup.coe_mul, map_mul] using hh.symm
  exact (pointNaturalExtension m.card hn).central_lt.ne (inf_eq_left.mpr hrad)

/-- The literal action equality implies containment modulo the original root core.
The possibly nontrivial central covering kernel is discharged by perfectness. -/
theorem secondary_le_second_sup_core_of_image_eq
    (hn : 1 < n) (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer)
    (hcore : m.second.pCoreIn 2 ≤ m.rootSpan) (KZ : Subgroup G)
    (hKN : KZ ≤ m.rootNormalizer) (hJK : m.second ≤ KZ)
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (he : image m KZ = image m m.second) : KZ ≤ m.second ⊔ m.rootCore := by
  let f : KZ →* Actor m := (projection m).comp (inclusion hKN)
  have hf : f.range = image m KZ := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨⟨k, hKN k.property⟩, k.property, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  let : Nontrivial f.range := (nontrivial_iff_ne_bot _).mpr (by
    rw [hf, he]
    exact second_image_ne_bot m hn hUN hcore)
  let := hquasi
  have hc : pCore 2 KZ ≤ f.rangeRestrict.ker := by
    intro k hk
    apply Subtype.ext
    apply core_le_kernel m hr
    have hm := secondaryCore_le_rootCore m hKN hnormal (mem_map_of_mem KZ.subtype hk)
    change (k : G) ∈ (pCore 2 m.rootNormalizer).map m.rootNormalizer.subtype at hm
    obtain ⟨z, hz, hez⟩ := hm
    exact (Subtype.ext hez : z = inclusion hKN k) ▸ hz
  have hj : (m.second.subgroupOf KZ).map f.rangeRestrict = ⊤ := by
    apply top_unique
    intro x _
    have hx : x.val ∈ image m m.second := he ▸ hf ▸ x.property
    obtain ⟨j, hj, hej⟩ := hx
    refine ⟨⟨j, hJK hj⟩, hj, ?_⟩
    exact Subtype.ext hej
  have hs := sup_core_eq_top_of_image_eq_top f.rangeRestrict
    f.rangeRestrict_surjective hc (m.second.subgroupOf KZ) hj
  have hm := congrArg (fun A : Subgroup KZ => A.map KZ.subtype) hs
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hJK,
    ← MonoidHom.range_eq_map, range_subtype] at hm
  calc
    KZ = m.second ⊔ KZ.pCoreIn 2 := hm.symm
    _ ≤ m.second ⊔ m.rootCore :=
      sup_le_sup_left (secondaryCore_le_rootCore m hKN hnormal) _

/-- Application to the original terminal consumer, with its containment premise
discharged. Only the two genuine classification equalities remain explicit. -/
theorem false_of_module_and_image_eq
    (D : Chapter12.Section02.ChosenModule T L V) (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m)) (KZ : Subgroup G)
    (hT : (T : Subgroup G) ≤ m.rootNormalizer)
    (hseed : conjugateSpanBy c.ordinaryModule m.second = m.second)
    (hU : m.rootSpan = m.second.pCoreIn 2)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (hcentral : KZ ≤ centralizer (m.root : Set G))
    (hKZ : conjugateSpanBy m.second KZ = KZ)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (he : image m KZ = image m m.second) : False := by
  have hJN : m.second ≤ m.rootNormalizer :=
    (map_subtype_le _).trans inf_le_right
  have hUN : m.rootSpan ≤ m.rootNormalizer :=
    hU.le.trans ((pCoreIn_le 2 _).trans hJN)
  have hJK : m.second ≤ KZ := (le_conjugateSpanBy _ _).trans_eq hKZ
  exact c.ordinary_false_of_root_module D hn m KZ hT hseed hU hQ hKZ
    (secondary_le_second_sup_core_of_image_eq m hn hr hUN hU.ge KZ
      (hcentral.trans (Subgroup.centralizer_le_normalizer _)) hJK hnormal hquasi he) hnormal

theorem span_le_core (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) : m.rootSpan ≤ m.rootCore := by
  intro u hu
  exact mem_map_of_mem m.rootNormalizer.subtype
    (hr.le_pCore (show (⟨u, hUN hu⟩ : m.rootNormalizer) ∈ moduleSubgroup m from hu))

theorem core_centralizes_span (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) :
    m.rootCore ≤ centralizer (m.rootSpan : Set G) := by
  rintro _ ⟨q, hq, rfl⟩ u hu
  exact congrArg Subtype.val
    ((le_centralizer_iff.mp hr.le_centralizer_pCore hq) ⟨u, hUN hu⟩ hu)

/-- Reducedness already supplies the normality needed by the fixed-factor
calculation. The module equality U = O₂(J) is not needed for this step. -/
theorem core_normalizes_second (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer)
    (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hseed : conjugateSpanBy c.ordinaryModule m.second = m.second)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G))) :
    m.rootCore ≤ normalizer (m.second : Set G) := by
  have hJN : m.second ≤ m.rootNormalizer :=
    (map_subtype_le _).trans inf_le_right
  have hNQ : m.rootNormalizer ≤ normalizer (m.rootCore : Set G) :=
    m.rootNormalizer.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  exact normalizes_of_fixed_factor_and_conjugate_generation c.ordinaryModule
    m.second m.rootCore (m.second.pCoreIn 2)
    (m.second.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
    (hJN.trans hNQ)
    (((core_centralizes_span m hr hUN).trans (centralizer_le hcore)).trans
      (Subgroup.centralizer_le_normalizer _))
    (pCoreIn_le 2 _) hQ hseed

/-- Equality of the actual images discharges both terminal premises. The
normal span equality follows from characteristic control after KZ = J. -/
theorem module_and_containment_of_image_eq
    (hn : 1 < n) (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer)
    (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hseed : conjugateSpanBy c.ordinaryModule m.second = m.second)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hKN : KZ ≤ m.rootNormalizer)
    (hKZ : conjugateSpanBy m.second KZ = KZ)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (he : image m KZ = image m m.second) :
    m.rootSpan = m.second.pCoreIn 2 ∧ KZ ≤ m.second ⊔ m.rootCore := by
  have hJK : m.second ≤ KZ := (le_conjugateSpanBy _ _).trans_eq hKZ
  have hle := secondary_le_second_sup_core_of_image_eq m hn hr hUN hcore KZ
    hKN hJK hnormal hquasi he
  have hKJ : KZ ≤ normalizer (m.second : Set G) := hle.trans
    (sup_le m.second.le_normalizer (core_normalizes_second m hr hUN hcore hseed hQ))
  have hEq : KZ = m.second := le_antisymm
    (hKZ ▸ conjugateSpanBy_le (le_refl _) hKJ) hJK
  have hNJ : m.rootNormalizer ≤ normalizer (m.second : Set G) := hEq ▸ hnormal
  have hJN : m.second ≤ m.rootNormalizer :=
    (map_subtype_le _).trans inf_le_right
  have hWJ : c.ordinaryModule ≤ m.second := (le_conjugateSpanBy _ _).trans_eq hseed
  have hseedCore : c.ordinaryModule ⊓ centralizer (L : Set G) ≤ m.second.pCoreIn 2 := by
    apply (le_inf
      ((le_conjugateSpanBy _ _).trans (span_le_core m hr hUN))
      (inf_le_left.trans hWJ)).trans
    exact inf_pCoreIn_le_of_normalizes hJN le_rfl m.second.le_normalizer
  refine ⟨le_antisymm ?_ hcore, hle⟩
  exact conjugateSpanBy_le hseedCore (hNJ.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))

/-- The literal consumer now needs only the outstanding classification of the
two actual images, rather than either of the terminal group conclusions. -/
theorem false_of_image_eq
    (D : Chapter12.Section02.ChosenModule T L V) (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer)
    (hcore : m.second.pCoreIn 2 ≤ m.rootSpan) (KZ : Subgroup G)
    (hT : (T : Subgroup G) ≤ m.rootNormalizer)
    (hseed : conjugateSpanBy c.ordinaryModule m.second = m.second)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (hcentral : KZ ≤ centralizer (m.root : Set G))
    (hKZ : conjugateSpanBy m.second KZ = KZ)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (he : image m KZ = image m m.second) : False := by
  obtain ⟨hU, hle⟩ := module_and_containment_of_image_eq m hn hr hUN hcore
    hseed hQ KZ (hcentral.trans (Subgroup.centralizer_le_normalizer _)) hKZ hquasi hnormal he
  exact c.ordinary_false_of_root_module D hn m KZ hT hseed hU hQ hKZ hle hnormal

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF
