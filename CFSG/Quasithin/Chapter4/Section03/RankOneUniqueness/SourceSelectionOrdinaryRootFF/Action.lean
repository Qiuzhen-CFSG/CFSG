module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceSelectionOrdinaryRootCore
public import Theory.Representation.NormalElementaryQuotient
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PCoreCentralKernelTransfer
public import Theory.GroupTheory.PerfectCenterFrattini
public import Theory.GroupTheory.ConjugateIntersectionCore
public import Theory.GroupTheory.ConjugateSpanFixedFactor
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ParabolicCores
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.OrthogonalCover
public import Theory.Representation.NormalElementaryQuotient.FixedIndex
public import Theory.GroupTheory.PerfectSmallNormalizer
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Action in the ordinary root argument before full-normalizer identification

This extension adapts the proofs in OrdinaryRootFF/Action, Kernel, Offender, BestOffender
to OutsideSymplecticMarking. Every actor is the literal original root
normalizer modulo the centralizer of the same full root span. No equality
H = N_G(K), secondary-component identification, or action classification is
added as a hypothesis. The constituent source arguments are documented below.
The final SourceSelectionOrdinaryComplete application discharges these inputs
and feeds the original uniqueness consumer.
-/



/-!
# The literal faithful action in the ordinary root argument

The actor is the actual root normalizer modulo the centralizer of its
normal closure U. The representation acts on U itself, with the original
conjugation formula. Reducedness makes the root two-core vanish in this
quotient. All subgroup images below use this one quotient projection.

Source: Aschbacher--Smith 4.3.6, printed p.615, following (*) and (**).
This construction does not assert the subsequent FF classification.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideRootFF
variable {G : Type*} [Group G] {T : Sylow 2 G} {L : Subgroup G}
  {c : OutsideChoice T L} {K0 : Subgroup c.H} {n : ℕ} (m : OutsideSymplecticMarking c K0 n)

/-- U inside its original normalizer, with no change of ambient group. -/
abbrev moduleSubgroup : Subgroup m.rootNormalizer :=
  m.rootSpan.subgroupOf m.rootNormalizer

instance moduleSubgroup_normal : (moduleSubgroup m).Normal :=
  normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)

/-- The source group G_Z^*. -/
abbrev Actor := m.rootNormalizer ⧸ centralizer (moduleSubgroup m : Set m.rootNormalizer)

/-- The quotient projection used for every source subgroup. -/
def projection : m.rootNormalizer →* Actor m :=
  QuotientGroup.mk' (centralizer (moduleSubgroup m : Set m.rootNormalizer))

def image (A : Subgroup G) : Subgroup (Actor m) :=
  (A.subgroupOf m.rootNormalizer).map (projection m)

theorem image_mono {A B : Subgroup G} (hAB : A ≤ B) : image m A ≤ image m B :=
  map_mono (fun _ hx => hAB hx)

theorem projection_kernel (hUN : m.rootSpan ≤ m.rootNormalizer) :
    (projection m).ker = (centralizer (m.rootSpan : Set G)).subgroupOf m.rootNormalizer := by
  rw [projection, QuotientGroup.ker_mk']
  ext x
  constructor
  · intro hx u hu
    exact congrArg Subtype.val (hx ⟨u, hUN hu⟩ hu)
  · intro hx u hu
    exact Subtype.ext (hx u hu)

/-- Conjugation descended to the actual centralizer quotient. -/
def representation (hr : IsPReduced 2 (moduleSubgroup m)) :
    letI := hr.elementary
    Representation (ZMod 2) (Actor m) (Additive (moduleSubgroup m)) :=
  letI := hr.elementary
  Representation.NormalElementaryQuotient.representation (moduleSubgroup m)
    (projection m) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)

theorem representation_injective (hr : IsPReduced 2 (moduleSubgroup m)) :
    letI := hr.elementary
    Function.Injective (representation m hr) := by
  let := hr.elementary
  exact Representation.NormalElementaryQuotient.representation_injective _ _ _ _

theorem representation_apply (hr : IsPReduced 2 (moduleSubgroup m)) :
    letI := hr.elementary
    ∀ (g : m.rootNormalizer) (u : Additive (moduleSubgroup m)),
      ((representation m hr (projection m g) u).toMul.val : G) =
        (g : G) * (u.toMul.val : G) * (g : G)⁻¹ := by
  let := hr.elementary
  intro g u
  exact congrArg Subtype.val
    (Representation.NormalElementaryQuotient.representation_apply _ _ _ _ g u)

/-- The source reducedness premise applies to precisely this actor. -/
theorem actor_pCore_eq_bot (hr : IsPReduced 2 (moduleSubgroup m)) :
    pCore 2 (Actor m) = ⊥ := hr.quotient_pCore_eq_bot

theorem core_le_kernel (hr : IsPReduced 2 (moduleSubgroup m)) :
    pCore 2 m.rootNormalizer ≤ (projection m).ker := by
  rw [projection, QuotientGroup.ker_mk']
  exact le_centralizer_iff.mp hr.le_centralizer_pCore

theorem core_image_eq_bot (hr : IsPReduced 2 (moduleSubgroup m)) :
    image m m.rootCore = ⊥ := by
  apply (Subgroup.map_eq_bot_iff _).mpr
  change ((pCore 2 m.rootNormalizer).map m.rootNormalizer.subtype).comap
    m.rootNormalizer.subtype ≤ _
  rw [comap_map_eq_self_of_injective m.rootNormalizer.subtype_injective]
  exact core_le_kernel m hr

theorem secondaryCore_le_rootCore {KZ : Subgroup G}
    (hKN : KZ ≤ m.rootNormalizer)
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G)) :
    KZ.pCoreIn 2 ≤ m.rootCore :=
  pCoreIn_mono_of_normalizes hKN hnormal

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideRootFF
end



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
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideRootFF
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : OutsideChoice T L} {K0 : Subgroup c.H} {n : ℕ} (m : OutsideSymplecticMarking c K0 n)

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

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideRootFF
end


/-!
# The actual ordinary-root failure-of-factorization module

The two marked radicals have equal order. Their mutual centralizers are their
intersection, using self-centralization inside the same symplectic carrier.
The supplied equality Q = R C_Q(W) therefore bounds |U:C_U(W)| by the order
of W's image in N/C_N(U). Reducedness kills R in that action, while normal
generation of J by W proves that W's image is nontrivial. This constructs an
offender on the faithful representation already defined in Action.

The final application restricts an actual best offender inside W's image to
the actual K_Z image. It proves the FF premise needed for B.5.1 without a
classification callback. The remaining odd-cubic exclusion and model-image
comparison remain with the ordinary-root classification owner.

Source: Aschbacher–Smith 4.3.6, printed p.615, following (*) and (**).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideRootFF
open Theory.SpecificGroups.SymplecticFour

private def pointCoordinates {F : Type*} [Field F] [CharP F 2] :
    pointRadical (F := F) ≃ (Fin 3 → F) where
  toFun q := ![q.val.val.val (.inl 1) (.inr 0), q.val.val.val (.inr 1) (.inr 0),
    q.val.val.val (.inl 0) (.inr 0)]
  invFun v := ⟨pointRadicalElement (v 0) (v 1) (v 2), pointRadicalElement_mem _ _ _⟩
  left_inv q := Subtype.ext (pointRadical_eq_element q.val q.property).symm
  right_inv v := by funext i; fin_cases i <;> rfl

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {c : OutsideChoice T L} {K0 : Subgroup c.H} {n : ℕ} (m : OutsideSymplecticMarking c K0 n)

omit [Finite G] in
theorem secondCore_card_eq_fullModule (hn : 1 < n) :
    Nat.card (m.second.pCoreIn 2) = Nat.card c.ordinaryModule := by
  rw [← m.pointRadical_image hn, ← m.planeRadical_image hn,
    card_map_of_injective m.modelEmbedding_injective,
    card_map_of_injective m.modelEmbedding_injective,
    card_map_of_injective pointLocal.subtype_injective,
    card_map_of_injective planeLocal.subtype_injective,
    Nat.card_congr (pointCoordinates (F := m.Field)),
    Nat.card_congr (Plane.OrthogonalCover.radicalCoordinates (F := m.Field)).toEquiv]
  rfl

include m in
omit [Finite G] in
theorem fullModule_elementary (hn : 1 < n) : IsElementaryAbelian 2 c.ordinaryModule := by
  rw [← m.planeRadical_image hn]
  let := Plane.radical_elementaryAbelian (F := m.Field)
  let := IsElementaryAbelian.map_subtype (p := 2) (H := Plane.radical (F := m.Field))
  exact IsElementaryAbelian.map m.modelEmbedding

omit [Finite G] in
theorem fullModule_inf_centralizer_secondCore (hn : 1 < n) :
    c.ordinaryModule ⊓ centralizer (m.second.pCoreIn 2 : Set G) =
      c.ordinaryModule ⊓ m.second.pCoreIn 2 := by
  let R : Subgroup (Sp m.Field) := pointRadicalAmbient
  let W : Subgroup (Sp m.Field) := planeRadicalAmbient
  have hc : W ⊓ centralizer (R : Set (Sp m.Field)) = W ⊓ R := by
    apply le_antisymm (inf_le_inf_left W (pointRadicalAmbient_selfCentralizing m.card hn))
    apply le_inf inf_le_left
    intro x hx r hr
    let := IsElementaryAbelian.map_subtype (p := 2) (H := pointRadical (F := m.Field))
    exact congrArg Subtype.val (mul_comm (⟨r, hr⟩ : R) ⟨x, hx.2⟩)
  have he := map_inf_centralizer_of_injective m.modelEmbedding m.modelEmbedding_injective W R
  rw [hc, map_inf _ _ _ m.modelEmbedding_injective] at he
  simpa only [show W.map m.modelEmbedding = c.ordinaryModule from m.planeRadical_image hn,
    show R.map m.modelEmbedding = m.second.pCoreIn 2 from m.pointRadical_image hn] using he

omit [Finite G] in
theorem secondCore_inf_centralizer_fullModule (hn : 1 < n) :
    m.second.pCoreIn 2 ⊓ centralizer (c.ordinaryModule : Set G) =
      m.second.pCoreIn 2 ⊓ c.ordinaryModule := by
  let R : Subgroup (Sp m.Field) := pointRadicalAmbient
  let W : Subgroup (Sp m.Field) := planeRadicalAmbient
  have hc : R ⊓ centralizer (W : Set (Sp m.Field)) = R ⊓ W := by
    apply le_antisymm (inf_le_inf_left R (planeRadicalAmbient_selfCentralizing m.card hn))
    apply le_inf inf_le_left
    intro x hx w hw
    let := IsElementaryAbelian.map_subtype (p := 2) (H := Plane.radical (F := m.Field))
    exact congrArg Subtype.val (mul_comm (⟨w, hw⟩ : W) ⟨x, hx.2⟩)
  have he := map_inf_centralizer_of_injective m.modelEmbedding m.modelEmbedding_injective R W
  rw [hc, map_inf _ _ _ m.modelEmbedding_injective] at he
  simpa only [show W.map m.modelEmbedding = c.ordinaryModule from m.planeRadical_image hn,
    show R.map m.modelEmbedding = m.second.pCoreIn 2 from m.pointRadical_image hn] using he

omit [Finite G] in
theorem image_card (hUN : m.rootSpan ≤ m.rootNormalizer)
    (A : Subgroup G) (hAN : A ≤ m.rootNormalizer) :
    Nat.card (image m A) = (centralizer (m.rootSpan : Set G)).relIndex A := by
  rw [image, ← relIndex_ker, projection_kernel m hUN, relIndex_subgroupOf hAN]

theorem fixedCodim_index (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (A : Subgroup G)
    (hAN : A ≤ m.rootNormalizer) :
    letI := hr.elementary
    (centralizer (A : Set G)).relIndex m.rootSpan =
      2 ^ fixedCodim (representation m hr) (image m A) := by
  let := hr.elementary
  have hc : centralizer (A.subgroupOf m.rootNormalizer : Set m.rootNormalizer) =
      (centralizer (A : Set G)).subgroupOf m.rootNormalizer := by
    ext x
    constructor
    · intro hx a ha
      exact congrArg Subtype.val (hx ⟨a, hAN ha⟩ ha)
    · intro hx a ha
      exact Subtype.ext (hx a ha)
  have he := Representation.NormalElementaryQuotient.centralizer_index_eq_fixedCodim
    (moduleSubgroup m) (projection m) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) (A.subgroupOf m.rootNormalizer)
  rw [hc, relIndex_subgroupOf hUN] at he
  exact he

omit [Finite G] in
theorem fullModule_image_ne_bot (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer)
    (hcore : m.second.pCoreIn 2 ≤ m.rootSpan) : image m c.ordinaryModule ≠ ⊥ := by
  intro he
  have hWN := (m.fullModule_le_second hn).trans m.second_le_rootNormalizer
  have hker := (Subgroup.map_eq_bot_iff _).mp he
  rw [projection_kernel m hUN] at hker
  have hWR : c.ordinaryModule ≤ m.second.pCoreIn 2 := by
    intro w hw
    have hc : w ∈ centralizer (m.second.pCoreIn 2 : Set G) :=
      centralizer_le hcore (hker (show (⟨w, hWN hw⟩ : m.rootNormalizer) ∈
        c.ordinaryModule.subgroupOf m.rootNormalizer from hw))
    exact ((fullModule_inf_centralizer_secondCore m hn).le ⟨hw,hc⟩).2
  have hJR : m.second ≤ m.second.pCoreIn 2 := by
    conv_lhs => rw [← m.fullModule_conjugateSpan_second hn]
    exact conjugateSpanBy_le hWR (m.second.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hi := image_mono m (hJR.trans (hcore.trans (span_le_core m hr hUN)))
  rw [core_image_eq_bot m hr] at hi
  exact second_image_ne_bot m hn hUN hcore (bot_unique hi)

theorem fullModule_isOffender (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer)
    (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G))) :
    letI := hr.elementary
    IsOffender (representation m hr) (image m c.ordinaryModule) := by
  let := hr.elementary
  let W := c.ordinaryModule
  let R := m.second.pCoreIn 2
  let CW := centralizer (W : Set G)
  let C := m.rootCore ⊓ CW
  have hRQ : R ≤ m.rootCore := hcore.trans (span_le_core m hr hUN)
  have hnC : C ≤ normalizer (R : Set G) := inf_le_left.trans
    (((core_centralizes_span m hr hUN).trans (centralizer_le hcore)).trans
      (Subgroup.centralizer_le_normalizer _))
  have hidx : CW.relIndex m.rootCore = CW.relIndex R := by
    have he := relIndex_sup_of_normalizes_left R C hnC
    change C.relIndex (R ⊔ C) = C.relIndex R at he
    rw [← hQ] at he
    have hleft : C.relIndex m.rootCore = CW.relIndex m.rootCore :=
      inf_relIndex_left _ _
    have hright : C.relIndex R = CW.relIndex R := by
      rw [← inf_relIndex_right C R, ← inf_relIndex_right CW R]
      congr 1
      ext x
      exact ⟨fun h => ⟨h.1.2,h.2⟩, fun h => ⟨⟨hRQ h.2,h.1⟩,h.2⟩⟩
    exact hleft.symm.trans (he.trans hright)
  have hsymm : CW.relIndex R = (centralizer (R : Set G)).relIndex W := by
    have hR := relIndex_mul_card_of_le (show R ⊓ CW ≤ R from inf_le_left)
    have hW := relIndex_mul_card_of_le
      (show W ⊓ centralizer (R : Set G) ≤ W from inf_le_left)
    rw [inf_relIndex_left, secondCore_inf_centralizer_fullModule m hn,
      secondCore_card_eq_fullModule m hn] at hR
    rw [inf_relIndex_left, fullModule_inf_centralizer_secondCore m hn, inf_comm W R] at hW
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := (R ⊓ W : Subgroup G)))
      (hR.trans hW.symm)
  have hbound : (centralizer (W : Set G)).relIndex m.rootSpan ≤
      Nat.card (image m W) := by
    rw [image_card m hUN W ((m.fullModule_le_second hn).trans m.second_le_rootNormalizer)]
    calc
      _ ≤ CW.relIndex m.rootCore := relIndex_le_of_le_right
        (span_le_core m hr hUN) index_ne_zero_of_finite
      _ = (centralizer (R : Set G)).relIndex W := hidx.trans hsymm
      _ ≤ _ := relIndex_le_of_le_left (centralizer_le hcore) index_ne_zero_of_finite
  let := fullModule_elementary m hn
  let := IsElementaryAbelian.subgroupOf (p := 2)
    ((m.fullModule_le_second hn).trans m.second_le_rootNormalizer)
  have ha : IsElementaryTwo (image m W) :=
    ⟨fullModule_image_ne_bot m hn hr hUN hcore, IsElementaryAbelian.map (projection m)⟩
  refine ⟨ha, ?_⟩
  rw [fixedCodim_index m hr hUN W
    ((m.fullModule_le_second hn).trans m.second_le_rootNormalizer), ha.card_eq_two_pow_rank] at hbound
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hbound

theorem exists_fullModule_bestOffender (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer)
    (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G))) :
    letI := hr.elementary
    ∃ A ≤ image m c.ordinaryModule, IsBestOffender (representation m hr) A := by
  let := hr.elementary
  exact (fullModule_isOffender m hn hr hUN hcore hQ).exists_bestOffender _

theorem secondary_isFFModule (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer)
    (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hJK : m.second ≤ KZ) :
    letI := hr.elementary
    IsFFModule ((representation m hr).comp (image m KZ).subtype) := by
  let := hr.elementary
  obtain ⟨A, hAW, hA⟩ := exists_fullModule_bestOffender m hn hr hUN hcore hQ
  have hAK : A ≤ image m KZ := hAW.trans (image_mono m ((m.fullModule_le_second hn).trans hJK))
  exact ⟨A.subgroupOf (image m KZ), (hA.subgroupOf (representation m hr) hAK).isOffender _⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideRootFF
end


/-!
# The marked full-module image is a best offender

An element of the plane radical outside the point radical has the same
centralizer in the point radical as the full plane radical. This is a direct
calculation in the original symplectic marking. The fixed-factor identity
Q = R C_Q(W) extends it to Q, so every nontrivial subgroup of W's actual
image fixes exactly C_U(W). The offender inequality and monotonicity of
subgroup order then show that the whole W-image is a best offender.

Source: Aschbacher–Smith 4.3.6, printed p.615, the FF* claim after (**).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative Pointwise Matrix
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideRootFF
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {c : OutsideChoice T L} {K0 : Subgroup c.H} {n : ℕ} (m : OutsideSymplecticMarking c K0 n)

private theorem plane_point_commute {F : Type*} [Field F] [CharP F 2]
    (w : Sp F) (hw : w ∈ planeRadicalAmbient) (hwn : w ∉ pointRadicalAmbient)
    (r : Sp F) (hr : r ∈ pointRadicalAmbient) (hc : Commute r w) :
    r ∈ planeRadicalAmbient := by
  obtain ⟨w, hw, rfl⟩ := hw
  obtain ⟨r, hr, rfl⟩ := hr
  let B := (Plane.radicalEquiv (⟨w,hw⟩ : Plane.radical)).toAdd
  have hwB : w = Plane.shear B :=
    congrArg Subtype.val (Plane.radicalEquiv.symm_apply_apply (⟨w,hw⟩ : Plane.radical)).symm
  have hsym : B.val 1 0 = B.val 0 1 := congrFun (congrFun B.property 0) 1
  have hB : B.val 1 1 ≠ 0 := by
    intro hz
    apply hwn
    refine ⟨pointRadicalElement (B.val 0 1) 0 (B.val 0 0), pointRadicalElement_mem _ _ _, ?_⟩
    rw [hwB]
    apply Subtype.ext
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      simp [pointRadicalElement, pointRadicalMatrix, Plane.shear, Plane.shearSp,
        Matrix.fromBlocks, hsym, hz]
  obtain ⟨u,v,z,he⟩ : ∃ u v z, r = pointRadicalElement u v z :=
    ⟨_,_,_,pointRadical_eq_element r hr⟩
  have hv : v = 0 := by
    have hm := congrArg (fun g : Sp F => g.val (.inl 0) (.inr 1)) hc.eq
    rw [hwB,he] at hm
    change (pointRadicalMatrix u v z * (Plane.shearSp B).val) (.inl 0) (.inr 1) =
      ((Plane.shearSp B).val * pointRadicalMatrix u v z) (.inl 0) (.inr 1) at hm
    simp [pointRadicalMatrix, Plane.shearSp, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two] at hm
    have hp : v * B.val 1 1 = 0 := by linear_combination hm
    exact (mul_eq_zero.mp hp).resolve_right hB
  subst v
  let C : Plane.symmetricMatrices F := ⟨!![z,u;u,0], by
    ext i j; fin_cases i <;> fin_cases j <;> rfl⟩
  refine ⟨Plane.shear C, Plane.quotientMap_shear C, ?_⟩
  rw [he]
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [C, pointRadicalElement, pointRadicalMatrix, Plane.shear, Plane.shearSp, Matrix.fromBlocks]

omit [Finite G] in
theorem fullModule_point_centralizer (hn : 1 < n)
    (w : G) (hw : w ∈ c.ordinaryModule) (hwn : w ∉ m.second.pCoreIn 2)
    (r : G) (hr : r ∈ m.second.pCoreIn 2) (hc : Commute r w) : r ∈ c.ordinaryModule := by
  obtain ⟨w',hw',hew⟩ := (m.planeRadical_image hn).ge hw
  obtain ⟨r',hr',her⟩ := (m.pointRadical_image hn).ge hr
  have hwr : w' ∉ pointRadicalAmbient := fun h => hwn
    (hew ▸ (m.pointRadical_image hn).le (mem_map_of_mem _ h))
  have hc' : Commute r' w' := by
    apply m.modelEmbedding_injective
    simpa only [map_mul,hew,her] using hc.eq
  exact her ▸ (m.planeRadical_image hn).le
    (mem_map_of_mem _ (plane_point_commute w' hw' hwr r' hr' hc'))

omit [Finite G] in
theorem core_centralizer_of_fullModule_element (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m)) (hUN : m.rootSpan ≤ m.rootNormalizer)
    (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (w : G) (hw : w ∈ c.ordinaryModule) (hwn : w ∉ m.second.pCoreIn 2)
    (q : G) (hq : q ∈ m.rootCore) (hc : Commute q w) :
    q ∈ centralizer (c.ordinaryModule : Set G) := by
  let R := m.second.pCoreIn 2
  let C := m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)
  have hnC : C ≤ normalizer (R : Set G) := inf_le_left.trans
    (((core_centralizes_span m hr hUN).trans (centralizer_le hcore)).trans
      (Subgroup.centralizer_le_normalizer _))
  have hp : q ∈ (R : Set G) * (C : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left R C hnC, ← hQ]
    exact hq
  obtain ⟨r,hr',d,hd,rfl⟩ := hp
  have hrw : Commute r w := by
    apply mul_right_cancel (b := d)
    calc
      (r*w)*d = (r*d)*w := by rw [mul_assoc,hd.2 w hw,← mul_assoc]
      _ = w*(r*d) := hc.eq
      _ = (w*r)*d := (mul_assoc _ _ _).symm
  have hrW := fullModule_point_centralizer m hn w hw hwn r hr' hrw
  let := fullModule_elementary m hn
  have hrC : r ∈ centralizer (c.ordinaryModule : Set G) := by
    intro a ha
    exact congrArg Subtype.val (mul_comm (⟨a,ha⟩ : c.ordinaryModule) ⟨r,hrW⟩)
  exact (centralizer (c.ordinaryModule : Set G)).mul_mem hrC hd.2

omit [Finite G] in
theorem fullModule_fixedSpace_eq (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m)) (hUN : m.rootSpan ≤ m.rootNormalizer)
    (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (B : Subgroup (Actor m)) (hB : B ≤ image m c.ordinaryModule) (hne : B ≠ ⊥) :
    letI := hr.elementary
    fixedSpace (representation m hr) B = fixedSpace (representation m hr) (image m c.ordinaryModule) := by
  let := hr.elementary
  obtain ⟨b,hb,hbne⟩ := B.bot_or_exists_ne_one.resolve_left hne
  obtain ⟨w,hw,hew⟩ := hB hb
  have hwn : (w : G) ∉ m.second.pCoreIn 2 := by
    intro hwR
    have hm : projection m w ∈ image m m.rootCore := mem_map_of_mem _
      (hcore.trans (span_le_core m hr hUN) hwR)
    rw [core_image_eq_bot m hr,mem_bot,hew] at hm
    exact hbne hm
  apply le_antisymm
  · intro v hv
    have he : representation m hr (projection m w) v = v := by
      rw [hew]
      exact hv ⟨b,hb⟩
    have hcomm := congrArg (fun x : Additive (moduleSubgroup m) => (x.toMul.val : G)) he
    rw [representation_apply m hr] at hcomm
    have huC := core_centralizer_of_fullModule_element m hn hr hUN hcore hQ w hw hwn
      v.toMul.val (span_le_core m hr hUN v.toMul.property)
      (mul_inv_eq_iff_eq_mul.mp hcomm).symm
    apply (Representation.NormalElementaryQuotient.mem_fixedSpace_image
      (moduleSubgroup m) (projection m) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _) (c.ordinaryModule.subgroupOf m.rootNormalizer) v).mpr
    intro a ha
    exact Subtype.ext (huC a ha)
  · intro v hv b'
    exact hv ⟨b',hB b'.property⟩

theorem fullModule_isBestOffender (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m)) (hUN : m.rootSpan ≤ m.rootNormalizer)
    (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G))) :
    letI := hr.elementary
    IsBestOffender (representation m hr) (image m c.ordinaryModule) := by
  let := hr.elementary
  have hoff := fullModule_isOffender m hn hr hUN hcore hQ
  refine ⟨hoff.1, ?_⟩
  intro B hB
  by_cases hb : B = ⊥
  · rw [hb,weight_bot]
    exact (fixedCodim_le_rank_iff _ _).mp hoff.2
  · unfold weight
    rw [fullModule_fixedSpace_eq m hn hr hUN hcore hQ B hB hb]
    apply Nat.add_le_add_right
    exact Nat.log_mono_right (Nat.card_le_card_of_injective (inclusion hB) (inclusion_injective hB))

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideRootFF
end
