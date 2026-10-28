module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.Setup
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Contracts

/-!
# Quotient generation for the other Lie-type cases of E.6.8

The quotient is the actual (L Q_L)/O₂(L Q_L), where Q_L = N_Q(L).
A family of subgroups generating the component image lifts to subgroups that,
together with the two-core, contain L. For the source applications Q_L = Q,
so the core lies in Q and hence in M. The block decomposition of E.6.7(1)
then puts every block-free lift in M, contradicting component escape.

This module proves that reduction, including the subgroup and kernel
transports. It does not construct the model parabolics or identify the S₈
exception. The full E.6.7 source statement is an explicit earlier theorem input;
the family of quotient subgroups is an output specification for the model
calculations, not a substitute for their construction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7(1)
and the invariant-parabolic argument in E.6.8, printed pp.246–248
(PDF pp.257–259).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes
open InvariantSubspaces.BlockSelection
variable {G : Type*} [Group G]

/-- The source N_Q(L); no ambient normality of L is assumed. -/
def componentNormalizer (Q L : Subgroup G) : Subgroup G :=
  Q ⊓ normalizer (L : Set G)

/-- The group in which the source two-core and quotient are computed. -/
def componentExtension (Q L : Subgroup G) : Subgroup G :=
  L ⊔ componentNormalizer Q L

abbrev ComponentQuotient (Q L : Subgroup G) :=
  componentExtension Q L ⧸ pCore 2 (componentExtension Q L)

def quotientMap (Q L : Subgroup G) : componentExtension Q L →* ComponentQuotient Q L :=
  QuotientGroup.mk' (pCore 2 (componentExtension Q L))

def componentImage (Q L : Subgroup G) : Subgroup (ComponentQuotient Q L) :=
  (L.subgroupOf (componentExtension Q L)).map (quotientMap Q L)

def sylowImage (Q L : Subgroup G) : Subgroup (ComponentQuotient Q L) :=
  ((componentNormalizer Q L).subgroupOf (componentExtension Q L)).map (quotientMap Q L)

/-- Full preimage in L Q_L, then its actual inclusion into G. -/
def quotientPreimage (Q L : Subgroup G) (P : Subgroup (ComponentQuotient Q L)) :
    Subgroup G :=
  (P.comap (quotientMap Q L)).map (componentExtension Q L).subtype

theorem componentNormalizer_eq {Q L : Subgroup G}
    (hN : Q ≤ normalizer (L : Set G)) : componentNormalizer Q L = Q :=
  inf_eq_left.mpr hN

theorem componentExtension_eq {Q L : Subgroup G}
    (hN : Q ≤ normalizer (L : Set G)) : componentExtension Q L = L ⊔ Q := by
  rw [componentExtension, componentNormalizer_eq hN]

theorem component_normal_in_extension (Q L : Subgroup G) :
    (L.subgroupOf (componentExtension Q L)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (show L ≤ componentExtension Q L from le_sup_left)).mpr
    (sup_le L.le_normalizer inf_le_right)

theorem quotientPreimage_le (Q L : Subgroup G) (P : Subgroup (ComponentQuotient Q L)) :
    quotientPreimage Q L P ≤ componentExtension Q L := map_subtype_le _

theorem mem_quotientPreimage {Q L : Subgroup G}
    {P : Subgroup (ComponentQuotient Q L)} {x : G}
    (hx : x ∈ componentExtension Q L) :
    x ∈ quotientPreimage Q L P ↔ quotientMap Q L ⟨x, hx⟩ ∈ P := by
  constructor
  · rintro ⟨y, hy, he⟩
    subst x
    exact hy
  · intro hp
    exact ⟨⟨x, hx⟩, hp, rfl⟩

/-- Pullback of the entire quotient is the actual extension, not G. -/
theorem quotientPreimage_top (Q L : Subgroup G) :
    quotientPreimage Q L ⊤ = componentExtension Q L := by
  ext x
  exact ⟨fun hx => quotientPreimage_le Q L ⊤ hx, fun hx => (mem_quotientPreimage hx).mpr (mem_top _)⟩

/-- The pullback kernel retains the central two-covers. -/
theorem quotientPreimage_bot (Q L : Subgroup G) :
    quotientPreimage Q L ⊥ = (componentExtension Q L).pCoreIn 2 := by
  simp only [quotientPreimage, quotientMap, MonoidHom.comap_bot, QuotientGroup.ker_mk']
  rfl

/-- Absence of chi-zero blocks is relative to the local overgroup D.
The intrinsic type is evaluated on the actual ambient subgroup B. -/
def NoChiZeroBlocks (D : Subgroup G) : Prop :=
  ∀ B : Subgroup G, B ≤ D → (B.subgroupOf D).IsSubnormal →
    ¬ ChapterC.IsChiZeroBlock B

/-- Applying the full source E.6.7 conclusion to a block-free group forces
it into M. Its relative subnormality and empty central product are retained. -/
theorem le_of_blockDecomposition {M Q V U D : Subgroup G}
    (d : E67Decomposition Q M V U D) (hfree : NoChiZeroBlocks D) : D ≤ M := by
  have hempty : IsEmpty (Fin d.count) :=
    ⟨fun i => hfree (d.block i) (d.le i) (d.subnormal i) (d.type i)⟩
  let := hempty
  have hspan : (⨆ i, d.block i) = ⊥ := iSup_of_empty _
  calc
    D = (D ⊓ M) ⊔ ⨆ i, d.block i := d.generated
    _ = D ⊓ M := by rw [hspan, sup_bot_eq]
    _ ≤ M := inf_le_right

/-- The geometric output needed from each excluded model. The P_i are
subgroups of the specified quotient, preserved by the actual Q_L image.
Model proofs construct them as parabolics; no label alone supplies a field. -/
structure BlockFreeQuotientFamily (Q L : Subgroup G) where
  count : ℕ
  subgroup : Fin count → Subgroup (ComponentQuotient Q L)
  le_component : ∀ i, subgroup i ≤ componentImage Q L
  invariant : ∀ i, sylowImage Q L ≤ normalizer (subgroup i : Set (ComponentQuotient Q L))
  characteristic_two : ∀ i,
    HasCharacteristicTwo ↥(quotientPreimage Q L (subgroup i) ⊔ Q)
  no_blocks : ∀ i, NoChiZeroBlocks (quotientPreimage Q L (subgroup i) ⊔ Q)
  generate : componentImage Q L ≤ ⨆ i, subgroup i

variable [Finite G] {K : GroupClass} {T : Sylow 2 G} {M V U Q L : Subgroup G}

/-- V lies in the source normalizer and is central in Q_L. -/
theorem V_le_componentNormalizer (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V) :
    V ≤ componentNormalizer Q L ⊓ centralizer (componentNormalizer Q L : Set G) := by
  have hVQ : V ≤ Q := hQ ▸ h.le_sylowCentralizer
  have hQV : Q ≤ centralizer (V : Set G) := hQ ▸ inf_le_right
  exact le_inf (le_inf hVQ (component_normalized_by_V h hU hL))
    ((le_centralizer_iff.mpr hQV).trans (centralizer_le inf_le_left))

omit [Finite G] in
theorem componentExtension_le_centralizer
    (hU : U ≤ V) (hL : L ≤ centralizer (U : Set G))
    (hQ : Q = sylowCentralizer (T : Subgroup G) V) :
    componentExtension Q L ≤ centralizer (U : Set G) := by
  have hc : Q ≤ centralizer (U : Set G) := by
    rw [hQ]
    exact inf_le_right.trans (centralizer_le hU)
  exact sup_le hL (inf_le_left.trans hc)

/-- Once the earlier component theorem gives Q_L = Q, restriction of the
actual Sylow subgroup supplies the Sylow of L Q_L. -/
theorem extension_sylow (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hN : Q ≤ normalizer (L : Set G)) :
    ∃ S : Sylow 2 (componentExtension Q L),
      (S : Subgroup (componentExtension Q L)).map (componentExtension Q L).subtype = Q := by
  have hQE : Q ≤ componentExtension Q L := by
    rw [componentExtension_eq hN]
    exact le_sup_right
  obtain ⟨S, hS⟩ := h.sylow_obstructionIntermediate hU
    (hQ ▸ hQE) (componentExtension_le_centralizer hU.1 hL.1 hQ)
  exact ⟨S, hS.trans hQ.symm⟩

/-- The source Q_L image is a Sylow subgroup of the literal core quotient. -/
theorem quotient_sylow (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hN : Q ≤ normalizer (L : Set G)) :
    ∃ S : Sylow 2 (ComponentQuotient Q L), (S : Subgroup _) = sylowImage Q L := by
  obtain ⟨S, hS⟩ := extension_sylow h hU hL hQ hN
  have hQE : Q ≤ componentExtension Q L := by
    rw [componentExtension_eq hN]
    exact le_sup_right
  have he : (S : Subgroup (componentExtension Q L)) = Q.subgroupOf (componentExtension Q L) := by
    apply map_injective (componentExtension Q L).subtype_injective
    rw [hS, map_subgroupOf_eq_of_le hQE]
  refine ⟨S.mapSurjective (f := quotientMap Q L) (QuotientGroup.mk'_surjective _), ?_⟩
  change (S : Subgroup (componentExtension Q L)).map (quotientMap Q L) = _
  rw [he, sylowImage, componentNormalizer_eq hN]

/-- The V-image lies in the center of the actual Q_L-image. This assertion
uses the quotient map and is valid even before proving Q_L = Q. -/
theorem quotient_V_central (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V) :
    (V.subgroupOf (componentExtension Q L)).map (quotientMap Q L) ≤
      sylowImage Q L ⊓ centralizer (sylowImage Q L : Set (ComponentQuotient Q L)) := by
  have hc := V_le_componentNormalizer h hU hL hQ
  rintro x ⟨v, hv, rfl⟩
  refine ⟨mem_map_of_mem (quotientMap Q L) (hc hv).1, ?_⟩
  rintro y ⟨q, hq, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact (hc hv).2 q hq

/-- The full two-core is in Q, so quotient generation loses no uncontrolled
kernel. This does not identify the kernel with the component center. -/
theorem extension_core_le_Q (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hN : Q ≤ normalizer (L : Set G)) : (componentExtension Q L).pCoreIn 2 ≤ Q := by
  obtain ⟨S, hS⟩ := extension_sylow h hU hL hQ hN
  exact (map_mono (pCore_isPGroup.le_sylow_of_normal S)).trans hS.le

omit [Finite G] in
/-- Generation in the quotient, with its kernel controlled, implies actual
containment of L in M. No order argument substitutes for the quotient maps. -/
theorem le_of_quotient_generation (hLMcore : (componentExtension Q L).pCoreIn 2 ≤ M)
    {ι : Sort*} (P : ι → Subgroup (ComponentQuotient Q L))
    (hgen : componentImage Q L ≤ ⨆ i, P i)
    (hP : ∀ i, quotientPreimage Q L (P i) ≤ M) : L ≤ M := by
  let E := componentExtension Q L
  let q := quotientMap Q L
  have hker : q.ker ≤ M.subgroupOf E := by
    rw [show q.ker = pCore 2 E from QuotientGroup.ker_mk' _]
    intro x hx
    exact hLMcore (mem_map_of_mem E.subtype hx)
  have hPi (i : ι) : P i ≤ (M.subgroupOf E).map q := by
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 E) x
    exact mem_map_of_mem q (hP i (mem_map_of_mem E.subtype hx))
  have himage : componentImage Q L ≤ (M.subgroupOf E).map q :=
    hgen.trans (iSup_le hPi)
  have hle : L.subgroupOf E ≤ M.subgroupOf E := by
    have hh := (map_le_iff_le_comap.mp himage)
    rwa [comap_map_eq_self hker] at hh
  intro x hx
  exact hle (show (⟨x, (show L ≤ E from le_sup_left) hx⟩ : E) ∈ L.subgroupOf E from hx)

/-- The invariant-parabolic exclusion in E.6.8, conditional on construction
of the genuine model family and the full earlier E.6.7 theorem. -/
theorem exclude_of_blockFreeQuotientFamily (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hN : Q ≤ normalizer (L : Set G))
    (blocks : E67Input T M V)
    (family : BlockFreeQuotientFamily Q L) : False := by
  have hQM : Q ≤ M := by
    rw [hQ]
    exact inf_le_left.trans h.sylow_le
  have hEH := componentExtension_le_centralizer hU.1 hL.1 hQ
  have hQE : Q ≤ componentExtension Q L := by
    rw [componentExtension_eq hN]
    exact le_sup_right
  apply component_not_le h earlier hU hL
  apply le_of_quotient_generation ((extension_core_le_Q h hU hL hQ hN).trans hQM)
    family.subgroup family.generate
  intro i
  have hlocal : quotientPreimage Q L (family.subgroup i) ⊔ Q ≤ centralizer (U : Set G) :=
    sup_le ((quotientPreimage_le Q L _).trans hEH) (hQE.trans hEH)
  obtain ⟨d⟩ := blocks U hU _ (hQ ▸ le_sup_right) hlocal (family.characteristic_two i)
  exact le_sup_left.trans (le_of_blockDecomposition d (family.no_blocks i))

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes
