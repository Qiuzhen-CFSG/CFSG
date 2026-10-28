module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Interface
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.BlockObstructions
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.GeneratorCover
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection


/-!
# Reducing the Higman–Sims block calculation to local geometry

Source: Aschbacher–Smith, 2.3.9(7), printed p.526, and GLS, volume 3,
Table 5.3m and the discussion of the faithful action on the elementary
abelian subgroup of order eight in the normalizer of `4³`.

The intended local group comes from the `4³.L₃(2)` normalizer, adjoined to
the supplied Sylow subgroup. Its normal two-perfect section can have several
factors when that Sylow subgroup permutes conjugates of the component.
The section is identified by an actual isomorphism, with both the outer
two-group quotient and the intrinsic two-core retained. A short subnormal
block then gives a subnormal subgroup of this direct power.

The other generating subgroup is the actual centralizer of the supplied
involution. We use its image in `L/O₂(L)`, rather than assuming that a
quotient-centralizing element has a centralizing lift. The inverse image of
the normalizer retains all of `O₂(L)`. Containment of the two published HS
generators in the quotient join proves the required generation upstairs.
The `2⁴.S₆` entry in Table 5.3m has two-part `2⁸`, whereas HS has two-part
`2⁹`, so that entry alone is not a Sylow overgroup.

These are conditional reductions. `LocalGeometry` has to be constructed
from the specified carrier and actual action. The separate `SectionOrders`
module proves `LinearThreeSectionOrders` using the structure of subnormal
subgroups of direct powers. Together these inputs imply the requested
`CentralizerBlockCover`; no geometry is supplied by a family tag.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.HigmanSims

open ChapterC Theory.GroupTheory Sporadic.LeechRelated.HS

/-- The concrete binary special linear group, not a group-family tag. -/
abbrev LinearThreeTwo := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

/-- The independent direct-power calculation, proved in `SectionOrders`:
quasisimple subnormal subgroups have order 168, and none has order three. -/
def LinearThreeSectionOrders : Prop :=
  ∀ (n : ℕ) (I : Subgroup (Fin n → LinearThreeTwo)), I.IsSubnormal →
    (IsQuasisimple I → Nat.card I = 168) ∧ Nat.card I ≠ 3

/-- A short subnormal block in such a local section cannot be an allowed
chi-zero block, once the independent direct-power calculation is proved. -/
theorem not_chiZero_of_normalDirectPowerSection
    (horders : LinearThreeSectionOrders) {K : Type*} [Group K] [Finite K]
    (d : NormalDirectPowerSection 2 K LinearThreeTwo)
    (B : Subgroup K) (hB : IsBlock B) : ¬ IsChiZeroBlock B := by
  obtain ⟨I, hI, ⟨e⟩⟩ := d.exists_subnormal_quotient_image B hB.subnormal hB.short.twoPerfect
  have hc : Nat.card (B ⧸ pCore 2 B) = Nat.card I := Nat.card_congr e.toEquiv
  rcases hB.short.quotient with hs | h3
  · let := hs
    have hIs := IsQuasisimple.of_mulEquiv e
    exact LieType.not_chiZero_of_quotient_card_168 (hc.trans ((horders _ I hI).1 hIs))
  · exact ((horders _ I hI).2 (hc.symm.trans h3)).elim

variable {G : Type*} [Group G] {L : Subgroup G} {z : G}

/-- The supplied quotient isomorphism composed with the actual two-core quotient. -/
noncomputable def quotientMap (d : SporadicQuotientInput L z .hs) : L →* Carrier :=
  d.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

/-- No surjectivity assumption beyond the supplied equivalence is needed. -/
theorem quotientMap_surjective (d : SporadicQuotientInput L z .hs) :
    Function.Surjective (quotientMap d) :=
  d.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)

/-- The quotient map retains exactly the source two-kernel. -/
theorem quotientMap_ker (d : SporadicQuotientInput L z .hs) :
    (quotientMap d).ker = pCore 2 L := by
  ext x
  change d.quotientIso (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ x ∈ pCore 2 L
  simp only [QuotientGroup.mk'_apply]
  constructor
  · intro hx
    apply (QuotientGroup.eq_one_iff x).mp
    apply d.quotientIso.injective
    simpa only [map_one] using hx
  · intro hx
    rw [(QuotientGroup.eq_one_iff x).mpr hx, map_one]

/-- Only genuinely centralizing elements of L are used in the quotient. -/
noncomputable def centralizerImage (d : SporadicQuotientInput L z .hs) : Subgroup Carrier :=
  ((centralizer ({z} : Set G)).subgroupOf L).map (quotientMap d)

/-- Adjoin the supplied Sylow subgroup to the full inverse image of P.
This definition also allows S to permute component conjugates. -/
noncomputable def localOvergroup (S : Subgroup G) (d : SporadicQuotientInput L z .hs)
    (P : Subgroup Carrier) : Subgroup G :=
  (P.comap (quotientMap d)).map L.subtype ⊔ S

/-- Every constructed overgroup contains the supplied subgroup. -/
theorem le_localOvergroup (S : Subgroup G) (d : SporadicQuotientInput L z .hs)
    (P : Subgroup Carrier) : S ≤ localOvergroup S d P := le_sup_right

/-- The constructed overgroup stays inside the source group LS. -/
theorem localOvergroup_le (S : Subgroup G) (d : SporadicQuotientInput L z .hs)
    (P : Subgroup Carrier) : localOvergroup S d P ≤ L ⊔ S :=
  sup_le_sup_right (map_subtype_le _) S

/-- The full embedded two-core is retained, including a central two-cover. -/
theorem pCoreIn_le_localOvergroup (S : Subgroup G) (d : SporadicQuotientInput L z .hs)
    (P : Subgroup Carrier) : L.pCoreIn 2 ≤ localOvergroup S d P := by
  rintro x ⟨y, hy, rfl⟩
  apply (show (P.comap (quotientMap d)).map L.subtype ≤ localOvergroup S d P from
    le_sup_left)
  refine ⟨y, ?_, rfl⟩
  change quotientMap d y ∈ P
  have hk : y ∈ (quotientMap d).ker := (quotientMap_ker d).symm ▸ hy
  rw [MonoidHom.mem_ker.mp hk]
  exact P.one_mem

/-- Quotient generator coverage lifts to generation with the actual centralizer;
the full kernel already lies in the inverse-image local subgroup. -/
theorem generated_of_generators (S : Subgroup G) (d : SporadicQuotientInput L z .hs)
    (P : Subgroup Carrier)
    (ha : generatorAElement ∈ centralizerImage d ⊔ P)
    (hb : generatorBElement ∈ centralizerImage d ⊔ P) :
    L ≤ centralizer ({z} : Set G) ⊔ localOvergroup S d P := by
  let U := centralizer ({z} : Set G) ⊔ localOvergroup S d P
  have hP : P ≤ (U.subgroupOf L).map (quotientMap d) := by
    intro x hx
    obtain ⟨y, rfl⟩ := quotientMap_surjective d x
    refine ⟨y, ?_, rfl⟩
    exact (show localOvergroup S d P ≤ U from le_sup_right)
      ((show (P.comap (quotientMap d)).map L.subtype ≤ localOvergroup S d P from
        le_sup_left) ⟨y, hx, rfl⟩)
  have hC : centralizerImage d ≤ (U.subgroupOf L).map (quotientMap d) := by
    apply map_mono
    exact comap_mono le_sup_left
  have htop : (U.subgroupOf L).map (quotientMap d) = ⊤ :=
    eq_top_of_generators_mem _ ((sup_le hC hP) ha) ((sup_le hC hP) hb)
  have hk : (quotientMap d).ker ≤ U.subgroupOf L := by
    intro x hx
    have hp : x ∈ P.comap (quotientMap d) := by
      change quotientMap d x ∈ P
      rw [MonoidHom.mem_ker.mp hx]
      exact P.one_mem
    exact (show localOvergroup S d P ≤ U from le_sup_right)
      ((show (P.comap (quotientMap d)).map L.subtype ≤ localOvergroup S d P from
        le_sup_left) ⟨x, hp, rfl⟩)
  have he := congrArg (Subgroup.comap (quotientMap d)) htop
  have hU : U.subgroupOf L = ⊤ := by
    simpa only [comap_map_eq, sup_eq_left.mpr hk, comap_top] using he
  exact subgroupOf_eq_top.mp hU

/-- The missing concrete normalizer calculation. These data assert actual
local structure and generator coverage; they do not assume a block obstruction. -/
structure LocalGeometry (S : Subgroup G) (d : SporadicQuotientInput L z .hs) where
  localSubgroup : Subgroup Carrier
  generatorA : generatorAElement ∈ centralizerImage d ⊔ localSubgroup
  generatorB : generatorBElement ∈ centralizerImage d ⊔ localSubgroup
  even : localOvergroup S d localSubgroup ∈ Chapter1.He G
  quotientSection : NormalDirectPowerSection 2 (localOvergroup S d localSubgroup) LinearThreeTwo

/-- Self-centralization forces the local two-core to be nontrivial, since the
overgroup contains the supplied nonidentity involution. -/
theorem localOvergroup_mem_HeOver {H M : Subgroup G} {S : Sylow 2 H}
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .hs)
    (g : LocalGeometry ((S : Subgroup H).map H.subtype) d) :
    localOvergroup ((S : Subgroup H).map H.subtype) d g.localSubgroup ∈
      Chapter1.HeOver G (((S : Subgroup H).map H.subtype) : Set G) := by
  let K := localOvergroup ((S : Subgroup H).map H.subtype) d g.localSubgroup
  have hz : z ∈ K := le_localOvergroup _ d g.localSubgroup h.mem_sylow
  refine ⟨g.even, ?_, le_localOvergroup _ d g.localSubgroup⟩
  change K.pCoreIn 2 ≠ ⊥
  intro he
  have hc : z ∈ centralizer (K.pCoreIn 2 : Set G) := by
    apply mem_centralizer_iff.mpr
    intro y hy
    have hy : y = 1 := by simpa only [he, Subgroup.coe_bot, Set.mem_singleton_iff] using hy
    simp [hy]
  have hm := g.even ⟨hz, hc⟩
  rw [he, mem_bot] at hm
  have := h.involution
  rw [hm, orderOf_one] at this
  norm_num at this

/-- Conditional final assembly: the concrete geometry and the independent
direct-power calculation must both be supplied before this gives an HS cover. -/
noncomputable def centralizerBlockCover_of_localGeometry {H M : Subgroup G}
    {S : Sylow 2 H} (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .hs)
    (g : LocalGeometry ((S : Subgroup H).map H.subtype) d)
    (horders : LinearThreeSectionOrders) :
    CentralizerBlockCover L M ((S : Subgroup H).map H.subtype) z := by
  let := h.finite
  let K := localOvergroup ((S : Subgroup H).map H.subtype) d g.localSubgroup
  refine { locals := {K}, generated := ?_, within := ?_, even := ?_, obstruction := ?_ }
  · simpa only [sSup_singleton] using generated_of_generators _ d g.localSubgroup g.generatorA g.generatorB
  · intro J hJ
    have he : J = K := Set.mem_singleton_iff.mp hJ
    subst J
    exact localOvergroup_le _ d g.localSubgroup
  · intro J hJ
    have he : J = K := Set.mem_singleton_iff.mp hJ
    subst J
    exact localOvergroup_mem_HeOver h d g
  · intro J hJ
    have he : J = K := Set.mem_singleton_iff.mp hJ
    subst J
    intro B hB _
    exact (not_chiZero_of_normalDirectPowerSection horders g.quotientSection B hB.1 hB.2).elim

end CFSG.Quasithin.Chapter2.ComponentRefinement.HigmanSims
