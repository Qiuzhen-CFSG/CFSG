module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticQuotient
public import Theory.GroupTheory.CenterFreeOddImageCore

/-!
# The ambient order of the original symplectic block

The original residual supplements a Sylow two-subgroup of the center-free
overgroup. Therefore its centralizer in the ambient two-core is trivial.
The central fixed part of its intrinsic block lies in that intersection,
so the block itself has the same order as its natural module quotient.
In the Sp4(4) row this gives order 256 for its literal image in G.

The original residual lies outside the distinguished maximal local group
and normalizes this same ambient block. The final conditional constructor
uses these facts with the literal plane surjection and equivariant natural
quotient. Constructing those two maps and proving whole-block recognition
remain with qt-d-tensor-sp4-plane; they are not asserted here.

Source: Aschbacher--Smith 9.3.6, 9.3.10 and the final paragraph of 9.3,
printed pp.734--735.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.InternalThompsonAction
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e}

namespace GenerationTwoOvergroup
variable (c : m.GenerationTwoOvergroup)

/-- Center-freeness of the original overgroup kills the central part of its block. -/
theorem blockFixed_eq_bot : ChapterC.blockFixed (pResidual 2 c.M) = ⊥ := by
  let K := pResidual 2 c.M
  obtain ⟨S,hS⟩ := c.sylow
  have he : (S : Subgroup c.M) =
      ((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M := by
    apply Subgroup.map_injective c.M.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le (c.generated ▸ le_sup_right)]
  have hcover : K ⊔ (S : Subgroup c.M) = ⊤ := by
    apply eq_top_iff.mpr
    intro g _
    obtain ⟨k,hk,r,hr,rfl⟩ := c.component_product.2.2.2 g
    exact (K ⊔ (S : Subgroup c.M)).mul_mem
      ((show K ≤ K ⊔ (S : Subgroup c.M) from le_sup_left) hk)
      ((show (S : Subgroup c.M) ≤ K ⊔ (S : Subgroup c.M) from le_sup_right)
        (by rwa [he]))
  have hc := inf_centralizer_eq_bot_of_centerfree_sylow_supplement S K (pCore 2 c.M)
    hcover pCore_isPGroup c.fitting_center.2
  have hQ : (pCore 2 K).map K.subtype ≤ pCore 2 c.M :=
    le_sSup ⟨inferInstance,pCore_isPGroup.map K.subtype⟩
  apply le_bot_iff.mp
  intro u hu
  have hum : (u.val : c.M) ∈ pCore 2 c.M ⊓ centralizer (K : Set c.M) := by
    refine ⟨hQ (mem_map_of_mem K.subtype (ChapterC.blockU_le_core u.property)),?_⟩
    intro k hk
    exact congrArg Subtype.val ((mem_center_iff.mp hu) ⟨k,hk⟩)
  have hz : (u.val : c.M) = 1 := mem_bot.mp (hc ▸ hum)
  exact Subtype.ext (Subtype.ext hz)

/-- The ambient image of the intrinsic block has the full required order 256. -/
theorem blockU_ambient_card (hblock : ChapterC.IsSp4FourBlock (pResidual 2 c.M)) :
    Nat.card (((ChapterC.blockU (pResidual 2 c.M)).map
      (pResidual 2 c.M).subtype).map c.M.subtype) = 256 := by
  rw [card_map_of_injective c.M.subtype_injective,
    card_map_of_injective (pResidual 2 c.M).subtype_injective]
  have he : Nonempty (ChapterC.blockU (pResidual 2 c.M) ≃*
      ChapterC.BlockModule (pResidual 2 c.M)) := by
    exact ⟨MulEquiv.ofBijective (QuotientGroup.mk' (ChapterC.blockFixed (pResidual 2 c.M)))
      ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk',c.blockFixed_eq_bot]),
        QuotientGroup.mk'_surjective _⟩⟩
  obtain ⟨d⟩ := he
  rw [Nat.card_congr d.toEquiv,hblock.module_card]
  decide

/-- The original residual, which normalizes its intrinsic block, lies outside M. -/
theorem residual_outside : ¬ (pResidual 2 c.M).map c.M.subtype ≤ D.maximalLocal := by
  intro hK
  apply c.outside
  intro g hg
  obtain ⟨k,hk,r,hr,hkr⟩ := c.component_product.2.2.2 ⟨g,hg⟩
  have hkM : (k : G) ∈ D.maximalLocal := hK (mem_map_of_mem c.M.subtype hk)
  have hrM : (r : G) ∈ D.maximalLocal := le_normalizer_componentOrbit L T hr.1
  have hh := D.maximalLocal.mul_mem hkM hrM
  change c.M.subtype (k*r) ∈ D.maximalLocal at hh
  rw [hkr] at hh
  exact hh

/-- The actual outside component normalizes the ambient block subgroup. -/
theorem residual_normalizes_blockU :
    (pResidual 2 c.M).map c.M.subtype ≤ normalizer
      (((ChapterC.blockU (pResidual 2 c.M)).map
        (pResidual 2 c.M).subtype).map c.M.subtype : Set G) := by
  let i := c.M.subtype.comp (pResidual 2 c.M).subtype
  have hn := (ChapterC.blockU (pResidual 2 c.M)).le_normalizer_map i
  rw [normalizer_eq_top,←MonoidHom.range_eq_map,MonoidHom.range_comp,range_subtype] at hn
  simpa only [i,map_map] using hn

end GenerationTwoOvergroup


open ClassicalOrthogonal.FourPlusMatrix
/-- Once the literal plane maps are constructed, the block order, outside
component and normalization fields follow on the original ambient subgroups. -/
theorem originalPlaneModel_of_block_maps (c : m.GenerationTwoOvergroup)
    (hblock : ChapterC.IsSp4FourBlock (pResidual 2 c.M)) :
    let U := ((ChapterC.blockU (pResidual 2 c.M)).map
      (pResidual 2 c.M).subtype).map c.M.subtype
    ∀ (q : L →* planeLocal (F := Binary.F)), Function.Surjective q →
      q.ker = U.subgroupOf L →
    ∀ (p : D.fullModule.subgroupOf L →* Multiplicative (Fin 2 → Binary.F)),
      Function.Surjective p →
      p.ker ≤ (U.subgroupOf L).comap (D.fullModule.subgroupOf L).subtype →
      (letI := fullModule_component_normal (D := D)
       ∀ (g : L) (v : D.fullModule.subgroupOf L),
         p (MulAut.conjNormal g v) = Multiplicative.ofAdd
           ((Plane.quotientMap (q g)).val.mulVec (p v).toAdd)) →
      Nonempty (OriginalPlaneModel D) := by
  intro U q hq hk p hp hpk he
  exact ⟨{ U := U
           K := (pResidual 2 c.M).map c.M.subtype
           quotient := q
           onto := hq
           kernel := hk
           natural := p
           natural_onto := hp
           natural_kernel := hpk
           equivariant := he
           card := c.blockU_ambient_card hblock
           normalized := c.residual_normalizes_blockU
           outside := c.residual_outside }⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
