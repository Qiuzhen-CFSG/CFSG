module
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.ComponentSections
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.Setup
/-!
# The rank-one block torus in the original E.6.11 section

The product (L ∩ M) = (L ∩ Q)X and Q ≤ C_G(V) make X a complement
to C_L(V). Its regular action on the original [V,X] proves disjointness
and faithfulness; no independent quotient action is substituted.
The E.6.7 direct decomposition and moved-space order identify the precise
field exponent with the original fixed-space corank.

At the actual global minimum, source maximality and E.6.9 eliminate the
local odd core and identify C_V(L) with U. The selected block and this
torus then construct every field of the E.6.24–25 regular-section input.
Source block selection and the intrinsic regular torus remain their earlier
producer's obligations.
Source: Aschbacher–Smith, E.6.7(3), E.6.11(2–3a), printed pp.246,249–250.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
open Components LocalFactors
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L X : Subgroup G}

/-- The literal E.6.7 product and regular action supply the intrinsic torus contract. -/
theorem torusAction_of_rankOne_data
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hLH : L ≤ centralizer (U : Set G))
    {n : ℕ} (hn : 1 < n)
    (hXP : X ≤ L ⊓ M) (hcyc : IsCyclic X) (hcard : Nat.card X = 2 ^ n - 1)
    (hgen : V = (V ⊓ centralizer (L : Set G)) ⊔ ⁅V,X⁆)
    (hWcard : Nat.card ↥⁅V,X⁆ = 2 ^ n)
    (hprod : ((L ⊓ M : Subgroup G) : Set G) =
      ((L ⊓ sylowCentralizer (T : Subgroup G) V : Subgroup G) : Set G) * (X : Set G))
    (hreg : RegularConjugationOnNonidentity X ⁅V,X⁆) : TorusAction M V L X n := by
  have hWV : ⁅V,X⁆ ≤ V :=
    (le_sup_right : ⁅V,X⁆ ≤ (V ⊓ centralizer (L : Set G)) ⊔ ⁅V,X⁆).trans hgen.symm.le
  have hcomp : (L ⊓ centralizer (V : Set G)) ⊔ X = L ⊓ M := by
    apply le_antisymm
    · exact sup_le (le_inf inf_le_left (inf_le_right.trans h.centralizer_le)) hXP
    · intro p hp
      have hp' : p ∈ ((L ⊓ sylowCentralizer (T : Subgroup G) V : Subgroup G) : Set G) *
          (X : Set G) := by rw [←hprod];exact hp
      obtain ⟨q,hq,x,hx,rfl⟩ := hp'
      exact ((L ⊓ centralizer (V : Set G)) ⊔ X).mul_mem
        ((le_sup_left : L ⊓ centralizer (V : Set G) ≤
          (L ⊓ centralizer (V : Set G)) ⊔ X) ⟨hq.1,hq.2.2⟩)
        ((le_sup_right : X ≤ (L ⊓ centralizer (V : Set G)) ⊔ X) hx)
  have hdis : (L ⊓ centralizer (V : Set G)) ⊓ X = ⊥ := by
    have hlarge : 1 < Nat.card ↥⁅V,X⁆ := by
      rw [hWcard]
      exact one_lt_pow₀ (by decide) (by omega)
    let : Nontrivial ↥⁅V,X⁆ := Finite.one_lt_card_iff_nontrivial.mp hlarge
    obtain ⟨w,hw⟩ := exists_ne (1 : ↥⁅V,X⁆)
    obtain ⟨z,_,hz⟩ := hreg.2 w hw w hw
    apply le_bot_iff.mp
    intro x hx
    apply mem_bot.mpr
    have hxf : x * (w : G) * x⁻¹ = w := by
      rw [←mem_centralizer_iff.mp hx.1.2 w (hWV w.property)]
      simp
    have h1f : ((1 : X) : G) * (w : G) * ((1 : X) : G)⁻¹ = w := by simp
    exact congrArg Subtype.val ((hz ⟨x,hx.2⟩ hxf).trans (hz 1 h1f).symm)
  have he : Nonempty (X ≃* Multiplicative (ZMod (2 ^ n - 1))) := by
    rw [←hcard]
    exact ⟨(zmodCyclicMulEquiv hcyc).symm⟩
  refine ⟨hXP,he,hcomp,hdis,
    commutator_eq_of_centralizing_sup hcomp inf_le_right
      (hXP.trans (component_intersection_normalizes h hU hLH)),hreg.1,?_⟩
  intro a ha ha1 b hb hb1
  exact hreg.2 ⟨a,ha⟩ (fun he => ha1 (congrArg Subtype.val he))
    ⟨b,hb⟩ (fun he => hb1 (congrArg Subtype.val he))

/-- The actual rank-one source torus supplies the block branch at the original minimum. -/
theorem block_regularSection_of_minimum
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hmin : (subgroupCorank V U : ℕ∞) = globalR V)
    (hr : 1 < subgroupCorank V U)
    (hLC : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G)))
    (hb : Hyperplanes.Enlargement.BlockInspection.CentralizerBlock U L)
    (hesc : ¬ L ≤ M) (hVL : V ≤ normalizer (L : Set G))
    {n : ℕ} (hLn : ChapterC.IsL2EvenBlock L n)
    (hXP : X ≤ L ⊓ M) (hcyc : IsCyclic X) (hcard : Nat.card X = 2 ^ n - 1)
    (hgen : V = (V ⊓ centralizer (L : Set G)) ⊔ ⁅V,X⁆)
    (hdis : Disjoint (V ⊓ centralizer (L : Set G)) ⁅V,X⁆)
    (hWcard : Nat.card ↥⁅V,X⁆ = 2 ^ n)
    (hprod : ((L ⊓ M : Subgroup G) : Set G) =
      ((L ⊓ sylowCentralizer (T : Subgroup G) V : Subgroup G) : Set G) * (X : Set G))
    (hB : L2BlockBorel L (M.subgroupOf L) n)
    (hreg : RegularConjugationOnNonidentity X ⁅V,X⁆) :
    Nonempty (MinimalRegularSection T M V U) := by
  let _ := h.elementary
  have hmax := h.maximal_escape_of_minimum hmin
  have ho := h.oddCore_eq_bot_of_maximal_escape (source_earlierLocalFacts h) hU hmax hr
  have hfixed : V ⊓ centralizer (L : Set G) = U :=
    (fixedSpace_eq_of_maximal_escape hU.1 hmax hLC.1 hesc).symm
  have hWV : ⁅V,X⁆ ≤ V :=
    (le_sup_right : ⁅V,X⁆ ≤ (V ⊓ centralizer (L : Set G)) ⊔ ⁅V,X⁆).trans hgen.symm.le
  have hWN : ⁅V,X⁆ ≤ normalizer (V ⊓ centralizer (L : Set G) : Set G) :=
    hWV.trans (V.le_centralizer.trans
      ((Subgroup.centralizer_le inf_le_left).trans (Subgroup.centralizer_le_normalizer _)))
  have hc := corank_of_direct_decomposition hgen hWN hdis hWcard
  rw [hfixed] at hc
  subst n
  have ht := torusAction_of_rankOne_data h hU hLC.1 hr hXP hcyc hcard hgen hWcard hprod hreg
  have hgen' : V = U ⊔ ⁅V,X⁆ := by simpa only [hfixed] using hgen
  have hdis' : U ⊓ ⁅V,X⁆ = ⊥ := by simpa only [hfixed] using hdis.eq_bot
  have hB' : L2BlockBorel L ((L ⊓ M).subgroupOf L) (subgroupCorank V U) := by
    simpa only [inf_subgroupOf_left] using hB
  exact ⟨⟨L,X,hLC,hesc,
    regularSection_of_torus h ho hU (Or.inr hb) hVL hfixed hgen' hdis' hr ht,
    hXP.trans inf_le_left,hfixed,Or.inr hLn,Or.inl ⟨hXP.trans inf_le_left,hB'⟩⟩⟩

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
