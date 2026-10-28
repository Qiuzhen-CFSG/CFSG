module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSeedMovement
public import Theory.Representation.BinaryConjugationSection.FixedImage

/-!
# Fixed-generated moving coordinates for the central seed

The first radius/core factor is fixed by V_beta modulo D; the second
is its conjugate by the retained opposite lift. Their images generate the
seed quotient, proving the fixed-generation hypothesis required by the
published correction to 5.12. The preceding residual displacement theorem
also detects nontrivial O^2(L_alpha) action in every coordinate realization.

Combining these facts with the constructed elementary quotient gives a
quadratic, fixed-generated and nontrivially moved representation on that
literal quotient. An SL2 action through the core quotient and equality
of the seed with Q_alpha are not asserted here.
Source: DGS, Groups and Graphs (1985), proof of 10.7, pp.158--159,
and the fixed-generation correction to 5.12.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped Pointwise commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The literal radius/core factors supply fixed-space generation. This is
the published correction required when 5.12 is applied to the seed. -/
theorem BTwoCenterActionData.seed_fixedSpace_generated
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m)
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) c.actor M)
    (e : BinaryConjugationSection c.actor (centralSeed F v m t) (D F m t) ρ) :
    GeneratedByFixedSpace ρ ((V F m 1).subgroupOf c.actor) := by
  let := finite_endpoints h
  have hS := source_kernel_sylow h hB hSyl
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift h ht hne
  obtain ⟨d,_,_⟩ := c.exists_oppositeGeometry h hS hb g hg hop
  have hZD : Z F v ≤ D F m t := (d.decomposition h hS hb) ▸ le_sup_left
  have hZm := (center_le_of_central_neighbor h hB hSyl c.middle hcentral).trans hZD
  have hV := graph_V_le_Q_of_short h hS m (i := 1) (by rw [hb]; decide)
  have hgv : (g : G) • v = v := c.actor_le g.property
  have hc : V F t 1 ⊓ Q F v = (V F m 1 ⊓ Q F v).conjBy (g : G) := by
    rw [conjBy,map_inf _ _ _ (MulAut.conj (g : G)).injective,←V_translate,←Q_translate,hg,hgv]
  have hfix : ⁅V F m 1,V F m 1 ⊓ Q F v⁆ ≤ D F m t :=
    ((commutator_mono le_rfl (inf_le_left.trans hV)).trans hcomm).trans hZm
  have hh := BinaryConjugationSection.pair_section_generated
    c.actor (centralSeed F v m t) (D F m t) (V F m 1 ⊓ Q F v)
    (V F t 1 ⊓ Q F v) (V F m 1) ρ (MonoidHom.id c.actor)
    (by simpa only [MonoidHom.comp_id] using e)
    (le_sup_left.trans le_sup_left) rfl g hc hfix
  simpa only [Subgroup.map_id] using hh

/-- The earlier obstruction forces genuine movement on every coordinate
realization of the seed quotient, by the literal local two-residual. -/
theorem BTwoCenterActionData.seed_residual_fixed_ne_top
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) c.actor M)
    (e : BinaryConjugationSection c.actor (centralSeed F v m t) (D F m t) ρ) :
    fixedSpace ρ (pResidual 2 c.actor) ≠ ⊤ := by
  intro hf
  apply c.seed_residual_not_le_D h hB hSyl hb ht hne hnot
  rw [commutator_comm]
  apply e.commutator_le_of_imageSpace_fixed _ _ (map_subtype_le _) le_rfl
  have hr : ((pResidual 2 c.actor).map c.actor.subtype).subgroupOf c.actor =
      pResidual 2 c.actor := by
    exact comap_map_eq_self_of_injective c.actor.subtype_injective _
  rw [hr,hf]
  exact le_top

/-- A quadratic, fixed-space-generated, nontrivially moved module on the
actual seed quotient. No quotient action through SL2 or V=Q premise is used. -/
theorem BTwoCenterActionData.central_seed_moving_representation
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G)) :
    ∃ hN : ((D F m t).subgroupOf (centralSeed F v m t)).Normal,
      letI := hN
      ∃ hE : IsElementaryAbelian 2 (centralSeed F v m t ⧸
        (D F m t).subgroupOf (centralSeed F v m t)),
      letI := hE
      ∃ ρ : Representation (ZMod 2) c.actor (Additive (centralSeed F v m t ⧸
        (D F m t).subgroupOf (centralSeed F v m t))),
        Nonempty (BinaryConjugationSection c.actor
          (centralSeed F v m t) (D F m t) ρ) ∧
        IsQuadratic ρ ((V F m 1).subgroupOf c.actor) ∧
        GeneratedByFixedSpace ρ ((V F m 1).subgroupOf c.actor) ∧
        fixedSpace ρ (pResidual 2 c.actor) ≠ ⊤ := by
  obtain ⟨hN,hE,ρ,⟨e⟩,hq⟩ := c.central_seed_representation h hB hSyl hb hactor
    hcentral ht hne hcomm
  refine ⟨hN,hE,ρ,⟨e⟩,hq,?_,?_⟩
  · exact c.seed_fixedSpace_generated h hB hSyl hb hcentral ht hne hcomm ρ e
  · exact c.seed_residual_fixed_ne_top h hB hSyl hb ht hne hnot ρ e

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
