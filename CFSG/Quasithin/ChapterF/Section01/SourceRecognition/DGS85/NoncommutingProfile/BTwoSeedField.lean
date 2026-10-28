module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSeedGeneration
public import Theory.Representation.SL2.ExtensionFieldDegree
public import Theory.Representation.BinaryConjugationSection.ImageDimensions

/-!
# The defining-field bound for the central seed

The radius-one actor has the prescribed Sylow image in the original
SL₂ quotient. Nontrivial O²-action survives on an irreducible section of
the seed module; the normal two-core acts trivially on that section.
The SL₂ displacement bound therefore applies without assuming that the
whole seed representation factors through the core quotient.

One radius/core factor is fixed modulo D. The two factors have equal
orders and their product is the seed quotient, bounding the fixed index
above by the order of either factor. Together these bounds prove the
first numerical inequality on p.159. The binary field case follows from
nontrivial residual movement. Saturation of the seed with Q_alpha and
identification of this factor order with q_beta remain separate steps.

Source: DGS, Groups and Graphs (1985), proof of 10.7, printed pp.158--159.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The whole radius-one actor has the same literal quotient image as
its contained critical center: the prescribed Sylow of SL₂(k). -/
theorem BTwoCenterActionData.radius_image
    (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x))
    (hb : b F = 2) {v m w : Vertex F}
    (c : BTwoCenterActionData F v m w k W) :
    ((V F m 1).subgroupOf c.actor).map c.quotient = c.imageSylow := by
  apply le_antisymm
  · rw [←c.neighbor_image]
    exact map_mono (comap_mono (graph_V_le_Q_of_short h hS m (by rw [hb]; decide)))
  · rw [←c.critical_image]
    apply map_mono
    apply comap_mono
    exact le_iSup_of_le w (le_iSup_of_le ((mem_ball_one _ _ _).mpr (Or.inl c.terminal)) le_rfl)

/-- The first numerical estimate of 10.7, before saturation: the source
field order is at most the order of either radius/core factor modulo D.
A nontrivial residual constituent supplies the lower bound without
assuming that the whole seed action descends through the two-core. -/
theorem BTwoCenterActionData.central_seed_field_bound
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
    Nat.card k ≤ (D F m t).relIndex (V F m 1 ⊓ Q F v) := by
  let := finite_endpoints h
  let : Finite c.actor := Finite.of_injective (inclusion c.actor_le) (inclusion_injective _)
  have hS := source_kernel_sylow h hB hSyl
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift h ht hne
  obtain ⟨d,hd,_⟩ := c.exists_oppositeGeometry h hS hb g hg hop
  have hJQ : centralSeed F v m t ≤ Q F v :=
    sup_le (sup_le inf_le_right inf_le_right) d.separated
  let : Finite (centralSeed F v m t) := Finite.of_injective
    (inclusion (hJQ.trans (Q_le_stabilizer F v))) (inclusion_injective _)
  obtain ⟨hN,hE,ρ,⟨e⟩,_,_,hmove⟩ := c.central_seed_moving_representation
    h hB hSyl hb hactor hcentral ht hne hcomm hnot
  let := hN
  let := hE
  let M := Additive (centralSeed F v m t ⧸ (D F m t).subgroupOf (centralSeed F v m t))
  let A := V F m 1 ⊓ Q F v
  let T := (V F m 1).subgroupOf c.actor
  let a := (D F m t).relIndex A
  have hcardM : Nat.card M = a^2 := by
    obtain ⟨_,hh⟩ := c.central_seed_card_square h hB hSyl hb hactor hcentral ht hne hcomm
    exact hh
  have hAJ : A ≤ centralSeed F v m t := le_sup_left.trans le_sup_left
  have hAcard : Nat.card (e.imageSpace A) = a := e.imageSpace_card_eq_relIndex A hAJ
  have ha : 0 < a := hAcard ▸ (Nat.card_pos : 0 < Nat.card (e.imageSpace A))
  have hZD : Z F v ≤ D F m t := (d.decomposition h hS hb) ▸ le_sup_left
  have hZm := (center_le_of_central_neighbor h hB hSyl c.middle hcentral).trans hZD
  have hV := graph_V_le_Q_of_short h hS m (i := 1) (by rw [hb]; decide)
  have hfix : e.imageSpace A ≤ fixedSpace ρ T := by
    intro x hx z
    exact e.fixed_on_imageSpace_of_commutator_le (V F m 1) A
      (((commutator_mono le_rfl (inf_le_left.trans hV)).trans hcomm).trans hZm)
      z z.property x hx
  have hfixcard : a ≤ Nat.card (fixedSpace ρ T) := by
    rw [←hAcard]
    exact Nat.card_le_card_of_injective _ (Submodule.inclusion_injective hfix)
  have hmul := Submodule.card_eq_card_quotient_mul_card (fixedSpace ρ T)
  change Nat.card M = Nat.card (fixedSpace ρ T) * Nat.card (M ⧸ fixedSpace ρ T) at hmul
  rw [Nat.mul_comm] at hmul
  have hupper : Nat.card (M ⧸ fixedSpace ρ T) ≤ a := by
    apply Nat.le_of_mul_le_mul_right (c := a) _ ha
    calc
      Nat.card (M ⧸ fixedSpace ρ T) * a ≤
          Nat.card (M ⧸ fixedSpace ρ T) * Nat.card (fixedSpace ρ T) :=
        Nat.mul_le_mul_left _ hfixcard
      _ = a*a := by rw [←hmul,hcardM,pow_two]
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  let n := Module.finrank (ZMod 2) k
  have hfield : Nat.card k = 2^n := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  by_cases hn : 1 < n
  · have hmap : T.map c.quotient = c.imageSylow := c.radius_image h hS hb
    have hp : IsPGroup 2 c.quotient.ker := by
      rw [c.kernel]
      exact (isPGroup_pCoreIn 2 (stabilizer F v)).comap_subtype
    have hnt : T.map c.quotient ≠ ⊥ := by
      intro hh
      have hc := Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 c.imageSylow).toEquiv
      have hsc : Nat.card c.imageSylow = Nat.card k := hc.symm
      rw [hmap] at hh
      have hsc' : Nat.card c.imageSylow = 1 := by
        rw [hh,card_bot]
      have hk2 : 1 < Nat.card k := by
        let := Fintype.ofFinite k
        rw [Nat.card_eq_fintype_card]
        exact Fintype.one_lt_card
      omega
    have hl := Representation.SL2.extension_fixedCodim_lower c.quotient c.onto hp ρ hmove T
      (hmap.symm ▸ c.imageSylow.isPGroup') hnt hn hfield
    apply le_trans _ hupper
    rw [hfield,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide) hl
  · have hk2 : Nat.card k ≤ 2 := by
      rw [hfield]
      simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show n ≤ 1 by omega)
    have ha2 : 2 ≤ a := by
      by_contra hlt
      have ha1 : a = 1 := by omega
      have hM1 : Nat.card M = 1 := by rw [hcardM,ha1,one_pow]
      let : Subsingleton M := (Nat.card_eq_one_iff_unique.mp hM1).1
      apply hmove
      apply top_unique
      intro x _ z
      exact Subsingleton.elim _ _
    exact hk2.trans ha2

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
