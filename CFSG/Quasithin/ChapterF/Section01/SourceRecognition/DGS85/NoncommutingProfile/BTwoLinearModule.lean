module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoLinearSeed
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoResidual
public import Theory.Representation.BinaryConjugationSection.ComplementaryFixed
public import Theory.Representation.RankOne.QuadraticRecognition.ElementFixedSpaces

/-!
# The actual alpha-core module in the linear branch of (10.7)

The proved linear-beta saturation identifies the seed with Q_alpha. Its
literal elementary quotient by D_alpha therefore carries a canonical
SL₂(alpha) action through the original quotient map. The two conjugate
radius/core factors give complementary coordinate images and eliminate
all global fixed vectors. Their quadratic action and fixed-space generation
then construct a direct sum of natural modules over the alpha field.

Consequently the beta field order is a positive power of the alpha field
order. No restriction of this multiplicity to one or three is asserted.
Every nonidentity odd-order quotient actor has no fixed vectors on the
section, and C_Q_alpha(W_alpha) is exactly the source C_D_alpha(W_alpha).
These supply the module calculations used after (10.7); they do not prove
general saturation, residual separation (10.8), or exceptional recognition.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(5.11)--(5.12), pp.112--114, and (10.7)--(10.10), pp.158--165.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local instance linearModuleAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

/-- Construct the natural copies on the literal full-core quotient, retaining
the original quotient projection and the original alpha actor. -/
theorem BTwoCenterActionData.linear_core_natural_copies
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (eβ : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SL(2,K)) :
    ∃ hN : ((D F m t).subgroupOf (Q F v)).Normal, letI := hN
      ∃ hE : IsElementaryAbelian 2 (Q F v ⧸ (D F m t).subgroupOf (Q F v)), letI := hE
        ∃ σ : Representation (ZMod 2) SL(2,k)
            (Additive (Q F v ⧸ (D F m t).subgroupOf (Q F v))),
          ∃ d : BinaryConjugationSection c.actor (Q F v) (D F m t) (σ.comp c.quotient),
            (∀ x : Q F v, (d.coordinates x).toAdd =
              Additive.ofMul (QuotientGroup.mk' ((D F m t).subgroupOf (Q F v)) x)) ∧
            fixedSpace σ ⊤ = ⊥ ∧ SL2SylowFixedRecognition.NaturalCoordinates σ := by
  let := finite_endpoints h
  let : Finite (Q F v) := Finite.of_injective
    (inclusion (Q_le_stabilizer F v)) (inclusion_injective _)
  have hS := source_kernel_sylow h hB hSyl
  obtain ⟨_,hN,hE,_⟩ := c.linear_central_core_structure h hB hSyl hb hactor hcentral
    ht hne hcomm hnot eβ
  let := hN
  let := hE
  have hs := (c.linear_seed_eq_core_and_index h hB hSyl hS hb ht hne hnot eβ).1
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift h ht hne
  obtain ⟨a,ha,_⟩ := c.exists_oppositeGeometry h hS hb g hg hop
  have hnD : c.actor ≤ normalizer (D F m t : Set G) := ha ▸ a.normalized h hS hb
  have hnQ : c.actor ≤ normalizer (Q F v : Set G) := c.actor_le.trans
    (CommutingNontrivial.stabilizer_normalizes_Q F v)
  obtain ⟨σ,d,hd⟩ := exists_canonical c.actor (Q F v) (D F m t)
    c.core_le a.separated hnQ hnD c.quotient c.onto c.kernel
  refine ⟨hN,hE,σ,d,hd,?_⟩
  let A := V F m 1 ⊓ Q F v
  let C := V F t 1 ⊓ Q F v
  have hgen : Q F v = (A ⊔ C) ⊔ D F m t := hs.symm
  have hgv : (g : G) • v = v := c.actor_le g.property
  have hconj : C = A.conjBy (g : G) := by
    dsimp only [A,C]
    rw [conjBy,map_inf _ _ _ (MulAut.conj (g : G)).injective,←V_translate,←Q_translate,hg,hgv]
  have hZD : Z F v ≤ D F m t := (a.decomposition h hS hb) ▸ le_sup_left
  have hZm := (center_le_of_central_neighbor h hB hSyl c.middle hcentral).trans hZD
  have hVm := graph_V_le_Q_of_short h hS m (i := 1) (by rw [hb]; decide)
  have hVt := graph_V_le_Q_of_short h hS t (i := 1) (by rw [hb]; decide)
  have hfix : ⁅V F m 1,A⁆ ≤ D F m t :=
    ((commutator_mono le_rfl (inf_le_left.trans hVm)).trans hcomm).trans hZm
  have hinter : (A ⊔ D F m t) ⊓ (C ⊔ D F m t) = D F m t := by
    apply le_antisymm
    · exact inf_le_inf (sup_le (inf_le_left.trans hVm) inf_le_left)
        (sup_le (inf_le_left.trans hVt) inf_le_right)
    · exact le_inf le_sup_right le_sup_right
  have hfree := fixed_preimage_of_complementary_pair c.actor (Q F v) (D F m t)
    A C (V F m 1) σ c.quotient c.onto d inf_le_right inf_le_right hgen hinter
    g hconj c.imageSylow (c.radius_image h hS hb) hfix
  have hglobal := section_fixed_bot_of_commutators c.actor (Q F v) (D F m t)
    σ c.quotient d hfree
  have hgenerated := pair_section_generated c.actor (Q F v) (D F m t) A C
    (V F m 1) σ c.quotient d inf_le_right hgen g hconj hfix
  rw [c.radius_image h hS hb] at hgenerated
  have htriple := c.seed_quadratic_commutator h hS hb a.separated hZm hcomm
  rw [hs] at htriple
  have hquad := isQuadratic_of_triple_commutator_le c.actor (Q F v) (D F m t)
    (V F m 1) σ c.quotient d htriple
  rw [c.radius_image h hS hb] at hquad
  exact ⟨hglobal,sl2_natural_copies σ c.imageSylow hquad hgenerated hglobal⟩

/-- The beta field is a positive integral power of the alpha field. -/
theorem BTwoCenterActionData.linear_core_field_power
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (eβ : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SL(2,K)) :
    ∃ n : ℕ, 0 < n ∧ Nat.card K = Nat.card k ^ n := by
  obtain ⟨hN,hE,σ,d,_,_,n,E,_⟩ := c.linear_core_natural_copies h hB hSyl hb hactor
    hcentral ht hne hcomm hnot eβ
  let := hN
  let := hE
  obtain ⟨_,_,_,hcard⟩ := c.linear_central_core_structure h hB hSyl hb hactor hcentral
    ht hne hcomm hnot eβ
  have hc := Nat.card_congr E.toEquiv
  simp only [Nat.card_fun,Nat.card_fin] at hc
  change Nat.card (Q F v ⧸ (D F m t).subgroupOf (Q F v)) = _ at hc
  rw [hcard] at hc
  have he : Nat.card K = Nat.card k ^ n := by
    apply Nat.pow_left_injective (n := 2) (by decide)
    simpa only [←pow_mul,Nat.mul_comm] using hc
  have hk : 1 < Nat.card K := by
    let := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  refine ⟨n,?_,he⟩
  by_contra! hn
  have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
  rw [hn0,pow_zero] at he
  omega

/-- Nonidentity odd-order quotient actors have no fixed points outside D_alpha. -/
theorem BTwoCenterActionData.linear_core_odd_fixed
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (eβ : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SL(2,K))
    (a : c.actor) (ho : Odd (orderOf (c.quotient a))) (ha : c.quotient a ≠ 1)
    (x : G) (hx : x ∈ Q F v) (hax : ⁅x,(a : G)⁆ ∈ D F m t) : x ∈ D F m t := by
  obtain ⟨hN,hE,σ,d,_,_,hnatural⟩ := c.linear_core_natural_copies h hB hSyl hb hactor
    hcentral ht hne hcomm hnot eβ
  let := hN
  let := hE
  have hf := odd_fixed_eq_bot_of_natural_copies σ hnatural (c.quotient a)
    ho (pow_orderOf_eq_one _) ha
  have hv : (d.coordinates ⟨x,hx⟩).toAdd ∈ fixedSpace σ (zpowers (c.quotient a)) :=
    (mem_fixedSpace_zpowers_iff σ _ _).mpr ((d.fixed_coordinate_iff_commutator_mem a ⟨x,hx⟩).mpr hax)
  have hz : (d.coordinates ⟨x,hx⟩).toAdd = 0 := by simpa only [hf,Submodule.mem_bot] using hv
  exact (d.coordinates_eq_one_iff ⟨x,hx⟩).mp (Multiplicative.toAdd.injective hz)

/-- The source residual C_D(W) is also the centralizer of W in the whole core. -/
theorem BTwoCenterActionData.linear_core_residual_centralizer
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (eβ : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SL(2,K)) :
    ∃ g : c.actor, (g : G) • m = t ∧
      Q F v ⊓ centralizer ((Z F w ⊔ Z F ((g : G) • w) : Subgroup G) : Set G) =
        bTwoResidual F m t w ((g : G) • w) := by
  obtain ⟨hN,hE,σ,d,_,hglobal,_⟩ := c.linear_core_natural_copies h hB hSyl hb hactor
    hcentral ht hne hcomm hnot eβ
  let := hN
  let := hE
  have hS := source_kernel_sylow h hB hSyl
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift h ht hne
  obtain ⟨a,ha,_⟩ := c.exists_oppositeGeometry h hS hb g hg hop
  let H := Z F w ⊔ Z F ((g : G) • w)
  have hgen : H ⊔ Q F v = c.actor := a.actor_generators.symm.trans ha
  have hHL : H ≤ c.actor := le_sup_left.trans hgen.le
  have hfull : (H.subgroupOf c.actor).map c.quotient = ⊤ := by
    have hh := congrArg (fun R : Subgroup G => (R.subgroupOf c.actor).map c.quotient) hgen
    rw [subgroupOf_sup hHL c.core_le,Subgroup.map_sup,←c.kernel,Subgroup.map_ker_self,
      sup_bot_eq,subgroupOf_self,map_top_of_surjective _ c.onto] at hh
    exact hh
  refine ⟨g,hg,le_antisymm ?_ (inf_le_inf_right _ a.separated)⟩
  intro x hx
  refine ⟨?_,hx.2⟩
  have hfixed : (d.coordinates ⟨x,hx.1⟩).toAdd ∈ fixedSpace σ ⊤ := by
    intro y
    obtain ⟨z,hz,he⟩ := (show y.val ∈ (H.subgroupOf c.actor).map c.quotient from
      hfull.symm ▸ mem_top _)
    change σ y.val (d.coordinates ⟨x,hx.1⟩).toAdd = _
    rw [←he]
    apply (d.fixed_coordinate_iff_commutator_mem z ⟨x,hx.1⟩).mpr
    have hcommute : Commute x (z : G) := (hx.2 z hz).symm
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hcommute.eq]
    exact one_mem _
  have hz : (d.coordinates ⟨x,hx.1⟩).toAdd = 0 := by
    simpa only [hglobal,Submodule.mem_bot] using hfixed
  exact (d.coordinates_eq_one_iff ⟨x,hx.1⟩).mp (Multiplicative.toAdd.injective hz)

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
