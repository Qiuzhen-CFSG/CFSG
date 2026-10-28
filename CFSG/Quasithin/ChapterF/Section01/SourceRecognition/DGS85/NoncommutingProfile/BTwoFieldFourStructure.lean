module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalFrattini
public import Theory.GroupAction.ThreeFixedFreeSpecial64
public import Theory.ElementaryAbelian.ExtraspecialPrimeAbelianBound
public import Theory.GroupTheory.PGroup.RankTwoFour
public import Theory.GroupAction.CardFourCubic

/-!
# The field-four alpha core and involutions in the adjacent intersection

The extraspecial beta core has no abelian subgroup of index two. The
literal adjacent-core index therefore makes the alpha core nonabelian.
Its constructed fixed-point-free cubic, central elementary quotient and
order sixty-four now identify its center, derived subgroup and Frattini
subgroup with the actual Z_alpha.

The beta elementary-rank bound also places every involution in
Q_beta intersect Q_alpha in Z_alpha. This is the disjointness input for
the invariant four-group complements required by (5.16); existence of
those complements and parabolic recognition remain separate obligations.
The beta Cartan centralizes the alpha four-group, because it fixes a
nonzero point supplied by the central beta center.
The companion source application discharges extraspeciality and rank
using the previously constructed original quintic actor.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(5.16), pp.116--117, and the field-four case of (10.9), p.163.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local instance fieldFourStructureAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

/-- The field-four alpha core is special, with the literal natural center. -/
theorem BTwoCenterActionData.field_four_alpha_special
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
    (hD : D F m t = Z F v) (E : W ≃ₗ[ZMod 2] (Fin 2 → k))
    (hk : Nat.card k = 2) (hK : Nat.card K = 4)
    (hExtra : IsExtraspecial 2 (Q F m)) :
    Nat.card (Q F v) = 64 ∧
      (center (Q F v)).map (Q F v).subtype = Z F v ∧
      (commutator (Q F v)).map (Q F v).subtype = Z F v ∧
      (frattini (Q F v)).map (Q F v).subtype = Z F v := by
  let : IsExtraspecial 2 (Q F m) := hExtra
  let := finite_endpoints h
  let : Finite (Q F v) := Finite.of_injective
    (inclusion (Q_le_stabilizer F v)) (inclusion_injective _)
  let : Finite (Q F m) := Finite.of_injective
    (inclusion (Q_le_stabilizer F m)) (inclusion_injective _)
  have hc := c.exceptional_linear_core_orders h hB hSyl hb hactor hcentral ht hne
    hcomm hnot eβ hD E
  have hQa : Nat.card (Q F v) = 64 := by simpa [hk,hK] using hc.1
  have hQb : Nat.card (Q F m) = 32 := by simpa [hk,hK] using hc.2
  have hi := relIndex_ker (K := (Q F m).subgroupOf c.actor) c.quotient
  rw [c.kernel,relIndex_subgroupOf c.neighbor_core_le,c.neighbor_image] at hi
  have hindex : ((Q F v).subgroupOf (Q F m)).index = 2 := hi.trans
    ((Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 c.imageSylow).symm.toEquiv).trans hk)
  have hI : Nat.card ((Q F v).subgroupOf (Q F m)) = 16 := by
    have hh := ((Q F v).subgroupOf (Q F m)).card_mul_index
    rw [hindex,hQb] at hh
    omega
  have hn : ¬ IsMulCommutative (Q F v) := by
    intro ha
    let := ha
    have hh := extraspecial_prime_abelian_card_sq_le_any (p := 2)
      ((Q F v).subgroupOf (Q F m))
    rw [hI,hQb] at hh
    omega
  have hZQ : Z F v ≤ Q F v := (source_Z_Q_U h v).1.trans (map_subtype_le _)
  let Z₀ := (Z F v).subgroupOf (Q F v)
  have hΦ := c.exceptional_linear_frattini h hB hSyl hb hactor hcentral ht hne
    hcomm hnot eβ hD E
  have hΦ₀ : frattini (Q F v) = Z₀ := by
    apply map_injective (Q F v).subtype_injective
    rw [hΦ,map_subgroupOf_eq_of_le hZQ]
  let hN : Z₀.Normal := hΦ₀ ▸ inferInstance
  have hp : IsPGroup 2 (Q F v) := isPGroup_pCoreIn 2 (stabilizer F v)
  let : IsElementaryAbelian 2 (Q F v ⧸ Z₀) :=
    @elementary_quotient_of_frattini_le (Q F v) _ _ 2 _ hp Z₀ hN hΦ₀.le
  have hZc : Z₀ ≤ center (Q F v) := by
    intro z hz
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (graph_Q_centralizes_Z h v x.property z hz).symm
  have hZcard : Nat.card Z₀ = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZQ).toEquiv,
      c.central_center_card E (c.omega_eq_bot_of_central_neighbor h hB hSyl hactor hcentral),hk]
    norm_num
  obtain ⟨a,_,_,ha,hfree⟩ := c.exceptional_linear_cubic h hB hSyl hb hactor hcentral
    ht hne hcomm hnot eβ hD
  obtain ⟨hcenter,hderived,hfrattini⟩ := three_fixed_free_special64 hQa Z₀ hZc hZcard
    hn (c.coreConjugation a) ha hfree
  refine ⟨hQa,?_,?_,hΦ⟩
  · rw [hcenter,map_subgroupOf_eq_of_le hZQ]
  · rw [hderived,map_subgroupOf_eq_of_le hZQ]

/-- The beta rank bound places every involution of the adjacent-core
intersection in the actual alpha center. -/
theorem BTwoCenterActionData.square_one_intersection
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hω : omegaCenterIn c.actor = ⊥)
    (hk : Nat.card k = 2)
    (hrank : ∀ A : Subgroup (Q F m), IsElementaryAbelian 2 A → Nat.card A < 8)
    (x : G) (hx : x ∈ Q F m ⊓ Q F v) : x ^ 2 = 1 ↔ x ∈ Z F v := by
  let := finite_endpoints h
  let : Finite (Q F m) := Finite.of_injective
    (inclusion (Q_le_stabilizer F m)) (inclusion_injective _)
  let : IsElementaryAbelian 2 (Z F v) := graph_Z_elementary h v
  have hZQ : Z F v ≤ Q F m := graph_Z_le_Q_of_short h
    (source_kernel_sylow h hB hSyl) (by
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr c.middle,hb]
      decide)
  let Z₁ := (Z F v).subgroupOf (Q F m)
  let : IsElementaryAbelian 2 Z₁ := IsElementaryAbelian.subgroupOf hZQ
  have hc : Nat.card Z₁ = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZQ).toEquiv,c.central_center_card E hω,hk]
    norm_num
  constructor
  · intro hxx
    have hm : (⟨x,hx.1⟩ : Q F m) ∈ Z₁ :=
      mem_four_of_square_eq_one_of_elementary_card_lt_eight hrank Z₁ hc
        (Subtype.ext hxx) (by
          intro z hz
          exact Subtype.ext (graph_Q_centralizes_Z h v hx.2 z hz))
    exact hm
  · exact elemPow_eq_one_of_isElementaryAbelian x

/-- A cubic beta actor centralizes the binary alpha center: it fixes a
nonzero beta-center point in this four-group. -/
theorem BTwoCenterActionData.binary_beta_cubic_centralizes_center
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v m w : Vertex F} (c : BTwoCenterActionData F v m w k W)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (hZm : Z F m ≠ ⊥)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hω : omegaCenterIn c.actor = ⊥)
    (hk : Nat.card k = 2) (a : G)
    (hav : a ∈ stabilizer F v) (ham : a ∈ graphLocalGroup F m) (ha : a ^ 3 = 1) :
    a ∈ centralizer (Z F v : Set G) := by
  let := finite_endpoints h
  let : Finite (Z F v) := Finite.of_injective
    (inclusion (Z_le_stabilizer F v)) (inclusion_injective _)
  let ρ : stabilizer F v →* MulAut (Z F v) :=
    (Z F v).normalizerMonoidHom.comp
      (inclusion (CommutingNontrivial.stabilizer_normalizes_Z F v))
  let a₀ : stabilizer F v := ⟨a,hav⟩
  have hρ : (ρ a₀) ^ 3 = 1 := by
    rw [←map_pow,show a₀ ^ 3 = 1 from Subtype.ext ha,map_one]
  have hcard : Nat.card (Z F v) = 4 := by
    rw [c.central_center_card E hω,hk]
    norm_num
  obtain ⟨z,hz⟩ := ne_bot_iff_exists_ne_one.mp hZm
  let z₀ : Z F v := ⟨z,center_le_of_central_neighbor h hB hSyl c.middle hcentral z.property⟩
  have hz₀ : z₀ ≠ 1 := by
    intro he
    apply hz
    apply Subtype.ext
    exact congrArg (fun x : Z F v => (x : G)) he
  have hfix : ρ a₀ z₀ = z₀ := by
    apply Subtype.ext
    change a * (z : G) * a⁻¹ = (z : G)
    rw [(hcentral z.property).2 a ham,mul_inv_cancel_right]
  have htrivial : ρ a₀ = 1 := by
    by_contra hn
    exact Theory.GroupAction.CardFourCubic.moves_nonidentity hcard (ρ a₀) hρ hn z₀ hz₀ hfix
  intro x hx
  have he := congrArg (fun f : MulAut (Z F v) => (f ⟨x,hx⟩ : G)) htrivial
  change a*x*a⁻¹=x at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
