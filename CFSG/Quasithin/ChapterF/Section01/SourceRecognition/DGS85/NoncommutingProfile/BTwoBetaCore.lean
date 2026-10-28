module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSeedIntersections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSeedField

/-!
# The beta-core product and Frattini subgroup in (10.7)

The radius-one group and the beta core have the same image in the marked
alpha quotient. Lifting this equality and using the adjacent-core product
therefore gives Q_beta = V_beta D_alpha without seed saturation or any
choice of beta quotient model.

In the central branch D_alpha is elementary. The earlier (7.4)(d) bound
puts the radius-one squares and its commutators with Q_beta in Z_beta.
The product formula then puts every square of Q_beta in Z_beta. The exact
(7.4)(d) identity gives the reverse Frattini containment, proving both
Phi(Q_beta) = Z_beta and Q_beta' = Z_beta. This is clause (10.7)(c);
it does not establish seed saturation or the recognition alternatives.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(7.4)(d), p.128, (10.4), pp.155--156, and (10.7)(c), pp.158--159.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The literal beta core is the product of its radius-one group and D_alpha. -/
theorem BTwoCenterActionData.beta_core_product
    (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x))
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (ht : (graph F).Adj v t) (hne : t ≠ m) :
    Q F m = V F m 1 ⊔ D F m t := by
  have hV := graph_V_le_Q_of_short h hS m (i := 1) (by rw [hb]; decide)
  have hi := c.seed_adjacent_intersection h hS hb ht hne
  have hm : ((Q F m).subgroupOf c.actor).map c.quotient =
      ((V F m 1).subgroupOf c.actor).map c.quotient :=
    c.neighbor_image.trans (c.radius_image h hS hb).symm
  apply le_antisymm _ (sup_le hV inf_le_left)
  intro x hx
  let xL : c.actor := ⟨x,c.neighbor_core_le hx⟩
  have hxI : c.quotient xL ∈ ((V F m 1).subgroupOf c.actor).map c.quotient := by
    rw [←hm]
    exact mem_map_of_mem _ hx
  obtain ⟨a,ha,he⟩ := hxI
  have hxk : xL * a⁻¹ ∈ c.quotient.ker := by
    change c.quotient (xL * a⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hxQa : x * (a : G)⁻¹ ∈ Q F v := by
    have hh : xL * a⁻¹ ∈ (Q F v).subgroupOf c.actor := c.kernel ▸ hxk
    exact hh
  have hxQm : x * (a : G)⁻¹ ∈ Q F m := (Q F m).mul_mem hx ((Q F m).inv_mem (hV ha))
  have hIJ : (V F m 1 ⊓ Q F v) ⊔ D F m t ≤ V F m 1 ⊔ D F m t :=
    sup_le (inf_le_left.trans le_sup_left) le_sup_right
  have hxJ : x * (a : G)⁻¹ ∈ V F m 1 ⊔ D F m t := hIJ (hi ▸ ⟨hxQa,hxQm⟩)
  have hxJ' : x * (a : G)⁻¹ * (a : G) ∈ V F m 1 ⊔ D F m t :=
    (V F m 1 ⊔ D F m t).mul_mem hxJ (mem_sup_left ha)
  simpa only [D,inv_mul_cancel_right] using hxJ'

/-- The central branch and the earlier commutator bound control every beta-core square. -/
theorem BTwoCenterActionData.beta_core_frattini_le
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m) :
    (frattini (Q F m)).map (Q F m).subtype ≤ Z F m := by
  let := finite_endpoints h
  let : Finite (Q F m) := Finite.of_injective
    (inclusion (Q_le_stabilizer F m)) (inclusion_injective _)
  have hS := source_kernel_sylow h hB hSyl
  have hω := c.omega_eq_bot_of_central_neighbor h hB hSyl hactor hcentral
  obtain ⟨g,hg,_,_,hD,_,_,_⟩ := c.central_D_structure h hS hb hω ht hne
  let : IsElementaryAbelian 2 (D F m t) := hD
  have hprod := c.beta_core_product h hS hb ht hne
  have hn : D F m t ≤ normalizer (V F m 1 : Set G) :=
    (inf_le_left.trans (Q_le_stabilizer F m)).trans (graph_stabilizer_normalizes_V h m 1)
  have hp : IsPGroup 2 (Q F m) := isPGroup_pCoreIn 2 (stabilizer F m)
  rw [map_le_iff_le_comap,hp.frattini_eq_closure_squares]
  apply (closure_le _).mpr
  rintro _ ⟨x,rfl⟩
  change (x : G)^2 ∈ Z F m
  have hx : (x : G) ∈ (V F m 1 : Set G) * (D F m t : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ hn,←hprod]
    exact x.property
  obtain ⟨a,ha,d,hd,he⟩ := hx
  have hid : (a*d)^2 = a^2*⁅a⁻¹,d⁆*d^2 := by
    simp [commutatorElement_def,pow_two,mul_assoc]
  rw [←he,hid,elemPow_eq_one_of_isElementaryAbelian d hd,mul_one]
  exact (Z F m).mul_mem (bTwo_radius_one_squares h hS hb m hcomm a ha)
    (hcomm (commutator_mem_commutator ((V F m 1).inv_mem ha) hd.1))

/-- Clause (10.7)(c), using the genuine earlier (7.4)(d) commutator identity. -/
theorem BTwoCenterActionData.beta_core_frattini_eq
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ = Z F m) :
    (frattini (Q F m)).map (Q F m).subtype = Z F m ∧
      ⁅Q F m,Q F m⁆ = Z F m := by
  let := finite_endpoints h
  let : Finite (Q F m) := Finite.of_injective
    (inclusion (Q_le_stabilizer F m)) (inclusion_injective _)
  let : Fact (IsPGroup 2 (Q F m)) := ⟨isPGroup_pCoreIn 2 (stabilizer F m)⟩
  have hPhi := c.beta_core_frattini_le h hB hSyl hb hactor hcentral ht hne hcomm.le
  have hZ : Z F m ≤ ⁅Q F m,Q F m⁆ := by
    rw [←hcomm]
    exact commutator_mono
      (graph_V_le_Q_of_short h (source_kernel_sylow h hB hSyl) m (by rw [hb]; decide)) le_rfl
  have hder : ⁅Q F m,Q F m⁆ ≤ (frattini (Q F m)).map (Q F m).subtype := by
    have hh := map_mono (f := (Q F m).subtype)
      (commutator_le_frattini_of_isPGroup (p := 2) (R := Q F m))
    simpa only [commutator_def,map_commutator,←MonoidHom.range_eq_map,range_subtype] using hh
  exact ⟨le_antisymm hPhi (hZ.trans hder),le_antisymm (hder.trans hPhi) hZ⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
