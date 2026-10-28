module

public import Theory.SpecificGroups.LeechRelated.HSRecognition.Uniqueness.LocalAction
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.Coverage.Intransitive
public import Theory.Mathieu.M22.Properties.HexadExtension

/-!
# Recovering the 77 Mathieu hexads from the rank-three graph

For an exterior vertex, its six common neighbors with the base point form a
six-point set in the natural M₂₂ coordinates. A Sylow two-subgroup fixes an
exterior vertex because there are 77 such vertices. It fixes a native hexad,
and contains that hexad's pointwise kernel of order sixteen. The kernel acts
freely outside its hexad, so the six-point set must be precisely that hexad.
Transitivity transports this identification to every exterior vertex.
Transitivity on the native hexads and equality of the two cardinalities then
make the literal incidence map a bijection.

This supplies the 77-point identification in Wales, "Uniqueness of the graph
of a rank three group", Pacific J. Math. 30 (1969), p.274. It uses the actual
Mathieu action on the 22 neighbors, with no assumption about the exterior
representation or the isomorphism type of the original permutation group.
-/

@[expose] public section
open MulAction
open scoped Pointwise
namespace Sporadic.LeechRelated.HS
open Sporadic.Mathieu
attribute [local instance] Classical.propDecidable
noncomputable section

variable {P : Subgroup (Equiv.Perm (Fin 100))} (h : RankThreeData P)

/-- The 77 vertices outside the base point and its neighborhood. -/
def RankThreeData.exterior : SubMulAction (stabilizer P (0 : Fin 100)) (Fin 100) where
  carrier := {x | x ≠ 0 ∧ ¬h.graph.Adj 0 x}
  smul_mem' := by
    intro g x hx
    refine ⟨?_, ?_⟩
    · intro he
      exact hx.1 (MulAction.injective g (he.trans g.property.symm))
    · intro he
      apply hx.2
      apply (h.graph_invariant g.val 0 x).mp
      change h.graph.Adj (g • 0) (g • x)
      rw [show g • (0 : Fin 100) = 0 from g.property]
      exact he

private theorem neighbor_card : Nat.card (h.graph.neighborSet 0) = 22 := by
  rw [Nat.card_eq_fintype_card, h.graph.card_neighborSet_eq_degree]
  exact h.graph_stronglyRegular.regular 0

theorem RankThreeData.exterior_card : Nat.card h.exterior = 77 := by
  have hs : (h.exterior : Set (Fin 100)) =
      (({0} : Set (Fin 100)) ∪ h.graph.neighborSet 0)ᶜ := by
    ext x
    change (x ≠ 0 ∧ ¬h.graph.Adj 0 x) ↔ ¬(x = 0 ∨ h.graph.Adj 0 x)
    exact not_or.symm
  change (h.exterior : Set (Fin 100)).ncard = 77
  rw [hs, Set.ncard_compl, Set.ncard_union_eq]
  · have hn := neighbor_card h
    rw [Nat.card_fin, Set.ncard_singleton]
    change 100 - (1 + Nat.card (h.graph.neighborSet 0)) = 77
    omega
  · exact Set.disjoint_singleton_left.mpr (h.graph.irrefl)

private theorem exterior_orbit (x : h.exterior) :
    orbit (stabilizer P (0 : Fin 100)) x.val = (h.exterior : Set (Fin 100)) := by
  obtain ⟨b, c, _, hb, hc, hcover⟩ := h.suborbits
  have hnb (z : Fin 100) : z ∈ orbit (stabilizer P (0 : Fin 100)) b ↔ h.graph.Adj 0 z := by
    constructor
    · intro hz
      change Nat.card (orbit (stabilizer P (0 : Fin 100)) z) = 22
      rw [orbit_eq_iff.mpr hz, hb]
    · intro hz
      rw [← h.suborbit_eq_of_card_eq (hz.trans hb.symm)]
      exact mem_orbit_self _
  have he : orbit (stabilizer P (0 : Fin 100)) c = (h.exterior : Set (Fin 100)) := by
    rw [hcover]
    ext z
    change (¬(z = 0 ∨ z ∈ orbit (stabilizer P (0 : Fin 100)) b)) ↔
      z ≠ 0 ∧ ¬h.graph.Adj 0 z
    rw [not_or, hnb]
  have hx : x.val ∈ orbit (stabilizer P (0 : Fin 100)) c := he ▸ x.property
  exact (orbit_eq_iff.mpr hx).trans he

theorem RankThreeData.exterior_transitive :
    IsPretransitive (stabilizer P (0 : Fin 100)) h.exterior := by
  constructor
  intro x y
  have hy : y.val ∈ orbit (stabilizer P (0 : Fin 100)) x.val :=
    (exterior_orbit h x) ▸ y.property
  obtain ⟨g, hg⟩ := hy
  exact ⟨g, Subtype.ext hg⟩

/-- The six neighbors of an exterior vertex, in the natural Mathieu coordinates. -/
def RankThreeData.sixSet (f : h.graph.neighborSet 0 ≃ Fin 22) (x : h.exterior) :
    Finset (Fin 22) := Finset.univ.filter (fun a => h.graph.Adj x.val (f.symm a).val)

@[simp] theorem RankThreeData.mem_sixSet (f : h.graph.neighborSet 0 ≃ Fin 22)
    (x : h.exterior) (a : Fin 22) : a ∈ h.sixSet f x ↔ h.graph.Adj x.val (f.symm a).val := by
  simp [sixSet]

theorem RankThreeData.sixSet_card (f : h.graph.neighborSet 0 ≃ Fin 22)
    (x : h.exterior) : (h.sixSet f x).card = 6 := by
  let e : (h.sixSet f x) ≃ h.graph.commonNeighbors 0 x.val := {
    toFun := fun a => ⟨(f.symm a.val).val, (f.symm a.val).property,
      (h.mem_sixSet f x a.val).mp a.property⟩
    invFun := fun y => ⟨f ⟨y.val, y.property.1⟩, by
      rw [h.mem_sixSet, f.symm_apply_apply]
      exact y.property.2⟩
    left_inv := fun _ => Subtype.ext (f.apply_symm_apply _)
    right_inv := by
      intro y
      apply Subtype.ext
      exact congrArg (fun z : h.graph.neighborSet 0 => z.val) (f.symm_apply_apply _) }
  have he := Nat.card_congr e
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, Nat.card_eq_fintype_card,
    h.graph_stronglyRegular.of_not_adj x.property.1.symm x.property.2] at he
  exact he

variable (e : stabilizer P (0 : Fin 100) ≃* M22)
  (f : h.graph.neighborSet 0 ≃ Fin 22)
  (hf : ∀ (g : stabilizer P (0 : Fin 100)) (x y : Fin 100)
    (hx : h.graph.Adj 0 x) (hy : h.graph.Adj 0 y),
    g • x = y → f ⟨y, hy⟩ = e g • f ⟨x, hx⟩)

include e hf

private theorem coordinate_smul (g : stabilizer P (0 : Fin 100)) (a : Fin 22) :
    (f.symm (e g • a)).val = g • (f.symm a).val := by
  have hy : h.graph.Adj 0 (g • (f.symm a).val) := by
    have hh := (h.graph_invariant g.val 0 (f.symm a).val).mpr (f.symm a).property
    change h.graph.Adj (g • 0) (g • (f.symm a).val) at hh
    rwa [show g • (0 : Fin 100) = 0 from g.property] at hh
  have he := hf g (f.symm a).val (g • (f.symm a).val) (f.symm a).property hy rfl
  rw [f.apply_symm_apply] at he
  exact congrArg Subtype.val (f.injective ((f.apply_symm_apply _).trans he.symm))

theorem RankThreeData.sixSet_smul (g : stabilizer P (0 : Fin 100)) (x : h.exterior) :
    h.sixSet f (g • x) = e g • h.sixSet f x := by
  ext a
  obtain ⟨a, rfl⟩ := (MulAction.bijective (e g)).surjective a
  rw [Finset.smul_mem_smul_finset_iff, h.mem_sixSet, h.mem_sixSet]
  rw [coordinate_smul h e f hf]
  exact h.graph_invariant g.val x.val (f.symm a).val

/-- Every exterior vertex gives a native Mathieu hexad. -/
theorem RankThreeData.sixSet_mem_blocks (x : h.exterior) : h.sixSet f x ∈ m22Blocks := by
  let K := stabilizer P (0 : Fin 100)
  let U : Sylow 2 K := Sylow.nonempty.some
  let A : SubMulAction U (Fin 100) := {
    carrier := h.exterior
    smul_mem' := fun g _ hx => h.exterior.smul_mem g.val hx }
  have hA : Nat.card A = 77 := h.exterior_card
  obtain ⟨y, hy⟩ := U.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card A
    (by rw [hA]; decide)
  let y' : h.exterior := ⟨y.val, y.property⟩
  let V := U.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨B, hB, hVB⟩ := M22SolvableSylow.sylow_preserves_hexad V
  have hVS : (V : Subgroup M22) ≤ stabilizer M22 (h.sixSet f y') := by
    intro g hg
    obtain ⟨u, hu, rfl⟩ := hg
    have hfix : (u : K) • y' = y' := by
      apply Subtype.ext
      exact congrArg Subtype.val ((mem_fixedPoints.mp hy) (⟨u, hu⟩ : U))
    exact (h.sixSet_smul e f hf u y').symm.trans (congrArg (h.sixSet f) hfix)
  have hsB : h.sixSet f y' = B := M22SolvableSylow.invariant_six_eq_hexad hB _
    (h.sixSet_card f y') ((M22SolvableSylow.kernel_le_of_sylow hB V hVB).trans hVS)
  let := h.exterior_transitive
  obtain ⟨g, rfl⟩ := exists_smul_eq K y' x
  rw [h.sixSet_smul e f hf, hsB]
  exact m22_smul_block_mem (e g) B hB

/-- The literal incidence map from the 77 vertices to the 77 native hexads. -/
def RankThreeData.hexadMap (x : h.exterior) : {B // B ∈ m22Blocks} :=
  ⟨h.sixSet f x, h.sixSet_mem_blocks e f hf x⟩

theorem RankThreeData.hexadMap_bijective : Function.Bijective (h.hexadMap e f hf) := by
  apply (Nat.bijective_iff_surjective_and_card _).mpr
  refine ⟨?_, ?_⟩
  · intro B
    obtain ⟨x⟩ : Nonempty h.exterior := Nat.card_pos_iff.mp (by rw [h.exterior_card]; decide) |>.1
    obtain ⟨u, hu⟩ := exists_smul_m22Hexad123_eq (h.sixSet_mem_blocks e f hf x)
    obtain ⟨v, hv⟩ := exists_smul_m22Hexad123_eq B.property
    let g := e.symm (v * u⁻¹)
    refine ⟨g • x, Subtype.ext ?_⟩
    change h.sixSet f (g • x) = B.val
    rw [h.sixSet_smul e f hf]
    simp only [g, e.apply_symm_apply, mul_smul, ← hu, inv_smul_smul, hv]
  · rw [h.exterior_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
      Finset.filter_mem_eq_inter, Finset.univ_inter, m22Blocks_cardinality]

/-- Exterior vertices are identified bijectively with their six-point hexads. -/
def RankThreeData.hexadEquiv : h.exterior ≃ {B // B ∈ m22Blocks} :=
  Equiv.ofBijective (h.hexadMap e f hf) (h.hexadMap_bijective e f hf)

end
end Sporadic.LeechRelated.HS
