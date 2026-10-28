module
public import Theory.GroupTheory.AmalgamGraph.OddPathOrderBound
public import Mathlib.Data.Fintype.Card
/-!
# A two-subgroup bound from one more odd path fixer

A two-subgroup fixing a nonempty path acts on the neighbors of its first
vertex other than the next vertex. If the fixers of all preceding
extensions have odd order, that orbit map is injective: its stabilizer
is both a two-group and a subgroup of an odd group. Hence the subgroup
has order at most the forward degree.

The DGS85 (12.9) application, printed p.189, applies this to an eight-path
with a linear endpoint, giving the bound q from the odd nine-path result.
Only vertex stabilizers need be finite; the graph need not be a tree.
-/
public noncomputable section
open Subgroup SimpleGraph SimpleGraph.BasedWalk
namespace Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G]
theorem two_subgroup_card_le_preceding_degree_of_odd_extensions
    (F : Bool → Subgroup G) [∀ i, Finite (F i)]
    {n : ℕ} {a : Vertex F} (p : BasedWalk (graph F) (n+1) a)
    (hdegree : 1 < Nat.card ((graph F).neighborSet a))
    (hodd : ∀ {z : Vertex F} (hz : (graph F).Adj z a),
      z ≠ (p.1 : Vertex F) →
      Odd (Nat.card (pathStabilizer F (n := n+2) (v := z) (⟨⟨a,hz⟩,p⟩ : BasedWalk (graph F) (n+2) z))))
    (T : Subgroup G) (hTp : IsPGroup 2 T) (hfix : T ≤ pathStabilizer F p) :
    Nat.card T ≤ Nat.card ((graph F).neighborSet a) - 1 := by
  classical
  let : Finite ((graph F).neighborSet a) := Theory.GroupTheory.AmalgamGraph.finite_neighbors F a
  let : Fintype ((graph F).neighborSet a) := Fintype.ofFinite _
  let X := {z : (graph F).neighborSet a // z ≠ p.1}
  have hX : Nat.card X = Nat.card ((graph F).neighborSet a) - 1 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl,Fintype.card_subtype_eq,
      ←Nat.card_eq_fintype_card]
  obtain ⟨z⟩ : Nonempty X := (Nat.card_pos_iff.mp (hX.symm ▸ (by omega : 0 < Nat.card ((graph F).neighborSet a)-1))).1
  have hza : (graph F).Adj (z.val : Vertex F) a := z.val.property.symm
  have hzne : (z.val : Vertex F) ≠ (p.1 : Vertex F) := fun he => z.property (Subtype.ext he)
  let q : BasedWalk (graph F) (n+2) (z.val : Vertex F) := ⟨⟨a,hza⟩,p⟩
  have ho : Odd (Nat.card (pathStabilizer F q)) := hodd hza hzne
  have hTa : T ≤ stabilizer F a := hfix.trans (pathStabilizer_le F p)
  have hTb : T ≤ stabilizer F (p.1 : Vertex F) := by
    intro t ht
    exact hfix ht _ (List.mem_cons_of_mem a (origin_mem_vertices F p.2))
  let f : T → X := fun t => ⟨⟨(t : G) • (z.val : Vertex F),by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F (t : G)).map_adj_iff.mpr z.val.property
    change (graph F).Adj ((t : G) • a) ((t : G) • (z.val : Vertex F)) at hh
    rwa [hTa t.property] at hh⟩,by
      intro he
      apply hzne
      apply MulAction.injective (t : G)
      exact (congrArg Subtype.val he).trans (hTb t.property).symm⟩
  have hf : Function.Injective f := by
    intro t u he
    have hs : (t : G) • (z.val : Vertex F) = (u : G) • (z.val : Vertex F) :=
      congrArg (fun w : X => (w.val : Vertex F)) he
    have hh : ((t : G)⁻¹ * u) ∈ pathStabilizer F q := by
      intro v hv
      change v ∈ (z.val : Vertex F) :: p.vertices at hv
      rcases List.mem_cons.mp hv with rfl | hv
      · rw [mul_smul,←hs,inv_smul_smul]
      · exact hfix (T.mul_mem (T.inv_mem t.property) u.property) v hv
    obtain ⟨r,hr⟩ := hTp (t⁻¹*u)
    have hd : orderOf ((t : G)⁻¹*u) ∣ 2^r := by
      change orderOf ((t⁻¹*u : T) : G) ∣ 2^r
      rw [Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hr
    have hd' : orderOf ((t : G)⁻¹*u) ∣ Nat.card (pathStabilizer F q) :=
      (pathStabilizer F q).orderOf_dvd_natCard hh
    apply Subtype.ext
    exact inv_mul_eq_one.mp (orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (ho.coprime_two_right.pow_right r) hd' hd))
  exact (Nat.card_le_card_of_injective f hf).trans_eq hX
end Subgroup.CosetGeometry.RankTwo
