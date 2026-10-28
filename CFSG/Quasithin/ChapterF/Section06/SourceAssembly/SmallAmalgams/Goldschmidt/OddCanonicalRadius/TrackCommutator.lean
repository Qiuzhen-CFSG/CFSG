module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.OddCanonicalRadius.NeighborhoodProduct
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.OddCanonicalRadius.CubicCentralizer
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.OddCanonicalRadius.CentralizerMover
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.OddCanonicalRadius.ForkCommutator

/-!
# The exact odd-radius track commutator

The three-branch product has centralizer of index at most two at its center.
The far commutation from (6.11.1) and the local centralizer mover construct a
track centralized by this product. The semilocal order-three centralizer then
forces the product to be trivial, identifying the original commutator with
the label four steps from its first center.

Source: Goldschmidt (1980), (6.11.2)–(6.11.3), printed p.402.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

/-- The exact source commutator in (6.11.3). -/
theorem CanonicalLabelSetup.odd_track_commutator
    (d : CanonicalLabelSetup F s) (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (htracks : ∀ t : Track (RankTwo.graph F) G, t.fixer ≠ ⊥ →
      ∃ i:Fin 2, ∃ q:G, orderOf q = 3 ∧ q ∈ RankTwo.stabilizer F (t.vertex i)  ∧
        q ∈ centralizer (t.fixer:Set G))
    (hr : 5 ≤ d.radius) (hodd : Odd d.radius) :
    ⁅d.label (d.track.vertex d.center),
        d.label (d.track.vertex (d.center+(d.radius:ℤ)+3))⁆  =
      d.label (d.track.vertex (d.center+4)) := by
  classical
  let p : ℤ → RankTwo.Vertex F := fun i => d.track.vertex (d.center+i)
  let z : ℤ → G := fun i => d.label (p i)
  let r : ℤ := d.radius
  obtain ⟨k,hk⟩ := hodd
  have hkr : r = 2*(k:ℤ)+1 := by dsimp [r]; omega
  have hadj (i : ℤ) : (RankTwo.graph F).Adj (p i) (p (i+1)) := by
    simpa only [p,add_assoc] using d.track.adjacent (d.center+i)
  have hinj : Function.Injective p := by
    intro i j he
    have := d.track.injective he
    omega
  have ht (j : ℤ) : (p (2*j)).type = d.side := d.shifted_type j
  have hf (j i : ℤ) : z (2*j) • p i = p i ↔ 2*j-(r+1) ≤ i ∧ i ≤ 2*j+(r+1) := by
    have hh := d.shifted_fixed_iff j (d.center+i)
    change z (2*j) • p i = p i ↔ _ at hh
    exact hh.trans (by dsimp [r]; omega)
  let x := z (r+3)
  let y := z (r+5)
  have hxf (i : ℤ) : x • p i = p i ↔ 2 ≤ i ∧ i ≤ 2*r+4 := by
    have he : r+3 = 2*((k:ℤ)+2) := by omega
    dsimp only [x]
    rw [he,hf]
    omega
  have hyf (i : ℤ) : y • p i = p i ↔ 4 ≤ i ∧ i ≤ 2*r+6 := by
    have he : r+5 = 2*((k:ℤ)+3) := by omega
    dsimp only [y]
    rw [he,hf]
    omega
  have hx2 : x • p 2 = p 2 := (hxf 2).2 (by dsimp [r]; omega)
  have hx3 : x • p 3 = p 3 := (hxf 3).2 (by dsimp [r]; omega)
  have hx1 : x • p 1 ≠ p 1 := by intro he; have := (hxf 1).1 he; omega
  have h13 : p 1 ≠ p 3 := fun he => by have := hinj he; omega
  have h1x : p 1 ≠ x • p 1 := Ne.symm hx1
  have hx13 : x • p 1 ≠ p 3 := by
    intro he
    exact h13 ((MulAction.toPerm x).injective (he.trans hx3.symm))
  let f : Fin 3 → (RankTwo.graph F).neighborSet (p 2) :=
    ![⟨p 1,(hadj 1).symm⟩,
      ⟨x • p 1,by
        change (RankTwo.graph F).Adj (p 2) (x • p 1)
        simpa only [show (1:ℤ)+1=2 by norm_num,hx2] using
          trackGraphAction.map_adj x (hadj 1).symm⟩,
      ⟨p 3,hadj 2⟩]
  have hfi : Function.Injective f := by
    intro i j he
    have he' := congrArg Subtype.val he
    fin_cases i <;> fin_cases j
    · rfl
    · exact (h1x he').elim
    · exact (h13 he').elim
    · exact (hx1 he').elim
    · rfl
    · exact (hx13 he').elim
    · exact (h13 he'.symm).elim
    · exact (hx13 he'.symm).elim
    · rfl
  let : Finite ((RankTwo.graph F).neighborSet (p 2)) :=
    Nat.finite_of_card_ne_zero (by rw [h.card_neighbor]; decide)
  let : Fintype ((RankTwo.graph F).neighborSet (p 2)) := Fintype.ofFinite _
  let e : Fin 3 ≃ (RankTwo.graph F).neighborSet (p 2) :=
    Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2
      ⟨hfi,by rw [Fintype.card_fin,← Nat.card_eq_fintype_card,h.card_neighbor]⟩)
  let u : Fin 3 → RankTwo.Vertex F := ![p 0,x • p 0,p 4]
  have hu : ∀ i, (RankTwo.graph F).Adj (e i).val (u i) := by
    intro i
    fin_cases i
    · exact (hadj 0).symm
    · exact trackGraphAction.map_adj x (hadj 0).symm
    · exact hadj 3
  have hua : ∀ i, u i ≠ p 2 := by
    intro i
    fin_cases i
    · exact fun he => by have := hinj he; omega
    · intro he
      have hh := hinj ((MulAction.toPerm x).injective (he.trans hx2.symm))
      omega
    · exact fun he => by have := hinj he; omega
  let v := ⁅z 0,x⁆*z 4
  have hvprod : v = d.label (u 0)*d.label (u 1)*d.label (u 2) := by
    change ⁅z 0,x⁆*z 4 = z 0*d.label (x • p 0)*z 4
    rw [d.conjugate x (p 0) (ht 0)]
    have hz0inv : (z 0)⁻¹ = z 0 := d.label_inv (ht 0)
    change (z 0*x*(z 0)⁻¹*x⁻¹)*z 4=z 0*(x*z 0*x⁻¹)*z 4
    rw [hz0inv]
    simp only [mul_assoc]
  have hindex : (centralizer ({v}:Set G)).relIndex (RankTwo.stabilizer F (p 2)) ≤ 2 := by
    rw [hvprod]
    exact d.threeBranchProduct_centralizer_index_le_two h (by omega) (by omega) (ht 1) e u hu hua
  have hvfix (i : ℤ) (hil : 2 ≤ i) (hir : i ≤ 4) : v • p i = p i := by
    have hz0 : z 0 • p i = p i := (hf 0 i).2 (by dsimp [r]; omega)
    have hz4 : z 4 • p i = p i := (hf 2 i).2 (by dsimp [r]; omega)
    have hx : x • p i = p i := (hxf i).2 (by dsimp [r]; omega)
    have hm0 : z 0 ∈ RankTwo.stabilizer F (p i) := hz0
    have hmx : x ∈ RankTwo.stabilizer F (p i) := hx
    let H := RankTwo.stabilizer F (p i)
    exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hm0 hmx) (H.inv_mem hm0)) (H.inv_mem hmx)) hz4
  have huv : Commute ⁅z 0,x⁆ y := by
    simpa only [z,p,x,y,r,add_zero,add_assoc] using
      d.far_commutator_commutes h hs hshort hr ⟨k,hk⟩
  have h4y : Commute (z 4) y := (d.central (p 4) (ht 2)).2 y
    ((hyf 4).2 (by dsimp [r]; omega))
  have hvy : Commute v y := huv.mul_left h4y
  obtain ⟨a,hva,ha2,ha3,ha4⟩ := h.exists_centralizer_edge_mover hC hA
    (hadj 2) (hadj 3) (fun he => by have := hinj he; omega) v hindex
  have hone : v = 1 := h.eq_one_of_commuting_track_movers htracks
    (hadj 2) (hadj 3) (fun he => by have := hinj he; omega)
    (hvfix 2 (by omega) (by omega)) (hvfix 3 (by omega) (by omega))
    (hvfix 4 (by omega) (by omega)) hva hvy ha2 ha3 ha4
    ((hyf 4).2 (by dsimp [r]; omega))
    (fun he => by have := (hyf 3).1 he; omega)
    (h.exists_cubic_centralizer_of_index_le_two (hadj 2) v hindex)
  have he : ⁅z 0,x⁆ = z 4 := (mul_eq_one_iff_eq_inv.mp hone).trans (d.label_inv (ht 2))
  simpa only [z,p,x,r,add_zero,add_assoc] using he

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
