module

public import Stellmacher.SectionTwo.LemmaTwoTwo

/-!
# The commutator endpoint of Stellmacher (2.2)

Let `Ē = [O₂′(Ḡ), J̄]J̄` be the normal product supplied by (2.2).  If a
subgroup `K` is its full commutator with the Baumann image `B̄`, then parts
(a)--(c) of (2.2) force `K` into `O₃(Ḡ)` and give `O₂(K) = 1`.  This is the
final use of (2.2) in Stellmacher (5.2); the action-module decomposition in
part (d) is not needed for this implication.

Indeed, (2.2)(b) puts `B̄ = J̄` inside the normal subgroup `Ē`.  Thus
`K = [K,B̄]` lies first in `Ē` and then in its derived subgroup.  Part (c)
writes `Ē` as an internal product of `SL₂(2)` factors, whose derived subgroup
is a 3-group.  Its ambient image is normal, so it lies in the 3-core; the
2-core of its subgroup `K` is then trivial by coprimeness.

Source: Stellmacher, Journal of Algebra 190 (1997), final paragraph of the
proof of Lemma (5.2), p. 29; see
`refs/latex/stellmacher-n-group.tex`.  In the journal scan the preceding
Fitting subgroup is `O₂′(F(M̄))`; the missing prime in the LaTeX transcription
does not affect this endpoint.
-/

open scoped Pointwise commutatorElement

namespace Stellmacher.SectionTwo

universe u

private theorem sl2_commutator_cube
    {H : Type u} [Group H] [Finite H] (h : IsSL2Two H)
    (x : H) (hx : x ∈ commutator H) : x ^ 3 = 1 := by
  obtain ⟨e⟩ := h
  have hmul : ∀ a b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
      a ^ 3 = 1 → b ^ 3 = 1 → (a * b) ^ 3 = 1 := by
    decide +kernel
  have hcomm : ∀ a b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
      ⁅a, b⁆ ^ 3 = 1 := by
    decide +kernel
  let C : Subgroup H :=
    { carrier := {x | (e x) ^ 3 = 1}
      one_mem' := by simp
      mul_mem' := by intro a b ha hb; simpa using hmul (e a) (e b) ha hb
      inv_mem' := by intro a ha; simp_all [inv_pow] }
  have hle : commutator H ≤ C := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    change e ⁅a, b⁆ ^ 3 = 1
    rw [map_commutatorElement]
    exact hcomm _ _
  have hcube : e x ^ 3 = 1 := hle hx
  exact e.injective (by simpa using hcube)

private theorem internalSL2Product_commutator_isPGroup_three
    {G : Type u} [Group G] [Finite G]
    {n : ℕ} (E : Subgroup G) (D : Fin n → Subgroup G)
    (hprod : IsInternalDirectProductFamily E D)
    (hSL : ∀ i, IsSL2Two (D i)) :
    IsPGroup 3 (commutator E) := by
  classical
  let P := ∀ i : Fin n, (D i)
  have hcomm : Pairwise (fun i j : Fin n => ∀ x y : G,
      x ∈ D i → y ∈ D j → Commute x y) := by
    intro i j hij x y hx hy
    exact hprod.2.2 i j hij x hx y hy
  let f : P →* G := Subgroup.noncommPiCoprod hcomm
  have hf : f.range = E := (Subgroup.noncommPiCoprod_range).trans hprod.1.symm
  have hmap : (commutator P).map f = (commutator E).map E.subtype := by
    rw [map_commutator_eq, hf, Subgroup.map_subtype_commutator]
  have hPp : IsPGroup 3 (commutator P) := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    funext i
    have heval : (x : P) i ∈ commutator (D i) := by
      have hm := Subgroup.mem_map_of_mem
        (Pi.evalMonoidHom (fun i : Fin n => (D i)) i) x.property
      rw [map_commutator_eq] at hm
      exact Subgroup.commutator_mono le_top le_top hm
    exact sl2_commutator_cube (hSL i) _ heval
  have himage : IsPGroup 3 ((commutator E).map E.subtype) := by
    rw [← hmap]
    exact hPp.map f
  exact himage.of_equiv
    ((commutator E).equivMapOfInjective E.subtype E.subtype_injective).symm

/-- If `K` is its full commutator with the Baumann image in the conclusion of
Stellmacher (2.2), then `K` lies in the ambient 3-core and has trivial 2-core. -/
public theorem lemmaTwoTwo_commutator_endpoint
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {barG : Type u} [Group barG] [Finite barG]
    (q : G →* barG) (barJ barB K : Subgroup barG)
    (h : LemmaTwoTwoConclusion S q barJ barB)
    (hcomm : K = ⁅K, barB⁆) :
    K ≤ pCore 3 barG ∧ pCore 2 K = ⊥ := by
  classical
  let Ebar := ⁅pPrimeCore 2 barG, barJ⁆ ⊔ barJ
  have hEnormal : Ebar.Normal := h.part_a
  let _ : Ebar.Normal := hEnormal
  have hBle : barB ≤ Ebar := by
    rw [← h.part_b]
    exact le_sup_right
  have hKleE : K ≤ Ebar := by
    rw [hcomm]
    exact (Subgroup.commutator_mono le_rfl hBle).trans
      (Subgroup.commutator_le_right K Ebar)
  have hKleDerived : K ≤ (commutator Ebar).map Ebar.subtype := by
    rw [Subgroup.map_subtype_commutator]
    rw [hcomm]
    exact Subgroup.commutator_mono hKleE hBle
  rcases h.part_c with ⟨n, D, hE, hprod, hSL⟩
  change Ebar = ⨆ i, D i at hE
  change IsInternalDirectProductFamily Ebar D at hprod
  have hderived : IsPGroup 3 (commutator Ebar) :=
    internalSL2Product_commutator_isPGroup_three Ebar D hprod hSL
  let R : Subgroup barG := (commutator Ebar).map Ebar.subtype
  have hRthree : IsPGroup 3 R := hderived.map Ebar.subtype
  have hRnormal : R.Normal := by
    change ((commutator Ebar).map Ebar.subtype).Normal
    rw [Subgroup.map_subtype_commutator]
    infer_instance
  have hRcore : R ≤ pCore 3 barG := le_sSup ⟨hRnormal, hRthree⟩
  have hKthree : IsPGroup 3 K := hRthree.to_le hKleDerived
  constructor
  · exact hKleDerived.trans hRcore
  · have htopThree : IsPGroup 3 (⊤ : Subgroup K) :=
      hKthree.of_equiv Subgroup.topEquiv.symm
    have hdis : Disjoint (pCore 2 K) (⊤ : Subgroup K) :=
      IsPGroup.disjoint_of_ne 2 3 (by decide) _ _ pCore_isPGroup htopThree
    simpa only [disjoint_top] using hdis

end Stellmacher.SectionTwo
