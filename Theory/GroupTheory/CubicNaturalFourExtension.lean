module

public import Theory.Representation.FourGroupMatrixCoordinates
public import Theory.GroupTheory.SelfCentralizingFourSymmetricFour
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# Splitting a central cubic from a natural four-group extension

Let `f : E →* SL₂(2) × B` be surjective, with `|B| = 3`, and identify
its kernel with the natural binary plane by coordinates intertwining actual
conjugation with `FourGroupMatrixCoordinates.naturalAction`. If a central
subgroup `D` of order three maps onto the second factor, then the kernel `J`
of the second projection is a complement to `D` and is isomorphic to `S₄`.
Moreover, the original kernel is exactly the image of `O₂(J)` in `E`.

The restriction of the second projection to `D` is a bijection by its order,
which proves the internal direct product. The first projection maps `J` onto
`SL₂(2)`, with the original kernel of order four. Thus `J` has order twenty-four.
Faithfulness of the prescribed natural action makes that normal four-group
self-centralizing in `J`, so the self-centralizing-four-group recognition theorem
identifies `J` with `S₄`. Composing the first projection with `SL₂(2) ≃ S₃`
identifies the four-group with the actual two-core.

This conditional extension theorem supplies the symmetric factor in the setup
preceding Aschbacher–Smith 15.3.60, combined manuscript (1 March 2004),
`refs/quasithin.pdf`, printed p.1150. The source application must construct the
surjection and the compatible coordinates from its actual centralizer action.
-/

open Subgroup
open scoped IsMulCommutative

namespace CubicNaturalFourExtension
private abbrev A := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
private abbrev W := Multiplicative (Fin 2 → ZMod 2)

variable {E B : Type*} [Group E] [Group B]

/-- The canonical complement is the kernel of the cubic projection. -/
@[expose] public def complement
    (f : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) × B) : Subgroup E :=
  ((MonoidHom.snd (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) B).comp f).ker

public instance complement_normal
    (f : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) × B) : (complement f).Normal :=
  inferInstanceAs
    (((MonoidHom.snd (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) B).comp f).ker.Normal)

private theorem ker_le_complement (f : E →* A × B) : f.ker ≤ complement f := by
  intro x hx
  change (f x).2 = 1
  rw [MonoidHom.mem_ker.mp hx]
  rfl

private theorem elementary_of_coordinates {H : Type*} [Group H] (e : H ≃* W) :
    IsElementaryAbelian 2 H := by
  refine { toIsMulCommutative := ⟨⟨fun x y => e.injective ?_⟩⟩
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  · simp only [map_mul, mul_comm]
  · intro x
    apply e.injective
    rw [map_pow, map_one, pow_two]
    apply Multiplicative.toAdd.injective
    ext i
    change (e x).toAdd i + (e x).toAdd i = 0
    exact CharTwo.add_self_eq_zero _

private theorem card_of_coordinates {H : Type*} [Group H] (e : H ≃* W) :
    Nat.card H = 4 := by
  rw [Nat.card_congr e.toEquiv]
  norm_num [W, Nat.card_eq_fintype_card]

private theorem central_cubic_complement [Finite E]
    (f : E →* A × B) (hB : Nat.card B = 3)
    (D : Subgroup E) (hD : D ≤ center E) (hDcard : Nat.card D = 3)
    (hDf : D.map f = (⊥ : Subgroup A).prod (⊤ : Subgroup B)) :
    Disjoint D (complement f) ∧
      D ≤ centralizer (complement f : Set E) ∧ D ⊔ complement f = ⊤ := by
  let g : D →* B := ((MonoidHom.snd A B).comp f).comp D.subtype
  have hgs : Function.Surjective g := by
    intro b
    have hb : (1, b) ∈ D.map f := by
      rw [hDf]
      exact ⟨Subgroup.one_mem _, Subgroup.mem_top _⟩
    obtain ⟨d, hd, he⟩ := hb
    exact ⟨⟨d, hd⟩, congrArg Prod.snd he⟩
  have hgi : Function.Injective g :=
    ((Nat.bijective_iff_surjective_and_card g).mpr ⟨hgs, hDcard.trans hB.symm⟩).1
  refine ⟨Subgroup.disjoint_def.mpr ?_, hD.trans (center_le_centralizer _), ?_⟩
  · intro d hd hj
    have he : g ⟨d, hd⟩ = g 1 := (show g ⟨d, hd⟩ = 1 from hj).trans g.map_one.symm
    exact congrArg Subtype.val (hgi he)
  · apply top_unique
    intro x _
    obtain ⟨d, hd⟩ := hgs ((f x).2)
    have hj : (d : E)⁻¹ * x ∈ complement f := by
      change (f ((d : E)⁻¹ * x)).2 = 1
      change (f (d : E)).2 = (f x).2 at hd
      rw [map_mul, map_inv]
      change (f (d : E)).2⁻¹ * (f x).2 = 1
      rw [hd, inv_mul_cancel]
    have hm := (D ⊔ complement f).mul_mem
      (show (d : E) ∈ D ⊔ complement f from (le_sup_left : D ≤ D ⊔ complement f) d.property)
      (show (d : E)⁻¹ * x ∈ D ⊔ complement f from (le_sup_right : complement f ≤ D ⊔ complement f) hj)
    simpa only [mul_inv_cancel_left] using hm

private theorem symmetric_factor [Finite E]
    (f : E →* A × B) (hf : Function.Surjective f)
    (κ : f.ker ≃* W)
    (hκ : letI := FourGroupMatrixCoordinates.naturalAction
      ∀ (x : E) (k : f.ker), κ (MulAut.conjNormal x k) = (f x).1 • κ k) :
    Nat.card (complement f) = 24 ∧
      centralizer (f.ker.subgroupOf (complement f) : Set (complement f)) =
        f.ker.subgroupOf (complement f) ∧
      (pCore 2 (complement f)).map (complement f).subtype = f.ker ∧
      Nonempty (complement f ≃* Equiv.Perm (Fin 4)) := by
  let J := complement f
  let U := f.ker.subgroupOf J
  let eU : U ≃* W := (Subgroup.subgroupOfEquivOfLe (ker_le_complement f)).trans κ
  have hUcard : Nat.card U = 4 := card_of_coordinates eU
  let _ : IsElementaryAbelian 2 U := elementary_of_coordinates eU
  let _ : U.Normal := inferInstanceAs (f.ker.subgroupOf J).Normal
  let g : J →* A := ((MonoidHom.fst A B).comp f).comp J.subtype
  have hgs : Function.Surjective g := by
    intro a
    obtain ⟨x, hx⟩ := hf (a, 1)
    have hxJ : x ∈ J := congrArg Prod.snd hx
    exact ⟨⟨x, hxJ⟩, congrArg Prod.fst hx⟩
  have hgker : g.ker = U := by
    ext x
    change (f (x : E)).1 = 1 ↔ f (x : E) = 1
    exact ⟨fun hx => Prod.ext hx x.property, fun hx => congrArg Prod.fst hx⟩
  obtain ⟨eA⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  have hAcard : Nat.card A = 6 := by
    rw [Nat.card_congr eA.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  have hJcard : Nat.card J = 24 := by
    have hc := g.ker.card_mul_index
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hgs, Subgroup.card_top,
      hgker, hUcard, hAcard] at hc
    exact hc.symm
  have hcent : centralizer (U : Set J) ≤ U := by
    let _ := FourGroupMatrixCoordinates.naturalAction
    let _ := FourGroupMatrixCoordinates.naturalAction_faithful
    intro x hx
    have hfirst : (f (x : E)).1 = 1 := by
      apply FaithfulSMul.eq_of_smul_eq_smul (α := W)
      intro w
      obtain ⟨k, rfl⟩ := κ.surjective w
      have hcomm := Subgroup.mem_centralizer_iff.mp hx
        (⟨k, ker_le_complement f k.property⟩ : J) k.property
      have hconj : MulAut.conjNormal (x : E) k = k := by
        apply Subtype.ext
        change (x : E) * (k : E) * (x : E)⁻¹ = (k : E)
        have hc := congrArg Subtype.val hcomm
        change (k : E) * (x : E) = (x : E) * (k : E) at hc
        rw [← hc, mul_inv_cancel_right]
      rw [← hκ, hconj, one_smul]
    exact Prod.ext hfirst x.property
  have hcentEq : centralizer (U : Set J) = U := le_antisymm hcent U.le_centralizer
  have hcore : pCore 2 J = U := by
    let g3 := eA.toMonoidHom.comp g
    have hk : g3.ker = U := (g.ker_comp_of_injective eA.toMonoidHom eA.injective).trans hgker
    have hp : IsPGroup 2 g3.ker := by
      rw [hk]
      exact IsElementaryAbelian.isPGroup 2 U
    exact (ker_eq_twoCore_of_surjective_perm_three g3 (eA.surjective.comp hgs) hp).symm.trans hk
  refine ⟨hJcard, hcentEq, ?_, ?_⟩
  · rw [hcore]
    exact Subgroup.map_subgroupOf_eq_of_le (ker_le_complement f)
  · exact mulEquiv_perm_four_of_selfCentralizing_four_card_twentyfour U hUcard hcent hJcard

/-- Construct the internal symmetric complement, its normal self-centralizing
four-group, and the identification of that four-group with its two-core.
The coordinates in the hypothesis intertwine the specified quotient map with
actual conjugation, using exactly the named natural matrix action. -/
public theorem exists_symmetric_complement [Finite E]
    (f : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) × B) (hf : Function.Surjective f) (hB : Nat.card B = 3)
    (κ : f.ker ≃* Multiplicative (Fin 2 → ZMod 2))
    (hκ : letI := FourGroupMatrixCoordinates.naturalAction
      ∀ (x : E) (k : f.ker), κ (MulAut.conjNormal x k) = (f x).1 • κ k)
    (D : Subgroup E) (hD : D ≤ center E) (hDcard : Nat.card D = 3)
    (hDf : D.map f = (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))).prod (⊤ : Subgroup B)) :
    ∃ (J : Subgroup E) (_ : J ≃* Equiv.Perm (Fin 4)),
      J = complement f ∧ J.Normal ∧
      Disjoint D J ∧ D ≤ centralizer (J : Set E) ∧ D ⊔ J = ⊤ ∧
      Nat.card f.ker = 4 ∧ Nat.card J = 24 ∧ f.ker ≤ J ∧
      (f.ker.subgroupOf J).Normal ∧
      centralizer (f.ker.subgroupOf J : Set J) = f.ker.subgroupOf J ∧
      (pCore 2 J).map J.subtype = f.ker := by
  obtain ⟨hd, hc, hs⟩ := central_cubic_complement f hB D hD hDcard hDf
  obtain ⟨hj, hu, hp, ⟨e⟩⟩ := symmetric_factor f hf κ hκ
  exact ⟨complement f, e, rfl, inferInstance, hd, hc, hs,
    card_of_coordinates κ, hj, ker_le_complement f, inferInstance, hu, hp⟩

end CubicNaturalFourExtension
