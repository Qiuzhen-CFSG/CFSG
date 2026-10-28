module
public import ABG.Recognition.ThreeLinearFixedSetGeometry
public import Theory.GroupAction.FourPointKernel
public import Mathlib.Data.Set.Card

/-!
# Eight defining elements for each four-line fixed set

A subgroup of order 27 centralizing a point element acts on its four fixed
lines. Its permutation kernel has at least nine elements. Each nonidentity
kernel element has order three and fixes those four lines; the one-line
alternative forces it to be a point element. Its four fixed lines are then
exactly the original fixed set. Inclusion into the ambient group injects
these at least eight elements into the precise `pointOf` fiber.

Source: Wong, *On finite groups whose 2-Sylow subgroups have cyclic subgroups
of index 2* (1964), Theorem 6(b), pp.110–111.
-/

namespace ABG.ThreeLinearPlane

variable (G L : Type*) [Group G] [Finite G] [Finite L] [MulAction G L]

/-- The centralizing exponent-three subgroup supplies eight distinct defining
 elements of the same point. -/
public theorem eight_le_card_pointOf_fiber_of_subgroup
    (hfour : ∀ g : G, IsPointElement G g → Nat.card (MulAction.fixedBy (Line G L) g) = 4)
    (hone : ∀ g : G, orderOf g = 3 → ¬ IsPointElement G g →
      Nat.card (MulAction.fixedBy (Line G L) g) = 1)
    (g : G) (hg : IsPointElement G g)
    (P : Subgroup G) (hP : Nat.card P = 27)
    (hcentral : P ≤ Subgroup.centralizer ({g} : Set G))
    (hexp : ∀ x : G, x ∈ P → x ≠ 1 → orderOf x = 3) :
    8 ≤ Nat.card {x : {x : G // IsPointElement G x} //
      pointOf G L x.1 x.2 = pointOf G L g hg} := by
  classical
  let S : SubMulAction P (Line G L) :=
    { carrier := MulAction.fixedBy (Line G L) g
      smul_mem' := by
        intro x l hl
        change g • ((x : G) • l) = (x : G) • l
        have hc := Subgroup.mem_centralizer_singleton_iff.mp (hcentral x.property)
        rw [← mul_smul, ← hc, mul_smul, hl] }
  let f := MulAction.toPermHom P S
  let K := f.ker
  have hK : 9 ≤ Nat.card K :=
    MulAction.nine_le_card_ker_toPermHom hP (hfour g hg)
  have hfix (k : K) : MulAction.fixedBy (Line G L) g ⊆
      MulAction.fixedBy (Line G L) (k.val : G) := by
    intro l hl
    have heq := Equiv.congr_fun (show f k.val = 1 from k.property) (⟨l, hl⟩ : S)
    exact congrArg Subtype.val heq
  have horder (k : K) (hk : k ≠ 1) : orderOf (k.val : G) = 3 := by
    apply hexp _ k.val.property
    intro heq
    apply hk
    exact Subtype.ext (Subtype.ext heq)
  have heligible (k : K) (hk : k ≠ 1) : IsPointElement G (k.val : G) := by
    by_contra hn
    have hle := Nat.card_le_card_of_injective (Set.inclusion (hfix k))
      (Set.inclusion_injective (hfix k))
    rw [hfour g hg, hone _ (horder k hk) hn] at hle
    omega
  have hsame (k : K) (hk : k ≠ 1) :
      MulAction.fixedBy (Line G L) (k.val : G) = MulAction.fixedBy (Line G L) g := by
    apply Eq.symm
    apply Set.eq_of_subset_of_ncard_le (hfix k)
    change Nat.card (MulAction.fixedBy (Line G L) (k.val : G)) ≤
      Nat.card (MulAction.fixedBy (Line G L) g)
    rw [hfour _ (heligible k hk), hfour g hg]
  let j : {k : K // k ≠ 1} →
      {x : {x : G // IsPointElement G x} // pointOf G L x.1 x.2 = pointOf G L g hg} :=
    fun k => ⟨⟨k.val.val.val, heligible k.val k.property⟩,
      Subtype.ext (hsame k.val k.property)⟩
  have hj : Function.Injective j := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x => x.val.val) hab
  have hcard : Nat.card {k : K // k ≠ 1} = Nat.card K - 1 := by
    let : Fintype K := Fintype.ofFinite K
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun k : K => k = 1),
      Fintype.card_subtype_eq]
  have hle := Nat.card_le_card_of_injective j hj
  rw [hcard] at hle
  omega

/-- Local centralizer data prove the fiber premise of
`plane_and_counts_of_fibers` for every actual fixed-set point. -/
public theorem eight_le_card_pointOf_fiber
    (hfour : ∀ g : G, IsPointElement G g → Nat.card (MulAction.fixedBy (Line G L) g) = 4)
    (hone : ∀ g : G, orderOf g = 3 → ¬ IsPointElement G g →
      Nat.card (MulAction.fixedBy (Line G L) g) = 1)
    (hsubgroup : ∀ g : G, IsPointElement G g → ∃ P : Subgroup G,
      Nat.card P = 27 ∧ P ≤ Subgroup.centralizer ({g} : Set G) ∧
      ∀ x : G, x ∈ P → x ≠ 1 → orderOf x = 3)
    (p : Point G L) :
    8 ≤ Nat.card {x : {x : G // IsPointElement G x} // pointOf G L x.1 x.2 = p} := by
  obtain ⟨g, hg, hgp⟩ := point_spec G L p
  have hp : p = pointOf G L g hg := Subtype.ext hgp
  rw [hp]
  obtain ⟨P, hP, hc, he⟩ := hsubgroup g hg
  exact eight_le_card_pointOf_fiber_of_subgroup G L hfour hone g hg P hP hc he

end ABG.ThreeLinearPlane
