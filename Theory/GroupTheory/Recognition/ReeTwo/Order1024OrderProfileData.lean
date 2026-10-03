module

public import Theory.GroupTheory.Recognition.ReeTwo.Order1024ResidualRepresentatives
public import Theory.GroupTheory.PGroup.FrattiniProfile
/-!
# Order-profile stabilizers for the residual Ree two representatives

The binary spaces have ranks two, three and four. The listed color tables
encode proposed element-order profiles in the Frattini cosets of eleven
residual representatives. Every linear automorphism preserving one of these
color tables has fourth power equal to the identity. The proof reconstructs
maps from their basis images and checks the finitely many color-preserving
tuples in Lean's kernel.

`OrderProfileModel` records the separate concrete quotient obligation; the
finite certificates do not assert that obligation. Counts of orders 1, 2,
and 4 suffice to distinguish the colors. The excluded indices 1, 5, 7 and 13
have dummy constant colors and are not covered by the stabilizer theorem.

The coordinate convention is Shinoda (1975), (2.3), pp. 81–82, as implemented
in `ReeTwo.Sylow`. Binary masks are little endian in the following ordered
bases, with `rj = root j` and `s = rootOne`:
* 0: `(r3,r2,r0,s²)`; 9: `(r3,r2,r1,s²)`;
* 12: `(r3,r2,s,r5)`;
* 2: `(r3,r0*r1,s²*r1)`;
* 3: `(r1*r3,r0,s²)`; 4: `(r1,r0,s²)`;
* 6: `(r1,r0*r3,s²*r3)`; 8: `(r1*r3,r0,s²*r3)`;
* 10: `(r1*r3,s*r0)`; 11: `(r1*r3,s*r0*r3)`;
* 14: `(r1,s*r0*r3)`.

These bases specify the intended coordinate constructions; this module proves
only the abstract stabilizers and the conditional assembly interface.
-/

namespace ReeTwo.SylowModel
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 4096
/-- An elementary abelian binary group in a specified rank. -/
public abbrev OrderProfileQuotient (n : ℕ) := Multiplicative (Fin n → ZMod 2)
/-- Rank of the proposed quotient for each residual representative. -/
@[expose] public def orderProfileRank (i : Fin 15) : ℕ :=
  ![4,3,3,3,3,3,3,3,3,4,2,2,4,3,2] i
/-- Color table indexed by the little-endian binary coordinate mask. -/
@[expose] public def orderProfileColor (i : Fin 15)
    (x : OrderProfileQuotient (orderProfileRank i)) : ℕ :=
  (![[0, 3, 3, 1, 2, 3, 3, 3, 1, 3, 3, 1, 4, 4, 4, 4],
    [],
    [0, 2, 2, 1, 3, 3, 3, 3],
    [0, 2, 1, 1, 1, 3, 3, 3],
    [0, 2, 1, 2, 1, 3, 3, 3],
    [],
    [0, 2, 2, 1, 2, 3, 3, 3],
    [],
    [0, 2, 1, 1, 2, 3, 3, 3],
    [0, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 3, 3, 3, 3],
    [0, 1, 2, 2],
    [0, 1, 2, 2],
    [0, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 3, 3, 3, 3],
    [],
    [0, 1, 2, 2]] i : List ℕ).getD
    (∑ j : Fin (orderProfileRank i), 2 ^ j.val * (x.toAdd j).val) 0
private def basis (n : ℕ) (j : Fin n) : OrderProfileQuotient n :=
  Multiplicative.ofAdd (fun k => if k = j then 1 else 0)
private def word2 (a b : OrderProfileQuotient 2) (x : OrderProfileQuotient 2) : OrderProfileQuotient 2 :=
  a ^ (x.toAdd 0).val * b ^ (x.toAdd 1).val
private theorem word2_hom (f : OrderProfileQuotient 2 →* OrderProfileQuotient 2) (x : OrderProfileQuotient 2) :
    word2 (f (basis 2 0)) (f (basis 2 1)) x = f x := by
  have hn : word2 (basis 2 0) (basis 2 1) x = x :=
    (by decide +kernel : ∀ x, word2 (basis 2 0) (basis 2 1) x = x) x
  simpa only [word2, map_mul, map_pow] using congrArg f hn
private def word3 (a b c : OrderProfileQuotient 3) (x : OrderProfileQuotient 3) : OrderProfileQuotient 3 :=
  a ^ (x.toAdd 0).val * b ^ (x.toAdd 1).val * c ^ (x.toAdd 2).val
private theorem word3_hom (f : OrderProfileQuotient 3 →* OrderProfileQuotient 3) (x : OrderProfileQuotient 3) :
    word3 (f (basis 3 0)) (f (basis 3 1)) (f (basis 3 2)) x = f x := by
  have hn : word3 (basis 3 0) (basis 3 1) (basis 3 2) x = x :=
    (by decide +kernel : ∀ x, word3 (basis 3 0) (basis 3 1) (basis 3 2) x = x) x
  simpa only [word3, map_mul, map_pow] using congrArg f hn
private def word4 (a b c d : OrderProfileQuotient 4) (x : OrderProfileQuotient 4) : OrderProfileQuotient 4 :=
  a ^ (x.toAdd 0).val * b ^ (x.toAdd 1).val * c ^ (x.toAdd 2).val * d ^ (x.toAdd 3).val
private theorem word4_hom (f : OrderProfileQuotient 4 →* OrderProfileQuotient 4) (x : OrderProfileQuotient 4) :
    word4 (f (basis 4 0)) (f (basis 4 1)) (f (basis 4 2)) (f (basis 4 3)) x = f x := by
  have hn : word4 (basis 4 0) (basis 4 1) (basis 4 2) (basis 4 3) x = x :=
    (by decide +kernel : ∀ x, word4 (basis 4 0) (basis 4 1) (basis 4 2) (basis 4 3) x = x) x
  simpa only [word4, map_mul, map_pow] using congrArg f hn
private theorem cert0 :
    ∀ a : OrderProfileQuotient 4, orderProfileColor 0 a = orderProfileColor 0 (basis 4 0) →
    ∀ b : OrderProfileQuotient 4, orderProfileColor 0 b = orderProfileColor 0 (basis 4 1) →
    ∀ c : OrderProfileQuotient 4, orderProfileColor 0 c = orderProfileColor 0 (basis 4 2) →
    ∀ d : OrderProfileQuotient 4, orderProfileColor 0 d = orderProfileColor 0 (basis 4 3) →
    (∀ x, orderProfileColor 0 (word4 a b c d x) = orderProfileColor 0 x) →
    ∀ x, (word4 a b c d)^[4] x = x := by
  unfold orderProfileColor orderProfileRank
  decide +kernel
private theorem cert2 :
    ∀ a : OrderProfileQuotient 3, orderProfileColor 2 a = orderProfileColor 2 (basis 3 0) →
    ∀ b : OrderProfileQuotient 3, orderProfileColor 2 b = orderProfileColor 2 (basis 3 1) →
    ∀ c : OrderProfileQuotient 3, orderProfileColor 2 c = orderProfileColor 2 (basis 3 2) →
    (∀ x, orderProfileColor 2 (word3 a b c x) = orderProfileColor 2 x) →
    ∀ x, (word3 a b c)^[4] x = x := by
  unfold orderProfileColor orderProfileRank
  decide +kernel
private theorem cert3 :
    ∀ a : OrderProfileQuotient 3, orderProfileColor 3 a = orderProfileColor 3 (basis 3 0) →
    ∀ b : OrderProfileQuotient 3, orderProfileColor 3 b = orderProfileColor 3 (basis 3 1) →
    ∀ c : OrderProfileQuotient 3, orderProfileColor 3 c = orderProfileColor 3 (basis 3 2) →
    (∀ x, orderProfileColor 3 (word3 a b c x) = orderProfileColor 3 x) →
    ∀ x, (word3 a b c)^[4] x = x := by
  unfold orderProfileColor orderProfileRank
  decide +kernel
private theorem cert4 :
    ∀ a : OrderProfileQuotient 3, orderProfileColor 4 a = orderProfileColor 4 (basis 3 0) →
    ∀ b : OrderProfileQuotient 3, orderProfileColor 4 b = orderProfileColor 4 (basis 3 1) →
    ∀ c : OrderProfileQuotient 3, orderProfileColor 4 c = orderProfileColor 4 (basis 3 2) →
    (∀ x, orderProfileColor 4 (word3 a b c x) = orderProfileColor 4 x) →
    ∀ x, (word3 a b c)^[4] x = x := by
  unfold orderProfileColor orderProfileRank
  decide +kernel
private theorem cert6 :
    ∀ a : OrderProfileQuotient 3, orderProfileColor 6 a = orderProfileColor 6 (basis 3 0) →
    ∀ b : OrderProfileQuotient 3, orderProfileColor 6 b = orderProfileColor 6 (basis 3 1) →
    ∀ c : OrderProfileQuotient 3, orderProfileColor 6 c = orderProfileColor 6 (basis 3 2) →
    (∀ x, orderProfileColor 6 (word3 a b c x) = orderProfileColor 6 x) →
    ∀ x, (word3 a b c)^[4] x = x := by
  unfold orderProfileColor orderProfileRank
  decide +kernel
private theorem cert8 :
    ∀ a : OrderProfileQuotient 3, orderProfileColor 8 a = orderProfileColor 8 (basis 3 0) →
    ∀ b : OrderProfileQuotient 3, orderProfileColor 8 b = orderProfileColor 8 (basis 3 1) →
    ∀ c : OrderProfileQuotient 3, orderProfileColor 8 c = orderProfileColor 8 (basis 3 2) →
    (∀ x, orderProfileColor 8 (word3 a b c x) = orderProfileColor 8 x) →
    ∀ x, (word3 a b c)^[4] x = x := by
  unfold orderProfileColor orderProfileRank
  decide +kernel
private theorem cert9 :
    ∀ a : OrderProfileQuotient 4, orderProfileColor 9 a = orderProfileColor 9 (basis 4 0) →
    ∀ b : OrderProfileQuotient 4, orderProfileColor 9 b = orderProfileColor 9 (basis 4 1) →
    ∀ c : OrderProfileQuotient 4, orderProfileColor 9 c = orderProfileColor 9 (basis 4 2) →
    ∀ d : OrderProfileQuotient 4, orderProfileColor 9 d = orderProfileColor 9 (basis 4 3) →
    (∀ x, orderProfileColor 9 (word4 a b c d x) = orderProfileColor 9 x) →
    ∀ x, (word4 a b c d)^[4] x = x := by
  unfold orderProfileColor orderProfileRank
  decide +kernel
private theorem cert10 :
    ∀ a : OrderProfileQuotient 2, orderProfileColor 10 a = orderProfileColor 10 (basis 2 0) →
    ∀ b : OrderProfileQuotient 2, orderProfileColor 10 b = orderProfileColor 10 (basis 2 1) →
    (∀ x, orderProfileColor 10 (word2 a b x) = orderProfileColor 10 x) →
    ∀ x, (word2 a b)^[4] x = x := by
  unfold orderProfileColor orderProfileRank
  decide +kernel
private theorem aut0_four (f : MulAut (OrderProfileQuotient 4))
    (h : ∀ x, orderProfileColor 0 (f x) = orderProfileColor 0 x) : f ^ 4 = 1 := by
  have hc := cert0 (f (basis 4 0)) (h _) (f (basis 4 1)) (h _) (f (basis 4 2)) (h _) (f (basis 4 3)) (h _)
  have hw := word4_hom f.toMonoidHom
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hw
  have hh := hc (by intro x; rw [hw]; exact h x)
  have he : word4 (f (basis 4 0)) (f (basis 4 1)) (f (basis 4 2)) (f (basis 4 3)) = f := funext hw
  rw [he] at hh
  apply MulEquiv.ext
  intro x
  exact hh x

private theorem aut2_four (f : MulAut (OrderProfileQuotient 3))
    (h : ∀ x, orderProfileColor 2 (f x) = orderProfileColor 2 x) : f ^ 4 = 1 := by
  have hc := cert2 (f (basis 3 0)) (h _) (f (basis 3 1)) (h _) (f (basis 3 2)) (h _)
  have hw := word3_hom f.toMonoidHom
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hw
  have hh := hc (by intro x; rw [hw]; exact h x)
  have he : word3 (f (basis 3 0)) (f (basis 3 1)) (f (basis 3 2)) = f := funext hw
  rw [he] at hh
  apply MulEquiv.ext
  intro x
  exact hh x

private theorem aut3_four (f : MulAut (OrderProfileQuotient 3))
    (h : ∀ x, orderProfileColor 3 (f x) = orderProfileColor 3 x) : f ^ 4 = 1 := by
  have hc := cert3 (f (basis 3 0)) (h _) (f (basis 3 1)) (h _) (f (basis 3 2)) (h _)
  have hw := word3_hom f.toMonoidHom
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hw
  have hh := hc (by intro x; rw [hw]; exact h x)
  have he : word3 (f (basis 3 0)) (f (basis 3 1)) (f (basis 3 2)) = f := funext hw
  rw [he] at hh
  apply MulEquiv.ext
  intro x
  exact hh x

private theorem aut4_four (f : MulAut (OrderProfileQuotient 3))
    (h : ∀ x, orderProfileColor 4 (f x) = orderProfileColor 4 x) : f ^ 4 = 1 := by
  have hc := cert4 (f (basis 3 0)) (h _) (f (basis 3 1)) (h _) (f (basis 3 2)) (h _)
  have hw := word3_hom f.toMonoidHom
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hw
  have hh := hc (by intro x; rw [hw]; exact h x)
  have he : word3 (f (basis 3 0)) (f (basis 3 1)) (f (basis 3 2)) = f := funext hw
  rw [he] at hh
  apply MulEquiv.ext
  intro x
  exact hh x

private theorem aut6_four (f : MulAut (OrderProfileQuotient 3))
    (h : ∀ x, orderProfileColor 6 (f x) = orderProfileColor 6 x) : f ^ 4 = 1 := by
  have hc := cert6 (f (basis 3 0)) (h _) (f (basis 3 1)) (h _) (f (basis 3 2)) (h _)
  have hw := word3_hom f.toMonoidHom
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hw
  have hh := hc (by intro x; rw [hw]; exact h x)
  have he : word3 (f (basis 3 0)) (f (basis 3 1)) (f (basis 3 2)) = f := funext hw
  rw [he] at hh
  apply MulEquiv.ext
  intro x
  exact hh x

private theorem aut8_four (f : MulAut (OrderProfileQuotient 3))
    (h : ∀ x, orderProfileColor 8 (f x) = orderProfileColor 8 x) : f ^ 4 = 1 := by
  have hc := cert8 (f (basis 3 0)) (h _) (f (basis 3 1)) (h _) (f (basis 3 2)) (h _)
  have hw := word3_hom f.toMonoidHom
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hw
  have hh := hc (by intro x; rw [hw]; exact h x)
  have he : word3 (f (basis 3 0)) (f (basis 3 1)) (f (basis 3 2)) = f := funext hw
  rw [he] at hh
  apply MulEquiv.ext
  intro x
  exact hh x

private theorem aut9_four (f : MulAut (OrderProfileQuotient 4))
    (h : ∀ x, orderProfileColor 9 (f x) = orderProfileColor 9 x) : f ^ 4 = 1 := by
  have hc := cert9 (f (basis 4 0)) (h _) (f (basis 4 1)) (h _) (f (basis 4 2)) (h _) (f (basis 4 3)) (h _)
  have hw := word4_hom f.toMonoidHom
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hw
  have hh := hc (by intro x; rw [hw]; exact h x)
  have he : word4 (f (basis 4 0)) (f (basis 4 1)) (f (basis 4 2)) (f (basis 4 3)) = f := funext hw
  rw [he] at hh
  apply MulEquiv.ext
  intro x
  exact hh x

private theorem aut10_four (f : MulAut (OrderProfileQuotient 2))
    (h : ∀ x, orderProfileColor 10 (f x) = orderProfileColor 10 x) : f ^ 4 = 1 := by
  have hc := cert10 (f (basis 2 0)) (h _) (f (basis 2 1)) (h _)
  have hw := word2_hom f.toMonoidHom
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hw
  have hh := hc (by intro x; rw [hw]; exact h x)
  have he : word2 (f (basis 2 0)) (f (basis 2 1)) = f := funext hw
  rw [he] at hh
  apply MulEquiv.ext
  intro x
  exact hh x

/-- Every automorphism preserving a listed order-profile color has fourth power one. -/
public theorem orderProfileColor_aut_four (i : Fin 15)
    (h1 : i ≠ 1) (h5 : i ≠ 5) (h7 : i ≠ 7) (h13 : i ≠ 13)
    (f : MulAut (OrderProfileQuotient (orderProfileRank i)))
    (h : ∀ x, orderProfileColor i (f x) = orderProfileColor i x) : f ^ 4 = 1 := by
  fin_cases i
  · exact aut0_four f h
  · exact (h1 rfl).elim
  · exact aut2_four f h
  · exact aut3_four f h
  · exact aut4_four f h
  · exact (h5 rfl).elim
  · exact aut6_four f h
  · exact (h7 rfl).elim
  · exact aut8_four f h
  · exact aut9_four f h
  · exact aut10_four f h
  · exact aut10_four f h
  · exact aut9_four f h
  · exact (h13 rfl).elim
  · exact aut10_four f h

/-- The concrete quotient and profile comparison still needed for a representative. -/
@[expose] public def OrderProfileModel (i : Fin 15) : Prop :=
  ∃ π : residualCandidate i →* OrderProfileQuotient (orderProfileRank i),
    Function.Surjective π ∧ π.ker = frattini (residualCandidate i) ∧
    ∀ x y, Subgroup.fiberProfile π orderOf x = Subgroup.fiberProfile π orderOf y →
      orderProfileColor i x = orderProfileColor i y

/-- Proposed counts of elements of orders 1, 2, and 4, respectively.
Their realization as group-theoretic counts is a separate obligation. -/
@[expose] public def orderProfileCounts (i : Fin 15)
    (x : OrderProfileQuotient (orderProfileRank i)) : ℕ × ℕ × ℕ :=
  (![[(1, 31, 32), (0, 16, 48), (0, 32, 32), (0, 0, 64), (0, 0, 0)],
    [],
    [(1, 47, 80), (0, 32, 96), (0, 0, 128), (0, 0, 0)],
    [(1, 47, 80), (0, 32, 96), (0, 0, 128), (0, 0, 0)],
    [(1, 47, 80), (0, 32, 96), (0, 0, 128), (0, 0, 0)],
    [],
    [(1, 47, 80), (0, 32, 96), (0, 0, 128), (0, 0, 0)],
    [],
    [(1, 47, 80), (0, 32, 96), (0, 0, 128), (0, 0, 0)],
    [(1, 47, 16), (0, 16, 48), (0, 0, 64), (0, 0, 0)],
    [(1, 47, 80), (0, 32, 224), (0, 0, 0)],
    [(1, 47, 80), (0, 32, 224), (0, 0, 0)],
    [(1, 47, 16), (0, 16, 48), (0, 0, 64), (0, 0, 0)],
    [],
    [(1, 47, 80), (0, 0, 256), (0, 0, 0)]] i : List (ℕ × ℕ × ℕ)).getD
    (orderProfileColor i x) (0,0,0)

/-- The three selected order counts distinguish the assigned colors. -/
public theorem orderProfileColor_eq_of_counts_eq (i : Fin 15) :
    ∀ x y, orderProfileCounts i x = orderProfileCounts i y →
      orderProfileColor i x = orderProfileColor i y := by
  fin_cases i <;> unfold orderProfileCounts orderProfileColor orderProfileRank <;> decide +kernel

/-- Exact counts for the three selected orders supply the profile comparison. -/
public theorem OrderProfileModel.of_counts (i : Fin 15)
    (π : residualCandidate i →* OrderProfileQuotient (orderProfileRank i))
    (hπ : Function.Surjective π) (hker : π.ker = frattini (residualCandidate i))
    (hc : ∀ x, (Subgroup.fiberProfile π orderOf x 1,
      Subgroup.fiberProfile π orderOf x 2, Subgroup.fiberProfile π orderOf x 4) =
        orderProfileCounts i x) : OrderProfileModel i := by
  refine ⟨π, hπ, hker, ?_⟩
  intro x y hxy
  apply orderProfileColor_eq_of_counts_eq i x y
  rw [← hc x, ← hc y, hxy]

end ReeTwo.SylowModel
