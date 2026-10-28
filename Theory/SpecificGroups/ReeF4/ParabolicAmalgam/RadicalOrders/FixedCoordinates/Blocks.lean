module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates.Scalars

/-!
# Geometric root-block data and the collected Ree twist

A root layout partitions a support into commuting pairs and B₂ quartets.
This is geometric data: an equivalence with the actual supported roots,
lengths, exceptional duality, inner products and root-sum identities. The
specified numbers of blocks are targets until a layout is constructed.

Two matrix relations suffice to collect the twist inside each block:
commutation of mixed-length roots with nonnegative inner product and the
B₂ swap with its two correction terms. Under those explicit relations the
collected maps are exactly `pairTwist` and `quartetTwist` from `Scalars`.
No inter-block commutation is used.

For the positive support, candidate blocks in simple-root coefficients are:
* pairs: (1000,0001), (1220,0121), (1222,1121), (1242,1221);
* quartets: (0100,0010,0110,0120), (0122,1110,1232,2342),
  (1100,0011,1111,1122), (1120,0111,1231,1342).
The Suzuki radical omits the first quartet, the linear radical the first pair.
This table is documentation, not a proved enumeration.

Source: the root calculation underlying Aschbacher–Smith F.1.12(I)(5),
printed p.263 (PDF p.274) of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section

namespace ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

def pairCount : Support → ℕ
  | .positive => 4
  | .radical .suzuki => 4
  | .radical .linear => 3

def quartetCount : Support → ℕ
  | .positive => 4
  | .radical .suzuki => 3
  | .radical .linear => 4

theorem dimension_eq (k : Support) :
    fixedDimension k = pairCount k + quartetCount k * 2 := by
  cases k with
  | positive => rfl
  | radical s => cases s <;> rfl

abbrev Slot (k : Support) :=
  (Fin (pairCount k) × Fin 2) ⊕ (Fin (quartetCount k) × Fin 4)

structure RootBlocks (k : Support) where
  roots : Slot k ≃ Root k
  pair_long (i : Fin (pairCount k)) : IsLongRoot (roots (.inl (i, 0))).val
  pair_dual (i : Fin (pairCount k)) :
    exceptionalRootPermutation (roots (.inl (i, 0))).val = (roots (.inl (i, 1))).val
  pair_dot (i : Fin (pairCount k)) :
    dot (roots (.inl (i, 0))).val.val (roots (.inl (i, 1))).val.val = 0
  quartet_long (i : Fin (quartetCount k)) : IsLongRoot (roots (.inr (i, 0))).val
  quartet_dual_zero (i : Fin (quartetCount k)) :
    exceptionalRootPermutation (roots (.inr (i, 0))).val = (roots (.inr (i, 1))).val
  quartet_short_two (i : Fin (quartetCount k)) : IsShortRoot (roots (.inr (i, 2))).val
  quartet_dual_two (i : Fin (quartetCount k)) :
    exceptionalRootPermutation (roots (.inr (i, 2))).val = (roots (.inr (i, 3))).val
  quartet_dot (i : Fin (quartetCount k)) :
    dot (roots (.inr (i, 0))).val.val (roots (.inr (i, 1))).val.val = -1
  quartet_add (i : Fin (quartetCount k)) :
    (roots (.inr (i, 2))).val.val =
      (roots (.inr (i, 0))).val.val + (roots (.inr (i, 1))).val.val
  quartet_add_two (i : Fin (quartetCount k)) :
    (roots (.inr (i, 3))).val.val =
      (roots (.inr (i, 0))).val.val + (2 : ℝ) • (roots (.inr (i, 1))).val.val

def MixedRootCommutation (m : ℕ) : Prop :=
  ∀ (r s : F4Chevalley.Root), typeF4RootPairing_base.IsPos r →
    typeF4RootPairing_base.IsPos s → IsLongRoot r → IsShortRoot s →
    0 ≤ dot r.val s.val → ∀ a b : CoefficientField m,
      Commute (rootGeneratorInGroup m r a) (rootGeneratorInGroup m s b)

def B2RootSwap (m : ℕ) : Prop :=
  ∀ (r s c d : F4Chevalley.Root), typeF4RootPairing_base.IsPos r →
    typeF4RootPairing_base.IsPos s → IsLongRoot r → IsShortRoot s →
    dot r.val s.val = -1 → c.val = r.val + s.val →
    d.val = r.val + (2 : ℝ) • s.val → ∀ a b : CoefficientField m,
      rootGeneratorInGroup m s b * rootGeneratorInGroup m r a =
        rootGeneratorInGroup m r a * rootGeneratorInGroup m s b *
          rootGeneratorInGroup m c (a * b) * rootGeneratorInGroup m d (a * b ^ 2)

def pairWord (m : ℕ) (r : Fin 2 → F4Chevalley.Root)
    (t : Fin 2 → CoefficientField m) : SplitGroup m :=
  rootGeneratorInGroup m (r 0) (t 0) * rootGeneratorInGroup m (r 1) (t 1)

def quartetWord (m : ℕ) (r : Fin 4 → F4Chevalley.Root)
    (t : Fin 4 → CoefficientField m) : SplitGroup m :=
  rootGeneratorInGroup m (r 0) (t 0) * rootGeneratorInGroup m (r 1) (t 1) *
    rootGeneratorInGroup m (r 2) (t 2) * rootGeneratorInGroup m (r 3) (t 3)

private theorem root_add (m : ℕ) (r : F4Chevalley.Root) (a b : CoefficientField m) :
    rootGeneratorInGroup m r (a + b) =
      rootGeneratorInGroup m r a * rootGeneratorInGroup m r b := by
  apply Subtype.ext
  exact F4Chevalley.rootCurve_add r a b

private theorem dual_back {r s : F4Chevalley.Root}
    (h : exceptionalRootPermutation r = s) : exceptionalRootPermutation s = r := by
  rw [← h, exceptionalRootPermutation_involutive]

private theorem dual_short {r s : F4Chevalley.Root}
    (hr : IsLongRoot r) (h : exceptionalRootPermutation r = s) : IsShortRoot s := by
  rw [← h]
  exact (exceptionalRootPermutation_long_iff r).mp hr

private theorem dual_long {r s : F4Chevalley.Root}
    (hr : IsShortRoot r) (h : exceptionalRootPermutation r = s) : IsLongRoot s := by
  rw [← h]
  exact (exceptionalRootPermutation_short_iff r).mp hr

theorem reeTwist_pairWord (m : ℕ) (r : Fin 2 → F4Chevalley.Root)
    (hl : IsLongRoot (r 0)) (hd : exceptionalRootPermutation (r 0) = r 1)
    (hc : ∀ a b : CoefficientField m,
      Commute (rootGeneratorInGroup m (r 0) a) (rootGeneratorInGroup m (r 1) b))
    (t : Fin 2 → CoefficientField m) :
    reeTwist m (pairWord m r t) = pairWord m r (pairTwist m t) := by
  rw [pairWord, map_mul, reeTwist_rootGenerator_long m _ hl,
    reeTwist_rootGenerator_short m _ (dual_short hl hd), hd, dual_back hd]
  exact (hc _ _).eq.symm

private theorem collect_four {G : Type*} [Monoid G] (P A D E B : G)
    (hD : Commute D B) (hE : Commute E B) :
    P * A * D * E * B = P * (A * B) * (D * E) := by
  have h := (hD.mul_left hE).eq
  calc
    P * A * D * E * B = P * A * (D * E * B) := by simp only [mul_assoc]
    _ = P * A * (B * (D * E)) := by rw [h]
    _ = P * (A * B) * (D * E) := by simp only [mul_assoc]

theorem reeTwist_quartetWord (m : ℕ) (r : Fin 4 → F4Chevalley.Root)
    (hl : IsLongRoot (r 0)) (hs : IsShortRoot (r 2))
    (h01 : exceptionalRootPermutation (r 0) = r 1)
    (h23 : exceptionalRootPermutation (r 2) = r 3)
    (hc : ∀ a b : CoefficientField m,
      Commute (rootGeneratorInGroup m (r 2) a) (rootGeneratorInGroup m (r 3) b))
    (hw : ∀ a b : CoefficientField m,
      rootGeneratorInGroup m (r 1) b * rootGeneratorInGroup m (r 0) a =
        rootGeneratorInGroup m (r 0) a * rootGeneratorInGroup m (r 1) b *
          rootGeneratorInGroup m (r 2) (a * b) * rootGeneratorInGroup m (r 3) (a * b ^ 2))
    (t : Fin 4 → CoefficientField m) :
    reeTwist m (quartetWord m r t) = quartetWord m r (quartetTwist m t) := by
  rw [quartetWord, map_mul, map_mul, map_mul,
    reeTwist_rootGenerator_long m _ hl,
    reeTwist_rootGenerator_short m _ (dual_short hl h01),
    reeTwist_rootGenerator_short m _ hs,
    reeTwist_rootGenerator_long m _ (dual_long hs h23),
    h01, dual_back h01, h23, dual_back h23, hw]
  change _ = rootGeneratorInGroup m (r 0) (titsEnd m (t 1)) *
    rootGeneratorInGroup m (r 1) (halfFrobenius m (t 0)) *
    rootGeneratorInGroup m (r 2)
      (titsEnd m (t 1) * halfFrobenius m (t 0) + halfFrobenius m (t 3)) *
    rootGeneratorInGroup m (r 3)
      (titsEnd m (t 1) * halfFrobenius m (t 0) ^ 2 + titsEnd m (t 2))
  rw [root_add, root_add]
  exact collect_four _ _ _ _ _ (hc _ _).symm (hc _ _).symm

theorem RootBlocks.quartet_top_dot {k : Support} (B : RootBlocks k)
    (i : Fin (quartetCount k)) :
    dot (B.roots (.inr (i, 3))).val.val (B.roots (.inr (i, 2))).val.val = 1 := by
  have hl := isLongRoot_norm _ (B.quartet_long i)
  have hs := isShortRoot_norm _ (dual_short (B.quartet_long i) (B.quartet_dual_zero i))
  have hdot := B.quartet_dot i
  rw [B.quartet_add, B.quartet_add_two]
  have hsym : dot (B.roots (.inr (i, 1))).val.val (B.roots (.inr (i, 0))).val.val = -1 := by
    simpa only [dot, mul_comm] using hdot
  change (_ + (2 : ℝ) • _) ⬝ᵥ (_ + _) = 1
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, smul_eq_mul]
  change dot _ _ + 2 * dot _ _ + (dot _ _ + 2 * dot _ _) = 1
  rw [hl, hs, hdot, hsym]
  norm_num

private theorem supported_positive {k : Support} {r : F4Chevalley.Root}
    (h : Supported k r) : typeF4RootPairing_base.IsPos r := by
  cases k with
  | positive => exact h
  | radical s => exact h.1

theorem RootBlocks.twist_pair {k : Support} (B : RootBlocks k) (m : ℕ)
    (hcomm : MixedRootCommutation m) (i : Fin (pairCount k))
    (t : Fin 2 → CoefficientField m) :
    reeTwist m (pairWord m (fun j => (B.roots (.inl (i, j))).val) t) =
      pairWord m (fun j => (B.roots (.inl (i, j))).val) (pairTwist m t) := by
  apply reeTwist_pairWord m _ (B.pair_long i) (B.pair_dual i)
  exact hcomm _ _ (supported_positive (B.roots (.inl (i, 0))).property)
    (supported_positive (B.roots (.inl (i, 1))).property)
    (B.pair_long i) (dual_short (B.pair_long i) (B.pair_dual i))
    (by rw [B.pair_dot])

theorem RootBlocks.twist_quartet {k : Support} (B : RootBlocks k) (m : ℕ)
    (hcomm : MixedRootCommutation m) (hswap : B2RootSwap m)
    (i : Fin (quartetCount k)) (t : Fin 4 → CoefficientField m) :
    reeTwist m (quartetWord m (fun j => (B.roots (.inr (i, j))).val) t) =
      quartetWord m (fun j => (B.roots (.inr (i, j))).val) (quartetTwist m t) := by
  apply reeTwist_quartetWord m _ (B.quartet_long i) (B.quartet_short_two i)
    (B.quartet_dual_zero i) (B.quartet_dual_two i)
  · intro a b
    exact (hcomm _ _ (supported_positive (B.roots (.inr (i, 3))).property)
      (supported_positive (B.roots (.inr (i, 2))).property)
      (dual_long (B.quartet_short_two i) (B.quartet_dual_two i))
      (B.quartet_short_two i) (by rw [B.quartet_top_dot]; norm_num) b a).symm
  · exact hswap _ _ _ _ (supported_positive (B.roots (.inr (i, 0))).property)
      (supported_positive (B.roots (.inr (i, 1))).property) (B.quartet_long i)
      (dual_short (B.quartet_long i) (B.quartet_dual_zero i))
      (B.quartet_dot i) (B.quartet_add i) (B.quartet_add_two i)

end ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates
