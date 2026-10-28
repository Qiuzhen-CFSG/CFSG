module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.FiniteBound.Criteria

/-!
# Normality witnesses and fixed-row bounds

Normality transfers membership across a pointwise conjugacy certificate.
Exponent two and commutativity exclude a moved square or a noncommuting
conjugate. Finally, forgetting subgroup-fixedness embeds `FixedMasks B` into
any finite set defined by row equations of elements of B.

All rows use the exact `starMask` convention of `FixedCoordinates`. The literal
permutations are those of `SylowData` (ATLAS max1 words), and the pair labels
are from `Image.StarData`. No catalogue or numerical table is assumed valid.
-/

@[expose] public section
namespace Janko4.LocalStructure.SylowCore.FiniteBoundCertificate.NormalWeights
open Cardinality.QuotientCount.Image
open Simplicity.Max1Fusion.QuotientInvolutions

/-- The actual eleven image rows, in the unchanged pair-label convention. -/
def rows (i : Index) : Fin 11 → ℕ :=
  fun k => pairLabel (perm i (basisPair k).1) (perm i (basisPair k).2)

/-- A pointwise certificate for conjugacy, avoiding inverse evaluation. -/
def Conjugates (i q y : Index) : Prop :=
  ∀ p : Fin 24, perm q (perm i p) = perm y (perm q p)

instance (i q y : Index) : Decidable (Conjugates i q y) :=
  inferInstanceAs (Decidable (∀ _p : Fin 24, _))

private theorem mem_of_mul_eq {G : Type*} [Group G] (B : Subgroup G)
    (hn : B.Normal) (x g y : G) (hx : x ∈ B) (h : g * x = y * g) : y ∈ B := by
  have hy : y = g * x * g⁻¹ := by rw [h, mul_inv_cancel_right]
  rw [hy]
  exact hn.conj_mem _ hx _

private theorem mem_of_perm_eq {G : Type*} [Group G] {X : Type*}
    (B : Subgroup G) (hn : B.Normal) (f : G →* Equiv.Perm X)
    (hf : Function.Injective f) (x g y : G) (hx : x ∈ B)
    (h : ∀ p, f g (f x p) = f y (f g p)) : y ∈ B := by
  apply mem_of_mul_eq B hn x g y hx
  apply hf
  simp only [map_mul]
  exact Equiv.ext h

private theorem permHom_injective : Function.Injective permHom := by
  intro x y h
  exact Subtype.ext (Subtype.ext h)

theorem mem_of_conjugates (B : Subgroup sylowCandidate) (hn : B.Normal)
    (i q y : Index) (hi : element i ∈ B) (h : Conjugates i q y) : element y ∈ B :=
  mem_of_perm_eq B hn permHom permHom_injective (element i) (element q) (element y) hi h

private theorem perm_square {G X : Type*} [Group G] (B : Subgroup G)
    [IsElementaryAbelian 2 B] (f : G →* Equiv.Perm X) (x : G) (hx : x ∈ B) (p : X) :
    f x (f x p) = p := by
  have h := congrArg (fun g : G => f g p)
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx)
  simpa only [map_pow, pow_two, map_mul, map_one, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using h

theorem square_point (B : Subgroup sylowCandidate) [IsElementaryAbelian 2 B]
    (i : Index) (hi : element i ∈ B) (p : Fin 24) : perm i (perm i p) = p :=
  perm_square B permHom (element i) hi p

private theorem perm_commute {G X : Type*} [Group G] (B : Subgroup G)
    [IsElementaryAbelian 2 B] (f : G →* Equiv.Perm X) (x y : G)
    (hx : x ∈ B) (hy : y ∈ B) (p : X) : f x (f y p) = f y (f x p) := by
  have h := congrArg (fun g : G => f g p) (setLike_mul_comm hx hy)
  simpa only [map_mul, Equiv.Perm.mul_apply] using h

theorem commute_point (B : Subgroup sylowCandidate) [IsElementaryAbelian 2 B]
    (i j : Index) (hi : element i ∈ B) (hj : element j ∈ B) (p : Fin 24) :
    perm i (perm j p) = perm j (perm i p) :=
  perm_commute B permHom (element i) (element j) hi hj p

/-- Masks satisfying a short list of cached row equations. -/
def RowSolutions (rs : List (Fin 11 → ℕ)) :=
  {m : Fin 2048 // rs.all (fun r => maskImage r m.val == m.val) = true}

instance (rs : List (Fin 11 → ℕ)) : Fintype (RowSolutions rs) :=
  inferInstanceAs (Fintype {_m : Fin 2048 // _})

theorem card_le_rows (B : Subgroup sylowCandidate) (cs : List Index)
    (rs : List (Fin 11 → ℕ)) (hr : cs.map rows = rs)
    (hm : ∀ i ∈ cs, element i ∈ B) (n : ℕ)
    (hc : Fintype.card (RowSolutions rs) = n) : Nat.card (FixedMasks B) ≤ n := by
  let f : FixedMasks B → RowSolutions rs := fun m => ⟨m.val, by
    rw [← hr, List.all_map]
    apply List.all_eq_true.mpr
    intro i hi
    apply beq_iff_eq.mpr
    exact m.property ⟨element i, hm i hi⟩⟩
  have h := Nat.card_le_card_of_injective f (by
    intro a b hab
    exact Subtype.ext (congrArg (fun z : RowSolutions rs => z.val) hab))
  simpa only [Nat.card_eq_fintype_card, hc] using h

theorem card_le_conjugate_rows (B : Subgroup sylowCandidate) (hn : B.Normal)
    (i : Index) (hi : element i ∈ B) (cs : List (Index × Index))
    (hs : ∀ c ∈ cs, Conjugates i c.1 c.2)
    (rs : List (Fin 11 → ℕ)) (hr : cs.map (fun c => rows c.2) = rs)
    (n : ℕ) (hc : Fintype.card (RowSolutions rs) = n) : Nat.card (FixedMasks B) ≤ n := by
  apply card_le_rows B (cs.map Prod.snd) rs (by simpa only [List.map_map, Function.comp_def] using hr) _ n hc
  intro y hy
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
  exact mem_of_conjugates B hn i c.1 c.2 hi (hs c hc)

end Janko4.LocalStructure.SylowCore.FiniteBoundCertificate.NormalWeights
