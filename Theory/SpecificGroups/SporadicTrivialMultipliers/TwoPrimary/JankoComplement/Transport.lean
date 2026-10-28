module
public import Theory.SpecificGroups.SporadicTrivialMultipliers.TwoPrimary.JankoComplement.Relations

/-!
# From an invariant binary character to a normal core complement

The kernel of a binary character separating the central double kernel maps
onto the core and is disjoint from that kernel. Invariance under lifts of the
two actual local generators, together with centrality of the covering kernel,
makes this subgroup normal in the whole extension.

For a coordinate lift, the actual group relators supply every premise of the
finite lower-row certificate. Its corrected functional gives the character;
no relation, action-factorization or normality assumption remains in this
transport beyond the explicitly supplied coordinate data.

Source: Aschbacher–Smith I.1.1–I.1.5, printed pp.407–408; GLS3 Section 6.1;
the marked generators are the literal ATLAS `J4G1-max1W1` outputs.
-/

@[expose] public section
namespace Janko4.TwoPrimary.InvariantComplement
open Cardinality Subgroup
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup

variable {L : Type*} [Group L] [Finite L]

/-- A binary character of the elementary preimage which separates the central
kernel and is fixed by the two actual local generators gives a normal complement. -/
theorem normal_complement_of_functional
    (q : L →* Local) (hq : Function.Surjective q) (hc : q.ker ≤ center L)
    (hk : Nat.card q.ker = 2) (z : q.ker) (hz : z ≠ 1)
    (a b : L) (ha : q a = x) (hb : q b = y)
    (ψ : Core.comap q →* Multiplicative Bool)
    (hψz : ψ ⟨z.val, by change q z.val ∈ Core; rw [z.property]; exact Core.one_mem⟩ =
      Multiplicative.ofAdd true)
    (hψa : ∀ n, ψ (MulAut.conjNormal a⁻¹ n) = ψ n)
    (hψb : ∀ n, ψ (MulAut.conjNormal b⁻¹ n) = ψ n) :
    ∃ T : Subgroup L, T.Normal ∧ Disjoint q.ker T ∧ T.map q = Core := by
  let N := Core.comap q
  let S := ψ.ker
  let T : Subgroup L := S.map N.subtype
  have normalizes (g : L) (hg : ∀ n, ψ (MulAut.conjNormal g⁻¹ n) = ψ n) :
      g ∈ normalizer (T : Set L) := by
    have hi : g⁻¹ ∈ normalizer (T : Set L) := by
      apply mem_normalizer_fintype
      rintro t ⟨n, hn, rfl⟩
      refine ⟨MulAut.conjNormal g⁻¹ n, ?_, ?_⟩
      · change ψ (MulAut.conjNormal g⁻¹ n) = 1
        exact (hg n).trans hn
      · change g⁻¹ * n.val * (g⁻¹)⁻¹ = g⁻¹ * n.val * (g⁻¹)⁻¹
        rfl
    simpa only [inv_inv] using (normalizer (T : Set L)).inv_mem hi
  have hker : q.ker ≤ normalizer (T : Set L) := by
    intro k hk'
    apply normalizes k
    intro n
    congr 1
    apply Subtype.ext
    change k⁻¹ * n.val * (k⁻¹)⁻¹ = n.val
    rw [← mem_center_iff.mp (hc (q.ker.inv_mem hk')) n.val, mul_inv_cancel_right]
  have hmap : (normalizer (T : Set L)).map q = ⊤ := by
    apply top_unique
    rw [← localXY_generate matrixA_mul_self matrixB_pow_four]
    apply (closure_le _).mpr
    intro g hg
    rcases hg with rfl | hg
    · exact ⟨a, normalizes a hψa, ha⟩
    · rw [Set.mem_singleton_iff] at hg
      subst g
      exact ⟨b, normalizes b hψb, hb⟩
  have hTn : T.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    intro g _
    have hm : q g ∈ (normalizer (T : Set L)).map q := hmap ▸ mem_top _
    obtain ⟨t, ht, htg⟩ := hm
    have hd : g * t⁻¹ ∈ q.ker := by
      change q (g * t⁻¹) = 1
      rw [map_mul, map_inv, htg, mul_inv_cancel]
    simpa only [inv_mul_cancel_right] using
      (normalizer (T : Set L)).mul_mem (hker hd) ht
  obtain ⟨z₀, hz₀, huniq⟩ := (Nat.card_eq_two_iff' (1 : q.ker)).mp hk
  have huniqz (w : q.ker) (hw : w ≠ 1) : w = z :=
    (huniq w hw).trans (huniq z hz).symm
  have hdisj : Disjoint q.ker T := by
    apply disjoint_def.mpr
    intro t ht hT
    obtain ⟨n, hn, rfl⟩ := hT
    by_cases h1 : n.val = 1
    · exact h1
    have hnz : n = ⟨z.val, by change q z.val ∈ Core; rw [z.property]; exact Core.one_mem⟩ :=
      Subtype.ext (congrArg (fun t : q.ker => (t : L)) (huniqz ⟨n.val, ht⟩
        (fun h => h1 (congrArg Subtype.val h))))
    change ψ n = 1 at hn
    rw [hnz, hψz] at hn
    exact Bool.noConfusion (congrArg Multiplicative.toAdd hn)
  have hTmap : T.map q = Core := by
    apply le_antisymm
    · rintro v ⟨t, ⟨n, hn, rfl⟩, rfl⟩
      exact n.property
    · intro v hv
      obtain ⟨t, ht⟩ := hq v
      let n : N := ⟨t, by change q t ∈ Core; rw [ht]; exact hv⟩
      let zN : N := ⟨z.val, by change q z.val ∈ Core; rw [z.property]; exact Core.one_mem⟩
      have hψzN : ψ zN = Multiplicative.ofAdd true := hψz
      cases hψn : (ψ n).toAdd
      · have hn : n ∈ S := by
          change ψ n = 1
          exact Multiplicative.toAdd.injective hψn
        exact ⟨n.val, ⟨n, hn, rfl⟩, ht⟩
      · refine ⟨(n * zN).val, ⟨n * zN, ?_, rfl⟩, ?_⟩
        · change ψ (n * zN) = 1
          rw [map_mul, hψzN]
          apply Multiplicative.toAdd.injective
          change (ψ n).toAdd + true = false
          rw [hψn]
          rfl
        · change q (t * z.val) = v
          rw [map_mul, ht, z.property, mul_one]
  exact ⟨T, hTn, hdisj, hTmap⟩

/-- Coordinates on a central-line lift of the literal eleven-space. The action
fields specify quotient matrices, with arbitrary lower rows retained. -/
structure LiftCoordinates (q : L →* Local) (a b : L) (z : q.ker)
    (d : Fin 22 → Bool) where
  equiv : Core.comap q ≃ V × Bool
  map_one : equiv 1 = (0, false)
  map_mul : ∀ n m, equiv (n * m) =
    ((equiv n).1 ^^^ (equiv m).1, (equiv n).2 + (equiv m).2)
  map_central : equiv ⟨z.val, by
    change q z.val ∈ Core; rw [z.property]; exact Core.one_mem⟩ = (0, true)
  map_conj_x : ∀ n, equiv (MulAut.conjNormal a⁻¹ n) = liftStep d false (equiv n)
  map_conj_y : ∀ n, equiv (MulAut.conjNormal b⁻¹ n) = liftStep d true (equiv n)

omit [Finite L] in
theorem LiftCoordinates.map_word
    {q : L →* Local} {a b : L} {z : q.ker} {d : Fin 22 → Bool}
    (c : LiftCoordinates q a b z d) (w : List Bool) (n : Core.comap q) :
    c.equiv (MulAut.conjNormal (wordValue a b w)⁻¹ n) = liftWord d w (c.equiv n) := by
  induction w generalizing n with
  | nil => simp only [wordValue, List.map_nil, List.prod_nil, inv_one, _root_.map_one,
      MulAut.one_apply, liftWord, List.foldl_nil]
  | cons s w ih =>
    simp only [wordValue, List.map_cons, List.prod_cons, mul_inv_rev, _root_.map_mul,
      MulAut.mul_apply]
    change c.equiv (MulAut.conjNormal (wordValue a b w)⁻¹
      (MulAut.conjNormal (if s then b else a)⁻¹ n)) = _
    rw [ih]
    cases s
    · exact congrArg (liftWord d w) (c.map_conj_x n)
    · exact congrArg (liftWord d w) (c.map_conj_y n)

omit [Finite L] in
theorem LiftCoordinates.relators
    {q : L →* Local} {a b : L} {z : q.ker} {d : Fin 22 → Bool}
    (c : LiftCoordinates q a b z d) (he : ElementaryPreimage q)
    (ha : q a = x) (hb : q b = y) :
    ∀ r : Fin 5, ∀ w : V × Bool, liftWord d (relator r) w = w := by
  intro r w
  obtain ⟨n, rfl⟩ := c.equiv.surjective w
  rw [← c.map_word]
  congr 1
  apply Subtype.ext
  simpa only [MulAut.conjNormal_apply, inv_inv] using
    lifted_relator_conj q he a b ha hb r n.val n.property

/-- Applying the binary certificate to coordinates of an actual central
extension constructs its normal complement. Only the coordinate construction
remains to be supplied; all relator and normality premises are discharged here. -/
theorem normal_complement_of_coordinates
    (q : L →* Local) (hq : Function.Surjective q) (hc : q.ker ≤ center L)
    (hk : Nat.card q.ker = 2) (he : ElementaryPreimage q)
    (z : q.ker) (hz : z ≠ 1) (a b : L) (ha : q a = x) (hb : q b = y)
    (d : Fin 22 → Bool) (c : LiftCoordinates q a b z d) :
    ∃ T : Subgroup L, T.Normal ∧ Disjoint q.ker T ∧ T.map q = Core := by
  let ψ : Core.comap q →* Multiplicative Bool := {
    toFun n := Multiplicative.ofAdd (functional d (c.equiv n))
    map_one' := by
      change functional d (c.equiv 1) = false
      rw [c.map_one]
      change false + evalRow (correction d) 0 = false
      rw [evalRow_zero]
      rfl
    map_mul' := by
      intro n m
      apply Multiplicative.toAdd.injective
      change functional d (c.equiv (n * m)) =
        functional d (c.equiv n) + functional d (c.equiv m)
      rw [c.map_mul, functional_add] }
  apply normal_complement_of_functional q hq hc hk z hz a b ha hb ψ
  · change functional d (c.equiv _) = true
    rw [c.map_central]
    exact functional_central d
  · intro n
    apply Multiplicative.toAdd.injective
    change functional d (c.equiv (MulAut.conjNormal a⁻¹ n)) = functional d (c.equiv n)
    rw [c.map_conj_x]
    exact fixed_functional d (c.relators he ha hb) false (c.equiv n)
  · intro n
    apply Multiplicative.toAdd.injective
    change functional d (c.equiv (MulAut.conjNormal b⁻¹ n)) = functional d (c.equiv n)
    rw [c.map_conj_y]
    exact fixed_functional d (c.relators he ha hb) true (c.equiv n)

end Janko4.TwoPrimary.InvariantComplement
