module

public import Theory.Mathieu.M22.UniversalMultiplier.CyclicFour.OrderCertificate.Lifts
public import Theory.GroupTheory.WordSubgroup.FiniteCover

/-!
# Order bounds from the lifted M₂₂ Schreier identities

Quotient the actual paired group by the powers of its specified central word.
The correction powers vanish, so word induction through the literal lifted
chain bounds the quotient by 22·21·20·16·3. The final cubic relation bounds
the last cyclic subgroup by three. Multiplying by the central subgroup's order,
at most four, gives 1,774,080. No kernel exhaustion, multiplier value or
recognition of the degree-4928 action is used.

The four finite transition families and the terminal cubic identity remain
explicit premises. They must be proved before the order bound is unconditional
apart from centrality and fourth-power triviality. Source application:
Aschbacher–Smith I.1.1 and I.1.3(4), printed p.407.
-/

namespace Sporadic.Mathieu.M22CyclicFour.OrderCertificate
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration

private theorem mapped_inv {G : Type*} [Group G] {n : ℕ}
    (f : Model →* G) (p : Fin n → Model) (i : Fin (n + n)) :
    f (symmGen p (symmInv i)) = (f (symmGen p i))⁻¹ := by
  rw [symmGen_inv, map_inv]

private noncomputable def imageWords {G : Type*} [Group G] {n : ℕ}
    (f : Model →* G) (p : Fin n → Model) : Subgroup G :=
  wordSubgroup (fun i => f (symmGen p i)) symmInv (mapped_inv f p)

private theorem imageWords_eq_closure {G : Type*} [Group G] {n : ℕ}
    (f : Model →* G) (p : Fin n → Model) :
    imageWords f p = Subgroup.closure (Set.range fun i => f (p i)) := by
  have he : (fun i => f (symmGen p i)) = symmGen (fun i => f (p i)) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [symmGen, Fin.addCases_left, Fin.addCases_right, map_inv]
  unfold imageWords
  simp only [he]
  exact symm_wordSubgroup_eq_closure _

private theorem step_bound {G : Type*} [Group G] [Finite G] {n p m : ℕ}
    (f : Model →* G) (hz : f centralWord = 1)
    (a : Fin n → Model) (b : Fin p → Model)
    (repWord : Fin m → List (Fin (n + n)))
    (act : Fin (n + n) → Fin m → Fin m)
    (factor : Fin (n + n) → Fin m → List (Fin (p + p)))
    (base : Fin m) (hbase : repWord base = [])
    (hb : ∀ i, f (b i) ∈ imageWords f a)
    (hstep : ∀ i r, ∃ k : Fin 4,
      symmGen a i * evalWord (symmGen a) (repWord r) =
        evalWord (symmGen a) (repWord (act i r)) *
          evalWord (symmGen b) (factor i r) * centralWord ^ k.val) :
    Nat.card (imageWords f a) ≤ m * Nat.card (imageWords f b) := by
  apply wordSubgroup_card_le_mul_next
    (fun i => f (symmGen a i)) symmInv (mapped_inv f a)
    (fun i => f (symmGen b i)) symmInv (mapped_inv f b)
    (fun r => evalWord (fun i => f (symmGen a i)) (repWord r)) act factor base
  · intro r
    exact ⟨repWord r, rfl⟩
  · apply wordSubgroup_le_of_gen_mem
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [imageWords, symmGen, Fin.addCases_left] using hb j
    · simpa only [imageWords, symmGen, Fin.addCases_right, map_inv] using (imageWords f a).inv_mem (hb j)
  · rw [hbase]

  · intro i r
    obtain ⟨k, hk⟩ := hstep i r
    simpa only [map_mul, map_evalWord, map_pow, hz, one_pow, mul_one] using congrArg f hk

private theorem quotient_bound {G : Type*} [Group G] [Finite G]
    (f : Model →* G) (hf : Function.Surjective f) (hz : f centralWord = 1)
    (h0 : Step0) (h1 : Step1) (h2 : Step2) (h3 : Step3) (ht : Terminal) :
    Nat.card G ≤ 443520 := by
  have htop : imageWords f positive0 = ⊤ := by
    rw [imageWords_eq_closure]
    have hr : (Set.range fun i => f (positive0 i)) = {f generatorA, f generatorB} := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp [positive0]
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    rw [hr]
    have hm := congrArg (fun H : Subgroup Model => H.map f) generators_closure
    rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hf] at hm
    exact hm
  have h4 : Nat.card (imageWords f positive4) ≤ 3 := by
    have he : imageWords f positive4 = Subgroup.zpowers (f (gen4 0)) := by
      rw [imageWords_eq_closure]
      have hr : (Set.range fun i => f (positive4 i)) = {f (gen4 0)} := by
        ext x
        constructor
        · rintro ⟨i, rfl⟩
          fin_cases i
          exact Set.mem_singleton _
        · rintro rfl
          exact ⟨0, rfl⟩
      rw [hr, ← Subgroup.zpowers_eq_closure]
    rw [he, Nat.card_zpowers]
    apply orderOf_le_of_pow_eq_one (by decide : 0 < 3)
    rw [← map_pow, ht, hz]
  have hbound3 : Nat.card (imageWords f positive3) ≤
      16 * Nat.card (imageWords f positive4) := by
    apply step_bound f hz positive3 positive4
      m22L3RepWord m22L3Act m22L3Factor 0 rfl
    · intro i
      change f (evalWord gen3 (m22L4GenWord (Fin.castAdd 1 i))) ∈ _
      rw [map_evalWord]
      exact ⟨m22L4GenWord (Fin.castAdd 1 i), rfl⟩
    · exact h3
  have hbound2 : Nat.card (imageWords f positive2) ≤
      20 * Nat.card (imageWords f positive3) := by
    apply step_bound f hz positive2 positive3
      m22L2RepWord m22L2Act m22L2Factor 0 rfl
    · intro i
      change f (evalWord gen2 (m22L3GenWord (Fin.castAdd 3 i))) ∈ _
      rw [map_evalWord]
      exact ⟨m22L3GenWord (Fin.castAdd 3 i), rfl⟩
    · exact h2
  have hbound1 : Nat.card (imageWords f positive1) ≤
      21 * Nat.card (imageWords f positive2) := by
    apply step_bound f hz positive1 positive2
      m22L1RepWord m22L1Act m22L1Factor 0 rfl
    · intro i
      change f (evalWord gen1 (m22L2GenWord (Fin.castAdd 4 i))) ∈ _
      rw [map_evalWord]
      exact ⟨m22L2GenWord (Fin.castAdd 4 i), rfl⟩
    · exact h1
  have hbound0 : Nat.card (imageWords f positive0) ≤
      22 * Nat.card (imageWords f positive1) := by
    apply step_bound f hz positive0 positive1
      m22L0RepWord m22L0Act m22L0Factor 0 rfl
    · intro i
      change f (evalWord gen0 (m22L1GenWord (Fin.castAdd 3 i))) ∈ _
      rw [map_evalWord]
      exact ⟨m22L1GenWord (Fin.castAdd 3 i), rfl⟩
    · exact h0
  rw [htop, Subgroup.card_top] at hbound0
  omega

/-- The finite lifted Schreier identities give the required order bound for
exactly the paired model. Centrality is used only to take the central quotient. -/
public theorem order_le_of_lifted_steps
    (hz : centralWord ^ 4 = 1) (hc : centralWord ∈ Subgroup.center Model)
    (h0 : Step0) (h1 : Step1) (h2 : Step2) (h3 : Step3) (ht : Terminal) :
    Nat.card Model ≤ 1774080 := by
  let Z := Subgroup.zpowers centralWord
  have hZ : Z ≤ Subgroup.center Model := Subgroup.zpowers_le.mpr hc
  let : Z.Normal := ⟨by
    intro n hn g
    rw [(Subgroup.mem_center_iff.mp (hZ hn)) g, mul_inv_cancel_right]
    exact hn⟩
  let f := QuotientGroup.mk' Z
  have hq : Nat.card (Model ⧸ Z) ≤ 443520 :=
    quotient_bound f (QuotientGroup.mk'_surjective Z)
      ((QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers centralWord))
      h0 h1 h2 h3 ht
  have hzcard : Nat.card Z ≤ 4 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by decide) hz
  have hcard := Z.card_mul_index
  rw [Subgroup.index_eq_card] at hcard
  calc
    Nat.card Model = Nat.card Z * Nat.card (Model ⧸ Z) := hcard.symm
    _ ≤ 4 * 443520 := Nat.mul_le_mul hzcard hq
    _ = 1774080 := rfl

end Sporadic.Mathieu.M22CyclicFour.OrderCertificate
