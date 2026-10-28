module
public import Theory.GroupTheory.WeakBNPair.RegularTree.ChainSeparation
public import Theory.GroupTheory.WeakBNPair.RegularTree.ApartmentPaths

/-!
# Apartment uniqueness and exchange imply separation

Paths inside a subset with valence at most two are determined by their
first edge. Source path transitivity aligns two length-`2n` apartment
paths on their first `n+1` vertices. Uniqueness then puts their images in
one apartment, so the aligning element also transports the far endpoint.
Exchange at their common midpoint replaces a close two-step identification
by one. The shortest-chain argument consequently separates all distinct
equivalent vertices at distance less than `2n`.

The exchange condition is stated for an element moving the first endpoint.
This is precisely the instance used in the source proof: an element fixing
the entire apartment does not trigger an exchange. The left-action order
is `y • (x • a)`, corresponding to the printed right-action exponent `xy`.
The chosen Cartan/root arguments producing this condition remain separate.

Source: DGS, *Groups and Graphs* (1985), Part II, (3.4)–(3.6), pp.74–78.
-/

@[expose] public section
namespace Theory.GroupTheory.WeakBNPair.RegularTree
open SimpleGraph SimpleGraph.Walk
variable {X V : Type*} [Group X] [MulAction X V]
variable {Γ : SimpleGraph V} {T : Set V}

/-- Internal valence at most two, written without a finiteness assumption. -/
def NoBranchingIn (Γ : SimpleGraph V) (A : Set V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    Γ.Adj a b → Γ.Adj a c → Γ.Adj a d → b ≠ c → d = b ∨ d = c

private theorem path_determined_by_first_edge {A : Set V}
    (hline : NoBranchingIn Γ A) {a b c : V}
    (p : Γ.Walk a b) (q : Γ.Walk a c) (hp : p.IsPath) (hq : q.IsPath)
    (hpA : ∀ z ∈ p.support, z ∈ A) (hqA : ∀ z ∈ q.support, z ∈ A)
    (hlen : p.length = q.length) (hfirst : p.snd = q.snd) : b = c := by
  have he : ∀ k, k ≤ p.length → p.getVert k = q.getVert k := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero => intro _; simp only [getVert_zero]
    | one => intro _; exact hfirst
    | more k ih₀ ih₁ =>
      intro hk
      have hk₀ : k ≤ p.length := by omega
      have hk₁ : k+1 ≤ p.length := by omega
      have he₀ := ih₀ hk₀
      have he₁ := ih₁ hk₁
      have hne : p.getVert k ≠ p.getVert (k+2) := by
        intro hh
        have := hp.getVert_injOn hk₀ hk hh
        omega
      have hback := (p.adj_getVert_succ (by omega : k < p.length)).symm
      have hnext := p.adj_getVert_succ (by omega : k+1 < p.length)
      have hother := q.adj_getVert_succ (by omega : k+1 < q.length)
      rw [← he₁] at hother
      rcases hline _ (hpA _ (p.getVert_mem_support (k+1)))
        _ (hpA _ (p.getVert_mem_support k))
        _ (hpA _ (p.getVert_mem_support (k+2)))
        _ (hqA _ (q.getVert_mem_support (k+2))) hback hnext hother hne with hh | hh
      · rw [he₀] at hh
        have := hq.getVert_injOn (by omega : k+2 ≤ q.length) (by omega : k ≤ q.length) hh
        omega
      · exact hh.symm
  have hh := he p.length le_rfl
  rw [getVert_length, hlen, getVert_length] at hh
  exact hh

def apartmentTranslate (T : Set V) (g : X) : Set V := {z | ∃ t ∈ T, g • t = z}

private theorem noBranching_translate
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    (hline : NoBranchingIn Γ T) (g : X) : NoBranchingIn Γ (apartmentTranslate T g) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ hab hac had hbc
  have hab' : Γ.Adj a b := by simpa only [inv_smul_smul] using hact g⁻¹ hab
  have hac' : Γ.Adj a c := by simpa only [inv_smul_smul] using hact g⁻¹ hac
  have had' : Γ.Adj a d := by simpa only [inv_smul_smul] using hact g⁻¹ had
  rcases hline a ha b hb c hc d hd hab' hac' had' (fun he => hbc (congrArg (g • ·) he)) with h | h
  · exact Or.inl (congrArg (g • ·) h)
  · exact Or.inr (congrArg (g • ·) h)

/-- The uniqueness clause for actual translates of the chosen apartment. -/
def ApartmentsUnique (Γ : SimpleGraph V) (T : Set V) (s : ℕ) : Prop :=
  ∀ {a b} (p : Γ.Walk a b), p.IsPath → p.length = s → ∀ g h : X,
    (∀ z ∈ p.support, z ∈ apartmentTranslate T g) →
    (∀ z ∈ p.support, z ∈ apartmentTranslate T h) →
    apartmentTranslate T g = apartmentTranslate T h

/-- The source path transitivity, with the common initial vertex retained. -/
def BasedPathTransitive (Γ : SimpleGraph V) (s : ℕ) : Prop :=
  ∀ {a b c} (p : Γ.Walk a b) (q : Γ.Walk a c), p.IsPath → q.IsPath →
    p.length = s → q.length = s → ∃ g : X, ∀ k ≤ s, g • p.getVert k = q.getVert k

/-- The movement form of apartment exchange used in the proof of (3.6).
The actor fixes the second half and moves the first endpoint; the correcting
actor fixes the first half. For left actions the printed right-action product
`xy` becomes `y * x`. -/
def ApartmentExchangeMoves (Γ : SimpleGraph V) (T : Set V) (n : ℕ) : Prop :=
  ∀ {a b} (p : Γ.Walk a b), p.IsPath → p.length = 2*n →
    InApartment (X := X) Γ T p → ∀ x : X,
    (∀ k, n ≤ k → k ≤ 2*n → x • p.getVert k = p.getVert k) →
    x • a ≠ a → ∃ y : X, (∀ k ≤ n, y • p.getVert k = p.getVert k) ∧ y • (x • a) = b

/-- Exchange on the single chosen apartment, before transporting by the action. -/
def ChosenApartmentExchange (Γ : SimpleGraph V) (T : Set V) (n : ℕ) : Prop :=
  ∀ {a b} (p : Γ.Walk a b), p.IsPath → p.length = 2*n →
    (∀ z ∈ p.support, z ∈ T) → ∀ x : X,
    (∀ k, n ≤ k → k ≤ 2*n → x • p.getVert k = p.getVert k) →
    x • a ≠ a → ∃ y : X, (∀ k ≤ n, y • p.getVert k = p.getVert k) ∧ y • (x • a) = b

/-- Conjugating the source exchange actors transports the condition to every
translate. This keeps the left-action order of the two correcting elements. -/
theorem apartmentExchangeMoves_of_chosen
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    {n : ℕ} (hexchange : ChosenApartmentExchange (X := X) Γ T n) :
    ApartmentExchangeMoves (X := X) Γ T n := by
  intro a b p hp hlen hpT x hx hmove
  obtain ⟨g, hg⟩ := hpT
  let f : Γ →g Γ := ⟨(g⁻¹ • ·), hact g⁻¹⟩
  have hpT' : ∀ z ∈ (p.map f).support, z ∈ T := by
    intro z hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨t, ht, rfl⟩ := hg w hw
    change g⁻¹ • (g • t) ∈ T
    simpa only [inv_smul_smul] using ht
  have hx' : ∀ k, n ≤ k → k ≤ 2*n →
      (g⁻¹*x*g) • (p.map f).getVert k = (p.map f).getVert k := by
    intro k hnk hkn
    simp only [getVert_map]
    change (g⁻¹*x*g) • (g⁻¹ • p.getVert k) = g⁻¹ • p.getVert k
    rw [mul_smul, mul_smul, smul_inv_smul, hx k hnk hkn]
  have hmove' : (g⁻¹*x*g) • (g⁻¹ • a) ≠ g⁻¹ • a := by
    simp only [mul_smul, smul_inv_smul]
    exact (MulAction.toPerm g⁻¹).injective.ne hmove
  obtain ⟨y, hy, hyend⟩ := hexchange (p.map f) (hp.map (MulAction.toPerm g⁻¹).injective)
    (by simpa only [length_map] using hlen) hpT' (g⁻¹*x*g) hx' hmove'
  refine ⟨g*y*g⁻¹, ?_, ?_⟩
  · intro k hk
    have hyk := hy k hk
    simp only [getVert_map] at hyk
    change y • (g⁻¹ • p.getVert k) = g⁻¹ • p.getVert k at hyk
    rw [mul_smul, mul_smul, hyk, smul_inv_smul]
  · change y • ((g⁻¹*x*g) • (g⁻¹ • a)) = g⁻¹ • b at hyend
    have hh := congrArg (g • ·) hyend
    simpa only [mul_smul, smul_inv_smul] using hh

theorem apartment_endpoint_transport
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    (hline : NoBranchingIn Γ T) {n : ℕ} (hn : 0 < n)
    (hunique : ApartmentsUnique (X := X) Γ T (n+1))
    (htrans : BasedPathTransitive (X := X) Γ (n+1))
    {b a c : V} (p : Γ.Walk b a) (q : Γ.Walk b c)
    (hp : p.IsPath) (hq : q.IsPath) (hp_len : p.length = 2*n) (hq_len : q.length = 2*n)
    (hpT : InApartment (X := X) Γ T p) (hqT : InApartment (X := X) Γ T q)
    (hcommon : ∀ k ≤ n, p.getVert k = q.getVert k) :
    ∃ x : X, (∀ k ≤ n, x • p.getVert k = p.getVert k) ∧ x • a = c := by
  have hp_s : (p.take (n+1)).length = n+1 := by rw [take_length, hp_len, min_eq_left (by omega)]
  have hq_s : (q.take (n+1)).length = n+1 := by rw [take_length, hq_len, min_eq_left (by omega)]
  obtain ⟨x, hx⟩ := htrans (p.take (n+1)) (q.take (n+1)) (hp.take _) (hq.take _) hp_s hq_s
  have hx' : ∀ k ≤ n+1, x • p.getVert k = q.getVert k := by
    intro k hk
    simpa only [take_getVert, min_eq_right hk] using hx k hk
  have hxfix : ∀ k ≤ n, x • p.getVert k = p.getVert k :=
    fun k hk => (hx' k (by omega)).trans (hcommon k hk).symm
  obtain ⟨g, hg⟩ := hpT
  obtain ⟨h, hh⟩ := hqT
  have hqA : ∀ z ∈ (q.take (n+1)).support, z ∈ apartmentTranslate T h := by
    intro z hz
    exact hh z (by rw [support_take] at hz; exact List.mem_of_mem_take hz)
  have hxA : ∀ z ∈ (q.take (n+1)).support, z ∈ apartmentTranslate T (x*g) := by
    intro z hz
    obtain ⟨k, hkz, hk⟩ := mem_support_iff_exists_getVert.mp hz
    rw [hq_s] at hk
    rw [take_getVert, min_eq_right hk] at hkz
    obtain ⟨t, ht, he⟩ := hg _ (p.getVert_mem_support k)
    exact ⟨t, ht, by rw [mul_smul, he, hx' k hk, hkz]⟩
  have heA := hunique (q.take (n+1)) (hq.take _) hq_s (x*g) h hxA hqA
  let f : Γ →g Γ := ⟨(x • ·), hact x⟩
  have hpA : ∀ z ∈ (p.map f).support, z ∈ apartmentTranslate T h := by
    intro z hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [← heA]
    obtain ⟨t, ht, he⟩ := hg w hw
    exact ⟨t, ht, by change (x*g) • t = x • w; rw [mul_smul, he]⟩
  have hxb : x • b = b := by simpa only [getVert_zero] using hxfix 0 (Nat.zero_le n)
  let p' : Γ.Walk b (x • a) := (p.map f).copy hxb rfl
  have hpp : p'.IsPath := by
    dsimp [p']
    rw [isPath_copy]
    exact hp.map (MulAction.toPerm x).injective
  refine ⟨x, hxfix, path_determined_by_first_edge (noBranching_translate hact hline h)
    p' q hpp hq ?_ hh ?_ ?_⟩
  · simpa only [p', support_copy] using hpA
  · simp only [p', length_copy, length_map, hp_len, hq_len]
  · simp only [p', snd, getVert_copy, getVert_map]
    exact hx' 1 (by omega)

/-- Exchange replaces two apartment identifications whose endpoints are close
by one. The common half is proved from the tree metric, and the actor aligning
the two apartments is constructed using path transitivity and uniqueness. -/
theorem apartment_shortcut_of_exchange
    (ht : Γ.IsTree)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    (hline : NoBranchingIn Γ T) {n : ℕ} (hn : 0 < n)
    (hunique : ApartmentsUnique (X := X) Γ T (n+1))
    (htrans : BasedPathTransitive (X := X) Γ (n+1))
    (hexchange : ApartmentExchangeMoves (X := X) Γ T n)
    {a b c : V} (hab : ApartmentStep (X := X) Γ T n a b)
    (hbc : ApartmentStep (X := X) Γ T n b c) (hclose : Γ.dist a c ≤ 2*n) :
    a = c ∨ ApartmentStep (X := X) Γ T n a c := by
  by_cases he : a = c
  · exact Or.inl he
  right
  obtain ⟨p, hp, hp_len, hpT⟩ := apartmentStep_symm hab
  obtain ⟨q, hq, hq_len, hqT⟩ := hbc
  obtain ⟨x, hxfix, hxa⟩ := apartment_endpoint_transport hact hline hn hunique htrans
    p q hp hq hp_len hq_len hpT hqT
    (tree_common_half ht p q hp hq hp_len hq_len hclose)
  have hpT' : InApartment (X := X) Γ T p.reverse := by
    obtain ⟨g, hg⟩ := hpT
    exact ⟨g, fun z hz => hg z (by simpa only [support_reverse, List.mem_reverse] using hz)⟩
  have hxhalf : ∀ k, n ≤ k → k ≤ 2*n →
      x • p.reverse.getVert k = p.reverse.getVert k := by
    intro k hk _
    rw [getVert_reverse, hp_len]
    exact hxfix (2*n-k) (by omega)
  obtain ⟨y, hyfix, hy⟩ := hexchange p.reverse hp.reverse
    (by simpa only [length_reverse] using hp_len) hpT' x hxhalf
    (by rw [hxa]; exact Ne.symm he)
  have hya : y • a = a := by
    simpa only [getVert_zero] using hyfix 0 (Nat.zero_le n)
  have hiy : y⁻¹ • a = a := by
    simpa only [inv_smul_smul] using congrArg (y⁻¹ • ·) hya.symm
  have hyc : y⁻¹ • b = c := by
    rw [hxa] at hy
    simpa only [inv_smul_smul] using congrArg (y⁻¹ • ·) hy.symm
  have hstep : ApartmentStep (X := X) Γ T n a b := ⟨p.reverse, hp.reverse,
    by simpa only [length_reverse] using hp_len, hpT'⟩
  simpa only [hiy, hyc] using apartmentStep_smul hact y⁻¹ hstep

/-- The separation conclusion of DGS (3.6) follows from the actual apartment
conditions. No separation, quotient injectivity or finite replacement group
is assumed. -/
theorem apartment_separated_of_exchange
    (ht : Γ.IsTree)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    (hline : NoBranchingIn Γ T) {n : ℕ} (hn : 0 < n)
    (hunique : ApartmentsUnique (X := X) Γ T (n+1))
    (htrans : BasedPathTransitive (X := X) Γ (n+1))
    (hexchange : ApartmentExchangeMoves (X := X) Γ T n) :
    Separated (apartmentSetoid (X := X) Γ T n) Γ (2*n) :=
  apartment_separated_of_shortcut ht hn
    (apartment_shortcut_of_exchange ht hact hline hn hunique htrans hexchange)

/-- Path transitivity and an apartment meeting each vertex orbit supply the
coverage used in the finite-class construction. -/
theorem apartments_cover_of_transitivity
    (ht : Γ.IsTree)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    (hdeg : TwoNeighborsIn Γ T) {s : ℕ}
    (htrans : BasedPathTransitive (X := X) Γ s)
    (horbit : ∀ a : V, ∃ g : X, a ∈ apartmentTranslate T g) :
    ApartmentsCover (X := X) Γ T s := by
  intro a b p hp hlen
  obtain ⟨g, hg⟩ := horbit a
  obtain ⟨c, q, hq, hqlen, hqT, _⟩ := path_extension_in_set ht.isAcyclic
    (twoNeighborsIn_translate hact hdeg g) (.nil : Γ.Walk a a) (.nil)
    (by intro z hz; simpa using (List.mem_singleton.mp hz) ▸ hg) (Nat.zero_le s)
  obtain ⟨x, hx⟩ := htrans q p hq hp hqlen hlen
  refine ⟨x*g, ?_⟩
  intro z hz
  obtain ⟨k, hkz, hk⟩ := mem_support_iff_exists_getVert.mp hz
  rw [hlen] at hk
  obtain ⟨t, htT, hgt⟩ := hqT _ (q.getVert_mem_support k)
  exact ⟨t, htT, by rw [mul_smul, hgt, hx k hk, hkz]⟩
end Theory.GroupTheory.WeakBNPair.RegularTree
