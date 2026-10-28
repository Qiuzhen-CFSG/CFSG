module
public import Theory.GroupTheory.WeakBNPair.RegularTree.ApartmentSeparation

/-!
# Neighbor lifting for the source apartment relation

For the source length n, extend a length-2n apartment path by one edge.
Path transitivity on n+1 edges and exchange transport every neighbor across
an elementary identification. Induction carries this through the equivalence
closure. The result applies to the natural four-edge branch as well as the
three-edge branch, without assuming a BN-pair or kernel-orbit equality.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(3.6), printed pp.77--78. This extends ApartmentNeighborLifting's cubic proof.
-/

open SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.WeakBNPair.RegularTree

@[expose] public section
namespace Theory.GroupTheory.WeakBNPair.RegularTree
variable {X V : Type*} [Group X] [MulAction X V]
variable {Γ : SimpleGraph V} {T : Set V}
variable (n : ℕ) (hn : 0 < n)
include hn

private theorem general_mapped_first_half
    (ht : Γ.IsTree)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    {a b : V} (p : Γ.Walk a b) (hp : p.IsPath) (hlen : p.length = (2*n))
    (z : X) (ha : z • a = b) (hm : z • p.getVert n = p.getVert n) :
    z • p.getVert 1 = p.getVert (2*n-1) := by
  let f : Γ →g Γ := ⟨(z • ·), hact z⟩
  have hrm : p.reverse.getVert n = p.getVert n := by
    rw [getVert_reverse, hlen]
    congr 1; omega
  let l : Γ.Walk b (p.getVert n) := ((p.take n).map f).copy ha hm
  let r : Γ.Walk b (p.getVert n) := (p.reverse.take n).copy rfl hrm
  have hl : l.IsPath := by
    dsimp [l]
    rw [isPath_copy]
    exact (hp.take n).map (MulAction.toPerm z).injective
  have hr : r.IsPath := by
    dsimp [r]
    rw [isPath_copy]
    exact hp.reverse.take n
  have he : l = r := congrArg Subtype.val (ht.isAcyclic.subsingleton_path _ _ |>.elim ⟨l,hl⟩ ⟨r,hr⟩)
  have hv := congrArg (fun w => w.getVert 1) he
  simp only [l,r,getVert_copy,getVert_map,take_getVert,show min n 1 = 1 from by omega,
    getVert_reverse,hlen] at hv
  change z • p.getVert 1 = p.getVert (2*n-1) at hv
  exact hv

/-- The exchange actor supplies the neighbor lift once its half-path action
is chosen by source path transitivity. This is independent of kernel orbits. -/
theorem general_neighbor_lift_of_exchange_actor
    (ht : Γ.IsTree)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    (hex : ApartmentExchangeMoves (X := X) Γ T n)
    {a b c aminus bplus : V}
    (p : Γ.Walk a b) (hp : p.IsPath) (hlen : p.length = (2*n))
    (hpT : InApartment (X := X) Γ T p)
    (ham : Γ.Adj a aminus)
    (hleft : (apartmentSetoid (X := X) Γ T n) (p.getVert (2*n-1)) aminus)
    (hright : (apartmentSetoid (X := X) Γ T n) bplus (p.getVert 1))
    (x : X) (hx : ∀ k, n ≤ k → k ≤ (2*n) → x • p.getVert k = p.getVert k)
    (hxc : x • bplus = c) :
    ∃ d, Γ.Adj a d ∧ (apartmentSetoid (X := X) Γ T n) c d := by
  have hinv := apartmentSetoid_invariant (T := T) (n := n) hact
  have hright' : (apartmentSetoid (X := X) Γ T n) c (x • p.getVert 1) := by
    rw [← hxc]
    exact hinv x hright
  by_cases hxa : x • a = a
  · refine ⟨x • p.getVert 1, ?_, hright'⟩
    have hh := hact x (p.adj_getVert_succ (by omega : 0 < p.length))
    simpa only [getVert_zero, hxa] using hh
  · obtain ⟨y,hy,hya⟩ := hex p hp hlen hpT x hx hxa
    have hya0 : y • a = a := by simpa only [getVert_zero] using hy 0 (by omega)
    have hmid : (y*x) • p.getVert n = p.getVert n := by
      rw [mul_smul,hx n (by omega) (by omega),hy n (by omega)]
    have hz : (y*x) • a = b := by simpa only [mul_smul] using hya
    have he := general_mapped_first_half n hn ht hact p hp hlen (y*x) hz hmid
    have he' : x • p.getVert 1 = y⁻¹ • p.getVert (2*n-1) := by
      rw [mul_smul] at he
      simpa only [inv_smul_smul] using congrArg (y⁻¹ • ·) he
    refine ⟨y⁻¹ • aminus, ?_, ?_⟩
    · have hi : y⁻¹ • a = a := by
        simpa only [inv_smul_smul] using congrArg (y⁻¹ • ·) hya0.symm
      simpa only [hi] using hact y⁻¹ ham
    · apply Relation.EqvGen.trans _ _ _ hright'
      rw [he']
      exact hinv y⁻¹ hleft


private theorem general_right_shifted_relation
    (ht : Γ.IsTree)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    (hdeg : TwoNeighborsIn Γ T)
    {a b : V} (p : Γ.Walk a b) (hp : p.IsPath) (hlen : p.length = (2*n))
    (hpT : InApartment (X := X) Γ T p) :
    ∃ c, Γ.Adj b c ∧ c ≠ p.getVert (2*n-1) ∧
      (apartmentSetoid (X := X) Γ T n) c (p.getVert 1) := by
  obtain ⟨g, hg⟩ := hpT
  obtain ⟨c, hc, d, hd, hbc, hbd, hcd⟩ :=
    twoNeighborsIn_translate hact hdeg g b (hg b p.end_mem_support)
  have hex : ∃ c, (∃ t ∈ T, g • t = c) ∧ Γ.Adj b c ∧ c ≠ p.getVert (2*n-1) := by
    by_cases he : c = p.getVert (2*n-1)
    · exact ⟨d, hd, hbd, fun hh => hcd (he.trans hh.symm)⟩
    · exact ⟨c, hc, hbc, he⟩
  obtain ⟨c, hc, hbc, hne⟩ := hex
  have hnew : c ∉ p.support := by
    intro hmem
    have he := ht.isAcyclic.eq_penultimate_of_adj_end hp hbc hmem
    exact hne (by simpa only [penultimate, hlen] using he)
  let q := p.concat hbc
  have hq : q.IsPath := hp.concat hnew hbc
  have he : q.getVert 1 = p.getVert 1 := by
    simp only [q, concat_eq_append, getVert_append', if_pos (by omega : 1 ≤ p.length)]
  have hqT : InApartment (X := X) Γ T (q.drop 1) := by
    refine ⟨g, ?_⟩
    intro z hz
    have hzq : z ∈ q.support := by
      rw [drop_support_eq_support_drop_min] at hz
      exact List.mem_of_mem_drop hz
    rw [support_concat, List.mem_append, List.mem_singleton] at hzq
    rcases hzq with hz | rfl
    · exact hg z hz
    · exact hc
  have hrel : ApartmentStep (X := X) Γ T n (p.getVert 1) c := by
    rw [← he]
    exact ⟨q.drop 1, hq.drop 1, by simp [q, hlen], hqT⟩
  exact ⟨c, hbc, hne, Relation.EqvGen.rel _ _ (apartmentStep_symm hrel)⟩

/-- Source (n+1)-path transitivity supplies the actor in the exchange lift. -/
theorem apartmentStep_neighbor_lift
    (ht : Γ.IsTree)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    (hdeg : TwoNeighborsIn Γ T)
    (htrans : BasedPathTransitive (X := X) Γ (n+1))
    (hex : ApartmentExchangeMoves (X := X) Γ T n)
    {a b c : V} (hab : ApartmentStep (X := X) Γ T n a b) (hbc : Γ.Adj b c) :
    ∃ d, Γ.Adj a d ∧ (apartmentSetoid (X := X) Γ T n) c d := by
  obtain ⟨p, hp, hlen, hpT⟩ := hab
  have hlen : p.length = (2*n) := hlen
  obtain ⟨bplus, hbplus, hplus, hright⟩ := general_right_shifted_relation n hn ht hact hdeg p hp hlen hpT
  have hrT : InApartment (X := X) Γ T p.reverse := by
    obtain ⟨g, hg⟩ := hpT
    exact ⟨g, fun z hz => hg z (by simpa only [support_reverse, List.mem_reverse] using hz)⟩
  obtain ⟨aminus, haminus, _, hleft⟩ := general_right_shifted_relation n hn ht hact hdeg
    p.reverse hp.reverse (by simpa only [length_reverse] using hlen) hrT
  have hleft' : (apartmentSetoid (X := X) Γ T n) (p.getVert (2*n-1)) aminus := by
    have hh := Relation.EqvGen.symm _ _ hleft
    rw [getVert_reverse, hlen] at hh
    exact hh
  by_cases hc : c = p.getVert (2*n-1)
  · exact ⟨aminus, haminus, hc ▸ hleft'⟩
  have hnew : ∀ d, Γ.Adj b d → d ≠ p.getVert (2*n-1) → d ∉ p.support := by
    intro d hbd hd hmem
    exact hd (by simpa only [penultimate, hlen] using
      ht.isAcyclic.eq_penultimate_of_adj_end hp hbd hmem)
  let q := (p.concat hbplus).drop n
  let q' := (p.concat hbc).drop n
  have hstart (d : V) (hbd : Γ.Adj b d) : (p.concat hbd).getVert n = p.getVert n := by
    rw [concat_eq_append, getVert_append', if_pos (by omega : n ≤ p.length)]
  let u : Γ.Walk (p.getVert n) bplus := q.copy (hstart _ hbplus) rfl
  let v : Γ.Walk (p.getVert n) c := q'.copy (hstart _ hbc) rfl
  have hu : u.IsPath := by
    rw [isPath_copy]
    exact (hp.concat (hnew _ hbplus hplus) hbplus).drop n
  have hv : v.IsPath := by
    rw [isPath_copy]
    exact (hp.concat (hnew _ hbc hc) hbc).drop n
  have hul : u.length = (n+1) := by simp [u, q, hlen]; omega
  have hvl : v.length = (n+1) := by simp [v, q', hlen]; omega
  obtain ⟨x, hx⟩ := htrans u v hu hv hul hvl
  have hxhalf : ∀ k, n ≤ k → k ≤ (2*n) → x • p.getVert k = p.getVert k := by
    intro k hk hk'
    have hh := hx (k-n) (by omega)
    change x • u.getVert (k-n) = v.getVert (k-n) at hh
    simp only [u, v, getVert_copy] at hh
    simp only [q, q', drop_getVert, show n+(k-n)=k from by omega,
      concat_eq_append, getVert_append', if_pos (by omega : k ≤ p.length)] at hh
    exact hh
  have hxc : x • bplus = c := by
    have hh := hx (n+1) le_rfl
    rw [← hul, getVert_length, hul, ← hvl, getVert_length] at hh
    exact hh
  exact general_neighbor_lift_of_exchange_actor n hn ht hact hex p hp hlen hpT haminus
    hleft' hright x hxhalf hxc

/-- Neighbor lifting holds through the full equivalence closure, on the same
source relation. This makes no claim about orbits of the action kernel. -/
theorem apartmentSetoid_neighbor_lift
    (ht : Γ.IsTree)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    (hdeg : TwoNeighborsIn Γ T)
    (htrans : BasedPathTransitive (X := X) Γ (n+1))
    (hex : ApartmentExchangeMoves (X := X) Γ T n)
    {a b c : V} (hab : (apartmentSetoid (X := X) Γ T n) a b) (hbc : Γ.Adj b c) :
    ∃ d, Γ.Adj a d ∧ (apartmentSetoid (X := X) Γ T n) c d := by
  have hh : (∀ c, Γ.Adj b c → ∃ d, Γ.Adj a d ∧ (apartmentSetoid (X := X) Γ T n) c d) ∧
      (∀ c, Γ.Adj a c → ∃ d, Γ.Adj b d ∧ (apartmentSetoid (X := X) Γ T n) c d) := by
    clear hbc
    induction hab with
    | rel a b hab =>
      exact ⟨fun _ hc => apartmentStep_neighbor_lift n hn ht hact hdeg htrans hex hab hc,
        fun _ hc => apartmentStep_neighbor_lift n hn ht hact hdeg htrans hex
          (apartmentStep_symm hab) hc⟩
    | refl a => exact ⟨fun c hc => ⟨c, hc, Relation.EqvGen.refl c⟩,
        fun c hc => ⟨c, hc, Relation.EqvGen.refl c⟩⟩
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ =>
      constructor
      · intro d hd
        obtain ⟨e, he, hde⟩ := ih₂.1 d hd
        obtain ⟨f, hf, hef⟩ := ih₁.1 e he
        exact ⟨f, hf, Relation.EqvGen.trans _ _ _ hde hef⟩
      · intro d hd
        obtain ⟨e, he, hde⟩ := ih₁.2 d hd
        obtain ⟨f, hf, hef⟩ := ih₂.2 e he
        exact ⟨f, hf, Relation.EqvGen.trans _ _ _ hde hef⟩
  exact hh.1 c hbc

end Theory.GroupTheory.WeakBNPair.RegularTree
