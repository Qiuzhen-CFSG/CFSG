module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SplitQuotient

/-!
# The actual Cartan orbit apartment and its finite marked quotient

Define the apartment as the two N-orbits of the original marked edge.
Its chosen local reflections give two neighbors at every vertex. When its
internal valence is at most two, every apartment edge is an N-translate of
the original edge; the normalizer therefore supplies all line symmetries.
Normalization and the original Hall property make K the Hall Cartan at every
such edge. Odd long-path stabilizers now give uniqueness and K = B intersect N.

These derived facts feed the literal universal-completion quotient and its
marked amalgam isomorphism. The original normal two-group/abelian Cartan
factorization supplies `SplitData`, with saturation proved on that quotient.
Neither uniqueness, original Cartan intersection nor saturation is assumed
by the final constructor.

The Cartan/reflection/root construction, absence of branching in this orbit
apartment, the Chapter 14 exchange alternative, quotient root signs and the
quotient Borel-normalizer intersection remain explicit source obligations.
This is a proved intermediate construction, not the unconditional (14.19)
or Theorem D. Source: DGS, *Groups and Graphs* (1985), Part II, (3.5)–(3.7),
pp.75–80, and (14.1),(14.2),(14.10), pp.210–211,216–217.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open Theory.GroupTheory Theory.GroupTheory.WeakBNPair.RegularTree
open Subgroup.CosetGeometry RankTwoAmalgam
universe u
variable {L B R : Type u} [Group L] [Group B] [Group R]
variable (α : RankTwoAmalgam L B R) (N : Subgroup α.Universal)

/-- The apartment is the union of the two actual N-orbits of the marked
edge vertices, as in DGS (3.5). -/
def cartanApartment : Set (SourceVertex α) :=
  {v | ∃ g ∈ N, ∃ i, g • base (Universal.cosetFamily α) i = v}

theorem cartanApartment_base (i : Bool) :
    base (Universal.cosetFamily α) i ∈ cartanApartment α N :=
  ⟨1, N.one_mem, i, one_smul _ _⟩

theorem cartanApartment_preserves {g : α.Universal} (hg : g ∈ N)
    {v : SourceVertex α} (hv : v ∈ cartanApartment α N) :
    g • v ∈ cartanApartment α N := by
  obtain ⟨h, hh, i, rfl⟩ := hv
  exact ⟨g*h, N.mul_mem hg hh, i, mul_smul _ _ _⟩

variable (roots : Bool → LocalRootAction (X := α.Universal) (sourceGraph α))
variable (ha : ∀ i, (roots i).a = base (Universal.cosetFamily α) i)
variable (hb : ∀ i, (roots i).b = base (Universal.cosetFamily α) (!i))
variable (hlift : ∀ i, (roots i).reflection ∈ N)

include ha hb hlift in
/-- The two reflection neighbors give internal valence at least two in the
actual N-orbit apartment. -/
theorem cartanApartment_twoNeighbors : TwoNeighborsIn (sourceGraph α) (cartanApartment α N) := by
  rintro v ⟨g, hg, i, rfl⟩
  have hc : (roots i).c ∈ cartanApartment α N := by
    rw [← (roots i).sends_b, hb i]
    exact cartanApartment_preserves α N (hlift i) (cartanApartment_base α N (!i))
  refine ⟨g • (roots i).b, cartanApartment_preserves α N hg (by rw [hb i]; exact cartanApartment_base α N (!i)),
    g • (roots i).c, cartanApartment_preserves α N hg hc, ?_, ?_, ?_⟩
  · rw [← ha i]
    exact source_action α g (roots i).adj_b
  · rw [← ha i]
    exact source_action α g (roots i).adj_c
  · exact fun he => (roots i).distinct ((MulAction.toPerm g).injective he)

variable (hline : NoBranchingIn (sourceGraph α) (cartanApartment α N))

include ha hb hlift hline in
/-- Each apartment edge is an N-translate of the same original marked
edge, with its orientation retained. -/
theorem cartanApartment_edge_coordinates {a b : SourceVertex α}
    (haT : a ∈ cartanApartment α N) (hbT : b ∈ cartanApartment α N)
    (hadj : (sourceGraph α).Adj a b) :
    ∃ g ∈ N, ∃ i, g • base (Universal.cosetFamily α) i = a ∧
      g • base (Universal.cosetFamily α) (!i) = b := by
  obtain ⟨g, hg, i, rfl⟩ := haT
  have hb0 : (roots i).b ∈ cartanApartment α N := by
    rw [hb i]; exact cartanApartment_base α N (!i)
  have hc0 : (roots i).c ∈ cartanApartment α N := by
    rw [← (roots i).sends_b]
    exact cartanApartment_preserves α N (hlift i) hb0
  have hgb := source_action α g (roots i).adj_b
  have hgc := source_action α g (roots i).adj_c
  rw [ha i] at hgb hgc
  have hne : g • (roots i).b ≠ g • (roots i).c := fun he =>
    (roots i).distinct ((MulAction.toPerm g).injective he)
  rcases hline _ (cartanApartment_preserves α N hg (cartanApartment_base α N i))
    _ (cartanApartment_preserves α N hg hb0)
    _ (cartanApartment_preserves α N hg hc0) _ hbT hgb hgc hadj hne with he | he
  · exact ⟨g, hg, i, rfl, by rw [← hb i]; exact he.symm⟩
  · refine ⟨g * (roots i).reflection, N.mul_mem hg (hlift i), i, ?_, ?_⟩
    · rw [mul_smul, ← ha i, (roots i).fixes_a]
    · rw [mul_smul, ← hb i, (roots i).sends_b, he]

include ha hb hlift hline in
/-- The actual orbit apartment has the required vertex and local edge
symmetries; these are constructed from its original reflection lifts. -/
theorem cartanApartment_symmetries :
    ApartmentSymmetries (sourceGraph α) (cartanApartment α N) N where
  preserves g hg _ hv := cartanApartment_preserves α N hg hv
  vertices := by
    rintro a ⟨g, hg, i, rfl⟩ b ⟨h, hh, j, rfl⟩ ⟨x, hx⟩
    have hij : i = j := congrArg (fun v : SourceVertex α => v.type) hx
    subst j
    exact ⟨h*g⁻¹, N.mul_mem hh (N.inv_mem hg), by simp only [mul_smul, inv_smul_smul]⟩
  neighbors := by
    intro a haT b hbT c hcT hab hac
    obtain ⟨g, hg, i, hga, hgb⟩ := cartanApartment_edge_coordinates α N roots ha hb hlift hline haT hbT hab
    obtain ⟨h, hh, j, hha, hhc⟩ := cartanApartment_edge_coordinates α N roots ha hb hlift hline haT hcT hac
    have hij : i = j := congrArg (fun v : SourceVertex α => v.type) (hga.trans hha.symm)
    subst j
    refine ⟨h*g⁻¹, N.mul_mem hh (N.inv_mem hg), ?_, ?_⟩
    · rw [mul_smul, ← hga, inv_smul_smul, hha]
      exact hga.symm
    · rw [mul_smul, ← hgb, inv_smul_smul, hhc]

variable (K : Subgroup α.Universal)
variable (hKN : K ≤ N)
variable (hKB : K ≤ originalMiddle α)
variable (hnorm : N ≤ Subgroup.normalizer (K : Set α.Universal))
variable (hL : Function.Injective α.left) (hR : Function.Injective α.right)

include hKB hnorm hL hR in
/-- A Cartan normalized by N and fixing the original edge fixes its whole
orbit apartment pointwise. -/
theorem cartanApartment_fixed : ∀ k ∈ K, ∀ a ∈ cartanApartment α N, k • a = a := by
  rintro k hk a ⟨g, hg, i, rfl⟩
  have hconj : g⁻¹*k*g ∈ K := by
    simpa only [inv_inv] using
      (Subgroup.mem_normalizer_iff.mp (hnorm (N.inv_mem hg)) k).mp hk
  have hmem : g⁻¹*k*g ∈ MulAction.stabilizer α.Universal (base (Universal.cosetFamily α) i) := by
    rw [stabilizer_base]
    have hm := hKB hconj
    change (g⁻¹*k*g) ∈ ((Universal.left α).comp α.left).range at hm
    rw [← Universal.overlap_eq α hL hR] at hm
    cases i
    · exact hm.1
    · exact hm.2
  have he : (g⁻¹*k*g) • base (Universal.cosetFamily α) i = base (Universal.cosetFamily α) i := hmem
  have hh := congrArg (g • ·) he
  simpa only [mul_smul, smul_inv_smul] using hh

private theorem hall_subgroupOf_conjugate {Y : Type*} [Group Y]
    {π : Set Nat.Primes} {K E : Subgroup Y} (hKE : K ≤ E)
    (hhall : IsHallSubgroup π (K.subgroupOf E)) {g : Y}
    (hg : g ∈ Subgroup.normalizer (K : Set Y)) :
    IsHallSubgroup π (K.subgroupOf (E.map (MulAut.conj g).toMonoidHom)) := by
  have hmap : K.map (MulAut.conj g).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hKE' : K ≤ E.map (MulAut.conj g).toMonoidHom := by
    rw [← hmap]
    exact Subgroup.map_mono hKE
  constructor
  · intro p hp
    apply hhall.p_in_pi_of_p_dvd_card p
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKE').toEquiv] at hp
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKE).toEquiv]
  · intro p hp
    apply hhall.p_in_pi_of_p_dvd_index p
    have hi : K.relIndex (E.map (MulAut.conj g).toMonoidHom) = K.relIndex E := by
      calc
        _ = (K.map (MulAut.conj g).toMonoidHom).relIndex
            (E.map (MulAut.conj g).toMonoidHom) := by rw [hmap]
        _ = _ := Subgroup.relIndex_map_map_of_injective K E (MulAut.conj g).injective
    change p.val ∣ K.relIndex (E.map (MulAut.conj g).toMonoidHom) at hp
    rwa [hi] at hp

include ha hb hlift hline hKB hnorm hL hR in
/-- The Hall property at the single original Borel transports to every
apartment edge, because K is normalized by the same N. -/
theorem cartanApartment_hall_edges {π : Set Nat.Primes}
    (hhall : IsHallSubgroup π (K.subgroupOf (originalMiddle α))) :
    ∀ a ∈ cartanApartment α N, ∀ b ∈ cartanApartment α N, (sourceGraph α).Adj a b →
      IsHallSubgroup π (K.subgroupOf
        (MulAction.stabilizer α.Universal a ⊓ MulAction.stabilizer α.Universal b)) := by
  intro a haT b hbT hab
  obtain ⟨g, hg, i, hga, hgb⟩ := cartanApartment_edge_coordinates α N roots ha hb hlift hline haT hbT hab
  have hedge : MulAction.stabilizer α.Universal a ⊓ MulAction.stabilizer α.Universal b =
      (originalMiddle α).map (MulAut.conj g).toMonoidHom := by
    rw [← hga, ← hgb, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      MulAction.stabilizer_smul_eq_stabilizer_map_conj, stabilizer_base, stabilizer_base,
      ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
    congr 1
    cases i
    · exact Universal.overlap_eq α hL hR
    · change (Universal.right α).range ⊓ (Universal.left α).range = _
      rw [inf_comm]
      exact Universal.overlap_eq α hL hR
  rw [hedge]
  exact hall_subgroupOf_conjugate hKB hhall (hnorm hg)

include ha hb hlift hline hKN hKB hnorm hL hR in
/-- DGS (14.10) on the chosen Cartan orbit apartment, using only the Hall
property at the original Borel and the actual odd s-path stabilizers. -/
theorem cartanApartment_unique [Finite L] [Finite R] (n : ℕ)
    (hhall : IsHallSubgroup Subgroup.OddHall.oddPrimes (K.subgroupOf (originalMiddle α)))
    (hodd : ∀ {a b} (p : (sourceGraph α).Walk a b), p.IsPath → p.length = n+1 →
      Odd (Nat.card (pathFixer (X := α.Universal) p))) :
    ApartmentsUnique (X := α.Universal) (sourceGraph α) (cartanApartment α N) (n+1) :=
  source_apartmentsUnique_of_odd_pathFixers α (cartanApartment α N) n K N hKN
    (cartanApartment_symmetries α N roots ha hb hlift hline) hline
    (cartanApartment_fixed α N K hKB hnorm hL hR)
    (cartanApartment_hall_edges α N roots ha hb hlift hline K hKB hnorm hL hR hhall) hodd

include ha hb hlift hline hKN hKB hnorm hL hR in
/-- The original Cartan is exactly the intersection of the original Borel
and its chosen apartment normalizer. An element of this intersection fixes
the initial edge, hence a long apartment path, hence belongs to K. -/
theorem cartanApartment_intersection [Finite L] [Finite R] (n : ℕ)
    (hhall : IsHallSubgroup Subgroup.OddHall.oddPrimes (K.subgroupOf (originalMiddle α)))
    (hodd : ∀ {a b} (p : (sourceGraph α).Walk a b), p.IsPath → p.length = n+1 →
      Odd (Nat.card (pathFixer (X := α.Universal) p))) :
    K = originalMiddle α ⊓ N := by
  apply le_antisymm (le_inf hKB hKN)
  intro x hx
  let a := base (Universal.cosetFamily α) false
  let c := base (Universal.cosetFamily α) true
  have hadj : (sourceGraph α).Adj a c :=
    ⟨Bool.false_ne_true, incident_base (Universal.cosetFamily α) false true⟩
  let e : (sourceGraph α).Walk a c := .cons hadj .nil
  have he : e.IsPath := by simpa [e] using hadj.ne
  have heT : ∀ z ∈ e.support, z ∈ cartanApartment α N := by
    intro z hz
    simp only [e, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact cartanApartment_base α N false
    · exact cartanApartment_base α N true
  obtain ⟨b, p, hp, hlen, hpT, hprefix⟩ := path_extension_in_set
    (Universal.cosetGraph_isTree α hL hR).2
    (cartanApartment_twoNeighbors α N roots ha hb hlift) e he heT
    (show e.length ≤ n+1 by simp [e])
  have hpc : p.getVert 1 = c := hprefix
  have hxa : x • a = a := by
    have hm := hx.1
    change x ∈ ((Universal.left α).comp α.left).range at hm
    rw [← Universal.overlap_eq α hL hR] at hm
    have hmem : x ∈ MulAction.stabilizer α.Universal a := by
      rw [show a = base (Universal.cosetFamily α) false from rfl, stabilizer_base]
      exact hm.1
    exact hmem
  have hxc : x • c = c := by
    have hm := hx.1
    change x ∈ ((Universal.left α).comp α.left).range at hm
    rw [← Universal.overlap_eq α hL hR] at hm
    have hmem : x ∈ MulAction.stabilizer α.Universal c := by
      rw [show c = base (Universal.cosetFamily α) true from rfl, stabilizer_base]
      exact hm.2
    exact hmem
  have hfix := fixes_path_of_fixes_first_edge (source_action α) hline p hp hpT
    (fun _ hv => cartanApartment_preserves α N hx.2 hv) hxa (by rwa [hpc])
  have hfixer := pathFixer_eq_cartan K (cartanApartment_fixed α N K hKB hnorm hL hR)
    (cartanApartment_hall_edges α N roots ha hb hlift hline K hKB hnorm hL hR hhall)
    (source_vertexStabilizer_finite α) p (by omega) hpT (source_pathFixer_pi α n hodd p hp hlen)
  rwa [hfixer] at hfix

variable (n : ℕ)
variable (hCartan : K = originalMiddle α ⊓ N)
variable (hgen : N ≤ Subgroup.closure
  ((K : Set α.Universal) ∪ Set.range fun i => (roots i).reflection))
variable (hsign : ∀ i x, x ∈ N →
  (∀ r ∈ (roots i).root, quotientMap α (cartanApartment α N) n (x⁻¹*r*x) ∈
    (originalMiddle α).map (quotientMap α (cartanApartment α N) n)) ∨
  (∀ r ∈ (roots i).root, quotientMap α (cartanApartment α N) n
    (((roots i).reflection*x)⁻¹*r*((roots i).reflection*x)) ∈
      (originalMiddle α).map (quotientMap α (cartanApartment α N) n)))

/-- The normal Cartan and the actual two reflection lifts supply the local
root algebra for the orbit apartment's literal quotient map. -/
def cartanRootData : RootQuotientData (quotientMap α (cartanApartment α N) n) :=
  localRootQuotientData α (cartanApartment α N) n hL hR roots ha hb N hlift
    (by
      rw [← hCartan]
      exact Subgroup.normal_subgroupOf_of_le_normalizer hnorm)
    (by rw [← hCartan]; exact hgen) hsign

variable (hhall : IsHallSubgroup Subgroup.OddHall.oddPrimes (K.subgroupOf (originalMiddle α)))
variable (hodd : ∀ {a b} (p : (sourceGraph α).Walk a b), p.IsPath → p.length = n+1 →
  Odd (Nat.card (pathFixer (X := α.Universal) p)))
variable (htrans : BasedPathTransitive (X := α.Universal) (sourceGraph α) (n+1))
variable (hexchange : ChosenApartmentExchange (X := α.Universal)
  (sourceGraph α) (cartanApartment α N) n)
variable (hn : 1 < n)
variable (hcore : ((Universal.left α).range ⊓ (Universal.right α).range).normalCore = ⊥)
variable (hBN : (originalMiddle α).map (quotientMap α (cartanApartment α N) n) ⊓
    N.map (quotientMap α (cartanApartment α N) n) =
  (originalMiddle α ⊓ N).map (quotientMap α (cartanApartment α N) n))

/-- The finite marked quotient for the actual Cartan orbit apartment.
Its valence, symmetries, Cartan fixation and uniqueness are derived above. -/
noncomputable abbrev cartanFiniteQuotient [Finite L] [Finite R] :=
  recognitionQuotient α (cartanApartment α N) n hL hR (cartanApartment_base α N)
    (cartanApartment_twoNeighbors α N roots ha hb hlift) htrans hline
    (cartanApartment_unique α N roots ha hb hlift hline K hKN hKB hnorm hL hR n hhall hodd)
    hexchange hn hcore (cartanRootData α N roots ha hb hlift K hnorm hL hR n (cartanApartment_intersection α N roots ha hb hlift hline K hKN hKB hnorm hL hR n hhall hodd) hgen hsign)
    rfl (fun _ => rfl) hBN

/-- The finite quotient keeps both original endpoint inclusions and the
whole original middle map, not only an unmarked parabolic equivalence. -/
noncomputable abbrev cartanFiniteMarkedIso [Finite L] [Finite R] :=
  geometricMarkedIso α (cartanApartment α N) n hL hR (cartanApartment_base α N)
    (cartanApartment_twoNeighbors α N roots ha hb hlift) htrans hline
    (cartanApartment_unique α N roots ha hb hlift hline K hKN hKB hnorm hL hR n hhall hodd)
    hexchange hn hcore (cartanRootData α N roots ha hb hlift K hnorm hL hR n (cartanApartment_intersection α N roots ha hb hlift hline K hKN hKB hnorm hL hR n hhall hodd) hgen hsign)
    rfl (fun _ => rfl) hBN

/-- The constructed finite quotient is split and saturated when the
original Borel has its source normal two-group/abelian Cartan factorization.
The quotient Cartan is literally B intersect N throughout. -/
noncomputable def cartanFiniteSplitData [Finite L] [Finite R]
    (U : Subgroup α.Universal)
    (hUnorm : originalMiddle α ≤ Subgroup.normalizer (U : Set α.Universal))
    (hTwo : IsPGroup 2 U) (hKabelian : IsMulCommutative K)
    (hfactor : U ⊔ K = originalMiddle α) :
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.SplitData
      (cartanFiniteQuotient α N roots ha hb hlift hline K hKN hKB hnorm hL hR n
        hgen hsign hhall hodd htrans hexchange hn hcore hBN).tits :=
  sourceSplitData α (cartanApartment α N) n hL hR hn
    (source_apartment_separated α (cartanApartment α N) n hL hR htrans hline
      (cartanApartment_unique α N roots ha hb hlift hline K hKN hKB hnorm hL hR n hhall hodd)
      hexchange (by omega)) K
    (cartanApartment_fixed α N K hKB hnorm hL hR)
    (cartanApartment_hall_edges α N roots ha hb hlift hline K hKB hnorm hL hR hhall)
    hodd (cartanApartment_base α N) (cartanApartment_twoNeighbors α N roots ha hb hlift)
    hcore (cartanRootData α N roots ha hb hlift K hnorm hL hR n (cartanApartment_intersection α N roots ha hb hlift hline K hKN hKB hnorm hL hR n hhall hodd) hgen hsign)
    rfl (fun _ => rfl) hBN (cartanApartment_intersection α N roots ha hb hlift hline K hKN hKB hnorm hL hR n hhall hodd) (fun _ hv => hv) U hUnorm hTwo hKabelian hfactor
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
