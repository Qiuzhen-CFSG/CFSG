module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.Basic
public import Theory.GroupTheory.SetStrongClosure
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.Induction
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.IntersectionGenerated
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.LocalFusion.SourceCompletion
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceCompletion

/-!
# The set-fusion deductions in 16.2.10

The two Sylow intersections form a strongly closed set for fusion in `H`
because `H` permutes the two components. Their strong closure for fusion in
`G` is an actual set of conjugates, rather than a generated subgroup.
A conjugate outside their union comes from outside `H`; its cyclic
two-subgroup supplies the involution required in 16.2.10(2).

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma 16.2.10, pp.1175–1176. The reexported
`Asc75.lemma_3_4` proves the full Aschbacher (1975) lemma from exact Theorem ZD.
Its Chapter 16 application to the strictness premise below remains separate;
the theorems here do not assert the completed numbered Lemma 16.2.10.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure

open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G] {T : Sylow 2 G} {L H : Subgroup G} {u : G}

/-- The two Sylow intersections in the proof of 16.2.10. -/
def sylowUnion (T : Sylow 2 G) (L : Subgroup G) (u : G) : Set G :=
  (componentSylow T L : Set G) ∪ (componentSylow T (conjugate L u) : Set G)

/-- Conjugation by an element of `T` transports its intersection with `L`. -/
theorem conjugate_componentSylow (hu : u ∈ T) :
    conjugate (componentSylow T L) u = componentSylow T (conjugate L u) := by
  have hT : conjugate (T : Subgroup G) u = T :=
    (mem_normalizer_iff_conjugate_eq _ _).mp (Subgroup.le_normalizer hu)
  change ((T : Subgroup G) ⊓ L).map (MulAut.conj u⁻¹).toMonoidHom = _
  rw [map_inf _ _ _ (MulAut.conj u⁻¹).injective]
  change conjugate (T : Subgroup G) u ⊓ conjugate L u = _
  rw [hT]
  rfl

/-- Permutation of the components gives strong closure of their union for
fusion in `H`, with no claim of strong closure for fusion in `G`. -/
theorem sylowUnion_stronglyClosed_in_overgroup (hu : u ∈ H)
    (hperm : ∀ g ∈ H, conjugate L g = L ∨ conjugate L g = conjugate L u) :
    IsStronglyClosedSet (sylowUnion T L u) (T : Subgroup G) H := by
  refine ⟨?_, ?_⟩
  · rintro x (hx | hx)
    · exact hx.1
    · exact hx.1
  · intro x hx g hg hyT
    have hmem : ∀ A : Subgroup G, x ∈ A → g⁻¹ * x * g ∈ conjugate A g := by
      intro A hxA
      simpa [conjugate, MulAut.conj_apply] using
        (mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hxA)
    rcases hx with hx | hx
    · rcases hperm g hg with he | he
      · exact Or.inl ⟨hyT, he ▸ hmem L hx.2⟩
      · exact Or.inr ⟨hyT, he ▸ hmem L hx.2⟩
    · have hy := hmem (conjugate L u) hx.2
      rw [conjugate_conjugate] at hy
      rcases hperm (u * g) (H.mul_mem hu hg) with he | he
      · exact Or.inl ⟨hyT, he ▸ hy⟩
      · exact Or.inr ⟨hyT, he ▸ hy⟩

/-- Both pieces of the union lie in the set strong closure of the first. -/
theorem sylowUnion_subset_closure (hu : u ∈ T)
    (hsecond : componentSylow T (conjugate L u) ≤ normalizer (L : Set G)) :
    sylowUnion T L u ⊆ setStrongClosure (componentSylow T L : Set G)
      ((T : Subgroup G) ⊓ normalizer (L : Set G)) ⊤ := by
  intro x hx
  rcases hx with hx | hx
  · exact subset_setStrongClosure (T := (T : Subgroup G) ⊓ normalizer (L : Set G))
      (fun y (hy : y ∈ componentSylow T L) => ⟨hy.1, Subgroup.le_normalizer hy.2⟩) hx
  · have hx' := hx
    rw [← conjugate_componentSylow hu] at hx'
    obtain ⟨a, ha, rfl⟩ := hx'
    exact ⟨⟨hx.1, hsecond hx⟩, a, ha, u, mem_top _, by simp⟩

/-- The strong-closure claim of 16.2.10(1) is equivalent to failure of
strong closure of the union. In particular, subgroup generation is absent. -/
theorem strict_closure_iff (hu : u ∈ T)
    (hsecond : componentSylow T (conjugate L u) ≤ normalizer (L : Set G)) :
    sylowUnion T L u ⊂ setStrongClosure (componentSylow T L : Set G)
      ((T : Subgroup G) ⊓ normalizer (L : Set G)) ⊤ ↔
    ¬ IsStronglyClosedSet (sylowUnion T L u)
      ((T : Subgroup G) ⊓ normalizer (L : Set G)) ⊤ :=
  ssubset_setStrongClosure_iff Set.subset_union_left
    (sylowUnion_subset_closure hu hsecond)

/-- The strict set containment of 16.2.10(1) implies the involution witness
of 16.2.10(2). The output uses `H ∩ N_G(L)`, hence relative normality. -/
theorem exists_outside_conjugate_involution_of_strict [Finite G]
    (hTH : (T : Subgroup G) ≤ H) (hu : u ∈ H)
    (hperm : ∀ g ∈ H, conjugate L g = L ∨ conjugate L g = conjugate L u)
    (hstrict : sylowUnion T L u ⊂ setStrongClosure (componentSylow T L : Set G)
      ((T : Subgroup G) ⊓ normalizer (L : Set G)) ⊤) :
    ∃ g : G, g ∉ H ∧ ∃ t : G,
      t ∈ conjugate L g ⊓ (H ⊓ normalizer (L : Set G)) ∧ orderOf t = 2 := by
  obtain ⟨y, hy, hyout⟩ := Set.exists_of_ssubset hstrict
  obtain ⟨hyN, x, hx, g, _, rfl⟩ := hy
  have hg : g ∉ H := by
    intro hg
    exact hyout ((sylowUnion_stronglyClosed_in_overgroup hu hperm).2
      x (Or.inl hx) g hg hyN.1)
  have hyne : g⁻¹ * x * g ≠ 1 := by
    intro he
    apply hyout
    rw [he]
    exact Or.inl (componentSylow T L).one_mem
  let P := conjugate (componentSylow T L) g ⊓
    ((T : Subgroup G) ⊓ normalizer (L : Set G))
  have hP : IsPGroup 2 P :=
    ((T.isPGroup'.to_le (show componentSylow T L ≤ T from inf_le_left)).map
      (MulAut.conj g⁻¹).toMonoidHom).to_inf_left
  have hyP : g⁻¹ * x * g ∈ P := ⟨by
    simpa [conjugate, MulAut.conj_apply] using
      (mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hx), hyN⟩
  have hyPne : (⟨g⁻¹ * x * g, hyP⟩ : P) ≠ 1 := by
    intro he
    exact hyne (congrArg Subtype.val he)
  have hdvd : 2 ∣ Nat.card P :=
    (hP.dvd_orderOf hyPne).trans (orderOf_dvd_natCard (⟨g⁻¹ * x * g, hyP⟩ : P))
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 hdvd
  refine ⟨g, hg, t, ⟨?_, hTH t.property.2.1, t.property.2.2⟩, ?_⟩
  · exact (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
      (show componentSylow T L ≤ L from inf_le_right)) t.property.1
  · exact (orderOf_injective P.subtype Subtype.coe_injective t).trans ht

/-- The intersection-generated group required by Asc75 is contained in the
actual H, using precisely the even-intersection conclusion of 16.2.8(1). -/
theorem source_intersectionGenerated_le [Finite G] {z : G}
    (h : CentralComponentSetup T z L) (o : TwoComponentOrbit T z L u)
    (intersection : ∀ g : G,
      Even (Nat.card (involutionContainer z L u ⊓
        conjugate (involutionContainer z L u) g : Subgroup G)) →
      g ∈ localComponentNormalizer z L) :
    intersectionGenerated (componentSylow T L) (componentSylow T (conjugate L u)) ≤
      localComponentNormalizer z L :=
  intersectionGenerated_le (o.swap_mem_localNormalizer h)
    (conjugate_componentSylow o.mem_sylow) (self_intersection_mem intersection)

/-- In the actual counterexample H₀ ≤ H < G; H₀ is not replaced by H. -/
theorem source_intersectionGenerated_ne_top [Finite G] {K : GroupClass} {z : G}
    (c : CounterexampleSetup K T z L) (o : TwoComponentOrbit T z L u)
    (intersection : ∀ g : G,
      Even (Nat.card (involutionContainer z L u ⊓
        conjugate (involutionContainer z L u) g : Subgroup G)) →
      g ∈ localComponentNormalizer z L) :
    intersectionGenerated (componentSylow T L)
      (componentSylow T (conjugate L u)) ≠ ⊤ := by
  intro he
  exact c.localNormalizer_ne_top (top_unique
    (he ▸ source_intersectionGenerated_le c.localSetup o intersection))

/-- Commuting components put the second Sylow intersection in N_T(L). -/
theorem source_second_le_normalizer {z : G}
    (h : CentralComponentSetup T z L) (o : TwoComponentOrbit T z L u) :
    componentSylow T (conjugate L u) ≤ normalizer (L : Set G) := by
  apply inf_le_right.trans
  apply (centralizer_le_normalizer (L : Set G)).trans'
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [commutator_comm]
  exact o.commute h

variable {z : G}

/-- Distinct Sylow intersections and permutation of the components identify the relative normalizer. -/
theorem sylow_normalizer_eq_of_distinct
    (hneq : componentSylow T L ≠ componentSylow T (conjugate L u))
    (hperm : ∀ g ∈ T, conjugate L g = L ∨ conjugate L g = conjugate L u) :
    (T : Subgroup G) ⊓ normalizer (componentSylow T L : Set G) =
      (T : Subgroup G) ⊓ normalizer (L : Set G) := by
  ext x
  constructor
  · rintro ⟨hxT, hxA⟩
    refine ⟨hxT, (mem_normalizer_iff_conjugate_eq L x).mpr ?_⟩
    rcases hperm x hxT with he | he
    · exact he
    · have hx := (mem_normalizer_iff_conjugate_eq (componentSylow T L) x).mp hxA
      rw [conjugate_componentSylow hxT, he] at hx
      exact (hneq hx.symm).elim
  · rintro ⟨hxT, hxL⟩
    refine ⟨hxT, (mem_normalizer_iff_conjugate_eq _ x).mpr ?_⟩
    rw [conjugate_componentSylow hxT, (mem_normalizer_iff_conjugate_eq L x).mp hxL]

/-- The two-component orbit has the same stabilizer for either component inside T. -/
theorem source_component_normalizers_eq
    (h : CentralComponentSetup T z L) (o : TwoComponentOrbit T z L u) :
    (T : Subgroup G) ⊓ normalizer (conjugate L u : Set G) =
      (T : Subgroup G) ⊓ normalizer (L : Set G) := by
  have perm (g : G) (hg : g ∈ T) :
      conjugate L g = L ∨ conjugate L g = conjugate L u :=
    o.orbit g (h.sylow_centralizes hg)
  ext g
  constructor
  · rintro ⟨hgT, hgU⟩
    refine ⟨hgT, (mem_normalizer_iff_conjugate_eq L g).mpr ?_⟩
    rcases perm g hgT with he | he
    · exact he
    · exact (o.moved (conjugate_injective g
        (((mem_normalizer_iff_conjugate_eq _ g).mp hgU).trans he.symm))).elim
  · rintro ⟨hgT, hgL⟩
    refine ⟨hgT, (mem_normalizer_iff_conjugate_eq _ g).mpr ?_⟩
    have hp := perm (u * g) (T.mul_mem o.mem_sylow hgT)
    rw [← conjugate_conjugate] at hp
    rcases hp with he | he
    · exact (o.moved (conjugate_injective g
        (he.trans ((mem_normalizer_iff_conjugate_eq L g).mp hgL).symm))).elim
    · exact he

/-- Strong closure for H restricts to the actual H₀, since both nontrivial members lie in H₀. -/
theorem source_union_closed_in_intersectionGenerated
    (h : CentralComponentSetup T z L) (o : TwoComponentOrbit T z L u)
    (hperm : ∀ g ∈ localComponentNormalizer z L,
      conjugate L g = L ∨ conjugate L g = conjugate L u)
    (intersection : ∀ g : G,
      Even (Nat.card (involutionContainer z L u ⊓
        conjugate (involutionContainer z L u) g : Subgroup G)) →
      g ∈ localComponentNormalizer z L)
    [Finite G]
    (hA : componentSylow T L ≠ ⊥) (hB : componentSylow T (conjugate L u) ≠ ⊥) :
    IsStronglyClosedSet (sylowUnion T L u)
      (intersectionGenerated (componentSylow T L) (componentSylow T (conjugate L u)) ⊓ T)
      (intersectionGenerated (componentSylow T L) (componentSylow T (conjugate L u))) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases hx with hx | hx
    · exact ⟨left_le_intersectionGenerated hA hx, hx.1⟩
    · exact ⟨right_le_intersectionGenerated hB hx, hx.1⟩
  · intro x hx g hg hy
    exact (sylowUnion_stronglyClosed_in_overgroup (o.swap_mem_localNormalizer h) hperm).2
      x hx g (source_intersectionGenerated_le h o intersection hg) hy.2

/-- Both normalizers required by Asc75 hypothesis (*) are exactly N_T(L). -/
theorem source_sylow_normalizers_eq
    (h : CentralComponentSetup T z L) (o : TwoComponentOrbit T z L u)
    (hneq : componentSylow T L ≠ componentSylow T (conjugate L u)) :
    ((T : Subgroup G) ⊓ normalizer (componentSylow T L : Set G) =
      (T : Subgroup G) ⊓ normalizer (L : Set G)) ∧
    ((T : Subgroup G) ⊓ normalizer (componentSylow T (conjugate L u) : Set G) =
      (T : Subgroup G) ⊓ normalizer (L : Set G)) := by
  refine ⟨sylow_normalizer_eq_of_distinct hneq
    (fun g hg => o.orbit g (h.sylow_centralizes hg)), ?_⟩
  have hneq' : componentSylow T (conjugate L u) ≠
      componentSylow T (conjugate (conjugate L u) u) := by
    rw [o.swap_twice h]
    exact hneq.symm
  have hp : ∀ g ∈ T, conjugate (conjugate L u) g = conjugate L u ∨
      conjugate (conjugate L u) g = conjugate (conjugate L u) u := by
    intro g hg
    have ho := o.orbit (u * g) (h.sylow_centralizes (T.mul_mem o.mem_sylow hg))
    rw [← conjugate_conjugate] at ho
    rcases ho with he | he
    · exact Or.inr (he.trans (o.swap_twice h).symm)
    · exact Or.inl he
  rw [sylow_normalizer_eq_of_distinct hneq' hp, source_component_normalizers_eq h o]

/-- Verification of Asc75 hypothesis (*) from the geometric inputs and the hypothetical strong closure. The rank and distinctness inputs are separate model obligations. -/
theorem source_hypotheses [Finite G]
    (h : CentralComponentSetup T z L) (o : TwoComponentOrbit T z L u)
    (hperm : ∀ g ∈ localComponentNormalizer z L,
      conjugate L g = L ∨ conjugate L g = conjugate L u)
    (intersection : ∀ g : G,
      Even (Nat.card (involutionContainer z L u ⊓
        conjugate (involutionContainer z L u) g : Subgroup G)) →
      g ∈ localComponentNormalizer z L)
    (hA : componentSylow T L ≠ ⊥) (hB : componentSylow T (conjugate L u) ≠ ⊥)
    (hneq : componentSylow T L ≠ componentSylow T (conjugate L u))
    (hrankA : BenderSuzuki.PFchapter1section1.TwoRankAtLeastTwo (componentSylow T L))
    (hrankB : BenderSuzuki.PFchapter1section1.TwoRankAtLeastTwo
      (componentSylow T (conjugate L u)))
    (hclosed : IsStronglyClosedSet (sylowUnion T L u)
      ((T : Subgroup G) ⊓ normalizer (L : Set G)) ⊤) :
    Asc75.Hypotheses T (componentSylow T L) (componentSylow T (conjugate L u)) := by
  have hn := source_sylow_normalizers_eq h o hneq
  refine ⟨inf_le_left, inf_le_left, ?_, hrankA, hrankB,
    source_union_closed_in_intersectionGenerated h o hperm intersection hA hB, ?_, ?_⟩
  · apply le_bot_iff.mp
    rw [← o.commute h]
    exact commutator_mono inf_le_right inf_le_right
  · rwa [hn.1]
  · rwa [hn.2]

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure
end
