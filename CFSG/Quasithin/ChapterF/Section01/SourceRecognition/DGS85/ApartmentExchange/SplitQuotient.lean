module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.CartanUniqueness
public import Theory.GroupTheory.WeakBNPair.RegularTree.CartanSaturation
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.SplitCore

/-!
# Saturation and splitness of the marked apartment quotient

The full original Borel fixes the marked edge. Every vertex of the chosen
apartment is in one of its endpoint N-orbits. An element in all conjugate
quotient Borels therefore fixes every quotient apartment vertex. Separation
lifts that fixation along a path; the odd path stabilizer equals the Cartan.
This proves saturation on the actual universal-completion quotient.

The original normal two-subgroup and abelian Cartan factorization then give
the finite-recognition owner's `SplitData` for the same Tits system. The odd
order of its Cartan follows from the Hall property. The original Cartan and
root construction, exchange, and Borel-normalizer intersection remain source
obligations; no model recognition or final classification is assumed.

Source: DGS, *Groups and Graphs* (1985), Part II, (3.6)–(3.7), pp.77–80,
and the Cartan/path-stabilizer argument of (14.10), pp.216–217.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open Theory.GroupTheory Theory.GroupTheory.WeakBNPair.RegularTree
open Subgroup.CosetGeometry RankTwoAmalgam
universe u
variable {L B R : Type u} [Group L] [Group B] [Group R]
variable (α : RankTwoAmalgam L B R) (T : Set (SourceVertex α)) (n : ℕ)
variable (hL : Function.Injective α.left) (hR : Function.Injective α.right)
variable (hn : 1 < n)
variable (hsep : Separated (sourceRelation α T n) (sourceGraph α) (2*n))
variable (K N : Subgroup α.Universal)
variable (hK : ∀ k ∈ K, ∀ a ∈ T, k • a = a)
variable (hHall : ∀ a ∈ T, ∀ b ∈ T, (sourceGraph α).Adj a b →
  IsHallSubgroup Subgroup.OddHall.oddPrimes
    (K.subgroupOf (MulAction.stabilizer α.Universal a ⊓ MulAction.stabilizer α.Universal b)))
variable (hodd : ∀ {a b} (p : (sourceGraph α).Walk a b), p.IsPath → p.length = n+1 →
  Odd (Nat.card (pathFixer (X := α.Universal) p)))
variable (hbase : ∀ i, base (Universal.cosetFamily α) i ∈ T)
variable (hdeg : TwoNeighborsIn (sourceGraph α) T)
variable (horbit : ∀ v ∈ T, ∃ g ∈ N, ∃ i, g • base (Universal.cosetFamily α) i = v)

include hL hR hn hsep hK hHall hodd hbase hdeg horbit in
/-- The literal quotient Borel is saturated with Cartan the image of K.
This derives saturation from separation, the apartment orbits, and the odd
path stabilizers, without assuming a Tits system. -/
theorem source_cartan_saturation [Finite L] [Finite R]
    (hKB : K ≤ originalMiddle α) (hnorm : N ≤ Subgroup.normalizer (K : Set α.Universal)) :
    (⨅ x : N.map (quotientMap α T n),
      ((originalMiddle α).map (quotientMap α T n)).comap
        (MulAut.conj (x : QuotientGroup α T n)).toMonoidHom) =
      K.map (quotientMap α T n) := by
  let a := base (Universal.cosetFamily α) false
  let c := base (Universal.cosetFamily α) true
  obtain ⟨b, p, hp, hlen, hpT, _⟩ := path_extension_in_set
    (Universal.cosetGraph_isTree α hL hR).2 hdeg
    (SimpleGraph.Walk.nil : (sourceGraph α).Walk a a)
    (SimpleGraph.Walk.IsPath.nil) (by simpa [a] using hbase false)
    (show 0 ≤ n+1 from Nat.zero_le _)
  have hfix : pathFixer (X := α.Universal) p = K :=
    pathFixer_eq_cartan K hK hHall (source_vertexStabilizer_finite α) p (by omega)
      hpT (source_pathFixer_pi α n hodd p hp hlen)
  have hBa : originalMiddle α ≤ MulAction.stabilizer α.Universal a := by
    rw [show a = base (Universal.cosetFamily α) false from rfl, stabilizer_base, originalMiddle,
      ← Universal.overlap_eq α hL hR]
    exact inf_le_left
  have hBc : originalMiddle α ≤ MulAction.stabilizer α.Universal c := by
    rw [show c = base (Universal.cosetFamily α) true from rfl, stabilizer_base, originalMiddle,
      ← Universal.overlap_eq α hL hR]
    exact inf_le_right
  apply image_saturation_of_pathFixer (quotientMap α T n)
    (apartmentSetoid_invariant (source_action α))
    (fun he v => related_of_quotient_eq (apartmentSetoid_invariant (source_action α)) he v)
    (Universal.cosetGraph_isTree α hL hR).1 (source_action α) hsep (by omega)
    (originalMiddle α) K N a c hBa hBc hKB hnorm p hfix.le
  intro k _
  obtain ⟨g, hg, i, hi⟩ := horbit _ (hpT _ (p.getVert_mem_support k))
  refine ⟨g, hg, ?_⟩
  cases i
  · exact Or.inl hi
  · exact Or.inr hi

include hK hHall hbase in
/-- Oddness of the Cartan follows from its Hall property; it is not an
additional splitness premise. -/
theorem source_cartan_odd : Nat.Coprime 2 (Nat.card K) := by
  let a := base (Universal.cosetFamily α) false
  let c := base (Universal.cosetFamily α) true
  have hadj : (sourceGraph α).Adj a c :=
    ⟨Bool.false_ne_true, incident_base (Universal.cosetFamily α) false true⟩
  have hKE : K ≤ MulAction.stabilizer α.Universal a ⊓ MulAction.stabilizer α.Universal c :=
    fun k hk => ⟨hK k hk a (hbase false), hK k hk c (hbase true)⟩
  have hH := hHall a (hbase false) c (hbase true) hadj
  apply Nat.prime_two.coprime_iff_not_dvd.mpr
  intro hdiv
  have hdiv' : 2 ∣ Nat.card (K.subgroupOf
      (MulAction.stabilizer α.Universal a ⊓ MulAction.stabilizer α.Universal c)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKE).toEquiv]
  exact hH.p_in_pi_of_p_dvd_card ⟨2, Nat.prime_two⟩ hdiv' rfl

variable (hcore : ((Universal.left α).range ⊓ (Universal.right α).range).normalCore = ⊥)
variable (roots : RootQuotientData (quotientMap α T n))
variable (hB : roots.B = originalMiddle α)
variable (hP : ∀ i, roots.endpoint i = Universal.cosetFamily α i)
variable (hBN : roots.B.map (quotientMap α T n) ⊓ roots.N.map (quotientMap α T n) =
  (roots.B ⊓ roots.N).map (quotientMap α T n))
variable (hCartan : K = originalMiddle α ⊓ roots.N)

/-- The original source split factorization descends to this same quotient;
the normal two-group, odd abelian complement and saturation all refer to
its actual B and N. No additional saturation hypothesis is needed. -/
noncomputable def sourceSplitData [Finite L] [Finite R]
    (hOrbit : ∀ v ∈ T, ∃ g ∈ roots.N, ∃ i, g • base (Universal.cosetFamily α) i = v)
    (U : Subgroup α.Universal)
    (hUnorm : originalMiddle α ≤ Subgroup.normalizer (U : Set α.Universal))
    (hTwo : IsPGroup 2 U)
    (hKabelian : IsMulCommutative K) (hfactor : U ⊔ K = originalMiddle α) :
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.SplitData
      (sourceTitsSystem α T n hL hR hsep hn hcore roots hB hP hBN) := by
  let q := quotientMap α T n
  have hU : U ≤ originalMiddle α := hfactor ▸ le_sup_left
  have hKodd := source_cartan_odd α T K hK hHall hbase
  have hint : roots.B.map q ⊓ roots.N.map q = K.map q := by
    rw [hBN, hCartan, hB]
  have hnorm : roots.N ≤ Subgroup.normalizer (K : Set α.Universal) := by
    rw [hCartan, ← hB]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mp roots.normal
  have hsat := source_cartan_saturation α T n hL hR hn hsep K roots.N hK hHall hodd
    hbase hdeg hOrbit (by rw [hCartan]; exact inf_le_left) hnorm
  refine {
    U := U.map q
    U_le := ?_
    normalizes := ?_
    isTwo := hTwo.map q
    odd := ?_
    abelian := ?_
    factorization := ?_
    saturation := ?_ }
  · change U.map q ≤ roots.B.map q
    rw [hB]
    exact Subgroup.map_mono hU
  · change roots.B.map q ≤ Subgroup.normalizer (U.map q : Set _)
    rw [hB]
    exact (Subgroup.map_mono hUnorm).trans (Subgroup.le_normalizer_map q)
  · change Nat.Coprime 2 (Nat.card (roots.B.map q ⊓ roots.N.map q : Subgroup _))
    rw [hint]
    exact hKodd.of_dvd_right (Subgroup.card_map_dvd K q)
  · change IsMulCommutative (roots.B.map q ⊓ roots.N.map q : Subgroup _)
    rw [hint]
    let := hKabelian
    infer_instance
  · change U.map q ⊔ (roots.B.map q ⊓ roots.N.map q) = roots.B.map q
    rw [hint, ← Subgroup.map_sup, hfactor, hB]
  · change (⨅ x : roots.N.map q, (roots.B.map q).comap
      (MulAut.conj (x : QuotientGroup α T n)).toMonoidHom) = roots.B.map q ⊓ roots.N.map q
    rw [hint, hB]
    exact hsat
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
