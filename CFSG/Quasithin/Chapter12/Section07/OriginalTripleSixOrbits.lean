module

public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Actions
public import Theory.Representation.HexacodeAction.EvenBinaryRecognition
public import Theory.Representation.HexacodeAction.EvenOrbits
public import Theory.GroupTheory.ConjugationOrbitSize
public import Theory.GroupTheory.DisjointConjugateCenter
public import Theory.GroupTheory.NormalSylowQuotientAction

/-!
# The original two orbits in the covered-six source case

Recognize the literal faithful irreducible six-dimensional quotient action,
including its actor automorphism, and transport both hexacode orbits to the
whole original chosen subgroup. A nonidentity element of its intersection
with the original Sylow center supplies z. Its local orbit is odd, and the
other orbit is even. These are the representatives used in 12.7.2--12.7.3.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, K.1.3 and
12.7.2--12.7.3, printed pp.453 and 839--840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- Coordinates on the full original triple-six space. The group equivalence
retains the automorphism supplied by faithful six-dimensional recognition. -/
theorem original_tripleSix_coordinates (D : ChosenModule T K U)
    (eK : (K ⧸ pCore 2 K) ≃* Atlas.Codes.HexEvenAutomorphisms)
    (hd : Module.finrank (ZMod 2) D.space = 6)
    (hf : Function.Injective D.quotientAction) (hi : IsIrreducible D.quotientAction) :
    Nonempty (ActionEquiv D.quotientAction Hexacode.evenAction) := by
  let σ := D.quotientAction.comp eK.symm.toMonoidHom
  have hs : IsIrreducible σ :=
    (irreducible_comp_surjective_iff eK.symm.toMonoidHom eK.symm.surjective _).mpr hi
  obtain ⟨a, f, he⟩ := Hexacode.EvenBinaryRecognition.exists_equivariant σ
    (hf.comp eK.symm.injective) hs hd
  refine ⟨⟨eK.trans a, f, ?_⟩⟩
  intro g v
  simpa only [σ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    eK.symm_apply_apply, MulEquiv.trans_apply] using he (eK g) v

omit [Finite G] in
private theorem orbit_index (x : G) :
    (conjugacyOrbit K x).ncard = (centralizer ({x} : Set G)).relIndex K := by
  let : MulAction K G := MulAction.compHom G (MulAut.conj.comp K.subtype)
  have hs : MulAction.stabilizer K x = (centralizer ({x} : Set G)).subgroupOf K := by
    ext k
    change (k : G) * x * (k : G)⁻¹ = x ↔ (k : G) ∈ centralizer ({x} : Set G)
    rw [mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  exact (MulAction.index_stabilizer K x).symm.trans (congrArg Subgroup.index hs)

private theorem original_two_orbits (D : ChosenModule T K U)
    (e : ActionEquiv D.quotientAction Hexacode.evenAction) :
    Nat.card U = 64 ∧ ∃ r s : G, r ∈ U ∧ r ≠ 1 ∧ s ∈ U ∧ s ≠ 1 ∧
      ∀ v ∈ U, v ≠ 1 → v ∈ conjugacyOrbit K r ∨ v ∈ conjugacyOrbit K s := by
  obtain ⟨a, f, he⟩ := D.conjugationModel_of_quotientAction e
  have hc : Nat.card U = 64 := (Nat.card_congr f.toEquiv).trans Atlas.Codes.hexacode_card
  obtain ⟨r, s, hr, hs, hcover⟩ := Hexacode.evenAction_two_nonzero_orbits
  let rU := f.symm (Multiplicative.ofAdd r)
  let sU := f.symm (Multiplicative.ofAdd s)
  have hr1 : (rU : G) ≠ 1 := by
    intro h
    have hh := congrArg f (show rU = 1 from Subtype.ext h)
    exact hr (by simpa [rU] using hh)
  have hs1 : (sU : G) ≠ 1 := by
    intro h
    have hh := congrArg f (show sU = 1 from Subtype.ext h)
    exact hs (by simpa [sU] using hh)
  refine ⟨hc, rU, sU, rU.property, hr1, sU.property, hs1, ?_⟩
  intro v hv hv1
  let vU : U := ⟨v, hv⟩
  have hv0 : (f vU).toAdd ≠ 0 := by
    intro h
    have hh : f vU = 1 := h
    have hh' : vU = 1 := f.injective (hh.trans f.map_one.symm)
    exact hv1 (congrArg Subtype.val hh')
  have htransport (w : Atlas.Codes.hexacode) (g : Atlas.Codes.HexEvenAutomorphisms)
      (hg : Hexacode.evenAction g w = (f vU).toAdd) :
      v ∈ conjugacyOrbit K (f.symm (Multiplicative.ofAdd w) : G) := by
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (pCore 2 K) (a.symm g)
    refine ⟨k, ?_⟩
    have hh := he k (f.symm (Multiplicative.ofAdd w))
    rw [hk, a.apply_symm_apply, f.apply_symm_apply] at hh
    change (f.symm (Multiplicative.ofAdd (Hexacode.evenAction g w)) : G) = _ at hh
    rw [hg] at hh
    change (f.symm (f vU) : G) = _ at hh
    rw [f.symm_apply_apply] at hh
    exact hh.symm
  rcases hcover (f vU).toAdd hv0 with ⟨g, hg⟩ | ⟨g, hg⟩
  · exact Or.inl (htransport r g hg)
  · exact Or.inr (htransport s g hg)

/-- The literal triple-six row supplies the original source representatives:
z is fixed by T, t has even K-orbit, and their two K-orbits cover U minus 1.
The only additional input is normalization of the chosen U by T, supplied
by the structural part of 12.2.2. -/
theorem original_tripleSix_orbit_entry (D : ChosenModule T K U)
    (eK : (K ⧸ pCore 2 K) ≃* Atlas.Codes.HexEvenAutomorphisms)
    (hd : Module.finrank (ZMod 2) D.space = 6)
    (hf : Function.Injective D.quotientAction) (hi : IsIrreducible D.quotientAction)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G)) :
    ∃ z t : G, z ∈ U ∧ z ≠ 1 ∧ t ∈ U ∧ t ≠ 1 ∧
      (T : Subgroup G) ≤ centralizer ({z} : Set G) ∧
      2 ∣ (centralizer ({t} : Set G)).relIndex K ∧
      ∀ v ∈ U, v ≠ 1 → ∃ k ∈ K, MulAut.conj k v = z ∨ MulAut.conj k v = t := by
  classical
  obtain ⟨e⟩ := original_tripleSix_coordinates D eK hd hf hi
  obtain ⟨hcard, r, s, hrU, hr1, hsU, hs1, hcover⟩ := original_two_orbits D e
  obtain ⟨⟨z, hz⟩, hz1'⟩ := ne_bot_iff_exists_ne_one.mp
    (inf_centerIn_ne_bot T.isPGroup' D.ne_bot D.le_sylow hTU)
  have hz1 : z ≠ 1 := fun h => hz1' (Subtype.ext h)
  have hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hz.2.2) t ht)
  let : MulAction K G := MulAction.compHom G (MulAut.conj.comp K.subtype)
  have hthrough : ∃ t ∈ U, t ≠ 1 ∧ ∀ v ∈ U, v ≠ 1 →
      v ∈ conjugacyOrbit K z ∨ v ∈ conjugacyOrbit K t := by
    rcases hcover z hz.1 hz1 with hzr | hzs
    · refine ⟨s, hsU, hs1, ?_⟩
      have heq : conjugacyOrbit K z = conjugacyOrbit K r := MulAction.orbit_eq_iff.mpr hzr
      intro v hv hv1
      rw [heq]
      exact hcover v hv hv1
    · refine ⟨r, hrU, hr1, ?_⟩
      have heq : conjugacyOrbit K z = conjugacyOrbit K s := MulAction.orbit_eq_iff.mpr hzs
      intro v hv hv1
      rw [heq, or_comm]
      exact hcover v hv hv1
  obtain ⟨t, htU, ht1, hthrough⟩ := hthrough
  have hone (x : G) (hx : x ≠ 1) : (1 : G) ∉ conjugacyOrbit K x := by
    rintro ⟨k, hk⟩
    exact hx ((MulAut.conj (k : G)).injective (hk.trans (map_one _).symm))
  have hsub (x : G) (hx : x ∈ U) : conjugacyOrbit K x ⊆ U := by
    rintro _ ⟨k, rfl⟩
    exact (D.normalizes k.property x).mp hx
  have hfull : insert 1 (conjugacyOrbit K z ∪ conjugacyOrbit K t) = (U : Set G) := by
    ext v
    constructor
    · rintro (rfl | hv | hv)
      · exact U.one_mem
      · exact hsub z hz.1 hv
      · exact hsub t htU hv
    · intro hv
      by_cases hv1 : v = 1
      · exact Or.inl hv1
      · exact Or.inr (hthrough v hv hv1)
  have hno7 : ¬ 7 ∣ Nat.card K := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_eq
    have hc := card_eq_card_quotient_mul_card_subgroup (pCore 2 K)
    rw [Nat.card_congr eK.toEquiv, Atlas.Codes.hexEven_card, hn] at hc
    rw [hc]
    intro h
    rcases (Nat.prime_seven.dvd_mul).mp h with h | h
    · norm_num at h
    · have := Nat.prime_seven.dvd_of_dvd_pow h
      norm_num at this
  have hdistinct : conjugacyOrbit K z ≠ conjugacyOrbit K t := by
    intro heq
    have hc := congrArg Set.ncard hfull
    rw [← heq, Set.union_self, Set.ncard_insert_of_notMem (hone z hz1)] at hc
    change (conjugacyOrbit K z).ncard + 1 = Nat.card U at hc
    rw [hcard] at hc
    have ho : (conjugacyOrbit K z).ncard = 63 := by omega
    have hdvd := (centralizer ({z} : Set G)).relIndex_dvd_card K
    rw [← orbit_index z, ho] at hdvd
    exact hno7 ((by norm_num : 7 ∣ 63).trans hdvd)
  have hdis : Disjoint (conjugacyOrbit K z) (conjugacyOrbit K t) := by
    apply Set.disjoint_left.mpr
    intro v hvz hvt
    exact hdistinct ((MulAction.orbit_eq_iff.mpr hvz).symm.trans
      (MulAction.orbit_eq_iff.mpr hvt))
  have hcount : (conjugacyOrbit K z).ncard + (conjugacyOrbit K t).ncard + 1 = 64 := by
    have hc := congrArg Set.ncard hfull
    rw [Set.ncard_insert_of_notMem (fun h => h.elim (hone z hz1) (hone t ht1)),
      Set.ncard_union_eq hdis] at hc
    change _ = Nat.card U at hc
    exact hc.trans hcard
  obtain ⟨P, hP⟩ := NormalSylowQuotientAction.intersection_sylow T K D.sylow_normalizes_component
  have hodd : ¬ 2 ∣ (conjugacyOrbit K z).ncard := by
    rw [orbit_index z]
    intro h
    apply P.not_dvd_index
    apply h.trans
    apply index_dvd_of_le
    rw [hP]
    exact fun k hk => hzT hk
  have heven : 2 ∣ (centralizer ({t} : Set G)).relIndex K := by
    rw [← orbit_index t]
    omega
  refine ⟨z, t, hz.1, hz1, htU, ht1, hzT, heven, ?_⟩
  intro v hv hv1
  rcases hthrough v hv hv1 with ⟨k, hk⟩ | ⟨k, hk⟩
  · refine ⟨(k : G)⁻¹, K.inv_mem k.property, Or.inl ?_⟩
    rw [← hk]
    simp [mul_assoc]
  · refine ⟨(k : G)⁻¹, K.inv_mem k.property, Or.inr ?_⟩
    rw [← hk]
    simp [mul_assoc]

end CFSG.Quasithin.Chapter12.Section07
