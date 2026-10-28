module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.Endpoints
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.NoncentralPoint
public import Theory.GroupTheory.CrossingFusionCentralizer.Translation
public import Theory.Representation.BinaryNaturalDual.ModelOrbits.Coordinate

/-!
# Matching on the two original natural supports

The full natural action is transitive on nonzero quotient vectors. An actual
element exchanging the supports joins the natural and dual pure classes.
Suitability lifts each specified match through the original central line.
Consequently every pure vector avoids the ambient conjugacy class of that
line. A common pure vector at a critical pair then gives a crossing for the
same suitable u, even when translating the endpoint changes its first edge.

These are conditional source consumers: the action markings come from
14.6.20--23, and the common pure vector must be constructed by the rank-one
or rank-two argument of 14.6.24(4). No common-vector existence is asserted.
Source: Aschbacher--Smith, printed pp.1038--1041.
-/

public section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.OrbitMatching
variable {G : Type*} [Group G]

/-- Transitivity on the literal natural section gives a specified match modulo
its original kernel, with the matching element in the original actor. -/
theorem natural_section_match_mod_point
    (A W Z : Subgroup G)
    (f : A →* BinaryLinear.GL (Fin 3 → ZMod 2)) (hf : Function.Surjective f)
    (c : BinaryConjugationSection A W Z
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f))
    (u v : G) (hu : u ∈ W) (hv : v ∈ W) (huz : u ∉ Z) (hvz : v ∉ Z) :
    ∃ x ∈ A, (MulAut.conj x) u * v⁻¹ ∈ Z := by
  have hu0 : (c.coordinates ⟨u,hu⟩).toAdd ≠ 0 :=
    fun he => huz ((c.coordinates_eq_one_iff ⟨u,hu⟩).mp he)
  have hv0 : (c.coordinates ⟨v,hv⟩).toAdd ≠ 0 :=
    fun he => hvz ((c.coordinates_eq_one_iff ⟨v,hv⟩).mp he)
  obtain ⟨g,hg⟩ := BinaryLinear.OuterCyclic.exists_linearEquiv_apply_eq hu0 hv0
  obtain ⟨x,hx⟩ := hf g
  let w : W := ⟨(MulAut.conj (x : G)) u,(c.normalized x.property u).mp hu⟩
  have he : c.coordinates w = c.coordinates ⟨v,hv⟩ := by
    apply Multiplicative.toAdd.injective
    change (c.coordinates ⟨(x : G) * u * (x : G)⁻¹,_⟩).toAdd = _
    rw [c.equivariant x ⟨u,hu⟩]
    change f x (c.coordinates ⟨u,hu⟩).toAdd = _
    rw [hx,hg]
  refine ⟨x,x.property,(c.coordinates_eq_one_iff (w * (⟨v,hv⟩ : W)⁻¹)).mp ?_⟩
  rw [map_mul,map_inv,he,mul_inv_cancel]

/-- The actual support exchanger joins the two pure orbits, modulo the same Z.
Only the natural action on W is needed; W' is its specified conjugate. -/
theorem natural_pair_match_mod_point
    (H W W' Z : Subgroup G) (hHZ : H ≤ normalizer (Z : Set G))
    (f : (H ⊓ normalizer (W : Set G) : Subgroup G) →*
      BinaryLinear.GL (Fin 3 → ZMod 2)) (hf : Function.Surjective f)
    (c : BinaryConjugationSection (H ⊓ normalizer (W : Set G)) W Z
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f))
    (s : G) (hs : s ∈ H) (hsW : W.map (MulAut.conj s).toMonoidHom = W')
    (u v : G) (hu : u ∈ W) (hv : v ∈ W ∨ v ∈ W') (huz : u ∉ Z) (hvz : v ∉ Z) :
    ∃ x ∈ H, (MulAut.conj x) u * v⁻¹ ∈ Z := by
  rcases hv with hv | hv
  · obtain ⟨x,hx,he⟩ := natural_section_match_mod_point _ W Z f hf c u v hu hv huz hvz
    exact ⟨x,hx.1,he⟩
  · obtain ⟨w,hw,hwv⟩ := mem_map.mp (hsW.symm ▸ hv)
    have hwz : w ∉ Z := by
      intro hz
      exact hvz (hwv ▸ (hHZ hs w).mp hz)
    obtain ⟨x,hx,he⟩ := natural_section_match_mod_point _ W Z f hf c u w hu hw huz hwz
    refine ⟨s * x,H.mul_mem hs hx.1,?_⟩
    have hh := (hHZ hs _).mp he
    rw [←hwv]
    simpa [MulAut.conj_apply,mul_assoc] using hh

variable [Finite G]
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (W W' : Subgroup G)
    (f : (Mc ⊓ normalizer (W : Set G) : Subgroup G) →*
      BinaryLinear.GL (Fin 3 → ZMod 2)) (hf : Function.Surjective f)
    (c : BinaryConjugationSection (Mc ⊓ normalizer (W : Set G)) W (centralInvolutions T)
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f))
    (s : G) (hs : s ∈ Mc) (hsW : W.map (MulAut.conj s).toMonoidHom = W')
    (u : G) (huW : u ∈ W)
    (hu : ComponentSupports.Suitable
      (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) Mc u)

include hu in
/-- Suitability excludes the original central line without changing u. -/
theorem suitable_not_mem_point : u ∉ centralInvolutions T := by
  let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  intro hz
  apply hu.2.2.2.1
  intro x hx
  exact mem_centralizer_singleton_iff.mpr
    (h.H_centralizes (pCoreIn_le 2 Mc hx) u hz).symm

include hf c hs hsW huW hu in
/-- Both lifts of every specified pure quotient vector are Mc-conjugate to the
same suitable u. This is transitivity on the pure supports, not ambient fusion. -/
theorem source_match_of_pure
    (v : G) (hv : v ∈ W ∨ v ∈ W') (hvz : v ∉ centralInvolutions T) :
    ∃ x ∈ Mc, (MulAut.conj x) u = v := by
  let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  apply match_of_match_mod_point h u hu.1 hu.2.2.2.1 v
  exact natural_pair_match_mod_point Mc W W' (centralInvolutions T)
    (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) f hf c s hs hsW u v huW hv
    (suitable_not_mem_point hG T hempty hM hunique hmany hcard e hab u hu) hvz

include hf c hs hsW huW hu in
/-- The whole pure orbit avoids every conjugate of the original point, as
required in both symmetric cases and in the asymmetric contradiction. -/
theorem source_pure_not_isConj_point
    (v : G) (hv : v ∈ W ∨ v ∈ W') (hvz : v ∉ centralInvolutions T)
    (z : G) (hz : z ∈ centralInvolutions T) : ¬ IsConj v z := by
  obtain ⟨x,_,he⟩ := source_match_of_pure hG T hempty hM hunique hmany hcard e hab
    W W' f hf c s hs hsW u huW hu v hv hvz
  have hux : IsConj u v := isConj_iff.mpr ⟨x,by simpa only [MulAut.conj_apply] using he⟩
  intro hvz'
  exact source_suitable_not_isConj_point hG T hempty hM hunique hmany hcard e hab Mc
    (ComponentSupports.terminal_outside hG T hempty hM hunique hmany hcard e)
    u hu.1 hu.2.2.1 hu.2.2.2.1 hu.2.2.2.2.1 hu.2.2.2.2.2 z hz (hux.trans hvz')

include hf c hs hsW huW hu in
/-- Once the two critical commutator descriptions yield a common pure vector,
construct the translated endpoint, all its labels, and the matching pair for
the original u. The translated endpoint need not normalize the original edge. -/
theorem source_crossing_of_common_pure
    (i : (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab).CriticalEndpoint)
    (a b : G) (ha : a ∈ W ∨ a ∈ W') (hb : b ∈ W ∨ b ∈ W')
    (haz : a ∉ centralInvolutions T) (hbz : b ∉ centralInvolutions T)
    (he : (MulAut.conj i.representative) b = a) :
    ∃ x ∈ Mc, ∃ k : G,
      k = x⁻¹ * i.representative ∧
      (∀ A : Subgroup G, A.map (MulAut.conj k).toMonoidHom =
        (i.conjugate A).map (MulAut.conj x⁻¹).toMonoidHom) ∧
      ∃ d : SourceCrossingGeometry (localModule T M) Mc Mc u,
        d.A = conjugateSpanBy (localModule T M) Mc ∧ d.g = k ∧
        ¬ centralizer ({u} : Set G) ≤ Mc := by
  let U := conjugateSpanBy (localModule T M) Mc
  have hn : Mc ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy _ _
  have hx := source_match_of_pure hG T hempty hM hunique hmany hcard e hab
    W W' f hf c s hs hsW u huW hu a ha haz
  have hy := source_match_of_pure hG T hempty hM hunique hmany hcard e hab
    W W' f hf c s hs hsW u huW hu b hb hbz
  obtain ⟨x,hxM,k,hk,hlabels,hmem,hmatch,hcross⟩ :=
    translated_crossing_of_orbit_intersection U Mc hn u hu.1 i.representative a b he hx hy
      (critical_spans_do_not_commute _ rfl i)
  let d : SourceCrossingGeometry (localModule T M) Mc Mc u :=
    ⟨U,le_rfl,hn,k,hmem,hmatch,hcross⟩
  let := hab
  exact ⟨x,hxM,k,hk,hlabels,d,rfl,rfl,
    centralizer_not_le_of_crossing_match U Mc U Mc le_rfl hn hn u k hmatch hcross⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.OrbitMatching
