module

public import Stellmacher.Recognition.Parrott.SecondNormalizer
public import Theory.GroupTheory.ElementaryInvolutionFixedJoinTransport
public import Theory.GroupTheory.FrattiniInvolutionCosets

/-!
# Transport between Parrott's supplied second elementary subgroups

The selected involutory cosets belong to one orbit. Indeed each orbit has
five elements, whereas the Frattini obstruction bounds the total number of
nonzero cosets with involutory lifts by nine. Two different orbits would
contradict this bound. Changing an involution lift within a coset preserves
its fixed join, so the supplied fixed joins are conjugate in C_G(z).

Conjugation transports their normalizers. Their intersections with C_G(z)
are the supplied Sylow subgroups, so self-normalization transports while
retaining both witnesses.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.674–676, especially the representative choice before S=C_T(a).
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Any two supplied involutory cosets are conjugate in the original centralizer. -/
public theorem exists_conjugate_coset (d e : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let DH := (commutator (pCore 2 H)).map (pCore 2 H).subtype
    ∃ g : H, QuotientGroup.mk' DH (g * d.a * g⁻¹) = QuotientGroup.mk' DH e.a := by
  classical
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let D := commutator J
  let DH := D.map J.subtype
  let a (c : ParrottSecondElementaryData z) : J := ⟨c.a, c.a_mem_core⟩
  let q := QuotientGroup.mk' D
  obtain ⟨f, _, heval⟩ := parrott_core_quotient_action z h
  let : MulDistribMulAction (H ⧸ J) (J ⧸ D) := MulDistribMulAction.compHom (J ⧸ D) f
  let O (c : ParrottSecondElementaryData z) := MulAction.orbit (H ⧸ J) (q (a c))
  have hO (c : ParrottSecondElementaryData z) : (O c).ncard = 5 := by
    exact (centralizer_index_eq_subgroup_quotient_orbit_card J D f heval (a c)).symm.trans
      c.coset_index
  let S : Set (J ⧸ D) := {x | x ≠ 1 ∧ ∃ b : J, b ^ 2 = 1 ∧ q b = x}
  have hOS (c : ParrottSecondElementaryData z) : O c ⊆ S := by
    rintro x ⟨g, rfl⟩
    have ha : q (a c) ≠ 1 := by
      intro hh
      exact c.a_not_mem_derived (mem_map_of_mem J.subtype
        ((QuotientGroup.eq_one_iff (N := D) (a c)).mp hh))
    refine ⟨fun hh => ha ((f g).injective (hh.trans (map_one (f g)).symm)), ?_⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective J g
    let b : J := ⟨g * c.a * g⁻¹, (inferInstance : J.Normal).conj_mem c.a c.a_mem_core g⟩
    refine ⟨b, ?_, (heval g (a c) b rfl).symm⟩
    apply Subtype.ext
    have hc : c.a ^ 2 = 1 := c.a_order ▸ pow_orderOf_eq_one c.a
    change (MulAut.conj g c.a) ^ 2 = 1
    rw [← map_pow, hc, map_one]
  obtain ⟨hElem, hcard⟩ := parrott_core_abelianization_structure z h
  let : IsElementaryAbelian 2 (J ⧸ D) := hElem
  obtain ⟨_, _, _, hPhi, hUpper, hD, _, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 D := hD
  have hsmall : S.ncard < 10 :=
    nonidentity_involutory_cosets_ncard_lt_ten D hPhi hUpper hcard
  have hmem : q (a e) ∈ O d := by
    by_contra hn
    have hdis : Disjoint (O d) (O e) := by
      apply Set.disjoint_left.mpr
      intro x hxd hxe
      have hd := MulAction.orbit_eq_iff.mpr hxd
      have he := MulAction.orbit_eq_iff.mpr hxe
      have hEq : O d = O e := hd.symm.trans he
      apply hn
      rw [hEq]
      exact MulAction.mem_orbit_self _
    have hbound := Set.ncard_le_ncard (Set.union_subset (hOS d) (hOS e))
    rw [Set.ncard_union_eq hdis, hO d, hO e] at hbound
    omega
  obtain ⟨g, hg⟩ := hmem
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective J g
  let b : J := ⟨g * d.a * g⁻¹, (inferInstance : J.Normal).conj_mem d.a d.a_mem_core g⟩
  have hq : q b = q (a e) := (heval g (a d) b rfl).symm.trans hg
  refine ⟨g, QuotientGroup.eq_iff_div_mem.mpr ?_⟩
  exact mem_map_of_mem J.subtype (QuotientGroup.eq_iff_div_mem.mp hq)

omit [Finite G] in
private theorem transport_fixed_join_map (d : ParrottSecondElementaryData z) :
    let H := centralizer ({z} : Set G)
    let DH := (commutator (pCore 2 H)).map (pCore 2 H).subtype
    (zpowers d.a ⊔ (DH ⊓ centralizer ({d.a} : Set H))).map H.subtype = d.F := by
  dsimp only
  rw [map_zpowers_sup_inf_centralizer _ _ _ (centralizer ({z} : Set G)).subtype_injective,
    map_map]
  exact d.fixed_join.symm

/-- The fixed joins of both supplied witnesses are conjugate under C_G(z). -/
public theorem exists_conjugate_fixed_join (d e : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    ∃ g : centralizer ({z} : Set G), d.F.map (MulAut.conj (g : G)) = e.F := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let DH := (commutator J).map J.subtype
  let F (c : ParrottSecondElementaryData z) :=
    zpowers c.a ⊔ (DH ⊓ centralizer ({c.a} : Set H))
  obtain ⟨g, hg⟩ := d.exists_conjugate_coset e h
  let b := MulAut.conj g d.a
  have hb : orderOf b = 2 := ((MulAut.conj g).orderOf_eq d.a).trans d.a_order
  have hbD : b ∉ DH := by
    intro hbD
    apply e.a_not_mem_derived
    apply (QuotientGroup.eq_one_iff (N := DH) e.a).mp
    exact hg.symm.trans ((QuotientGroup.eq_one_iff (N := DH) b).mpr hbD)
  obtain ⟨_, _, _, _, _, hD, _, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 (commutator J) := hD
  let : IsElementaryAbelian 2 DH := IsElementaryAbelian.map J.subtype
  have hmap : (F d).map (MulAut.conj g) = F e := by
    rw [map_zpowers_sup_inf_centralizer _ _ _ (MulAut.conj g).injective,
      Subgroup.Normal.map_conj_eq]
    exact elementary_involution_fixed_join_eq_of_quotient_eq DH b e.a
      hb e.a_order hbD e.a_not_mem_derived hg
  refine ⟨g, ?_⟩
  calc
    d.F.map (MulAut.conj (g : G)) =
        ((F d).map H.subtype).map (MulAut.conj (g : G)) := by rw [transport_fixed_join_map]
    _ = ((F d).map (MulAut.conj g)).map H.subtype := by
      rw [map_map, map_map]
      congr 1
    _ = e.F := by rw [hmap, transport_fixed_join_map]

/-- Self-normalization transports between the two supplied second elementary
witnesses, retaining their original ambient Sylow subgroups. -/
public theorem normalizer_eq_sylow_of_normalizer_eq_sylow
    (d e : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (hd : normalizer (d.F : Set G) = (d.sylow : Subgroup G)) :
    normalizer (e.F : Set G) = (e.sylow : Subgroup G) := by
  let H := centralizer ({z} : Set G)
  obtain ⟨g, hg⟩ := d.exists_conjugate_fixed_join e h
  have hH : H.map (MulAut.conj (g : G)) = H :=
    mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer g.property)
  have hle : normalizer (e.F : Set G) ≤ H := by
    rw [← hg, ← map_normalizer_eq_of_bijective _ (MulAut.conj (g : G)).bijective, hd]
    exact (map_mono d.sylow_le_centralizer).trans hH.le
  exact (inf_eq_left.mpr hle).symm.trans (e.normalizer_inf_centralizer h)

end Stellmacher.Recognition.ParrottSecondElementaryData
