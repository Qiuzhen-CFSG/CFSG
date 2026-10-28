module
public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion.Plane
public import Theory.GroupTheory.UniqueFixedCosetQuotient

/-!
# The first AS91 fixed-coset argument

Let U be any pure pair plane through t and N its normalizer inside I=C_G(t).
For g in N outside M, the exact earlier intersection theorem bounds E∩E^g
by four. An elementary subgroup of E^g inside N∩M has order at most 4*16,
using the proved rank-four quotient. If conjugation by g returns v in E\U
to N∩M, its image lies outside E and centralizes 128 elements of E.
Conjugating that centralizer back normalizes U joined with v, whose normalizer
is already contained in M. This contradicts the 64-element bound.

Thus every v in E\U, and every subgroup of E properly containing U, has the
unique base coset in N/(N∩M). The relative subgroups and conjugation maps
are the literal original ones. The subsequent nontransitivity argument and
the second standard fixed-coset step remain separate obligations.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), proof of (6.3), p.602.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceFusion
open SourceIncidence LocalGeometry.LocalSubgroups Sporadic.Mathieu MathieuCode
open Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

/-- An elementary subgroup of the pair normalizer, lying in a distinct
conjugate radical, has order at most 4*16. -/
theorem purePairNormalizer_conjugate_subgroup_card_le (a : LocalData h)
    (hi : MarkerIntersection a) (U : Subgroup G) (hUE : U ≤ a.P.E)
    (ht : second a ∈ U) (hc : 2 < Nat.card U)
    (hp : ∀ u ∈ U, u ≠ 1 → ∃ m ∈ a.P.M, MulAut.conj m (second a) = u) (g : G) (hgc : g ∈ centralizer (second a)) (hgm : g ∉ a.P.M)
    (D : Subgroup G) (hDN : D ≤ pairNormalizer a U)
    (hDE : D ≤ a.P.E.map (MulAut.conj g).toMonoidHom) : Nat.card D ≤ 64 := by
  let := a.P.E_elementary
  let : IsElementaryAbelian 2 (a.P.E.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_injective
    (inclusion hDE) (inclusion_injective hDE)
  let f := (pairNormalizerProjection a U).comp (inclusion hDN)
  have hker : Nat.card f.ker ≤ 4 := by
    let j : f.ker → (a.P.E ⊓ a.P.E.map (MulAut.conj g).toMonoidHom : Subgroup G) := fun x =>
      ⟨x.val.val,by
        have hx : (⟨x.val.val,hDN x.val.property⟩ : pairNormalizer a U) ∈
            (pairNormalizerProjection a U).ker := x.property
        rw [pairNormalizerProjection_ker] at hx
        exact ⟨hx,hDE x.val.property⟩⟩
    have hj : Function.Injective j := by
      intro x y he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : (a.P.E ⊓ a.P.E.map (MulAut.conj g).toMonoidHom : Subgroup G) => (x : G)) he
    exact (Nat.card_le_card_of_injective j hj).trans
      (centralizer_intersection_card_le_four a hi g hgc hgm)
  let H := (pairNormalizerProjection a U).range
  have hLH : f.range ≤ H := by
    rintro _ ⟨d,rfl⟩
    exact ⟨inclusion hDN d,rfl⟩
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let : IsElementaryAbelian 2 (f.range.subgroupOf H) :=
    IsElementaryAbelian.of_injective (subgroupOfEquivOfLe hLH).toMonoidHom
      (subgroupOfEquivOfLe hLH).injective
  have hr : primeRank 2 H ≤ 4 := by
    rw [←primeRank_equiv 2 (pairNormalizerQuotientEquiv a U)]
    exact pairNormalizer_quotient_rank_le_four a U hUE ht hc hp
  have him := (primeRank_le_iff_elementary_card_le H).mp hr (f.range.subgroupOf H) inferInstance
  rw [Nat.card_congr (subgroupOfEquivOfLe hLH).toEquiv] at him
  have hc : Nat.card D = Nat.card f.ker * Nat.card f.range := by
    rw [←f.ker.card_mul_index,index_ker]
  rw [hc]
  exact (Nat.mul_le_mul hker him).trans (by decide)

end Theory.GroupTheory.Recognition.JankoFour.SourceFusion

namespace Theory.GroupTheory.Recognition.JankoFour.SourceFusion
open SourceIncidence LocalGeometry.LocalSubgroups Sporadic.Mathieu MathieuCode
open Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

/-- The returning-element form of the first source fixed-coset argument. -/
theorem purePair_transporter_mem (a : LocalData h) (hi : MarkerIntersection a)
    (U : Subgroup G) (hUE : U ≤ a.P.E) (ht : second a ∈ U) (hc : 2 < Nat.card U)
    (hp : ∀ u ∈ U, u ≠ 1 → ∃ m ∈ a.P.M, MulAut.conj m (second a) = u)
    (g v : G) (hgU : g ∈ normalizer (U : Set G))
    (hgc : g ∈ centralizer (second a)) (hvE : v ∈ a.P.E) (hvU : v ∉ U)
    (hwN : g*v*g⁻¹ ∈ pairNormalizer a U) : g ∈ a.P.M := by
  let := a.P.E_elementary
  let w := g*v*g⁻¹
  let C := a.P.E ⊓ centralizer w
  have hUcard : Nat.card U = 4 := pair_subgroup_card_eq_four a U hUE hc hp
  have hv2 : v^2=1 := elemPow_eq_one_of_isElementaryAbelian v hvE
  have hw2 : w^2=1 := by
    change (MulAut.conj g v)^2=1
    rw [←map_pow,hv2,map_one]
  by_contra hgm
  have hiCard := centralizer_intersection_card_le_four a hi g hgc hgm
  have hUinter : U ≤ a.P.E ⊓ a.P.E.map (MulAut.conj g).toMonoidHom := by
    apply le_inf hUE
    have hmap := mem_normalizer_iff_map_conj_eq.mp hgU
    change U.map (MulAut.conj g).toMonoidHom = U at hmap
    rw [←hmap]
    exact map_mono hUE
  have hinter : a.P.E ⊓ a.P.E.map (MulAut.conj g).toMonoidHom = U :=
    (eq_of_le_of_card_ge hUinter (by omega)).symm
  have hwE : w ∉ a.P.E := by
    intro hw
    have hwI : w ∈ a.P.E ⊓ a.P.E.map (MulAut.conj g).toMonoidHom :=
      ⟨hw,v,hvE,rfl⟩
    rw [hinter] at hwI
    exact hvU ((mem_normalizer_iff.mp hgU v).mpr hwI)
  let m : pairNormalizer a U := ⟨w,hwN⟩
  have hmorder : orderOf (pairNormalizerProjection a U m) = 2 := by
    apply orderOf_eq_prime
    · rw [←map_pow]
      have hm2 : m^2=1 := Subtype.ext hw2
      rw [hm2,map_one]
    · intro he
      have hmker : m ∈ (pairNormalizerProjection a U).ker := he
      rw [pairNormalizerProjection_ker] at hmker
      exact hwE hmker
  have hCcard : Nat.card C = 128 := pairNormalizer_involution_centralizer_card a U
    hUE ht hc hp m hmorder
  let V := U ⊔ zpowers v
  have hVE : V ≤ a.P.E := sup_le hUE (zpowers_le.mpr hvE)
  have hUV : U < V := lt_of_le_of_ne le_sup_left (by
    intro he
    have hvV : v ∈ V := (le_sup_right : zpowers v ≤ V) (mem_zpowers v)
    apply hvU
    rw [he]
    exact hvV)
  have hb := strict_pair_overgroup_normalizer_le a hi U V hVE hUV
    hc hp
  let D := C.map (MulAut.conj g⁻¹).toMonoidHom
  have hDN : D ≤ pairNormalizer a U := by
    rintro x ⟨c,hc,rfl⟩
    have hcU : c ∈ Subgroup.centralizer (U : Set G) := by
      intro u hu
      exact setLike_mul_comm (hUE hu) hc.1
    have hxU : MulAut.conj g⁻¹ c ∈ Subgroup.centralizer (U : Set G) := by
      intro u hu
      have hgu : g*u*g⁻¹ ∈ U := (mem_normalizer_iff.mp hgU u).mp hu
      have hcomm : Commute (g*u*g⁻¹) c := hcU _ hgu
      have hh := hcomm.map (MulAut.conj g⁻¹)
      have he : MulAut.conj g⁻¹ (g*u*g⁻¹) = u := by
        simp [mul_assoc]
      rw [he] at hh
      exact hh.eq
    have hxv : MulAut.conj g⁻¹ c ∈ centralizer v := by
      have hcomm : Commute c w := mem_centralizer_singleton_iff.mp hc.2
      have hh := hcomm.map (MulAut.conj g⁻¹)
      apply mem_centralizer_singleton_iff.mpr
      have he : MulAut.conj g⁻¹ w = v := by
        simp [w,mul_assoc]
      rw [he] at hh
      exact hh.eq
    have hxV : MulAut.conj g⁻¹ c ∈ Subgroup.centralizer (V : Set G) := by
      have hle : V ≤ Subgroup.centralizer ({MulAut.conj g⁻¹ c} : Set G) := by
        apply sup_le
        · intro u hu
          exact mem_centralizer_singleton_iff.mpr (hxU u hu)
        · exact zpowers_le.mpr
            (mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hxv).symm)
      intro u hu
      exact mem_centralizer_singleton_iff.mp (hle hu)
    have hxI : MulAut.conj g⁻¹ c ∈ centralizer (second a) := by
      have hcI : c ∈ centralizer (second a) :=
        (E_le_pairNormalizer a U hUE hc.1).2.1
      change g⁻¹*c*g⁻¹⁻¹ ∈ centralizer (second a)
      rw [inv_inv]
      exact (centralizer (second a)).mul_mem
        ((centralizer (second a)).mul_mem ((centralizer (second a)).inv_mem hgc) hcI)
        hgc
    exact ⟨Subgroup.centralizer_le_normalizer _ hxU,
      hb ⟨Subgroup.centralizer_le_normalizer _ hxV,hxI⟩⟩
  have hDE : D ≤ a.P.E.map (MulAut.conj g⁻¹).toMonoidHom := map_mono inf_le_left
  have hbound := purePairNormalizer_conjugate_subgroup_card_le a hi U hUE ht hc hp g⁻¹
    ((centralizer (second a)).inv_mem hgc) (fun he => hgm (a.P.M.inv_mem_iff.mp he)) D hDN hDE
  have hDc : Nat.card D = Nat.card C := card_map_of_injective (MulAut.conj g⁻¹).injective
  omega

end Theory.GroupTheory.Recognition.JankoFour.SourceFusion


public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceFusion
open SourceIncidence
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

theorem purePair_unique_fixed_coset (a : LocalData h) (hi : MarkerIntersection a)
    (U : Subgroup G) (hUE : U ≤ a.P.E) (ht : second a ∈ U) (hc : 2 < Nat.card U)
    (hp : ∀ u ∈ U, u ≠ 1 → ∃ m ∈ a.P.M, MulAut.conj m (second a) = u)
    (v : ↥(normalizer (U : Set G) ⊓ centralizer (second a)))
    (hvE : (v : G) ∈ a.P.E) (hvU : (v : G) ∉ U) :
    ∃! q : ↥(normalizer (U : Set G) ⊓ centralizer (second a)) ⧸
      a.P.M.subgroupOf (normalizer (U : Set G) ⊓ centralizer (second a)), v • q = q := by
  apply UniqueFixedCoset.unique_of_transporter
    (G := ↥(normalizer (U : Set G) ⊓ centralizer (second a)))
    (M := a.P.M.subgroupOf (normalizer (U : Set G) ⊓ centralizer (second a)))
    (a.P.E_le hvE)
  intro g hg
  apply purePair_transporter_mem a hi U hUE ht hc hp g.val v.val
    g.property.1 g.property.2 hvE hvU
  have hn := (g*v*g⁻¹).property
  exact ⟨hn.1,hn.2,hg⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceFusion

public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceFusion
open SourceIncidence
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

/-- The 64-element bound specialized to the constructed coordinate plane. -/
theorem pairNormalizer_conjugate_subgroup_card_le (a : LocalData h)
    (hi : MarkerIntersection a) (g : G) (hgc : g ∈ centralizer (second a)) (hgm : g ∉ a.P.M)
    (D : Subgroup G) (hDN : D ≤ pairNormalizer a (secondPlane a))
    (hDE : D ≤ a.P.E.map (MulAut.conj g).toMonoidHom) : Nat.card D ≤ 64 :=
  purePairNormalizer_conjugate_subgroup_card_le a hi (secondPlane a) (secondPlane_le a)
    (second_mem_secondPlane a) (by rw [secondPlane_card]; decide) (secondPlane_orbit a)
    g hgc hgm D hDN hDE

/-- The first transporter bound specialized to the constructed coordinate plane. -/
theorem pairPlane_transporter_mem (a : LocalData h) (hi : MarkerIntersection a)
    (g v : G) (hgU : g ∈ normalizer (secondPlane a : Set G))
    (hgc : g ∈ centralizer (second a)) (hvE : v ∈ a.P.E) (hvU : v ∉ secondPlane a)
    (hwN : g*v*g⁻¹ ∈ pairNormalizer a (secondPlane a)) : g ∈ a.P.M :=
  purePair_transporter_mem a hi (secondPlane a) (secondPlane_le a)
    (second_mem_secondPlane a) (by rw [secondPlane_card]; decide) (secondPlane_orbit a)
    g v hgU hgc hvE hvU hwN

end Theory.GroupTheory.Recognition.JankoFour.SourceFusion
@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceFusion
open SourceIncidence
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

/-- The full normalizer of the constructed plane inside I=C_G(t). -/
noncomputable abbrev pairAmbientNormalizer (a : LocalData h) : Subgroup G :=
  normalizer (secondPlane a : Set G) ⊓ centralizer (second a)

/-- The first standard fixed-coset conclusion, with its literal relative
normalizer and left coset action. Every element of E outside U fixes exactly
one coset; hence every subgroup V of E properly containing U does also. -/
theorem pairPlane_unique_fixed_coset (a : LocalData h) (hi : MarkerIntersection a)
    (v : pairAmbientNormalizer a) (hvE : (v : G) ∈ a.P.E)
    (hvU : (v : G) ∉ secondPlane a) :
    ∃! q : pairAmbientNormalizer a ⧸ a.P.M.subgroupOf (pairAmbientNormalizer a), v • q = q := by
  apply UniqueFixedCoset.unique_of_transporter (G := pairAmbientNormalizer a)
    (M := a.P.M.subgroupOf (pairAmbientNormalizer a)) (a.P.E_le hvE)
  intro g hg
  apply pairPlane_transporter_mem a hi g.val v.val g.property.1 g.property.2 hvE hvU
  have hn := (g*v*g⁻¹).property
  exact ⟨hn.1,hn.2,hg⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceFusion

public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceFusion
open SourceIncidence
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

/-- Source (6.3)'s first fixed-point statement for each proper overgroup V
of U in E, in the original N_I(U)/N_(I ∩ M)(U) action. -/
theorem pairPlane_overgroup_unique_fixed_coset (a : LocalData h) (hi : MarkerIntersection a)
    (V : Subgroup G) (hUV : secondPlane a < V) (hVE : V ≤ a.P.E) :
    ∃! q : pairAmbientNormalizer a ⧸ a.P.M.subgroupOf (pairAmbientNormalizer a),
      ∀ v : V.subgroupOf (pairAmbientNormalizer a), (v : pairAmbientNormalizer a) • q = q := by
  let N := pairAmbientNormalizer a
  let H := a.P.M.subgroupOf N
  have hbase : ∀ v : V.subgroupOf N, (v : N) • (QuotientGroup.mk (1 : N) : N ⧸ H) =
      QuotientGroup.mk 1 := by
    intro v
    apply (UniqueFixedCoset.fixed_iff H (v : N) 1).mpr
    simpa only [inv_one,one_mul,mul_one] using
      (show (v : N) ∈ H from a.P.E_le (hVE v.property))
  refine ⟨QuotientGroup.mk 1,hbase,?_⟩
  intro q hq
  obtain ⟨v,hvV,hvU⟩ := SetLike.exists_of_lt hUV
  have hvE := hVE hvV
  have hvN' := E_le_pairNormalizer a (secondPlane a) (secondPlane_le a) hvE
  let vN : N := ⟨v,hvN'.1,hvN'.2.1⟩
  exact (pairPlane_unique_fixed_coset a hi vN hvE hvU).unique
    (hq ⟨vN,hvV⟩) (hbase ⟨vN,hvV⟩)

end Theory.GroupTheory.Recognition.JankoFour.SourceFusion
