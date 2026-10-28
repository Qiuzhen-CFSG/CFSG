module
public import CFSG.Quasithin.Chapter1.Section03.Basic
public import Theory.GroupTheory.PrimeRankNormalPair
public import Theory.Frattini.PGroup
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent
public import Theory.GroupTheory.NonsolvableTwoLocal
public import Theory.Quasithin.LocalRank

/-!
# Fusion of elementary-quotient Xi subgroups

Two mutually normalizing conjugates of an Xi subgroup with elementary odd
quotient coincide when their join has odd-prime rank at most two and the
same actor normalizes both. Irreducibility puts the intersection either
over the whole odd quotient or inside the two-core. Two-perfectness gives
containment in the first case; rank additivity excludes the second.

The point-centralizer application obtains mutual normalization from the
literal conjugation and a subgroup centralized by X. It uses only the
original actor's irreducibility, not a separate assertion for its conjugate.
This proves the elementary-quotient branch of the Xi fusion step in
Aschbacher--Smith 9.4.1, printed pp.735--736. The extraspecial alternative
requires a separate argument for the common Frattini line.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1
variable {G : Type*} [Group G] [Finite G]

/-- Equal-order, mutually normalizing Xi actors coincide in the elementary
odd-quotient case. Only X needs the full Xi conditions. -/
theorem XiMember.eq_of_elementary_quotient_of_card_eq
    {p : ℕ} [Fact p.Prime] (ho : Odd p) {T X Y : Subgroup G}
    (hX : XiMember T X) (hY : T ≤ normalizer (Y : Set G))
    (hXY : X ≤ normalizer (Y : Set G)) (hYX : Y ≤ normalizer (X : Set G))
    (he : IsElementaryAbelian p (XiQuotient X))
    (hc : Nat.card (XiQuotient X) = p ^ 2)
    (hcard : Nat.card X = Nat.card Y)
    (hrY : 2 ≤ primeRank p Y)
    (hr : primeRank p (X ⊔ Y : Subgroup G) ≤ 2) : X = Y := by
  let _ := he
  let _ : Fact (IsPGroup p (XiQuotient X)) := ⟨IsElementaryAbelian.isPGroup p _⟩
  let I := (X ⊓ Y : Subgroup G).subgroupOf X
  let q := QuotientGroup.mk' (pCore 2 X)
  let r := QuotientGroup.mk' (frattini (XiQuotient X))
  let A := (I.map q).map r
  have hA : ∀ t : T, ∀ a ∈ A, xiFrattiniAction T X hX.invariant t a ∈ A := by
    rintro t a ⟨b, ⟨x, hx, rfl⟩, rfl⟩
    let z : X := ⟨(t : G) * x * (t : G)⁻¹,
      (mem_normalizer_iff.mp (hX.invariant t.property) x).mp x.property⟩
    have hz : z ∈ I := ⟨z.property,
      (mem_normalizer_iff.mp (hY t.property) x).mp hx.2⟩
    refine ⟨q z, ⟨z, hz, rfl⟩, ?_⟩
    simp only [r, q, xiFrattiniAction, MonoidHom.comp_apply, quotientAut_apply_mk]
    rfl
  have hphi : frattini (XiQuotient X) = ⊥ :=
    frattini_eq_bot_of_isElementaryAbelian (R := XiQuotient X) (p := p)
  have hrX : 2 ≤ primeRank p X := by
    let _ : IsElementaryAbelian p (⊤ : Subgroup (XiQuotient X)) :=
      { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x =>
          Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p p (XiQuotient X)) x) }
    have hh : 2 ≤ primeRank p (XiQuotient X) :=
      IsElementaryAbelian.primeRank_ge_of_card (⊤ : Subgroup (XiQuotient X))
        (by simpa only [card_top] using hc)
    exact hh.trans (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup)
  rcases hX.irreducible A hA with hb | ht
  · have hi : I ≤ pCore 2 X := by
      intro x hx
      have hxA : r (q x) ∈ A := mem_map_of_mem r (mem_map_of_mem q hx)
      have hxbot : r (q x) ∈ (⊥ : Subgroup (XiFrattiniQuotient X)) := hb ▸ hxA
      have hq : q x ∈ frattini (XiQuotient X) :=
        (QuotientGroup.eq_one_iff _).mp (mem_bot.mp hxbot)
      rw [hphi] at hq
      exact (QuotientGroup.eq_one_iff _).mp hq
    have hI : IsPGroup 2 (X ⊓ Y : Subgroup G) := by
      have hh : IsPGroup 2 I := pCore_isPGroup.to_le hi
      exact hh.of_equiv (subgroupOfEquivOfLe (show X ⊓ Y ≤ X from inf_le_left))
    have hsum := primeRank_add_le_of_normalizes_of_twoGroup_intersection ho X Y hXY hYX hI
    omega
  · have himage : I.map q = ⊤ := by
      apply frattini_nongenerating
      have hh := congrArg (Subgroup.comap r) ht
      simpa only [A, comap_map_eq, r, QuotientGroup.ker_mk', comap_top] using hh
    have hsup : I ⊔ pCore 2 X = ⊤ := by
      have hh := congrArg (Subgroup.comap q) himage
      simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hh
    have hI : I.Normal := by
      apply normal_subgroupOf_of_le_normalizer
      exact (le_inf X.le_normalizer hXY).trans inf_normalizer_le_normalizer_inf
    let _ := hI
    have hquot : IsPGroup 2 (X ⧸ I) :=
      isPGroup_quotient_of_sup_eq_top _ _ pCore_isPGroup hsup
    have htop : I = ⊤ := hX.perfect _ hI hquot
    have hle : X ≤ Y := by
      have hh := subgroupOf_eq_top.mp htop
      exact hh.trans inf_le_right
    exact eq_of_le_of_card_ge hle hcard.ge

theorem XiMember.eq_conjugate_of_elementary_quotient
    {p : ℕ} [Fact p.Prime] (ho : Odd p) {T X : Subgroup G}
    (hX : XiMember T X) (g : G)
    (hn : T ≤ normalizer (X.map (MulAut.conj g).toMonoidHom : Set G))
    (hXY : X ≤ normalizer (X.map (MulAut.conj g).toMonoidHom : Set G))
    (hYX : X.map (MulAut.conj g).toMonoidHom ≤ normalizer (X : Set G))
    (he : IsElementaryAbelian p (XiQuotient X))
    (hc : Nat.card (XiQuotient X) = p ^ 2)
    (hr : primeRank p (X ⊔ X.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2) :
    X = X.map (MulAut.conj g).toMonoidHom := by
  let f := X.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hrX : 2 ≤ primeRank p X := by
    let _ := he
    let _ : IsElementaryAbelian p (⊤ : Subgroup (XiQuotient X)) :=
      { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x =>
          Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p p (XiQuotient X)) x) }
    have hh : 2 ≤ primeRank p (XiQuotient X) :=
      IsElementaryAbelian.primeRank_ge_of_card (⊤ : Subgroup (XiQuotient X))
        (by simpa only [card_top] using hc)
    exact hh.trans (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup)
  exact hX.eq_of_elementary_quotient_of_card_eq ho hn hXY hYX he hc
    (Nat.card_congr f.toEquiv) ((primeRank_congr p f) ▸ hrX) hr

omit [Finite G] in
/-- A conjugate point centralizer normalizes the literal conjugate subgroup. -/
theorem pointCentralizer_normalizes_conjugate {v w g : G} {X : Subgroup G}
    (hX : centralizer ({v} : Set G) ≤ normalizer (X : Set G))
    (hconj : MulAut.conj g v = w) :
    centralizer ({w} : Set G) ≤
      normalizer (X.map (MulAut.conj g).toMonoidHom : Set G) := by
  have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hX
  simpa only [map_centralizer_equiv, Set.image_singleton, hconj,
    map_equiv_normalizer_eq] using hh

/-- The literal point-fusion configuration identifies the two Xi conjugates
when X/O₂(X) is elementary. The local rank bound is supplied by quasithinness. -/
theorem XiMember.eq_conjugate_at_point_of_elementary_quotient
    (hqt : IsQuasithin G) {p : ℕ} [Fact p.Prime] (ho : Odd p)
    {T X U : Subgroup G} {v w g : G} (hX : XiMember T X)
    (he : IsElementaryAbelian p (XiQuotient X))
    (hc : Nat.card (XiQuotient X) = p ^ 2)
    (hv : orderOf v = 2) (hvU : v ∈ U)
    (hXU : X ≤ centralizer (U : Set G))
    (hNv : centralizer ({v} : Set G) ≤ normalizer (X : Set G))
    (hg : g ∈ normalizer (U : Set G))
    (hconj : MulAut.conj g v = w)
    (hTw : T ≤ centralizer ({w} : Set G)) :
    X = X.map (MulAut.conj g).toMonoidHom ∧
      centralizer ({w} : Set G) ≤ normalizer (X : Set G) := by
  have hUw : w ∈ U := hconj ▸ (mem_normalizer_iff.mp hg v).mp hvU
  have hNw := pointCentralizer_normalizes_conjugate hNv hconj
  have hCU : centralizer (U : Set G) ≤ centralizer ({v} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.mpr hvU)
  have hXw : X ≤ centralizer ({w} : Set G) :=
    hXU.trans (centralizer_le (Set.singleton_subset_iff.mpr hUw))
  have hYU : X.map (MulAut.conj g).toMonoidHom ≤ centralizer (U : Set G) := by
    have hU : U.map (MulAut.conj g).toMonoidHom = U :=
      mem_normalizer_iff_map_conj_eq.mp hg
    have hh := (map_mono (f := (MulAut.conj g).toMonoidHom) hXU).trans
      (map_centralizer_le_centralizer_image (U : Set G) (MulAut.conj g).toMonoidHom)
    change X.map (MulAut.conj g).toMonoidHom ≤
      centralizer (U.map (MulAut.conj g).toMonoidHom : Set G) at hh
    rwa [hU] at hh
  have hr : primeRank p (X ⊔ X.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 := by
    exact (primeRank_mono p (sup_le (hXU.trans hCU) (hYU.trans hCU))).trans
      ((Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hqt) _
        (Theory.GroupTheory.isTwoLocal_involution_centralizer hv) p Fact.out ho)
  have heq := hX.eq_conjugate_of_elementary_quotient ho g (hTw.trans hNw)
    (hXw.trans hNw) (hYU.trans (hCU.trans hNv)) he hc hr
  exact ⟨heq, heq ▸ hNw⟩

end CFSG.Quasithin.Chapter1
