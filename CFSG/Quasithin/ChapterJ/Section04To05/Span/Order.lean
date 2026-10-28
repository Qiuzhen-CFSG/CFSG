module

public import CFSG.Quasithin.ChapterJ.Section04To05.Span.Order.Structure
public import Theory.GroupTheory.QuotientIntersection
public import CFSG.Quasithin.ChapterJ.Section04To05.Span.Containment

/-!
# The original J.4 span has order 512

The original S₂ provides an independently proved upper bound of 512 for W.
The explicit sixteen-element subgroup of W/U gives the matching lower bound.
Thus W/U is elementary abelian of order sixteen and W has order 512.
Its intersection with Q₅/U is the actual displacement plane, so the literal
quotient Q₅/(Q₅ ∩ W) is elementary abelian of order four.

The containment W ≤ S₂ uses only the invariant Steinberg section and the
central-preimage identity, so the order argument is independent of the later
identification W = S₂. Source: Aschbacher–Smith J.4.2(2–3), printed p.440.
-/

public section
noncomputable section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} {p : Plane d}

theorem Plane.hat_W_card (p : Plane d) :
    Nat.card (hat d p.W)=16 := by
  have hc := card_le_of_le p.W_le_S₂
  rw [p.card_S₂] at hc
  obtain ⟨s⟩ := p.exists_sourceChoice
  obtain ⟨B5,hi⟩ := s.inverts_sylow_five
  have hl := card_le_of_le s.spanFour_le_hat_W
  rw [s.spanFour_card B5 hi] at hl
  have hh := hat_card d p.W (p.W_le_S.trans d.S_le_H)
  rw [inf_eq_right.mpr p.U_le_W,d.ru2.card_U d.card_Z] at hh
  omega

theorem Plane.card_W (p : Plane d) :
    Nat.card p.W=512 := by
  have hh := hat_card d p.W (p.W_le_S.trans d.S_le_H)
  rw [p.hat_W_card,inf_eq_right.mpr p.U_le_W,d.ru2.card_U d.card_Z] at hh
  exact hh.symm

theorem SourceChoice.spanFour_eq_hat_W (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hi : ∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    : s.spanFour=hat d p.W :=
  eq_of_le_of_card_ge s.spanFour_le_hat_W
    (by rw [s.spanFour_card B5 hi,p.hat_W_card])

theorem hat_inf_of_U_le (A B : Subgroup G) (hB : d.toTypeRuSetup.U≤B) :
    hat d (A⊓B)=hat d A⊓hat d B := by
  change ((A.subgroupOf d.toTypeRuSetup.H⊓B.subgroupOf d.toTypeRuSetup.H).map (hatMap d))=_
  apply map_inf_of_ker_le
  intro x hx
  exact hB ((hatMap_eq_one d x).mp hx)

theorem SourceChoice.hat_Q₅_inf_W (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hi : ∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    : hat d (Q₅ d B5⊓p.W)=hat d s.displacement := by
  rw [hat_inf_of_U_le _ _ p.U_le_W,← s.spanFour_eq_hat_W B5 hi,inf_comm]
  exact s.spanFour_inf_hat_Q₅ B5 hi

theorem SourceChoice.hat_Q₅_inf_W_card (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hi : ∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    : Nat.card (hat d (Q₅ d B5⊓p.W))=4 := by
  rw [s.hat_Q₅_inf_W B5 hi,s.hat_displacement_card B5 hi]

theorem Plane.W_normalized_Q (p : Plane d) :
    d.toTypeRuSetup.Q ≤ normalizer (p.W:Set G) := by
  have hQT : d.toTypeRuSetup.Q ≤ (d.T : Subgroup G) := p.R₂_sup_Q ▸ le_sup_right
  have hn := (le_inf (hQT.trans (p.sylow_le_parabolic.trans p.W₀_normalized))
    ((pCoreIn_le 2 _).trans (Q₀_normalized d))).trans
      (normalizer_inf_normalizer_le_normalizer_sup p.W₀ (Q₀ d))
  intro q hq
  have hprod : p.W=p.W₀⊔Q₀ d := by
    apply SetLike.coe_injective
    rw [p.W_eq_product,coe_mul_of_left_le_normalizer_right]
    exact p.W₀_le_S.trans (d.S_le_H.trans (Q₀_normalized d))
  simpa only [hprod] using hn hq

instance Plane.Q₅_inf_W_normal (p : Plane d) (B5 : Sylow 5 d.toTypeRuSetup.H) :
    ((Q₅ d B5⊓p.W).subgroupOf (Q₅ d B5)).Normal :=
  normal_subgroupOf_of_le_normalizer
    ((le_inf (Q₅ d B5).le_normalizer ((Q₅_le_Q d B5).trans p.W_normalized_Q)).trans
      inf_normalizer_le_normalizer_inf)

abbrev Plane.fiveSpanQuotient (p : Plane d) (B5 : Sylow 5 d.toTypeRuSetup.H) :=
  Q₅ d B5 ⧸ (Q₅ d B5⊓p.W).subgroupOf (Q₅ d B5)

theorem Plane.fiveSpanQuotient_elementary (p : Plane d)
    (B5 : Sylow 5 d.toTypeRuSetup.H) : IsElementaryAbelian 2 (p.fiveSpanQuotient B5) := by
  let I := (Q₅ d B5⊓p.W).subgroupOf (Q₅ d B5)
  let f := QuotientGroup.mk' I
  have hpow (a : Q₅ d B5) : f a^2=1 := by
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    refine ⟨(a^2).property,p.U_le_W ?_⟩
    let q : d.toTypeRuSetup.Q := inclusion (Q₅_le_Q d B5) a
    change ((q^2 : d.toTypeRuSetup.Q):G) ∈ d.toTypeRuSetup.U
    apply (d.ru2.six.coordinates_eq_one_iff (q^2)).mp
    rw [map_pow]
    change (2:ℕ) • (d.ru2.six.coordinates q).toAdd=0
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2),ZMod.natCast_self,zero_smul]
  refine {toIsMulCommutative := ⟨⟨?_⟩⟩,exponent_dvd_p := ?_}
  · intro x y
    apply Commute.of_orderOf_dvd_two
    intro z
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective I z
    exact orderOf_dvd_of_pow_eq_one (hpow a)
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective I x
    exact hpow a

theorem SourceChoice.fiveSpanQuotient_card (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hi : ∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    : Nat.card (p.fiveSpanQuotient B5)=4 := by
  have hI := hat_card d (Q₅ d B5⊓p.W)
    (inf_le_left.trans ((Q₅_le_Q d B5).trans (pCoreIn_le 2 _)))
  rw [s.hat_Q₅_inf_W_card B5 hi,
    inf_eq_right.mpr (le_inf (U_le_Q₅ d B5) p.U_le_W),d.ru2.card_U d.card_Z] at hI
  have hQ := hat_card d (Q₅ d B5) ((Q₅_le_Q d B5).trans (pCoreIn_le 2 _))
  rw [hat_Q₅_card,inf_eq_right.mpr (U_le_Q₅ d B5),d.ru2.card_U d.card_Z] at hQ
  have h := card_eq_card_quotient_mul_card_subgroup
    ((Q₅ d B5⊓p.W).subgroupOf (Q₅ d B5))
  rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv] at h
  change Nat.card (Q₅ d B5)=Nat.card (p.fiveSpanQuotient B5)*Nat.card (Q₅ d B5⊓p.W:Subgroup G) at h
  rw [← hI,← hQ] at h
  norm_num at h
  omega

/-- J.4.2(2–3), with the same selected involution and an actual inverted Sylow five-subgroup. -/
theorem SourceChoice.source_span (s : SourceChoice p) :
    ∃ B5 : Sylow 5 d.toTypeRuSetup.H,
      (∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) ∧
      IsElementaryAbelian 2 (hat d p.W) ∧ Nat.card (hat d p.W)=16 ∧
      Nat.card p.W=512 ∧ Nat.card (hat d (Q₅ d B5⊓p.W))=4 ∧
      IsElementaryAbelian 2 (p.fiveSpanQuotient B5) ∧
      Nat.card (p.fiveSpanQuotient B5)=4 := by
  obtain ⟨B5,hi⟩ := s.inverts_sylow_five
  exact ⟨B5,hi,p.hat_W_elementary,p.hat_W_card,p.card_W,
    s.hat_Q₅_inf_W_card B5 hi,p.fiveSpanQuotient_elementary B5,
    s.fiveSpanQuotient_card B5 hi⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup
