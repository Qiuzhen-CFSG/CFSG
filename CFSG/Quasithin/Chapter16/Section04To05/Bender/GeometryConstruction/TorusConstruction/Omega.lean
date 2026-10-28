module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.Component
public import CFSG.Quasithin.Chapter16.Section01To02.Local

/-!
# Placing the external omega subgroup in the Bender space

An involution in T ∩ C_G(L)L has an involutory component representative:
its square is central, and the source cover input lifts involutions. Its
component representative normalizes T_L and hence lies in T_L by Sylow
maximality. Both factors are therefore involutions in the specified Sylows.

Faithfulness on L makes Ω₁(R) elementary once Ω₁(T_L) is elementary:
the square of each element of C_G(L)Ω₁(T_L) lies in C_G(L), and R meets
that centralizer trivially. Conjugacy R = T_C^g then makes Ω₁(T_C)
elementary too. This avoids assuming that conclusion in the Δ₀ input.

Source: Aschbacher–Smith, Proposition 16.5.1, first paragraph, printed
p.1194, using 16.4.10–11 and the cover clauses 16.1.2 and I.2.2(4).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction
open Subgroup
variable {G : Type*} [Group G]

/-- Multiplication supplies representatives in a join of commuting subgroups. -/
theorem exists_mul_of_commuting {A B : Subgroup G}
    (hc : A ≤ centralizer (B : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have hcomm (a : A) (b : B) : Commute (a : G) (b : G) :=
    (hc a.property b b.property).symm
  have hr := MonoidHom.noncommCoprod_range A.subtype B.subtype hcomm
  rw [A.range_subtype, B.range_subtype] at hr
  obtain ⟨⟨a, b⟩, hab⟩ := hr.symm ▸ hx
  exact ⟨a, a.property, b, b.property, hab⟩

private theorem elementary_of_squares {H : Type*} [Group H]
    (h : ∀ x : H, x ^ 2 = 1) : IsElementaryAbelian 2 H :=
  { is_comm := ⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (h x)) a b).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr h }

/-- The center-free alternative satisfies the same raw lifting input. -/
theorem involutionLifting_of_center_eq_bot {L : Subgroup G} (hZ : center L = ⊥) :
    InvolutionLifting L := by
  refine ⟨?_, ?_⟩
  · apply elementary_of_squares
    intro x
    have hx : (x : L) = 1 := mem_bot.mp (hZ ▸ x.property)
    exact Subtype.ext (by simp [hx])
  · intro x hx
    refine ⟨x, ?_, rfl⟩
    apply mem_bot.mp
    rw [← hZ]
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (center L) (x ^ 2) = 1
    simpa only [map_pow] using hx

/-- Every lift is involutory when the central kernel is elementary and
involutions have involutory lifts. -/
theorem InvolutionLifting.square_eq_one {L : Subgroup G} (h : InvolutionLifting L)
    (x : L) (hx : x ^ 2 ∈ center L) : x ^ 2 = 1 := by
  let := h.1
  obtain ⟨y, hy, hq⟩ := h.2 x (by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hx)
  have hc : x / y ∈ center L := QuotientGroup.eq_iff_div_mem.mp hq.symm
  have hc2 : (x / y) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hc
  have hcomm : Commute (x / y) y := (mem_center_iff.mp hc y).symm
  simpa only [div_mul_cancel, hc2, hy, mul_one] using hcomm.mul_pow 2

variable [Finite G]

/-- An inner involution in T has both factors in the first omega subgroups
of the specified commuting and component Sylows. -/
theorem involution_mem_space {T : Sylow 2 G} {z : G} {L : Subgroup G}
    (h : StandardSetup T z L) (hlift : InvolutionLifting L)
    {a : G} (haT : a ∈ T) (ha2 : a ^ 2 = 1)
    (haKL : a ∈ centralizer (L : Set G) ⊔ L) : a ∈ benderSpace T L := by
  obtain ⟨c, hc, l, hl, rfl⟩ := exists_mul_of_commuting le_rfl haKL
  have hcl : Commute c l := (hc l hl).symm
  have hprod : c ^ 2 * l ^ 2 = 1 := (hcl.mul_pow 2).symm.trans ha2
  have hl2K : l ^ 2 ∈ centralizer (L : Set G) := by
    rw [eq_inv_of_mul_eq_one_right hprod]
    exact (centralizer (L : Set G)).inv_mem ((centralizer (L : Set G)).pow_mem hc 2)
  let lL : L := ⟨l, hl⟩
  have hl2 : l ^ 2 = 1 := congrArg L.subtype
    (hlift.square_eq_one lL (mem_center_iff.mpr fun x =>
      Subtype.ext (hl2K x x.property)))
  have hc2 : c ^ 2 = 1 := by simpa only [hl2, mul_one] using hprod
  obtain ⟨P, hP⟩ := h.toCentralComponentSetup.exists_component_sylow
  have hln : lL ∈ normalizer (P : Set L) := by
    rw [← P.coe_coe, hP]
    apply mem_normalizer_iff.mpr
    intro x
    have he : (c * l) * (x : G) * (c * l)⁻¹ = l * (x : G) * l⁻¹ := by
      calc
        _ = c * (l * (x : G) * l⁻¹) * c⁻¹ := by group
        _ = _ := by
          rw [← hc _ (L.mul_mem (L.mul_mem hl x.property) (L.inv_mem hl))]
          group
    change (x : G) ∈ T ↔ l * (x : G) * l⁻¹ ∈ T
    rw [← he]
    exact (T : Subgroup G).le_normalizer haT x
  let : IsElementaryAbelian 2 (zpowers lL) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (Subtype.ext hl2)
  have hlP : lL ∈ P := by
    have hi := (IsElementaryAbelian.isPGroup 2 (zpowers lL)).inf_normalizer_sylow P
    have hm : lL ∈ zpowers lL ⊓ normalizer (P : Set L) := ⟨mem_zpowers lL, hln⟩
    rw [hi] at hm
    exact hm.2
  have hlT : l ∈ T := by
    change lL ∈ (P : Subgroup L) at hlP
    rw [hP] at hlP
    exact hlP
  have hcT : c ∈ T := by
    change c ∈ (T : Subgroup G)
    simpa only [mul_inv_cancel_right] using T.mul_mem haT (T.inv_mem hlT)
  exact (benderSpace T L).mul_mem
    ((le_sup_left : omegaOneAmbient (commutingSylow T L) ≤ benderSpace T L)
      ((omegaOneAmbient_le_iff _ _).mp le_rfl c ⟨hcT, hc⟩ hc2))
    ((le_sup_right : omegaOneAmbient (componentSylow T L) ≤ benderSpace T L)
      ((omegaOneAmbient_le_iff _ _).mp le_rfl l ⟨hlT, hl⟩ hl2))

/-- The genuine Δ₀ containment suffices; containment in V is a conclusion. -/
theorem omega_le_space {T : Sylow 2 G} {z g : G} {L R : Subgroup G}
    (h : IntersectionSetup T z L g R) (hlift : InvolutionLifting L)
    (hdelta : omegaOneAmbient R ≤ centralizer (L : Set G) ⊔ L) :
    omegaOneAmbient R ≤ benderSpace T L := by
  apply (omegaOneAmbient_le_iff _ _).mpr
  intro a ha ha2
  exact involution_mem_space h.toStandardSetup hlift (h.le_sylow ha) ha2
    (hdelta ((omegaOneAmbient_le_iff _ _).mp le_rfl a ha ha2))

/-- Faithfulness makes the external omega subgroup elementary, without
assuming elementary abelianness of the commuting factor. -/
theorem omega_elementary {T : Sylow 2 G} {z g : G} {L R : Subgroup G}
    (h : IntersectionSetup T z L g R) (hlift : InvolutionLifting L)
    (hdelta : omegaOneAmbient R ≤ centralizer (L : Set G) ⊔ L)
    (hfaith : Disjoint R (centralizer (L : Set G)))
    [IsElementaryAbelian 2 (omegaOneAmbient (componentSylow T L))] :
    IsElementaryAbelian 2 (omegaOneAmbient R) := by
  have hU := omega_le_space h hlift hdelta
  apply elementary_of_squares
  intro a
  apply Subtype.ext
  have haKL : (a : G) ∈ centralizer (L : Set G) ⊔
      omegaOneAmbient (componentSylow T L) :=
    (sup_le_sup_right
      (show omegaOneAmbient (commutingSylow T L) ≤ centralizer (L : Set G) from
        (omegaOneAmbient_le _).trans inf_le_right) _) (hU a.property)
  obtain ⟨c, hc, l, hl, he⟩ := exists_mul_of_commuting
    (centralizer_le ((omegaOneAmbient_le _).trans inf_le_right)) haKL
  have hl2 : l ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian
    (A := omegaOneAmbient (componentSylow T L)) _ hl
  have hcl : Commute c l :=
    (hc l (((omegaOneAmbient_le _).trans inf_le_right) hl)).symm
  have ha2K : (a : G) ^ 2 ∈ centralizer (L : Set G) := by
    rw [← he, hcl.mul_pow, hl2, mul_one]
    exact (centralizer (L : Set G)).pow_mem hc 2
  exact disjoint_def.mp hfaith
    (R.pow_mem (omegaOneAmbient_le R a.property) 2) ha2K

/-- The source conjugacy transfers elementary abelianness to U_C. -/
theorem commuting_omega_elementary {T : Sylow 2 G} {z g : G} {L R : Subgroup G}
    (h : IntersectionSetup T z L g R)
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (htransport : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g)
    (hlift : InvolutionLifting L)
    (hdelta : omegaOneAmbient R ≤ centralizer (L : Set G) ⊔ L)
    (hfaith : Disjoint R (centralizer (L : Set G)))
    [IsElementaryAbelian 2 (omegaOneAmbient (componentSylow T L))] :
    IsElementaryAbelian 2 (omegaOneAmbient (commutingSylow T L)) := by
  let := omega_elementary h hlift hdelta hfaith
  have he := omega_conjugate (h.eq_conjugate_commutingSylow hR htransport)
  have hback : (omegaOneAmbient R).conjBy g⁻¹ =
      omegaOneAmbient (commutingSylow T L) := by
    rw [he, conjBy_conjBy, inv_mul_cancel, conjBy_one]
  rw [← hback]
  exact IsElementaryAbelian.map (MulAut.conj g⁻¹).toMonoidHom

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction
