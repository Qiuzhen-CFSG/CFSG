module

public import CFSG.Quasithin.ChapterJ.Section04To05.SecondQuotient.Definitions
public import CFSG.Quasithin.ChapterJ.Section04To05.SourceCore

/-!
# The actual four-group and its line in the second quotient

The proved W=S₂ identifies the original Q₅ image with its source four-group
quotient. The orders of R₂/S₂ and T/S₂ and the genuine product T=R₂Q₅
then give an intersection of order two. The first-core order shows that
Q₅/S₂ meets S/S₂ trivially, so this line supplies an outside involution.

Source: Aschbacher–Smith, J.4.4(1), printed p.441.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (p : Plane d)

theorem Plane.secondBar_sup (A B : Subgroup G) (hA : A ≤ p.parabolic)
    (hB : B ≤ p.parabolic) : p.secondBar (A ⊔ B) = p.secondBar A ⊔ p.secondBar B := by
  rw [Plane.secondBar,subgroupOf_sup hA hB,Subgroup.map_sup]
  rfl

theorem Plane.secondBar_normalized (A B : Subgroup G) (h : B ≤ normalizer (A : Set G)) :
    p.secondBar B ≤ normalizer (p.secondBar A : Set p.SecondQuotient) := by
  rintro _ ⟨b,hb,rfl⟩
  apply (A.subgroupOf p.parabolic).le_normalizer_map p.secondMap
  refine mem_map.mpr ⟨b,?_,rfl⟩
  exact le_normalizer_comap p.parabolic.subtype (h hb)

private theorem Q₅_le_parabolic (B5 : Sylow 5 d.toTypeRuSetup.H) :
    Q₅ d B5 ≤ p.parabolic := by
  exact (show Q₅ d B5 ≤ (d.T : Subgroup G) from
    (p.R₂_sup_Q₅ B5) ▸ le_sup_right).trans p.sylow_le_parabolic

theorem Plane.secondBar_Q₅_elementary (B5 : Sylow 5 d.toTypeRuSetup.H) :
    IsElementaryAbelian 2 (p.secondBar (Q₅ d B5)) := by
  have hp (x : p.secondBar (Q₅ d B5)) : x^2=1 := by
    obtain ⟨a,ha,he⟩ := x.property
    apply Subtype.ext
    change (x:p.SecondQuotient)^2=1
    rw [← he,← map_pow]
    apply (p.secondMap_eq_one _).mpr
    apply p.U_le_S₂
    let q : d.toTypeRuSetup.Q := ⟨a,Q₅_le_Q d B5 ha⟩
    change ((q^2 : d.toTypeRuSetup.Q):G) ∈ d.toTypeRuSetup.U
    apply (d.ru2.six.coordinates_eq_one_iff (q^2)).mp
    rw [map_pow]
    change (2:ℕ) • (d.ru2.six.coordinates q).toAdd=0
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2),ZMod.natCast_self,zero_smul]
  refine {toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp}
  intro a b
  exact Commute.of_orderOf_dvd_two (fun x => orderOf_dvd_of_pow_eq_one (hp x)) a b


theorem SourceChoice.secondBar_Q₅_card (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hi : ∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    Nat.card (p.secondBar (Q₅ d B5))=4 := by
  have hI := hat_card d (Q₅ d B5⊓p.W)
    (inf_le_left.trans ((Q₅_le_Q d B5).trans (pCoreIn_le 2 _)))
  rw [s.hat_Q₅_inf_W_card B5 hi,
    inf_eq_right.mpr (le_inf (U_le_Q₅ d B5) p.U_le_W),d.ru2.card_U d.card_Z,
    p.W_eq_S₂] at hI
  have h := p.secondBar_card (Q₅ d B5) (Q₅_le_parabolic p B5)
  rw [card_Q₅,← hI] at h
  omega

theorem Plane.secondBar_T_card : Nat.card (p.secondBar (d.T : Subgroup G))=32 := by
  have h := p.secondBar_card (d.T : Subgroup G) p.sylow_le_parabolic
  rw [inf_eq_right.mpr (p.S₂_le_S.trans d.S_le_T),p.card_S₂,
    d.toTypeRuSetup.card_T_of_card_Z d.card_Z] at h
  omega

theorem SourceChoice.secondBar_line_card (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hi : ∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    Nat.card (p.secondBar (Q₅ d B5) ⊓ p.secondBar p.R₂ : Subgroup p.SecondQuotient)=2 := by
  have hn : p.secondBar (Q₅ d B5) ≤ normalizer (p.secondBar p.R₂ : Set p.SecondQuotient) :=
    p.secondBar_normalized _ _ ((Q₅_le_parabolic p B5).trans p.R₂_normalized)
  have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (p.secondBar p.R₂) (p.secondBar (Q₅ d B5)) hn
  rw [p.secondBar_R₂_card,s.secondBar_Q₅_card p B5 hi,
    ← p.secondBar_sup _ _ (p.R₂_le_T.trans p.sylow_le_parabolic) (Q₅_le_parabolic p B5),
    p.R₂_sup_Q₅ B5,p.secondBar_T_card,inf_comm] at h
  omega


private theorem R₁_le_parabolic (B5 : Sylow 5 d.toTypeRuSetup.H) :
    d.toTypeRuSetup.R₁ ≤ p.parabolic := by
  rw [← Q₅_sup_S d B5]
  exact sup_le (Q₅_le_parabolic p B5) p.S_le_parabolic

private theorem card_R₁ (B5 : Sylow 5 d.toTypeRuSetup.H) :
    Nat.card d.toTypeRuSetup.R₁ = 8192 := by
  have hs : d.toTypeRuSetup.S ≤ d.toTypeRuSetup.R₁ := by
    rw [← Q₅_sup_S d B5]; exact le_sup_right
  have h := (d.toTypeRuSetup.S.subgroupOf d.toTypeRuSetup.R₁).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hs).toEquiv,d.ru1.card_S] at h
  change 2048 * d.toTypeRuSetup.S.relIndex d.toTypeRuSetup.R₁ = _ at h
  rw [Fusion.index_R₁_S] at h
  exact h.symm

private theorem secondBar_R₁_card (B5 : Sylow 5 d.toTypeRuSetup.H) :
    Nat.card (p.secondBar d.toTypeRuSetup.R₁)=16 := by
  have hs : d.toTypeRuSetup.S ≤ d.toTypeRuSetup.R₁ := by
    rw [← Q₅_sup_S d B5]; exact le_sup_right
  have h := p.secondBar_card d.toTypeRuSetup.R₁ (R₁_le_parabolic p B5)
  rw [inf_eq_right.mpr (p.S₂_le_S.trans hs),p.card_S₂,card_R₁ B5] at h
  omega

theorem SourceChoice.secondBar_Q₅_disjoint_S (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hi : ∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    Disjoint (p.secondBar (Q₅ d B5)) (p.secondBar d.toTypeRuSetup.S) := by
  have hn : p.secondBar (Q₅ d B5) ≤
      normalizer (p.secondBar d.toTypeRuSetup.S : Set p.SecondQuotient) :=
    p.secondBar_normalized _ _ (((Q₅_le_parabolic p B5).trans
      (show p.parabolic ≤ d.L from fun x hx => ((p.mem_parabolic x).mp hx).1)).trans
      d.ru1.steinberg.normalized)
  have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (p.secondBar d.toTypeRuSetup.S) (p.secondBar (Q₅ d B5)) hn
  rw [p.secondBar_S_card,s.secondBar_Q₅_card p B5 hi,
    ← p.secondBar_sup _ _ p.S_le_parabolic (Q₅_le_parabolic p B5),
    sup_comm,Q₅_sup_S,secondBar_R₁_card p B5] at h
  have he : p.secondBar d.toTypeRuSetup.S ⊓ p.secondBar (Q₅ d B5)=⊥ :=
    card_eq_one.mp (by omega)
  exact disjoint_iff_inf_le.mpr (by rw [inf_comm,he])

/-- The actual Q₅ line supplies an involution outside the original S image. -/
theorem SourceChoice.exists_second_line (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hi : ∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    ∃ a : p.SecondQuotient,
      zpowers a=p.secondBar (Q₅ d B5)⊓p.secondBar p.R₂ ∧
      orderOf a=2 ∧ a∉p.secondBar d.toTypeRuSetup.S := by
  let I := p.secondBar (Q₅ d B5)⊓p.secondBar p.R₂
  have hc : Nat.card I=2 := s.secondBar_line_card p B5 hi
  let : Nontrivial I := Finite.one_lt_card_iff_nontrivial.mp (by rw [hc]; decide)
  obtain ⟨a,ha⟩ := exists_ne (1:I)
  have hn : (a:p.SecondQuotient)≠1 := fun h => ha (Subtype.ext h)
  let := p.secondBar_Q₅_elementary B5
  have hp : (a:p.SecondQuotient)^2=1 := elemPow_eq_one_of_isElementaryAbelian _ a.property.1
  have ho : orderOf (a:p.SecondQuotient)=2 := orderOf_eq_prime hp hn
  refine ⟨a,eq_of_le_of_card_ge (zpowers_le.mpr a.property)
    (by rw [Nat.card_zpowers,ho,hc]),ho,?_⟩
  intro hs
  have hd := s.secondBar_Q₅_disjoint_S p B5 hi
  exact hn (show (a:p.SecondQuotient)=1 from
    (disjoint_iff_inf_le.mp hd) (show (a:p.SecondQuotient)∈
      p.secondBar (Q₅ d B5)⊓p.secondBar d.toTypeRuSetup.S from ⟨a.property.1,hs⟩))

end CFSG.Quasithin.ChapterJ.RuSubgroup
