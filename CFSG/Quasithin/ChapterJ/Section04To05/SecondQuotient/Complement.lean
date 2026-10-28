module

public import CFSG.Quasithin.ChapterJ.Section04To05.SecondQuotient.Action
public import CFSG.Quasithin.ChapterJ.Section04To05.CubicLift.Quotient
public import Theory.Representation.BinaryNormalOrbitSpan

/-!
# The normal four-group complement in the actual second quotient

The original Sylow image has index three and fixes the intersection line.
The fixed-free cubic action makes the normal closure of that line a binary
plane. Its image modulo S is the full radical, so it complements S/S₂.
The full preimage A is normal in the original second parabolic and has
order2048. No complement or cardinality premise is assumed.

Source: Aschbacher–Smith, J.4.4(2), printed p.441.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} (p:Plane d)

theorem Plane.secondQuotient_card : Nat.card p.SecondQuotient=96 := by
  have h:=card_eq_card_quotient_mul_card_subgroup (p.S₂.subgroupOf p.parabolic)
  rw [p.card_parabolic,Nat.card_congr (subgroupOfEquivOfLe
    (p.S₂_le_S.trans p.S_le_parabolic)).toEquiv,p.card_S₂] at h
  change 49152=Nat.card p.SecondQuotient*512 at h
  omega

theorem Plane.secondBar_T_index : (p.secondBar (d.T:Subgroup G)).index=3 := by
  have h:=(p.secondBar (d.T:Subgroup G)).card_mul_index
  rw [p.secondBar_T_card,p.secondQuotient_card] at h
  omega

/-- The actual parabolic span of the intersection line. -/
def Plane.Abar (B5:Sylow 5 d.toTypeRuSetup.H) : Subgroup p.SecondQuotient :=
  normalClosure (p.secondBar (Q₅ d B5)⊓p.secondBar p.R₂ : Set p.SecondQuotient)

instance Plane.AbarNormal (B5:Sylow 5 d.toTypeRuSetup.H) : (p.Abar B5).Normal :=
  inferInstanceAs (normalClosure _).Normal

theorem Plane.Abar_le_R₂bar (B5:Sylow 5 d.toTypeRuSetup.H) : p.Abar B5≤p.secondBar p.R₂ :=
  normalClosure_le_normal inf_le_right

theorem Plane.line_le_Abar (B5:Sylow 5 d.toTypeRuSetup.H) :
    p.secondBar (Q₅ d B5)⊓p.secondBar p.R₂≤p.Abar B5 := subset_normalClosure

private theorem Abar_eq_singleton (B5:Sylow 5 d.toTypeRuSetup.H) (a:p.SecondQuotient)
    (ha:zpowers a=p.secondBar (Q₅ d B5)⊓p.secondBar p.R₂) :
    p.Abar B5=normalClosure ({a}:Set p.SecondQuotient) := by
  apply le_antisymm
  · apply normalClosure_le_normal
    change p.secondBar (Q₅ d B5)⊓p.secondBar p.R₂≤normalClosure ({a}:Set p.SecondQuotient)
    rw [← ha]
    exact zpowers_le.mpr (subset_normalClosure (Set.mem_singleton a))
  · apply normalClosure_le_normal
    intro x hx
    exact (show x=a from hx).symm ▸ (p.line_le_Abar B5 (ha ▸ mem_zpowers a))

theorem SourceChoice.Abar_card (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) : Nat.card (p.Abar B5)=4 := by
  obtain ⟨a,ha,ho,hn⟩:=s.exists_second_line p B5 hi
  have hm:=ha ▸ mem_zpowers a
  let x:p.secondBar p.R₂:=⟨a,hm.2⟩
  have hx:Additive.ofMul x≠0:=by
    intro h
    have he:a=1:=congrArg (fun v:Additive (p.secondBar p.R₂)=>(v.toMul:p.SecondQuotient)) h
    rw [he,orderOf_one] at ho
    omega
  obtain ⟨c,hcube,hfixed⟩:=p.exists_second_cubic_action
  rw [Abar_eq_singleton p B5 a ha,
    card_normalClosure_eq_orbit_span (p.secondBar p.R₂) p.secondAction p.secondAction_apply x]
  apply index_three_orbit_span_card p.secondAction (p.secondBar (d.T:Subgroup G))
    p.secondBar_T_index (Additive.ofMul x) hx _ c hcube hfixed
  intro t ht
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [p.secondAction_apply]
  have he:=p.secondBar_line_central B5 hm t ht
  change t*a*t⁻¹=a
  rw [he,mul_inv_cancel_right]

theorem Plane.Abar_elementary (B5:Sylow 5 d.toTypeRuSetup.H) :
    IsElementaryAbelian 2 (p.Abar B5) := IsElementaryAbelian.of_le (p.Abar_le_R₂bar B5)

theorem SourceChoice.Abar_sup_Sbar (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    p.Abar B5⊔p.secondBar d.toTypeRuSetup.S=p.secondBar p.R₂ := by
  obtain ⟨a,ha,_,hn⟩:=s.exists_second_line p B5 hi
  have hm:=ha ▸ mem_zpowers a
  apply le_antisymm (sup_le (p.Abar_le_R₂bar B5) (p.secondBar_mono p.S_le_R₂))
  intro x hx
  by_cases hxs:x∈p.secondBar d.toTypeRuSetup.S
  · exact (show p.secondBar d.toTypeRuSetup.S≤p.Abar B5⊔p.secondBar d.toTypeRuSetup.S from le_sup_right) hxs
  obtain ⟨g,hg⟩:=p.secondBar_coset_orbit a hm.2 hn x hx hxs
  have hconj:g*a*g⁻¹∈p.Abar B5:=
    Subgroup.Normal.conj_mem inferInstance a (p.line_le_Abar B5 hm) g
  have he:x=(x*(g*a*g⁻¹)⁻¹)*(g*a*g⁻¹):=by group
  rw [he]
  exact (p.Abar B5⊔p.secondBar d.toTypeRuSetup.S).mul_mem ((show p.secondBar d.toTypeRuSetup.S≤p.Abar B5⊔p.secondBar d.toTypeRuSetup.S from le_sup_right) hg)
    ((show p.Abar B5≤p.Abar B5⊔p.secondBar d.toTypeRuSetup.S from le_sup_left) hconj)

theorem SourceChoice.Abar_disjoint_Sbar (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    Disjoint (p.Abar B5) (p.secondBar d.toTypeRuSetup.S) := by
  have h:=card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (p.Abar B5) (p.secondBar d.toTypeRuSetup.S) (le_normalizer_of_normal)
  rw [s.Abar_card p B5 hi,p.secondBar_S_card,s.Abar_sup_Sbar p B5 hi,p.secondBar_R₂_card] at h
  have he:p.Abar B5⊓p.secondBar d.toTypeRuSetup.S=⊥:=card_eq_one.mp (by omega)
  exact disjoint_iff_inf_le.mpr (by rw [he])

/-- The source A is the full preimage of the line span in the original G₂. -/
def Plane.A (B5:Sylow 5 d.toTypeRuSetup.H) : Subgroup G :=
  ((p.Abar B5).comap p.secondMap).map p.parabolic.subtype

theorem Plane.A_le_parabolic (B5:Sylow 5 d.toTypeRuSetup.H) : p.A B5≤p.parabolic := map_subtype_le _

theorem Plane.mem_A (B5:Sylow 5 d.toTypeRuSetup.H) (a:p.parabolic) :
    (a:G)∈p.A B5 ↔ p.secondMap a∈p.Abar B5 :=
  mem_map_iff_mem p.parabolic.subtype_injective

theorem Plane.A_normalized (B5:Sylow 5 d.toTypeRuSetup.H) :
    p.parabolic≤normalizer (p.A B5:Set G) := by
  have h:=((p.Abar B5).comap p.secondMap).le_normalizer_map p.parabolic.subtype
  simpa only [Plane.A,normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using h

theorem Plane.S₂_le_A (B5:Sylow 5 d.toTypeRuSetup.H) : p.S₂≤p.A B5 := by
  intro x hx
  apply (p.mem_A B5 ⟨x,(p.S₂_le_S.trans p.S_le_parabolic) hx⟩).mpr
  rw [(p.secondMap_eq_one _).mpr hx]
  exact (p.Abar B5).one_mem

theorem Plane.secondBar_A (B5:Sylow 5 d.toTypeRuSetup.H) : p.secondBar (p.A B5)=p.Abar B5 := by
  ext y
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact (p.mem_A B5 a).mp ha
  · intro hy
    obtain ⟨a,rfl⟩:=QuotientGroup.mk'_surjective (p.S₂.subgroupOf p.parabolic) y
    exact ⟨a,(p.mem_A B5 a).mpr hy,rfl⟩

theorem Plane.secondBar_mem_iff (B:Subgroup G) (hB:p.S₂≤B) (a:p.parabolic) :
    p.secondMap a∈p.secondBar B ↔ (a:G)∈B := by
  change a∈((B.subgroupOf p.parabolic).map p.secondMap).comap p.secondMap ↔ _
  rw [comap_map_eq_self]
  · rfl
  · intro x hx
    exact hB ((p.secondMap_eq_one x).mp hx)

theorem Plane.A_le_R₂ (B5:Sylow 5 d.toTypeRuSetup.H) : p.A B5≤p.R₂ := by
  intro x hx
  let a:p.parabolic:=⟨x,p.A_le_parabolic B5 hx⟩
  exact (p.secondBar_mem_iff p.R₂ p.S₂_le_R₂ a).mp
    (p.Abar_le_R₂bar B5 ((p.mem_A B5 a).mp hx))

theorem SourceChoice.card_A (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) : Nat.card (p.A B5)=2048 := by
  have h:=p.secondBar_card (p.A B5) (p.A_le_parabolic B5)
  rw [p.secondBar_A,inf_eq_right.mpr (p.S₂_le_A B5),s.Abar_card p B5 hi,p.card_S₂] at h
  exact h.symm

end CFSG.Quasithin.ChapterJ.RuSubgroup
