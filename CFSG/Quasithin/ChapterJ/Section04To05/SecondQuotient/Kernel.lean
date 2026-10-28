module

public import CFSG.Quasithin.ChapterJ.Section04To05.SecondQuotient.Complement

/-!
# The original five-subgroup in the complement quotient

The intersection of Q₅/S₂ with the normal complement is precisely the
original order-two line. Counting the literal kernels gives image order
two under G₂→G₂/A. The join of the two four-groups has order eight, so
Q₅/S₂ has index two there and is normalized by the complement. Lifting
preserves the original subgroup Q₅S₂.

Source: Aschbacher–Smith J.4.4(3–5), printed p.441.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} (p:Plane d)

private theorem Q₅_le_parabolic (B5:Sylow 5 d.toTypeRuSetup.H) : Q₅ d B5≤p.parabolic :=
  (show Q₅ d B5≤(d.T:Subgroup G) from (p.R₂_sup_Q₅ B5) ▸ le_sup_right).trans p.sylow_le_parabolic

theorem Plane.Q₅bar_inf_Abar (B5:Sylow 5 d.toTypeRuSetup.H) :
    p.secondBar (Q₅ d B5)⊓p.Abar B5=p.secondBar (Q₅ d B5)⊓p.secondBar p.R₂ :=
  le_antisymm (inf_le_inf_left _ (p.Abar_le_R₂bar B5)) (le_inf inf_le_left (p.line_le_Abar B5))

theorem Plane.secondBar_inf_of_kernel_le (B C:Subgroup G) (hC:p.S₂≤C) :
    p.secondBar (B⊓C)=p.secondBar B⊓p.secondBar C := by
  change ((B.subgroupOf p.parabolic)⊓(C.subgroupOf p.parabolic)).map p.secondMap=_
  rw [map_inf_of_ker_le]
  · rfl
  · intro x hx
    exact hC ((p.secondMap_eq_one x).mp hx)

instance Plane.AKernelNormal (B5:Sylow 5 d.toTypeRuSetup.H) :
    ((p.A B5).subgroupOf p.parabolic).Normal := normal_subgroupOf_of_le_normalizer (p.A_normalized B5)

/-- The image order needed for the actual Sylow selection modulo A. -/
theorem SourceChoice.Q₅_image_mod_A_card (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    Nat.card (((Q₅ d B5).subgroupOf p.parabolic).map
      (QuotientGroup.mk' ((p.A B5).subgroupOf p.parabolic)))=2 := by
  have hQ:=p.secondBar_card (Q₅ d B5) (Q₅_le_parabolic p B5)
  rw [s.secondBar_Q₅_card p B5 hi,card_Q₅] at hQ
  have hI:=p.secondBar_card (Q₅ d B5⊓p.A B5) (inf_le_left.trans (Q₅_le_parabolic p B5))
  rw [p.secondBar_inf_of_kernel_le _ _ (p.S₂_le_A B5),p.secondBar_A,p.Q₅bar_inf_Abar,
    s.secondBar_line_card p B5 hi,inf_assoc,inf_eq_right.mpr (p.S₂_le_A B5)] at hI
  have hIc:Nat.card (Q₅ d B5⊓p.A B5:Subgroup G)=256:=by omega
  let f:Q₅ d B5→*p.parabolic⧸(p.A B5).subgroupOf p.parabolic:=
    (QuotientGroup.mk' _).comp (inclusion (Q₅_le_parabolic p B5))
  have hk:f.ker=(Q₅ d B5⊓p.A B5).subgroupOf (Q₅ d B5):=by
    ext a
    change QuotientGroup.mk' _ (inclusion (Q₅_le_parabolic p B5) a)=1 ↔ (a:G)∈Q₅ d B5⊓p.A B5
    refine (QuotientGroup.eq_one_iff (inclusion (Q₅_le_parabolic p B5) a)).trans ?_
    exact ⟨fun h=>⟨a.property,h⟩,fun h=>h.2⟩
  have hr:f.range=((Q₅ d B5).subgroupOf p.parabolic).map
      (QuotientGroup.mk' ((p.A B5).subgroupOf p.parabolic)):=by
    rw [MonoidHom.range_comp,inclusion_range]
  have h:=f.ker.card_mul_index
  rw [hk,Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv,hIc,
    ← hk,index_ker,hr,card_Q₅] at h
  omega

/-- The same four-groups form a subgroup of order eight in the second quotient. -/
theorem SourceChoice.Abar_sup_Q₅bar_card (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    Nat.card (p.Abar B5⊔p.secondBar (Q₅ d B5):Subgroup p.SecondQuotient)=8 := by
  have h:=card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (p.Abar B5) (p.secondBar (Q₅ d B5)) le_normalizer_of_normal
  rw [s.Abar_card p B5 hi,s.secondBar_Q₅_card p B5 hi,inf_comm,p.Q₅bar_inf_Abar,
    s.secondBar_line_card p B5 hi] at h
  omega

theorem SourceChoice.Abar_normalizes_Q₅bar (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    p.Abar B5≤normalizer (p.secondBar (Q₅ d B5):Set p.SecondQuotient) := by
  let J:=p.Abar B5⊔p.secondBar (Q₅ d B5)
  have h:=(p.secondBar (Q₅ d B5)).subgroupOf J |>.card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show p.secondBar (Q₅ d B5)≤J from le_sup_right)).toEquiv,
    s.secondBar_Q₅_card p B5 hi,s.Abar_sup_Q₅bar_card p B5 hi] at h
  have hi2:((p.secondBar (Q₅ d B5)).subgroupOf J).index=2:=by omega
  let := normal_of_index_eq_two hi2
  exact (show p.Abar B5≤J from le_sup_left).trans
    (le_normalizer_of_normal_subgroupOf (show p.secondBar (Q₅ d B5)≤J from le_sup_right))

theorem Plane.secondBar_mem_sup_kernel (B:Subgroup G) (hB:B≤p.parabolic) (a:p.parabolic) :
    p.secondMap a∈p.secondBar B ↔ (a:G)∈B⊔p.S₂ := by
  change a∈((B.subgroupOf p.parabolic).map p.secondMap).comap p.secondMap ↔ _
  rw [comap_map_eq]
  have hk:p.secondMap.ker=p.S₂.subgroupOf p.parabolic:=QuotientGroup.ker_mk' _
  rw [hk,← subgroupOf_sup hB (p.S₂_le_S.trans p.S_le_parabolic)]
  rfl

/-- The actual complement normalizes the original five-subgroup times S₂. -/
theorem SourceChoice.A_normalizes_Q₅S₂ (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    p.A B5≤normalizer ((Q₅ d B5⊔p.S₂:Subgroup G):Set G) := by
  apply le_normalizer_iff.mpr
  intro a ha x hx
  let aP:p.parabolic:=⟨a,p.A_le_parabolic B5 ha⟩
  let xP:p.parabolic:=⟨x,(sup_le (Q₅_le_parabolic p B5)
    (p.S₂_le_S.trans p.S_le_parabolic)) hx⟩
  have hn:=s.Abar_normalizes_Q₅bar p B5 hi ((p.mem_A B5 aP).mp ha)
  have hm:=(mem_normalizer_iff.mp hn (p.secondMap xP)).mp
    ((p.secondBar_mem_sup_kernel (Q₅ d B5) (Q₅_le_parabolic p B5) xP).mpr hx)
  apply (p.secondBar_mem_sup_kernel (Q₅ d B5) (Q₅_le_parabolic p B5) (aP*xP*aP⁻¹)).mp
  simpa only [map_mul,map_inv] using hm

/-- The complement preimage supplements the original S in R₂. -/
theorem SourceChoice.A_sup_S (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) : p.A B5⊔d.toTypeRuSetup.S=p.R₂ := by
  apply le_antisymm (sup_le (p.A_le_R₂ B5) p.S_le_R₂)
  intro x hx
  let a:p.parabolic:=⟨x,(p.R₂_le_T.trans p.sylow_le_parabolic) hx⟩
  apply (p.secondBar_mem_iff (p.A B5⊔d.toTypeRuSetup.S)
    ((p.S₂_le_A B5).trans le_sup_left) a).mp
  rw [p.secondBar_sup _ _ (p.A_le_parabolic B5) p.S_le_parabolic,p.secondBar_A,
    s.Abar_sup_Sbar p B5 hi]
  exact ⟨a,hx,rfl⟩

/-- The complement preimage meets the original S in exactly S₂. -/
theorem SourceChoice.A_inf_S (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) : p.A B5⊓d.toTypeRuSetup.S=p.S₂ := by
  apply le_antisymm _ (le_inf (p.S₂_le_A B5) p.S₂_le_S)
  intro x hx
  let a:p.parabolic:=⟨x,p.A_le_parabolic B5 hx.1⟩
  apply (p.secondMap_eq_one a).mp
  exact (disjoint_iff_inf_le.mp (s.Abar_disjoint_Sbar p B5 hi))
    ⟨(p.mem_A B5 a).mp hx.1,⟨a,hx.2,rfl⟩⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup
