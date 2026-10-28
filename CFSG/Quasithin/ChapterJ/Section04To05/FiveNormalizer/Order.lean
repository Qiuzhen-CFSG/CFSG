module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveNormalizer.Recognition
public import CFSG.Quasithin.ChapterJ.Section04To05.SecondParabolic.Middle
public import Theory.GroupTheory.SylowPrimeIndexSelfNormalizer

/-!
# The exact order and core of the first source parabolic

The two-group A meets B₅Q₅ in A∩Q₅ because its quotient image cannot meet
the odd five-subgroup. The unchanged T_F=AQ₅ has order4096, so this
intersection has order256. The actual product (B₅Q₅)A therefore has
order20480. Its Suzuki projection then has kernel of order1024, forcing
F₁∩Q=Q₀Q₅. The actual common subgroup T_F is Sylow and self-normalizing.

Source: Aschbacher–Smith, J.4.5(3) and its preceding local setup, pp.441–442.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} (p:Plane d)
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem A_inf_fiveProduct (B5:Sylow 5 d.toTypeRuSetup.H) :
    p.A B5⊓(B5Image B5⊔Q₅ d B5)=p.A B5⊓Q₅ d B5 := by
  have hB : ((B5Image B5).subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap=
      B5.map d.ru2.quotientMap := by
    change (((B5:Subgroup d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype).comap
      d.toTypeRuSetup.H.subtype).map d.ru2.quotientMap=_
    rw [comap_map_eq_self_of_injective d.toTypeRuSetup.H.subtype_injective]
  have h5 : ((Q₅ d B5).subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap=⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [d.ru2.quotient_kernel]
    exact fun _ hx=>Q₅_le_Q d B5 hx
  have hJ : ((B5Image B5⊔Q₅ d B5).subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap=
      B5.map d.ru2.quotientMap := by
    rw [subgroupOf_sup (map_subtype_le _) ((Q₅_le_Q d B5).trans (pCoreIn_le 2 _)),
      Subgroup.map_sup,hB,h5,sup_bot_eq]
  have hA : IsPGroup 2 (p.A B5) := d.T.isPGroup'.to_le ((p.A_le_R₂ B5).trans p.R₂_le_T)
  have hd := (hA.comap_subtype.map d.ru2.quotientMap).disjoint_of_coprime
    (B5.isPGroup'.map d.ru2.quotientMap) (by decide:Nat.Coprime 2 5)
  apply le_antisymm _ (inf_le_inf_left _ le_sup_right)
  intro x hx
  let xH:d.toTypeRuSetup.H:=⟨x,p.A_le_H B5 hx.1⟩
  have hxQ : x∈d.toTypeRuSetup.Q := by
    have hz : d.ru2.quotientMap xH=1 := disjoint_def.mp hd
      (mem_map.mpr ⟨xH,hx.1,rfl⟩) (hJ ▸ mem_map.mpr ⟨xH,hx.2,rfl⟩)
    have hk : xH∈d.ru2.quotientMap.ker := hz
    rwa [d.ru2.quotient_kernel] at hk
  exact ⟨hx.1,(fiveProduct_inf_Q d B5).le ⟨hx.2,hxQ⟩⟩

private theorem A_inf_Q₅_card (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    Nat.card (p.A B5⊓Q₅ d B5:Subgroup G)=256 := by
  have h:=card_mul_eq_card_inf_mul_card_sup_of_normalizes (Q₅ d B5) (p.A B5)
    (s.A_normalizes_Q₅ p B5 hi)
  rw [card_Q₅,s.card_A p B5 hi,inf_comm,sup_comm] at h
  change 512*2048=Nat.card (p.A B5⊓Q₅ d B5:Subgroup G)*Nat.card (p.T_F B5) at h
  rw [s.card_T_F p B5 hi] at h
  omega

theorem SourceChoice.card_F₁ (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) : Nat.card (p.F₁ B5)=20480 := by
  have hd : Disjoint (Q₅ d B5) (B5Image B5) := disjoint_of_coprime_natCard (by
    rw [card_Q₅,B5Image_card d.card_Z B5]
    decide)
  have hcJ : Nat.card (B5Image B5⊔Q₅ d B5:Subgroup G)=2560 := by
    rw [sup_comm,card_sup_eq_mul_of_normalizes_of_disjoint _ _
      (normalizer_commutator_ge_right _ _) hd,card_Q₅,B5Image_card d.card_Z B5]
  have h:=card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (B5Image B5⊔Q₅ d B5) (p.A B5) (s.A_normalizes_fiveProduct p B5 hi)
  rw [hcJ,s.card_A p B5 hi,inf_comm,A_inf_fiveProduct p B5,A_inf_Q₅_card p s B5 hi] at h
  have he : (B5Image B5⊔Q₅ d B5)⊔p.A B5=p.F₁ B5 := by
    change (B5Image B5⊔Q₅ d B5)⊔p.A B5=(p.A B5⊔Q₅ d B5)⊔B5Image B5
    ac_rfl
  rw [he] at h
  omega

theorem SourceChoice.F₁_inf_Q (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    p.F₁ B5⊓d.toTypeRuSetup.Q=fiveHyperplane d B5 := by
  obtain ⟨f,hf,hk⟩:=s.F₁_projection p B5 hi
  have hr : Nat.card f.range=20 := by
    rw [f.range_eq_top_of_surjective hf,card_top,BenderSuzuki.MatrixGroups.suzukiZero_card]
  have hc:=f.ker.card_mul_index
  rw [index_ker,hr,s.card_F₁ p B5 hi,hk] at hc
  have hiq : d.toTypeRuSetup.Q.subgroupOf (p.F₁ B5)=
      (p.F₁ B5⊓d.toTypeRuSetup.Q).subgroupOf (p.F₁ B5) := by
    ext x
    exact ⟨fun h=>⟨x.property,h⟩,fun h=>h.2⟩
  rw [hiq,Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv] at hc
  apply (eq_of_le_of_card_ge (le_inf (p.fiveHyperplane_le_F₁ B5)
    (fiveHyperplane_le_Q d B5)) ?_).symm
  rw [fiveHyperplane_card]
  omega

theorem SourceChoice.F₁_core_eq_fiveHyperplane (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    (p.F₁ B5).pCoreIn 2=fiveHyperplane d B5 :=
  (s.F₁_twoCore p B5 hi).trans (s.F₁_inf_Q p B5 hi)

theorem Plane.T_F_le_F₁ (B5:Sylow 5 d.toTypeRuSetup.H) : p.T_F B5≤p.F₁ B5 := le_sup_left

theorem SourceChoice.T_F_sylow_F₁ (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    ∃ T:Sylow 2 (p.F₁ B5), (T:Subgroup (p.F₁ B5))=(p.T_F B5).subgroupOf (p.F₁ B5) := by
  let T:=Sylow.ofCard (p:=2) ((p.T_F B5).subgroupOf (p.F₁ B5)) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe (p.T_F_le_F₁ B5)).toEquiv,
      s.card_T_F p B5 hi,s.card_F₁ p B5 hi,
      show 20480=2^12*5 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization,Nat.prime_five.factorization])
  exact ⟨T,rfl⟩

theorem SourceChoice.T_F_selfNormalizing_F₁ (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    normalizer ((p.T_F B5).subgroupOf (p.F₁ B5):Set (p.F₁ B5))=
      (p.T_F B5).subgroupOf (p.F₁ B5) := by
  obtain ⟨T,hT⟩:=s.T_F_sylow_F₁ p B5 hi
  have hc : Nat.card (T:Subgroup (p.F₁ B5))=4096 := by
    rw [hT,Nat.card_congr (subgroupOfEquivOfLe (p.T_F_le_F₁ B5)).toEquiv,s.card_T_F p B5 hi]
  have hindex : (T:Subgroup (p.F₁ B5)).index=5 := by
    have h:=(T:Subgroup (p.F₁ B5)).card_mul_index
    rw [hc,s.card_F₁ p B5 hi] at h
    omega
  have hcore : Nat.card (pCore 2 (p.F₁ B5))=1024 := by
    have h:=congrArg (fun M:Subgroup G=>Nat.card M) (s.F₁_core_eq_fiveHyperplane p B5 hi)
    rw [pCoreIn,card_map_of_injective (p.F₁ B5).subtype_injective,fiveHyperplane_card] at h
    exact h
  have hnot : ¬(T:Subgroup (p.F₁ B5))≤pCore 2 (p.F₁ B5) := by
    intro h
    have hb:=card_le_of_le h
    rw [hc,hcore] at hb
    omega
  have h:=T.normalizer_eq_of_prime_index_not_le_core (by rw [hindex];decide) hnot
  change normalizer ((T:Subgroup (p.F₁ B5)):Set (p.F₁ B5))=(T:Subgroup (p.F₁ B5)) at h
  rwa [hT] at h

end CFSG.Quasithin.ChapterJ.RuSubgroup
