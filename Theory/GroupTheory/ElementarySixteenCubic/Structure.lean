module
public import Theory.GroupTheory.ElementarySixteenCubic.Lift
public import Theory.GroupTheory.ElementarySixteenCubic.CentralizerBound
public import Theory.GroupTheory.ElementarySixteenCubic.Quotient

/-!
# The actual cubic normalizer above an A6 plane quotient

Coprime lifting and the faithful action of the elementary sixteen identify
the fixed-four centralizer and the literal quotient by the original cubic
as S4. No splitting of the plane extension is assumed.
Source: Aschbacher (1994), 45.7(3).
-/

public section
open Subgroup
namespace ElementarySixteenCubic
variable {G:Type*} [Group G] [Finite G]

theorem normalizer_structure
    (f:G→*alternatingGroup (Fin 6)) (hf:Function.Surjective f)
    [IsElementaryAbelian 2 f.ker] (hR:Nat.card f.ker=16)
    (hself:centralizer (f.ker:Set G)≤f.ker)
    (U:Subgroup G) (hU:Nat.card U=3)
    (hS:Nat.card (f.ker⊓centralizer (U:Set G):Subgroup G)=4) :
    Nat.card (normalizer (U:Set G))=72 ∧
    centralizer (((f.ker⊓centralizer (U:Set G)).subgroupOf (normalizer (U:Set G))):
      Set (normalizer (U:Set G)))=
      (f.ker⊓centralizer (U:Set G)).subgroupOf (normalizer (U:Set G)) ⊔
      U.subgroupOf (normalizer (U:Set G)) ∧
    Nonempty (((normalizer (U:Set G))⧸U.subgroupOf (normalizer (U:Set G)))≃*
      Equiv.Perm (Fin 4)) := by
  let N:=normalizer (U:Set G)
  let S:=f.ker⊓centralizer (U:Set G)
  let Sn:=S.subgroupOf N
  let Un:=U.subgroupOf N
  have hSN:S≤N:=inf_le_right.trans (centralizer_le_normalizer _)
  have hRN:=kernel_inf_normalizer f hR U hU
  have hSn:Sn=f.ker.subgroupOf N:=by
    ext x
    exact ⟨fun hx=>hx.1,fun hx=>hRN.le ⟨hx,x.property⟩⟩
  let : Sn.Normal:=hSn ▸ (inferInstance:(f.ker.subgroupOf N).Normal)
  let : IsElementaryAbelian 2 S:=IsElementaryAbelian.of_injective
    (inclusion (show S≤f.ker from inf_le_left)) (inclusion_injective _)
  let : IsElementaryAbelian 2 Sn:=IsElementaryAbelian.subgroupOf hSN
  have hSnC:Nat.card Sn=4:=(Nat.card_congr (subgroupOfEquivOfLe hSN).toEquiv).trans hS
  have hUnC:Nat.card Un=3:=(Nat.card_congr (subgroupOfEquivOfLe U.le_normalizer).toEquiv).trans hU
  obtain ⟨hN,π,hπ,hπval,hπker⟩:=normalizer_lift f hf hR U hU hS
  let D:=U.map f
  have hD:Nat.card D=3:=by
    have hi:=injective_comp_subtype_of_coprime_ker f
      (show Nat.Coprime 3 (Nat.card f.ker) by rw [hR];decide) U
      (IsPGroup.of_card (n:=1) (by simpa using hU))
    rw [show D=(f.comp U.subtype).range by rw [MonoidHom.range_comp,range_subtype],
      ← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv,hU]
  obtain ⟨ψ,hψ,hψker⟩:=AlternatingSix.CubicNormalizer.exists_symmetric_three_surjection D hD
  let κ:=ψ.comp π
  have hκ:Function.Surjective κ:=hψ.comp hπ
  have hκker:κ.ker=Sn⊔Un:=by
    apply le_antisymm
    · intro x hx
      have hpx:π x∈ψ.ker:=hx
      rw [hψker] at hpx
      have hfx:f (x:G)∈D:=hπval x ▸ hpx
      obtain ⟨u,hu,he⟩:=hfx
      let un:N:=⟨u,U.le_normalizer hu⟩
      have hxu:x*un⁻¹∈Sn:=by
        rw [hSn]
        change f ((x:G)*u⁻¹)=1
        rw [map_mul,map_inv,he,mul_inv_cancel]
      have heq:x=(x*un⁻¹)*un:=by simp
      rw [heq]
      exact (Sn⊔Un).mul_mem (mem_sup_left hxu) (mem_sup_right hu)
    · apply sup_le
      · rw [← show π.ker=Sn from hπker]
        intro x hx
        change ψ (π x)=1
        rw [show π x=1 from hx,map_one]
      · intro u hu
        change ψ (π u)=1
        apply MonoidHom.mem_ker.mp
        rw [hψker]
        change (π u:alternatingGroup (Fin 6))∈D
        rw [hπval]
        exact mem_map_of_mem f hu
  have hC:Nat.card (centralizer (Sn:Set N))∣24:=by
    have hc:=fixed_four_centralizer_card_dvd f.ker U hR hU hself hRN hS
    have he:(centralizer (Sn:Set N)).map N.subtype=N⊓centralizer (S:Set G):=by
      ext x
      constructor
      · rintro ⟨a,ha,rfl⟩
        refine ⟨a.property,mem_centralizer_iff.mpr ?_⟩
        intro s hs
        exact congrArg Subtype.val (mem_centralizer_iff.mp ha (⟨s,hSN hs⟩:N) hs)
      · rintro ⟨hxN,hxC⟩
        refine ⟨⟨x,hxN⟩,mem_centralizer_iff.mpr ?_,rfl⟩
        intro s hs
        exact Subtype.ext (mem_centralizer_iff.mp hxC s hs)
    change Nat.card (N⊓centralizer (S:Set G):Subgroup G)∣24 at hc
    rw [←he,card_map_of_injective N.subtype_injective] at hc
    exact hc
  have hres:=symmetric_four_quotient Sn Un hSnC hUnC hN κ hκ hκker hC
  exact ⟨hN,hres⟩
end ElementarySixteenCubic
