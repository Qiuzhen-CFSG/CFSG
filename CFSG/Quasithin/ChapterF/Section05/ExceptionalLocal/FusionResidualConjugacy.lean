module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionResidualJoin
public import Theory.SpecificGroups.SymmetricFourResidualFusion
/-!
# Fusion inside the graph-centralizer residual

Three-cycles conjugate the three nonidentity elements of each endpoint
Klein four. Their cubic order relation places their literal endpoint images
in O²(Dᵢ), and functoriality places the common-subgroup conjugators in
O²(C_G(f)). The injective graph quotient then gives fusion inside
O²(C_G(f)/⟨f⟩), with the same distinguished image of tz.

This strengthens only the conjugator location needed by the F.5.5 use of
I.4.1(2). Source: Aschbacher–Smith, printed pp.301–302.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.SymmetricSix.DuadCalculation
open ResidualJoinModel
local notation "hn" => Nat.le_refl 1
local notation "C2" => Multiplicative (ZMod 2)
local notation "S4" => Equiv.Perm (Fin 4)
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0)) (i : G0 →* G)

/-- Endpoint-core fusion is realized inside the endpoint two-residual. -/
theorem sourceEndpointResidualCore_conjugate_in_residual (hi : Function.Injective i) (b : Bool)
    (x : G) (hx : x∈sourceEndpointResidualCore c i b) (hx1 : x≠1)
    (y : G) (hy : y∈sourceEndpointResidualCore c i b) (hy1 : y≠1) :
    ∃ g∈(pResidual 2 (Dendpoint c i b)).map (Dendpoint c i b).subtype, g*x*g⁻¹=y := by
  rw [sourceEndpointResidualCore_eq_map c i hi b] at hx hy
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨d,hd,rfl⟩ := hy
  have ha1 : a≠1 := by intro h; apply hx1; rw [h,map_one]
  have hd1 : d≠1 := by intro h; apply hy1; rw [h,map_one]
  obtain ⟨g,hg3,hg⟩ := Theory.SpecificGroups.SymmetricFour.core_cubic_conjugate a ha ha1 d hd hd1
  let f : S4 →* Dendpoint c i b :=
    (source_Dendpoint_equiv c i hi b).symm.toMonoidHom.comp (MonoidHom.inr C2 S4)
  have hf3 : (f g)^3=1 := by rw [←map_pow,hg3,map_one]
  have hfR : f g∈pResidual 2 (Dendpoint c i b) :=
    mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hf3))
  refine ⟨sourceEndpointCoreMap c i hi b g,⟨f g,hfR,rfl⟩,?_⟩
  rw [←map_inv,←map_mul,←map_mul,hg]

/-- Every involution of the literal join is fused to tz inside O²(C_G(f)). -/
theorem sourceResidualJoin_involution_conjugate_in_residual (hi : Function.Injective i)
    (x : G) (hx : x∈sourceResidualJoin c i) (hx2 : x^2=1) (hx1 : x≠1) :
    ∃ g∈(pResidual 2 (C c i)).map (C c i).subtype,
      g*x*g⁻¹=sourceHom c i (.r 2) := by
  rw [sourceResidualJoin_eq_range c i hi] at hx
  obtain ⟨a,rfl⟩ := hx
  have ha2 : a^2=1 := sourceHom_injective c i hi (by simpa only [map_pow,map_one] using hx2)
  have hz1 : sourceHom c i (.r 2)≠1 := by
    intro hh
    exact common_center_mem.2.2 (sourceHom_injective c i hi (hh.trans (map_one _).symm))
  have hf (b : Bool) (ha : sourceHom c i a∈sourceEndpointResidualCore c i b)
      (hz : sourceHom c i (.r 2)∈sourceEndpointResidualCore c i b) :
      ∃g∈(pResidual 2 (C c i)).map (C c i).subtype,
        g*sourceHom c i a*g⁻¹=sourceHom c i (.r 2) := by
    obtain ⟨g,⟨v,hv,hvg⟩,he⟩ :=
      sourceEndpointResidualCore_conjugate_in_residual c i hi b _ ha hx1 _ hz hz1
    let j : Dendpoint c i b →* C c i := inclusion ((Dendpoint_le_E c i b).trans inf_le_right)
    exact ⟨g,⟨j v,map_pResidual_le 2 j (mem_map_of_mem j hv),hvg⟩,he⟩
  rcases involution_mem_four a ha2 with hp | hp
  · apply hf false
    · rw [sourceEndpointResidualCore_point c i hi]
      exact mem_map_of_mem _ hp
    · rw [sourceEndpointResidualCore_point c i hi]
      exact mem_map_of_mem _ common_center_mem.1
  · apply hf true
    · rw [sourceEndpointResidualCore_plane c i hi]
      exact mem_map_of_mem _ hp
    · rw [sourceEndpointResidualCore_plane c i hi]
      exact mem_map_of_mem _ common_center_mem.2.1

/-- The literal quotient involutions are conjugate inside its two-residual. -/
theorem sourceResidualJoinQuotient_involution_conjugate_in_residual
    (hi : Function.Injective i) (x : sourceResidualJoinQuotient c i) (hx2 : orderOf x=2) :
    IsConj (⟨sourceResidualQuotientCenter c i hi,
      sourceResidualJoinQuotient_le_twoResidual c i
        (sourceResidualQuotientCenter_mem c i hi)⟩ : pResidual 2 (graphCentralQuotient c i))
      ⟨x.val,sourceResidualJoinQuotient_le_twoResidual c i x.property⟩ := by
  let q := QuotientGroup.mk' (zpowers (graphInCentralizer c i))
  obtain ⟨a,ha,he⟩ := x.property
  let u : sourceResidualJoin c i := ⟨a.val,ha⟩
  let qU := sourceOrdinaryGraphQuotientMap c i (sourceResidualJoin c i) (sourceResidualJoin_le_C c i)
  have hqU : Function.Injective qU := sourceOrdinaryGraphQuotientMap_injective c i hi _
    (sourceResidualJoin_le_ordinary c i hi) (sourceResidualJoin_le_C c i)
  have hqa : orderOf (q a)=2 := by rw [he]; exact (orderOf_coe x).trans hx2
  have huo : orderOf u=2 := (orderOf_injective qU hqU u).symm.trans hqa
  have hao : orderOf a.val=2 := (orderOf_coe u).trans huo
  have ha2 : a.val^2=1 := by rw [←hao]; exact pow_orderOf_eq_one _
  have ha1 : a.val≠1 := by intro hh; rw [hh,orderOf_one] at hao; omega
  obtain ⟨g,⟨gC,hgC,hg⟩,hconj⟩ :=
    sourceResidualJoin_involution_conjugate_in_residual c i hi a.val ha ha2 ha1
  let gW : pResidual 2 (graphCentralQuotient c i) :=
    ⟨q gC,map_pResidual_le 2 q (mem_map_of_mem q hgC)⟩
  have hC : gC*a*gC⁻¹=sourceResidualCenterInC c i hi := by
    apply Subtype.ext
    change gC.val*a.val*gC.val⁻¹=sourceHom c i (.r 2)
    change gC.val=g at hg
    rw [hg]
    exact hconj
  have hW : gW*⟨x.val,sourceResidualJoinQuotient_le_twoResidual c i x.property⟩*gW⁻¹ =
      ⟨sourceResidualQuotientCenter c i hi,
        sourceResidualJoinQuotient_le_twoResidual c i
          (sourceResidualQuotientCenter_mem c i hi)⟩ := by
    apply Subtype.ext
    change q gC*x.val*(q gC)⁻¹=q (sourceResidualCenterInC c i hi)
    rw [←he,←map_inv,←map_mul,←map_mul,hC]
  exact (isConj_iff.mpr ⟨gW,hW⟩).symm

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
