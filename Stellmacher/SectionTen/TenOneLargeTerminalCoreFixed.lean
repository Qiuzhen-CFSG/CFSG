module
public import Stellmacher.SectionTen.TenOneLargeOmegaCenter
public import Stellmacher.SectionTen.TenOneLargeGeneratedTerminalIntersection
public import Stellmacher.SectionTen.TenOneLargeTerminalIrreducible

/-!
# The terminal residual core fixes exactly the terminal center

In the actual large Section Ten branch, the points of the terminal module
fixed by the terminal residual two-core form exactly the terminal center.
The statement retains the original no-transvection context and uses no
source-(18) quotient or choice of residual model.

The image of this fixed subgroup in the literal terminal quotient is
invariant under the terminal stabilizer. Irreducibility makes it zero or
the whole quotient. In the latter case the residual core centralizes the
whole module. Its middle-generated subgroup W would then lie in the module:
the proved omega-center equality and fixed-component splitting imply the
valid containment C_W(V) ≤ V. This contradicts the generated-terminal
intersection theorem. The center already centralizes the stabilizer,
giving the reverse inclusion in the zero-image case.

This is a local transfer used in Stellmacher (10.1), printed p.64, between
(18) and (19). It avoids the false earlier printed equality C_W(V)=I.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_terminal_core_fixed_line
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    VAt ctx.Γ ctx.criticalPath.a' ⊓ Subgroup.centralizer
      (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a') : Set G) =
      ZAt ctx.Γ ctx.criticalPath.a' := by
  let P := GAt ctx.Γ ctx.criticalPath.a'
  let V := VAt ctx.Γ ctx.criticalPath.a'
  let Z := ZAt ctx.Γ ctx.criticalPath.a'
  let E := EAt ctx.Γ ctx.criticalPath.a'
  let U := twoCoreIn E
  let C := V ⊓ Subgroup.centralizer (U : Set G)
  let W := conjugateClosure
    (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle)
  let O := omegaOneCenter (GeneratedNeighborhoodV ctx.Γ middle)
  let Y := (W ⊓ Subgroup.centralizer (V : Set G)) ⊔ O
  have hshort : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  obtain ⟨alignment,_,halign⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  obtain ⟨hN,hModule,action,hformula,hkernel⟩ := nine_next_quotient_conjugation_action
    ctx.toAmbientSectionNineContext hshort ctx.criticalPath.a' ⟨alignment,halign⟩
  let _ := hN
  let _ := hModule
  let q := QuotientGroup.mk' (Z.subgroupOf V)
  have hE : E = twoResidualIn P := ctx.Γ.twoResidualAt_def _
  have hEP : E ≤ P := hE ▸ twoResidualIn_le P
  have hUP : U ≤ P := (twoCoreIn_le E).trans hEP
  have hPU : P ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUP).mp
      (twoCoreIn_normal_of_normal E P hEP (hE ▸ twoResidualIn_normal P))
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := stabilizer_le_normalizer_v ctx.Γ _
  have hPC : P ≤ Subgroup.normalizer (C : Set G) :=
    (le_inf hPV (hPU.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _)))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hZV : Z ≤ V :=
    (ten_one_large_terminal_residual_centralizer ctx middle hpath hno).symm.le.trans inf_le_left
  have hZC : Z ≤ C := le_inf hZV (Subgroup.le_centralizer_iff.mp
    (hUP.trans (nine_next_center_centralizes_stabilizer
      ctx.toLocalContext.toSectionNineLocalContext ctx.criticalPath.a' ⟨alignment,halign⟩)))
  let Cbar := (C.subgroupOf V).map q
  have hstable : ∀ p : P, ∀ x, x ∈ Cbar → action p x ∈ Cbar := by
    intro p x hx
    obtain ⟨v,hv,rfl⟩ := hx
    refine ⟨⟨(p:G)*(v:G)*(p:G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hPV p.property) _).mp v.property⟩,
      (Subgroup.mem_normalizer_iff.mp (hPC p.property) _).mp hv,?_⟩
    exact (hformula p v).symm
  rcases ten_one_large_terminal_irreducible ctx middle hpath hno action hformula hkernel Cbar hstable
      with hbot | htop
  · apply le_antisymm ?_ hZC
    intro c hc
    have hq : q (⟨c,hc.1⟩ : V) = 1 := hbot.le (Subgroup.mem_map_of_mem q hc)
    exact (QuotientGroup.eq_one_iff (N := Z.subgroupOf V) (⟨c,hc.1⟩ : V)).mp hq
  · have hVC : V ≤ Subgroup.centralizer (U : Set G) := by
      intro v hv
      obtain ⟨c,hc,heq⟩ := (show q (⟨v,hv⟩ : V) ∈ Cbar by rw [htop]; trivial)
      have hratio : (c:G)/v ∈ Z := by
        have hh : c/(⟨v,hv⟩ : V) ∈ Z.subgroupOf V := QuotientGroup.eq_iff_div_mem.mp heq
        exact hh
      have hmem : ((c:G)/v)⁻¹*(c:G) ∈ C := C.mul_mem (C.inv_mem (hZC hratio)) hc
      have hvc : v ∈ C := by
        simpa only [div_eq_mul_inv,mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,mul_one] using hmem
      exact hvc.2
    obtain ⟨hsplit,hDO,_,_,_⟩ := ten_one_large_omega_fixed_component ctx middle hpath hno
    have hOV : O ≤ V := (ten_one_large_neighborhood_omega_center ctx middle hpath hno).le.trans inf_le_right
    have hBV : Y ⊔ V ≤ V := hsplit.le.trans (sup_le le_rfl (hDO.trans hOV))
    have hCWV : W ⊓ Subgroup.centralizer (V : Set G) ≤ V :=
      (le_sup_left.trans le_sup_left).trans hBV
    have hWU := (ten_one_large_first_residual_index ctx middle hpath hno).2
    have hWV : W ≤ V := (le_inf le_rfl
      (hWU.trans (Subgroup.le_centralizer_iff.mp hVC))).trans hCWV
    exact ((ten_one_large_generated_terminal_intersection ctx middle hpath hno).2 hWV).elim

end Stellmacher.SectionTen
