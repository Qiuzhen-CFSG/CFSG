module
public import Stellmacher.SectionEight.EightFourSourceNineData
public import Stellmacher.SectionEight.EightFourControlledFirstConfiguration
public import Stellmacher.SectionEight.EightFourSourceNineForward
public import Stellmacher.SectionEight.EightFourSecondConfiguration
public import Stellmacher.SectionEight.EightFourFirstResidualCore
public import Stellmacher.SectionEight.EightFourLengthTwoExclusion
/-!
# The actual first and second configurations for source (9)

The data record retains a single controlled initial factor, its actual first
extraction, and the actual second extraction. Both source-(6) alternatives
keep their numerical or containment clause, and the record stores the
source-(7) implication for every subgroup of the selected edge-fixed group.
The final field is the forward source-(9) intersection bound.

Choose the canonical four-factor with its initial-stabilizer centralizer
control, apply the exponent-two first extraction, and form the residual core
of its terminal-core supplement. Its proved core noncontainment and local
upper bound permit the second extraction. The same original family supplies
the star in both alternatives. Finally source (8) and the initial length
bound give critical distance greater than two; the forward-intersection
lemma applies to these exact witnesses.

The local producer constructs the same data on the supplied local graph,
using only its two proved ambient callbacks. The unchanged canonical record
is re-exported from `EightFourSourceNineData`; the canonical producer converts
its local data field by field through the existing adapter.
No new geometric context or edge family is constructed inside the record.
This preserves the witnesses needed for the remaining intersection and
commutator arguments on p.40 of Stellmacher, Journal of Algebra 190 (1997),
(8.4)(9). Reverse inclusion and final normality are proved separately.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_four_source_nine_configuration_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : EightFourLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
 : Nonempty (EightFourSourceNineLocalData ctx.toLocalContext F) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  let prev := cp.path ⟨cp.length-1,by omega⟩
  obtain ⟨A,hA,hcard,hAnot,hAprev,hcontrol,x,L0,hL0,hLgen,hx,hfirstfull⟩ :=
    eight_four_controlled_first_configuration_local ctx.toLocalContext hcenter w
  let d := Γ.act x⁻¹ prev
  let L := L0 ⊔ QAt Γ cp.a'
  let Q := twoCoreIn (twoResidualIn L)
  have hpos := cp.length_pos
  have hprevadj : Γ.adjacent cp.a' prev := by
    have he := cp.path_adj ⟨cp.length-1,by omega⟩
    have hi : (⟨cp.length-1,by omega⟩ : Fin cp.length).succ =
        ⟨cp.length,Nat.lt_succ_self _⟩ := by apply Fin.ext; dsimp; omega
    rw [hi,cp.path_end] at he
    exact Γ.adjacent_symm he
  have hprev := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hprevadj
  have hQP : Q ≤ QAt Γ cp.a' := local_residual_core_le_vertex_core h Γ cp.a' prev hprev L
    (sup_le hL0 (by rw [show QAt Γ cp.a' = twoCoreIn (GAt Γ cp.a') from Γ.twoCoreAt_def cp.a']; exact Subgroup.map_subtype_le _))
  have hQnot : ¬ Q ≤ QAt Γ d := eight_four_first_residual_core_noncontainment_local ctx hcenter
    prev hprevadj A L0 x hAprev hAnot hL0 hLgen hx hfirstfull
  have hfix : Γ.act x⁻¹ cp.a' = cp.a' := by
    have hh := (GAt Γ cp.a').inv_mem (hL0 hx)
    change x⁻¹ ∈ (Γ.vertexStabilizer cp.a' : Set H) at hh
    rw [Γ.stabilizer_def] at hh
    exact hh
  have hdadj : Γ.adjacent d cp.a' := by
    have hh := adjacent_act Γ x⁻¹ (Γ.adjacent_symm hprevadj)
    rwa [hfix] at hh
  obtain ⟨y,Ltilde,hy,hLt,hadj,hfull,hcase⟩ :=
    eight_four_second_configuration_local ctx.toLocalContext hcenter w hbranch d hdadj Q hQP hQnot
  have hCb := (eight_four_edge_star_closure_local ctx.toLocalContext w F hbase hcov hsub hformula).1
  dsimp only at hCb
  dsimp only [EightFourLocalContext.toLocalContext] at hCb hcase
  have hcase' : Ltilde = (⨆k,F k cp.firstStep) ⊔ QAt Γ (Γ.act y⁻¹ cp.a') ∨
      Ltilde = Q ⊔ QAt Γ (Γ.act y⁻¹ cp.a') := by
    rcases hcase with hc | hc
    · exact Or.inl (by simpa only [← hCb, EightFourLocalContext.toLocalContext, Γ, cp] using hc.1)
    · exact Or.inr hc.1
  have hs7 : ∀D : Subgroup H,D≤F (Γ.act y⁻¹ cp.a') d → ⁅D,A⁆≤ZAt Γ cp.a' →D≤ZAt Γ d := by
    intro D hD hDA
    exact eight_four_source_seven_local ctx hcenter w hbranch F hbase hcov hsub hformula
      A L0 x hA hL0 hLgen hx d (Γ.act y⁻¹ cp.a') rfl hadj Ltilde hfull hcase' D hD hDA
  have hlen : 2 < cp.length := by
    have hgt : 1 < cp.length := eight_four_centered_length_gt_one_local ctx.toLocalContext hcenter
    have hne : cp.length ≠ 2 := eight_four_length_ne_two_of_nontrivial_closure_local ctx hcenter w hbranch
    change 2 < cp.length
    omega
  refine ⟨⟨A,L0,x,d,y,Ltilde,hA,hcard,hAnot,hAprev,hcontrol,hL0,hLgen,hx,hfirstfull,
    rfl,hy,hLt,hadj,hfull,?_,hs7,?_⟩⟩
  · simpa only [← hCb, EightFourLocalContext.toLocalContext, Γ, cp, Q, L] using hcase
  · exact eight_four_source_nine_forward_local ctx hcenter w hbranch F hbase hcov hsub hformula
      A L0 x hA hL0 hLgen hx d (Γ.act y⁻¹ cp.a') rfl hadj Ltilde hfull hcase' hlen hcontrol
public theorem eight_four_source_nine_configuration
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
 : Nonempty (EightFourSourceNineData ctx F)  := by
  obtain ⟨configuration⟩ := eight_four_source_nine_configuration_local
    ctx.toEightFourContext hcenter w hbranch F hbase hcov hsub hformula
  exact ⟨EightFourSourceNineData.ofLocal configuration⟩

end Stellmacher.SectionEight
