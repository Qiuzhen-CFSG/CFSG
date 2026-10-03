module
public import Stellmacher.SectionEight.EightFourSourceSeven
/-!
# The forward initial-stabilizer intersection bound in source (9)

For the actual first and second configurations of (8.4), suppose the selected
initial factor has the centralizer control supplied by the controlled first
extraction. At critical distance greater than two, the edge-fixed subgroup
at the second new edge meets the original initial stabilizer inside the
first new vertex center.

The endpoint and second new vertex are connected by two genuine edges.
Critical minimality puts the endpoint center in the second vertex core,
which that vertex's center centralizes. The intersection in the theorem
therefore centralizes the endpoint center. The selected factor's retained
control bounds its commutator, and the exact source-(7) implication gives
the desired containment. All witnesses, factors, actors and edge families
are supplied unchanged. The local theorem uses the same graph and the proved
ambient callbacks in `EightFourLocalContext`; the original canonical theorem
is retained as a wrapper through `ctx.toEightFourContext`.
Source: Stellmacher (8.4)(9), Journal of Algebra 190 (1997), printed p.40.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_four_source_nine_forward_local
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
    (A L0 : Subgroup H) (x : H)
    (hA : A ≤ ZAt ctx.Γ ctx.criticalPath.a)
    (hL0 : L0 ≤ GAt ctx.Γ ctx.criticalPath.a')
    (hLgen : L0 = A ⊔ A.conjBy x) (hx : x ∈ L0)
    (d next2 : ctx.Γ.Vertex)
    (hd : d = ctx.Γ.act x⁻¹ (ctx.criticalPath.path
      ⟨ctx.criticalPath.length-1,by omega⟩))
    (hadj : ctx.Γ.adjacent d next2)
    (Ltilde : Subgroup H)
    (hfull : Ltilde ⊔ (GAt ctx.Γ d ⊓ GAt ctx.Γ next2) = GAt ctx.Γ d)
    (hcase : Ltilde = (⨆ k, F k ctx.criticalPath.firstStep) ⊔ QAt ctx.Γ next2 ∨
      Ltilde = twoCoreIn (twoResidualIn (L0 ⊔ QAt ctx.Γ ctx.criticalPath.a')) ⊔
        QAt ctx.Γ next2)
    (hlen : 2 < ctx.criticalPath.length)
    (hcontrol : ∀ T : Subgroup H, T ≤ GAt ctx.Γ ctx.criticalPath.a →
      ⁅T,ZAt ctx.Γ ctx.criticalPath.a'⁆ = ⊥ →
      ⁅T,A⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a') :
    F next2 d ⊓ GAt ctx.Γ ctx.criticalPath.a ≤ ZAt ctx.Γ d := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  let D := F next2 d ⊓ GAt Γ cp.a
  have hlength : 2 < cp.length := hlen
  have hpos := cp.length_pos
  let prev := cp.path ⟨cp.length-1,by omega⟩
  have hprevadj : Γ.adjacent cp.a' prev := by
    have he := cp.path_adj ⟨cp.length-1,by omega⟩
    have hi : (⟨cp.length-1,by omega⟩ : Fin cp.length).succ =
        ⟨cp.length,Nat.lt_succ_self _⟩ := by apply Fin.ext; dsimp; omega
    rw [hi,cp.path_end] at he
    exact Γ.adjacent_symm he
  have hfix : Γ.act x⁻¹ cp.a' = cp.a' := by
    have hh := (GAt Γ cp.a').inv_mem (hL0 hx)
    change x⁻¹ ∈ (Γ.vertexStabilizer cp.a' : Set H) at hh
    rw [Γ.stabilizer_def] at hh
    exact hh
  have hdadj : Γ.adjacent cp.a' d := by
    have hh := adjacent_act Γ x⁻¹ hprevadj
    rwa [hfix,← hd] at hh
  have hdist : Γ.distance cp.a' next2 ≤ 2 := by
    let f : Fin 3 → Γ.Vertex := ![cp.a',d,next2]
    have hf : ∀i : Fin 2, Γ.adjacent (f i.castSucc) (f i.succ) := by
      intro i
      fin_cases i
      · exact hdadj
      · exact hadj
    exact Γ.distance_le_of_path 2 f hf
  have hEQ : ZAt Γ cp.a' ≤ QAt Γ next2 :=
    SevenSix.critical_minimality Γ cp (by change Γ.distance cp.a' next2 < cp.length; omega)
  have hZcent : ZAt Γ next2 ≤ Subgroup.centralizer (QAt Γ next2 : Set H) :=
    ((lemma_seven_three h Γ).center_core next2 d
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hadj))).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans (SevenSix.centerAmbient_le_centralizer _))
  have hDC : ⁅D,ZAt Γ cp.a'⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      ((inf_le_left.trans ((hsub next2 d).trans inf_le_left)).trans
        (hZcent.trans (Subgroup.centralizer_le hEQ)))
  exact eight_four_source_seven_local ctx hcenter w hbranch F hbase hcov hsub hformula
    A L0 x hA hL0 hLgen hx d next2 hd hadj Ltilde hfull hcase D inf_le_left
    (hcontrol D inf_le_right hDC)

public theorem eight_four_source_nine_forward
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
    (A L0 : Subgroup H) (x : H)
    (hA : A ≤ ZAt ctx.Γ ctx.criticalPath.a)
    (hL0 : L0 ≤ GAt ctx.Γ ctx.criticalPath.a')
    (hLgen : L0 = A ⊔ A.conjBy x) (hx : x ∈ L0)
    (d next2 : ctx.Γ.Vertex)
    (hd : d = ctx.Γ.act x⁻¹ (ctx.criticalPath.path
      ⟨ctx.criticalPath.length-1,by omega⟩))
    (hadj : ctx.Γ.adjacent d next2)
    (Ltilde : Subgroup H)
    (hfull : Ltilde ⊔ (GAt ctx.Γ d ⊓ GAt ctx.Γ next2) = GAt ctx.Γ d)
    (hcase : Ltilde = (⨆ k, F k ctx.criticalPath.firstStep) ⊔ QAt ctx.Γ next2 ∨
      Ltilde = twoCoreIn (twoResidualIn (L0 ⊔ QAt ctx.Γ ctx.criticalPath.a')) ⊔
        QAt ctx.Γ next2)
    (hlen : 2 < ctx.criticalPath.length)
    (hcontrol : ∀ T : Subgroup H, T ≤ GAt ctx.Γ ctx.criticalPath.a →
      ⁅T,ZAt ctx.Γ ctx.criticalPath.a'⁆ = ⊥ →
      ⁅T,A⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a') :
    F next2 d ⊓ GAt ctx.Γ ctx.criticalPath.a ≤ ZAt ctx.Γ d := by
  exact eight_four_source_nine_forward_local ctx.toEightFourContext hcenter w hbranch F hbase hcov hsub hformula A L0 x hA hL0 hLgen hx d next2 hd hadj Ltilde hfull hcase hlen hcontrol
end Stellmacher.SectionEight
