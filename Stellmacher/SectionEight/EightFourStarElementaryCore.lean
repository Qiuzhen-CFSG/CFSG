module
public import Stellmacher.SectionEight.EightFourEdgeStarClosure
public import Stellmacher.SectionEight.EightFourFixedClosureElementary

/-!
# The transported star family is elementary and lies in the vertex cores

Use the exact edge-fixed family from the central-first-step, nontrivial-closure
branch of Stellmacher (8.4). At every vertex l, its star join C(l) is elementary
abelian of exponent two and lies in the actual vertex two-core Q_l.

The edge-star closure theorem identifies C at the initial first-step vertex
with the original fixed-center normal closure and gives covariance and normality
for the same family. At a vertex in the first-step orbit, conjugation transports
the proved elementary structure of that initial closure. Outside the orbit,
the transporter formula has no witnesses, so every summand and the whole join
are trivial. In either case C(l) is a normal two-subgroup of G_l. Restricting
to that literal stabilizer and applying the definition of its two-core gives
the stated ambient containment.

These are the Vstar vertex-core containments used in source (7), with the
original source (4) closure retained throughout. Source: Stellmacher (8.4),
Journal of Algebra190 (1997), printed p39, `refs/files/stellmacher-n-group.pdf`.

The local version uses the same family and graph; its original canonical
statement remains available as an exact local-context wrapper.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u
/-- Every star join of the actual edge-fixed family is an elementary normal core subgroup. -/
public theorem eight_four_star_elementary_core_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
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
      (w.oneJFixedPoints S).conjBy g⁻¹) :
    let C := fun l => ⨆ d, F d l
    ∀ l, IsElementaryAbelian 2 (C l) ∧ C l ≤ QAt ctx.Γ l := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let C := fun l => ⨆ d, F d l
  obtain ⟨hCb,hCc,_,hCn⟩ := eight_four_edge_star_closure_local ctx w F hbase hcov hsub hformula
  change C cp.firstStep = _ at hCb
  change ∀ g l, C (Γ.act g l) = (C l).conjBy g⁻¹ at hCc
  change ∀ l, IsElementaryAbelian 2 (C l) ∧ C l ≤ QAt Γ l
  have hCe : IsElementaryAbelian 2 (C cp.firstStep) := by
    rw [hCb]
    exact eight_four_fixed_closure_elementary_local ctx hcenter w hbranch
  intro l
  have hCl : IsElementaryAbelian 2 (C l) := by
    by_cases horbit : ∃ g : H, Γ.act g cp.firstStep = l
    · obtain ⟨g,rfl⟩ := horbit
      rw [hCc]
      let _ := hCe
      exact IsElementaryAbelian.map (MulAut.conj g⁻¹).toMonoidHom
    · have hbot : C l = ⊥ := by
        apply le_bot_iff.mp
        apply iSup_le
        intro d
        rw [hformula]
        apply iSup_le
        intro g
        apply iSup_le
        intro hg
        exact (horbit ⟨g,hg.2⟩).elim
      rw [hbot]
      exact
        { toIsMulCommutative := inferInstance
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
            fun x => Subsingleton.elim _ _ }
  refine ⟨hCl, ?_⟩
  let P := GAt Γ l
  have hcp : IsPGroup 2 ((C l).subgroupOf P) := by
    let _ := hCl
    exact (IsElementaryAbelian.isPGroup 2 (C l)).comap_subtype
  have hcore : (C l).subgroupOf P ≤ pCore 2 P := le_sSup ⟨(hCn l).2,hcp⟩
  have hm := Subgroup.map_mono hcore (f := P.subtype)
  rw [Subgroup.map_subgroupOf_eq_of_le (hCn l).1] at hm
  exact hm.trans_eq (Γ.twoCoreAt_def l).symm

/-- Canonical specialization retaining the given edge family and witness. -/
public theorem eight_four_star_elementary_core
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
      (w.oneJFixedPoints S).conjBy g⁻¹) :
    let C := fun l => ⨆ d, F d l
    ∀ l, IsElementaryAbelian 2 (C l) ∧ C l ≤ QAt ctx.Γ l := by
  exact eight_four_star_elementary_core_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula

end Stellmacher.SectionEight
