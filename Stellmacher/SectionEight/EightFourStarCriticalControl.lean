module
public import Stellmacher.SectionEight.EightFourFixedClosureControl
public import Stellmacher.SectionFiveToSeven.PrescribedCriticalPairNormalization
/-!
# Star-closure control along a transported critical pair

In the central-first-step, nontrivial-closure branch of (8.4) in the actual
local Section Eight context, let C be an
inverse-conjugation-equivariant vertex-subgroup family whose value at the
initial first step is the actual fixed-center normal closure. For any
noncommuting critical pair and a prescribed first neighbor on a geodesic,
C at that neighbor lies in the endpoint core.

Normalize the critical pair through the prescribed neighbor, retaining the
orientation of the anchored edge. The reversed orientation would place the
new initial center at the original central first-step vertex. The reverse
containment of (7.4) would then force its endpoint commutator to vanish.
Consequently the normalized path starts at the literal original edge.
Rebuild its local context with the same Section Seven and (6.3) data and
those same vertices, so the original faithful
quotient witness is definitionally the required one, and apply source (4).
Covariance of C and of the vertex cores carries this containment back along
the injective conjugation automorphism. The canonical public statement is
retained as an exact wrapper through the same local graph.

The actual family C is the join of the equivariant edge-fixed subgroups;
its construction is separate so the original family is retained throughout.
This is the use of source (4) on reversed conjugate critical paths just
before and in (8.4)(7), Stellmacher, Journal of Algebra 190 (1997), p.39,
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u
public theorem eight_four_star_le_core_of_critical_pair_local
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
    (C : ctx.Γ.Vertex → Subgroup H)
    (hC : ∀ g d, C (ctx.Γ.act g d) = (C d).conjBy g⁻¹)
    (hbase : C ctx.criticalPath.firstStep = (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype)
    (left right next : ctx.Γ.Vertex)
    (hcritical : IsCriticalPair ctx.Γ left right)
    (hcomm : ⁅ZAt ctx.Γ left,ZAt ctx.Γ right⁆ ≠ ⊥)
    (hadj : ctx.Γ.adjacent left next)
    (hnear : ctx.Γ.distance left right = ctx.Γ.distance next right + 1) :
    C next ≤ QAt ctx.Γ right := by
  let Γ := ctx.Γ
  let cp0 := ctx.criticalPath
  let h := ctx.sectionSeven
  obtain ⟨g,cp,ha,ha',hb,hlen,horient⟩ :=
    exists_criticalPath_through_neighbor_with_orientation h Γ cp0 left right next hcritical hadj hnear
  have hcomm' : ⁅z Γ cp.a,z Γ cp.a'⁆ ≠ ⊥ := by
    rw [ha,ha',z_act,z_act]
    rw [← Subgroup.map_commutator]
    intro hh
    apply hcomm
    exact Subgroup.map_injective (MulAut.conj g⁻¹).injective
      (hh.trans (Subgroup.map_bot _).symm)
  have hcorrect : cp.a = cp0.a ∧ cp.firstStep = cp0.firstStep := by
    rcases horient with hok | hbad
    · exact hok
    · exfalso
      have hzcenter : z Γ cp.a ≤ CenterAmbient (stabilizer Γ cp.a) := by
        rw [hbad.1]
        exact hcenter
      apply hcomm'
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (hzcenter.trans ((SevenSix.centerAmbient_le_centralizer _).trans
          (Subgroup.centralizer_le (lemma_seven_four h Γ cp).reverse_containment.1)))
  rcases cp with ⟨a,a',n,hn,hcrit,b,hab,hde,f,hf0,hfn,hf1,hfadj,hSP,hpair⟩
  dsimp only at ha ha' hb hlen hcomm' hcorrect
  rcases hcorrect with ⟨ha0,hb0⟩
  have hfirst : cp0.firstStep = Γ.act g next := hb0.symm.trans hb
  have hf0new : f 0 = cp0.a := hf0.trans ha0
  have hf1new : f ⟨1,by omega⟩ = cp0.firstStep := hf1.trans hb0
  clear horient ha hf0 hb hf1
  subst a b
  let cp' : CriticalPath Γ := ⟨cp0.a,a',n,hn,hcrit,cp0.firstStep,hab,hde,f,hf0new,hfn,hf1new,hfadj,hSP,hpair⟩
  let ctx' : SectionEightLocalContext H S P1 P2 :=
    { sectionSeven := ctx.sectionSeven
      sixThree := ctx.sixThree
      Γ := Γ
      criticalPath := cp'
      commutator_ne := hcomm' }
  have hbound := (eight_four_fixed_closure_control_local ctx' hcenter w hbranch).1
  have hmap : (C next).conjBy g⁻¹ ≤ q Γ (Γ.act g right) := by
    rw [← hC g next,← hfirst,hbase,← ha']
    exact hbound
  rw [SevenSix.q_act] at hmap
  exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hmap

/-- Canonical-context wrapper with the unchanged graph, path and faithful witness. -/
public theorem eight_four_star_le_core_of_critical_pair
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
    (C : ctx.Γ.Vertex → Subgroup H)
    (hC : ∀ g d, C (ctx.Γ.act g d) = (C d).conjBy g⁻¹)
    (hbase : C ctx.criticalPath.firstStep = (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype)
    (left right next : ctx.Γ.Vertex)
    (hcritical : IsCriticalPair ctx.Γ left right)
    (hcomm : ⁅ZAt ctx.Γ left,ZAt ctx.Γ right⁆ ≠ ⊥)
    (hadj : ctx.Γ.adjacent left next)
    (hnear : ctx.Γ.distance left right = ctx.Γ.distance next right + 1) :
    C next ≤ QAt ctx.Γ right := by
  exact eight_four_star_le_core_of_critical_pair_local
    ctx.toLocalContext hcenter w hbranch C hC hbase left right next hcritical hcomm hadj hnear

end Stellmacher.SectionEight
