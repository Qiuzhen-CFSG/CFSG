module
public import Stellmacher.SectionEight.EightFourStarCriticalControl
/-!
# The predecessor star is contained in the initial core

In the pure local Section Eight context, retain the original critical path
and the actual equivariant star family
whose first-step value is the initial fixed-center normal closure. Its value
at the path predecessor of the terminal vertex lies in the initial core.
Conjugating this containment gives the bound at the first extracted new
neighbor, and hence centralization of the conjugated initial center.

The nonzero endpoint commutator gives the reversed critical pair by (7.4).
The original path bounds the predecessor's return distance by length minus
one. Conversely, prepend the final edge to a shortest return path to bound
the full endpoint distance. These inequalities identify the predecessor as
a geodesic first step for the reversed pair. Apply the proved transported
source-(4) control to that exact pair and neighbor. The original canonical
statement remains an exact wrapper through the same local graph.

This is the predecessor and conjugate-predecessor use of source (4) in
(8.4)(7), Stellmacher, Journal of Algebra 190 (1997), printed p.39,
`refs/files/stellmacher-n-group.pdf`. No arbitrary neighbor or new star
family is chosen.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u
public theorem eight_four_predecessor_star_le_initial_core_local
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
    : C (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,by omega⟩) ≤
      QAt ctx.Γ ctx.criticalPath.a := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  have hpos := cp.length_pos
  let previous := cp.path ⟨cp.length - 1,by omega⟩
  have hadj : Γ.adjacent cp.a' previous := by
    have he := cp.path_adj ⟨cp.length - 1,by omega⟩
    have hi : (⟨cp.length - 1,by omega⟩ : Fin cp.length).succ =
        ⟨cp.length,Nat.lt_succ_self _⟩ := by apply Fin.ext; dsimp; omega
    rw [hi,cp.path_end] at he
    exact Γ.adjacent_symm he
  have hprevle : Γ.distance previous cp.a ≤ cp.length - 1 := by
    have hh := SevenSix.path_distance_le Γ cp 0 (cp.length - 1) (by omega) (by omega)
    have hd : Γ.distance cp.a previous ≤ cp.length - 1 := by
      simpa [previous,cp.path_start] using hh
    rwa [Γ.distance_symm cp.a previous] at hd
  have hendle : Γ.distance cp.a' cp.a ≤ Γ.distance previous cp.a + 1 := by
    obtain ⟨tail,h0,he,hpath⟩ := Γ.distance_path previous cp.a
    let f : Fin (Γ.distance previous cp.a + 1 + 1) → Γ.Vertex := Fin.cases cp.a' tail
    have hf : ∀ i : Fin (Γ.distance previous cp.a + 1), Γ.adjacent (f i.castSucc) (f i.succ) := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change Γ.adjacent cp.a' (tail 0)
        rwa [h0]
      · simpa [f] using hpath j
    simpa [f,he] using Γ.distance_le_of_path (Γ.distance previous cp.a + 1) f hf
  have hnear : Γ.distance cp.a' cp.a = Γ.distance previous cp.a + 1 := by
    rw [Γ.distance_symm cp.a' cp.a,cp.endpoint_distance] at hendle ⊢
    omega
  exact eight_four_star_le_core_of_critical_pair_local ctx hcenter w hbranch C hC hbase
    cp.a' cp.a previous ((lemma_seven_four h Γ cp).commutator_case ctx.commutator_ne).2
    (by simpa only [Subgroup.commutator_comm] using ctx.commutator_ne) hadj hnear

/-- Canonical-context wrapper with the original path, witness and star family. -/
public theorem eight_four_predecessor_star_le_initial_core
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
    : C (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,by omega⟩) ≤
      QAt ctx.Γ ctx.criticalPath.a := by
  exact eight_four_predecessor_star_le_initial_core_local
    ctx.toLocalContext hcenter w hbranch C hC hbase

end Stellmacher.SectionEight
