module
public import Stellmacher.SectionEight.EightFourStarCriticalControl

/-!
# The initial star centralizes the predecessor module

Retain the actual local Section Eight context with central first-step center,
its faithful fixed-center witness and nontrivial closure branch, and the
actual equivariant star family. If its first-step value lies in the first-step
neighbor module, that star centralizes the entire predecessor neighbor module.
The star's covariance and base value are exactly those of the transported
source-(4) theorem; the separate star-to-module leaf supplies its containment.

Consider a center Z_l contributing to the predecessor module. Its distance
from the first step is less than the critical distance b. If every center
contributing to the first-step module commutes with Z_l, so does the star.
Otherwise choose a noncommuting center Z_k. The path through the first step
bounds the k-to-l distance by b, while critical minimality bounds it below
by b. Thus (k,l) is an actual noncommuting critical pair with the first step
on a geodesic. The transported local source-(4) theorem puts the initial star in
Q_l, which centralizes Z_l. Joining over all l proves the assertion. The
canonical public statement remains an exact wrapper on the same local graph.

This supplies the centralization in Stellmacher (8.4)(7), Journal of Algebra
190 (1997), p.39, refs/files/stellmacher-n-group.pdf: the source subgroup D
lies in the predecessor star joined with the terminal center, hence in the
predecessor module. No selected factor identity, second extraction assumption,
or replacement critical path is added to the caller's context.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem adjacent_distance_bound
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (a b c : Γ.Vertex)
    (hab : Γ.adjacent a b) : Γ.distance a c ≤ Γ.distance b c + 1 := by
  obtain ⟨path,h0,he,hpath⟩ := Γ.distance_path b c
  let f : Fin (Γ.distance b c + 1 + 1) → Γ.Vertex := Fin.cases a path
  have hf : ∀ i : Fin (Γ.distance b c + 1), Γ.adjacent (f i.castSucc) (f i.succ) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Γ.adjacent a (path 0)
      rwa [h0]
    · simpa [f] using hpath j
  simpa [f,he] using Γ.distance_le_of_path (Γ.distance b c + 1) f hf

/-- The actual initial star centralizes the predecessor's entire neighbor module. -/
public theorem eight_four_star_centralizes_predecessor_module_local
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
    (hCV : C ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.firstStep) :
    ⁅C ctx.criticalPath.firstStep,
      VAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,by omega⟩)⁆ = ⊥ := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let previous := cp.path ⟨cp.length - 1,by omega⟩
  let h := ctx.sectionSeven
  have hb : 1 < cp.length := eight_four_centered_length_gt_one_local ctx hcenter
  have hdist : Γ.distance cp.firstStep previous ≤ cp.length - 2 := by
    have hh := path_distance_le Γ cp 1 (cp.length - 1) (by omega) (by omega)
    simpa only [cp.path_first, Nat.sub_sub] using hh
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  apply Subgroup.le_centralizer_iff.mpr
  change v Γ previous ≤ Subgroup.centralizer (C cp.firstStep : Set H)
  rw [v,Γ.vAt_def]
  apply sSup_le
  rintro _ ⟨l,hl,rfl⟩
  apply Subgroup.le_centralizer_iff.mpr
  have hlback : Γ.adjacent l previous :=
    Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hl)
  have hldist : Γ.distance cp.firstStep l < cp.length := by
    have hh := adjacent_distance_bound Γ l previous cp.firstStep hlback
    rw [Γ.distance_symm l cp.firstStep,Γ.distance_symm previous cp.firstStep] at hh
    omega
  have hZlC : ZAt Γ l ≤ Subgroup.centralizer (QAt Γ l : Set H) :=
    ((lemma_seven_three h Γ).center_core l previous
      ((mem_neighborhood_iff_adjacent Γ).mpr hlback)).trans
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  by_cases hall : ∀ k ∈ neighborhood Γ cp.firstStep, ⁅ZAt Γ k,ZAt Γ l⁆ = ⊥
  · apply hCV.trans
    change v Γ cp.firstStep ≤ Subgroup.centralizer (z Γ l : Set H)
    rw [v,Γ.vAt_def]
    apply sSup_le
    rintro _ ⟨k,hk,rfl⟩
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hall k hk)
  · push Not at hall
    obtain ⟨k,hk,hcomm⟩ := hall
    have hkadj : Γ.adjacent k cp.firstStep :=
      Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hk)
    have hbound := adjacent_distance_bound Γ k cp.firstStep l hkadj
    have hnot : ¬ ZAt Γ k ≤ QAt Γ l := by
      intro hle
      apply hcomm
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (hle.trans (Subgroup.le_centralizer_iff.mp hZlC))
    have hlower : cp.length ≤ Γ.distance k l := by
      by_contra hh
      exact hnot (critical_minimality Γ cp (by omega))
    have heq : Γ.distance k l = cp.length := by omega
    have hcritical : IsCriticalPair Γ k l :=
      ⟨heq.trans (cp.endpoint_distance.symm.trans cp.critical.1),hnot⟩
    have hnear : Γ.distance k l = Γ.distance cp.firstStep l + 1 := by omega
    exact (eight_four_star_le_core_of_critical_pair_local ctx hcenter w hbranch C hC hbase
      k l cp.firstStep hcritical hcomm hkadj hnear).trans
      (Subgroup.le_centralizer_iff.mp hZlC)


/-- Canonical-context wrapper retaining the exact star family and quotient witness. -/
public theorem eight_four_star_centralizes_predecessor_module
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
    (hCV : C ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.firstStep) :
    ⁅C ctx.criticalPath.firstStep,
      VAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,by omega⟩)⁆ = ⊥ := by
  exact eight_four_star_centralizes_predecessor_module_local ctx.toLocalContext hcenter w hbranch C hC hbase hCV

end Stellmacher.SectionEight
