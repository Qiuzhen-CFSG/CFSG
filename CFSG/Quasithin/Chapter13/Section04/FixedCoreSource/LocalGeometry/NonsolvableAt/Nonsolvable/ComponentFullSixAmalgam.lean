module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.PlanePairAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentFullSixAmalgam
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentFullSixPair
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.SourceAmalgam
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.OriginalLinearAmalgam

/-!
# The linear alternative for the original nonsolvable centralizer pair: structure at the original group

The original pair supplies every applicability premise of the retained
13.4.7 input. In its linear alternative, the actual S₃ parabolic excludes
the outer extension of the L₃(2) component. The resulting quotient lattice
identifies the unique outside parabolic and its intersection with L₂T.
In every local overgroup Y, the centralizer of the full orbit of Ω₁Z(T)
lies in the intersection of the two original parabolics, hence in T.
The source overgroup formula therefore gives Y=H₀. Applying this to the
normalizer of the nontrivial Thompson subgroup identifies H₀=N_G(J(T))
and proves maximal two-locality, as required in 13.4.10(8ii).

PlaneAmalgamSource1347 remains an explicit earlier-source input owned by
qt-d-1341-fixed-core-source. Its product commutator alternative alone does
not supply the module-weight conclusions of 13.4.10(8i). Those conclusions,
the both-weight comparison, and the later commutator and graph arguments
remain with qt-d-1341-nonsolvable-source.
Source: Aschbacher–Smith 13.4.10(8), printed pp.909–910.

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/ComponentFullSixAmalgam` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The linear alternative is the full Thompson normalizer and is maximal
among two-local subgroups. The literal intersection data discharges the
centralizer term in the earlier overgroup formula. -/
theorem original_linear_pair_maximal_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : G) (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (P B : Subgroup G)
    (hP : P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hTB : (T : Subgroup G) ≤ B) (hBM : B ≤ normalizer (L : Set G))
    (eP : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (hlocal : P ⊔ B ∈ Chapter1.HOver G (T : Set G))
    (hinter : ∀ Y : Subgroup G, Y ∈ Chapter1.H G → P ≤ Y → B ≤ Y →
      Y ⊓ normalizer (L : Set G) = B ∧ Y ⊓ centralizer ({z} : Set G) = P)
    (hlinear : Solvable.LinearAmalgamConclusion T (P ⊔ B)) :
    P ⊔ B = normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
      IsMaximalTwoLocal (P ⊔ B) ∧
      Nonempty (((P ⊔ B : Subgroup G) ⧸ pCore 2 (P ⊔ B : Subgroup G)) ≃* Matrix.PSL3Two.SL) ∧
      (∀ Q ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
        Q ≤ P ⊔ B → Q = P) := by
  let X := P ⊔ B
  obtain ⟨⟨K,_,_,_,hTK,hX,⟨eK⟩⟩,hnormal,hsupp⟩ := hlinear
  obtain ⟨e⟩ := Solvable.third_quotient_of_normalized_linear_component X K P hX hTK eK
    hP.1.1.2 le_sup_left eP
  let e' : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.SL := e.trans Matrix.PSL3Two.equiv.symm
  have hout : ¬ X ≤ normalizer (L : Set G) := fun hh => hP.1.2 (le_sup_left.trans hh)
  have hTB' : (T : Subgroup G) < B := lt_of_le_not_ge hTB (fun hh =>
    Solvable.not_twoGroup_of_symmetricThree_quotient eB (T.isPGroup'.to_le hh))
  have hBX : B < X := lt_of_le_not_ge le_sup_right (fun hh => hout (hh.trans hBM))
  obtain ⟨Q,_,_,_,_,hBP,hunique⟩ := small_quotient_unique_outside T
    (normalizer (L : Set G)) X B D.sylow_normalizes_component hlocal hout hTB' hBX hBM
    (Or.inl ⟨e'⟩)
  have hPQ : P = Q := hunique P hP le_sup_left
  rw [←hPQ] at hBP hunique
  have hcent : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤
      normalizer (L : Set G) := by
    rw [←fixed_centralizer_eq_normalizer_at h structural D m]
    exact centralizer_le (LocalGeometry.fixed_le_original_omegaCenter_at h structural D m)
  have hover (Y : Subgroup G) (hY : Y ∈ Chapter1.H G) (hXY : X ≤ Y) : Y ≤ X := by
    obtain ⟨hYM,hYH⟩ := hinter Y hY (le_sup_left.trans hXY) (le_sup_right.trans hXY)
    have hc : Y ⊓ centralizer
        (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X : Set G) ≤
          (T : Subgroup G) := by
      apply le_trans ?_ hBP.le
      intro c hc
      have hcz := centralizer_le (le_conjugateSpanBy
        (omegaOneCenterAmbient (T : Subgroup G)) X) hc.2
      refine ⟨?_,?_⟩
      · rw [←hYM]
        exact ⟨hc.1,hcent hcz⟩
      · rw [←hYH]
        exact ⟨hc.1,centralizer_le (Set.singleton_subset_iff.mpr hz) hcz⟩
    intro y hy
    obtain ⟨a,ha,c,hc',rfl⟩ := (hsupp Y ⟨hY,hXY⟩).le hy
    exact X.mul_mem ha (hlocal.2 (hc hc'))
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  let N := normalizer (J : Set G)
  have hJT : J ≤ (T : Subgroup G) := sSup_le fun _ hA => hA.1
  have hN : IsTwoLocal N :=
    ⟨J,Solvable.original_maxJ_ne_bot D m,T.isPGroup'.to_le hJT,rfl⟩
  have heq : X = N := le_antisymm hnormal
    (hover N (Chapter1.mem_H_of_isTwoLocal hN) hnormal)
  refine ⟨heq,?_,⟨e'⟩,hunique⟩
  refine ⟨?_,?_⟩
  · change IsTwoLocal X
    rwa [heq]
  · intro Y hY hXY
    exact hover Y (Chapter1.mem_H_of_isTwoLocal hY) hXY

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
