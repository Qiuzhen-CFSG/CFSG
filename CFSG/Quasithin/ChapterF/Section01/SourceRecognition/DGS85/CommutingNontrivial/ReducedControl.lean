module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.KernelControl
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.KernelSylow
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.GraphLayers

/-!
# Initial Chapter 8 conclusions on the reduced F1.11 graph

The commuting critical pair gives opposite vertex orbits, odd distance at
least three, a trivial local center on the starting orbit, and the full
kernel bound for the centralizer of each neighboring center span. The
radius-one spans are elementary and act quadratically on one another.
Nonzero H supplies a moving neighbor and a nonzero full-span commutator.

The reduced application constructs the exact 6.2(d) Sylow embeddings from
F1.11; they are not an extra hypothesis. The remaining local-group data are
explicit earlier Chapter 6 inputs, owned by the setup and obstruction proof.
The full Borel, reduced completion, and endpoint maps are unchanged.

Source: DGS, *Groups and Graphs* (1985), 8.0 and 8.1(a)--(e), pp.132--133.
Local generation, the quotient-center action, and 8.2--8.7 remain to be proved.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G]

/-- The genuine earlier local-group inputs, with the already proved kernel-Sylow
clause omitted. No Chapter 8 conclusion is a field of this structure. -/
structure RemainingLocalTheorems (F : Bool → Subgroup G) where
  localGroup : Vertex F → Subgroup G
  local_le : ∀ v, localGroup v ≤ stabilizer F v
  conjugate : ∀ g v, localGroup (g • v) = (localGroup v).map (MulAut.conj g).toMonoidHom
  sylow_le : ∀ v (T : Sylow 2 (stabilizer F v)),
    (T : Subgroup (stabilizer F v)).map (stabilizer F v).subtype ≤ localGroup v
  common_sylow : ∀ v w, (graph F).Adj v w →
    ∃ (T : Sylow 2 (stabilizer F v)) (T' : Sylow 2 (stabilizer F w)),
      (T : Subgroup (stabilizer F v)).map (stabilizer F v).subtype =
        (T' : Subgroup (stabilizer F w)).map (stabilizer F w).subtype
  sylow_or_center : ∀ v,
    (∃ T : Sylow 2 ↥(stabilizer F v ⊓ centralizer (Z F v : Set G) : Subgroup G),
      (T : Subgroup ↥(stabilizer F v ⊓ centralizer (Z F v : Set G) : Subgroup G)).map
        (stabilizer F v ⊓ centralizer (Z F v : Set G)).subtype = Q F v) ∨
      Z F v = omegaCenterIn (localGroup v)
  transitive : ∀ v (x y : (graph F).neighborSet v),
    ∃ g ∈ localGroup v, g • x.val = y.val
  core_span_obstruction : ∀ v w, (graph F).Adj v w →
    ¬ ∃ T : Sylow 2 (conjugateSpanBy (Q F w) (localGroup v)),
      (T : Subgroup (conjugateSpanBy (Q F w) (localGroup v))).map
        (conjugateSpanBy (Q F w) (localGroup v)).subtype = Q F w

/-- Reconstitute the existing generic interface using the proved reduced 6.2(d).
The original generic API remains available for other graph carriers. -/
def reducedEarlierLocalTheorems {J : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 J S) (d : RemainingLocalTheorems (Reduction.reducedFamily J S)) :
    EarlierLocalTheorems (Reduction.reducedFamily J S) where
  localGroup := d.localGroup
  local_le := d.local_le
  conjugate := d.conjugate
  sylow_le := d.sylow_le
  common_sylow := d.common_sylow
  kernel_sylow := Reduction.reduced_kernel_sylow h
  sylow_or_center := d.sylow_or_center
  transitive := d.transitive
  core_span_obstruction := d.core_span_obstruction

/-- Initial Chapter 8 geometry and centralizer control at an arbitrary ordered
critical pair. This formulation also applies to the opposite pair in 9.2. -/
theorem source_critical_initial_control
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (hne : ⁅V (family P) beta 1 ⊓ Q (family P) a', V (family P) a' 1⁆ ≠ ⊥) :
    let F := family P
    Odd (b F) ∧ 3 ≤ b F ∧ center (d.localGroup a) = ⊥ ∧
      Z F beta = omegaCenterIn (d.localGroup beta) ∧
      d.localGroup beta ⊓ centralizer (V F beta 1 : Set G) ≤ U F beta ∧
      d.localGroup a' ⊓ centralizer (V F a' 1 : Set G) ≤ U F a' ∧
      IsElementaryAbelian 2 (V F beta 1) ∧ IsElementaryAbelian 2 (V F a' 1) ∧
      ⁅⁅V F beta 1, V F a' 1⁆, V F beta 1⁆ = ⊥ ∧
      ⁅⁅V F beta 1, V F a' 1⁆, V F a' 1⁆ = ⊥ ∧
      ⁅V F beta 1, V F a' 1⁆ ≠ ⊥ ∧
      (∃ w : (graph F).neighborSet a',
        ⁅V F beta 1 ⊓ Q F a', Z F w.val⁆ ≠ ⊥ ∧ ¬ V F beta 1 ⊓ Q F a' ≤ Q F w.val) ∧
      ∃ prev : Vertex F, (graph F).Adj a' prev ∧
        (graph F).dist beta prev + 1 = (graph F).dist beta a' ∧
        V F beta 1 ≤ Q F prev ∧ ¬ Q F prev ≤ Q F a' := by
  dsimp only
  let := finite_endpoints h
  obtain ⟨hodd, hb3, hZ, hquad, prev, hp, hdprev, hV, he⟩ :=
    source_critical_geometry h d hc hab hd hb hcomm
  exact ⟨hodd, hb3, local_center_eq_bot_of_neighbor_central h d hab hZ, hZ,
    (inf_le_inf_right _ (d.local_le beta)).trans (source_span_centralizer_le_kernel h hab.symm),
    (inf_le_inf_right _ (d.local_le a')).trans (source_span_centralizer_le_kernel h hp),
    CommutingThreeProfile.V_elementary (family P) h.generate (fun v => (source_Z_Q_U h v).1)
      d.kernel_sylow (by omega) beta,
    CommutingThreeProfile.V_elementary (family P) h.generate (fun v => (source_Z_Q_U h v).1)
      d.kernel_sylow (by omega) a',
    hquad.1, hquad.2, radius_one_commutator_ne_bot (family P) beta a' hne,
    exists_moving_neighbor (family P) (fun v => (source_Z_Q_U h v).1) beta a' hne,
    prev, hp, hdprev, hV, he⟩

/-- Literal reduced-F1.11 application of the initial Chapter 8 conclusions.
There is no kernel-Sylow premise: `reduced_kernel_sylow` discharges it. -/
theorem reduced_critical_initial_control
    {J : Fin 2 → Subgroup G} {S : Subgroup G} (h : HypothesisF11 J S)
    (d : RemainingLocalTheorems (Reduction.reducedFamily J S))
    {a beta a' : Vertex (Reduction.reducedFamily J S)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S) a a')
    (hab : (graph (Reduction.reducedFamily J S)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S)).dist beta a' + 1 = b (Reduction.reducedFamily J S))
    (hb : 1 < b (Reduction.reducedFamily J S))
    (hcomm : ⁅Z (Reduction.reducedFamily J S) a, Z (Reduction.reducedFamily J S) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S) beta 1 ⊓ Q (Reduction.reducedFamily J S) a',
      V (Reduction.reducedFamily J S) a' 1⁆ ≠ ⊥) :
    let F := Reduction.reducedFamily J S
    Odd (b F) ∧ 3 ≤ b F ∧ center (d.localGroup a) = ⊥ ∧
      Z F beta = omegaCenterIn (d.localGroup beta) ∧
      d.localGroup beta ⊓ centralizer (V F beta 1 : Set (Reduction.G₀ J S)) ≤ U F beta ∧
      d.localGroup a' ⊓ centralizer (V F a' 1 : Set (Reduction.G₀ J S)) ≤ U F a' ∧
      IsElementaryAbelian 2 (V F beta 1) ∧ IsElementaryAbelian 2 (V F a' 1) ∧
      ⁅⁅V F beta 1, V F a' 1⁆, V F beta 1⁆ = ⊥ ∧
      ⁅⁅V F beta 1, V F a' 1⁆, V F a' 1⁆ = ⊥ ∧
      ⁅V F beta 1, V F a' 1⁆ ≠ ⊥ ∧
      (∃ w : (graph F).neighborSet a',
        ⁅V F beta 1 ⊓ Q F a', Z F w.val⁆ ≠ ⊥ ∧ ¬ V F beta 1 ⊓ Q F a' ≤ Q F w.val) ∧
      ∃ prev : Vertex F, (graph F).Adj a' prev ∧
        (graph F).dist beta prev + 1 = (graph F).dist beta a' ∧
        V F beta 1 ≤ Q F prev ∧ ¬ Q F prev ≤ Q F a' :=
  source_critical_initial_control (Reduction.reduced_triple h)
    (reducedEarlierLocalTheorems h d) hc hab hd hb hcomm hne

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
