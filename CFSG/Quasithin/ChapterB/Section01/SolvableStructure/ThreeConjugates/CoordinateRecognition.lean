module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.CoordinateRecognition.Seed
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.CoordinateRecognition.OddCores
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.ImageData

/-!
# Recognizing the cyclic-three coordinates in the reduced action

The source commutator identity and stability at ratio one put K in one
concrete factor. Its order identifies it with that factor's intrinsic odd
core. Factor permutation then identifies all S-conjugates with coordinate
cores. Conversely, the quotient by the S-conjugate closure is a two-group,
so every coordinate core lies in that closure; independence forces every
coordinate to occur. The same independence shows that the stable generated
subproduct contains all factors.

`coordinateRecognition` constructs the actual subgroup-family equivalence
and its conjugation compatibility. `localImage_coordinateRecognition` applies
it to the original fixed-space reduction and the literal image subgroups.
The universal solvable FF theorem and factor permutation remain explicit
upstream inputs. This module completes finite-factor recognition; lifting
to the original conjugates and M/O₂(M) belongs to the B.1.12 assembly.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, B.1.12,
printed p. 73 (PDF p. 84).
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ThreeConjugates
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

private theorem factorOddCore_le_closure (d : SolvableFFFactors ρ)
    {K S : Subgroup G} (hS : IsPGroup 2 S) (hgen : K ⊔ S = ⊤) (i : Fin d.count) :
    d.factorOddCore i ≤ conjugateClosure K S := by
  let N := conjugateClosure K S
  have hn : N.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    exact sup_le ((le_conjugateClosure K S).trans N.le_normalizer)
      (le_normalizer_conjugateClosure K S)
  let := hn
  let q := QuotientGroup.mk' N
  have hq : IsPGroup 2 (G ⧸ N) := isPGroup_quotient_of_sup_eq_top N S hS
    ((conjugateClosure_sup K S).trans hgen)
  have hthree : IsPGroup 3 (d.factorOddCore i) :=
    IsPGroup.of_card (n := 1) (by simpa using d.factorOddCore_card i)
  have hb : (d.factorOddCore i).map q = ⊥ := disjoint_self.mp
    ((hthree.map q).disjoint_of_coprime (hq.to_subgroup _)
      (by decide : Nat.Coprime 3 2))
  intro x hx
  exact (QuotientGroup.eq_one_iff (N := N) x).mp
    (mem_bot.mp (hb ▸ mem_map_of_mem q hx))

/-- Generation by K and a two-subgroup forces every coordinate into K's orbit. -/
theorem factorOddCore_mem_conjugateFamily (d : SolvableFFFactors ρ)
    (hperm : ∀ (g : G) (i : Fin d.count),
      ∃ j, (d.factor i).map (MulAut.conj g).toMonoidHom = d.factor j)
    {K S : Subgroup G} (hS : IsPGroup 2 S) (hgen : K ⊔ S = ⊤)
    {i₀ : Fin d.count} (hseed : K = d.factorOddCore i₀) (i : Fin d.count) :
    d.factorOddCore i ∈ conjugateFamily K S := by
  let I : Set (Fin d.count) := {j | d.factorOddCore j ∈ conjugateFamily K S}
  have hN : conjugateClosure K S ≤ ⨆ j ∈ I, d.factor j := by
    refine iSup_le fun s => ?_
    obtain ⟨j, hj⟩ := hperm (s : G) i₀
    have he : K.map (MulAut.conj (s : G)).toMonoidHom = d.factorOddCore j := by
      rw [hseed]
      exact d.factorOddCore_map_conj (s : G) hj
    have hjI : j ∈ I := ⟨s, he⟩
    rw [he]
    exact (d.factorOddCore_le j).trans
      (le_iSup_of_le j (le_iSup_of_le hjI le_rfl))
  exact d.mem_of_factorOddCore_le_subproduct I
    ((factorOddCore_le_closure d hS hgen i).trans hN)

/-- The equality is between actual subgroup families, with each core occurring once. -/
theorem conjugateFamily_eq_range_factorOddCore (d : SolvableFFFactors ρ)
    (hperm : ∀ (g : G) (i : Fin d.count),
      ∃ j, (d.factor i).map (MulAut.conj g).toMonoidHom = d.factor j)
    {K S : Subgroup G} (hS : IsPGroup 2 S) (hgen : K ⊔ S = ⊤)
    {i₀ : Fin d.count} (hseed : K = d.factorOddCore i₀) :
    conjugateFamily K S = Set.range d.factorOddCore := by
  ext A
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨j, hj⟩ := hperm (s : G) i₀
    refine ⟨j, ?_⟩
    rw [hseed]
    exact (d.factorOddCore_map_conj (s : G) hj).symm
  · rintro ⟨i, rfl⟩
    exact factorOddCore_mem_conjugateFamily d hperm hS hgen hseed i

variable [FiniteDimensional (ZMod 2) V]

/-- The stable family generates the entire offender subgroup once its seed
coordinate has the full Sylow orbit. No equality with its saturation is used. -/
theorem generated_eq_of_coordinate (d : SolvableFFStructure ρ)
    (hperm : ∀ (g : G) (i : Fin d.count),
      ∃ j, (d.factor i).map (MulAut.conj g).toMonoidHom = d.factor j)
    {P : Set (Subgroup G)} (hP : IsStable ρ P) {K S : Subgroup G}
    (hS : IsPGroup 2 S) (hgen : K ⊔ S = ⊤)
    (hcomm : K = ⁅K, generatedBy P S⁆)
    {i₀ : Fin d.count} (hseed : K = d.toSolvableFFFactors.factorOddCore i₀) :
    generatedBy P ⊤ = offenderSubgroup ρ := by
  let J := generatedBy P ⊤
  let : J.Normal := hP.generatedBy_normal ρ
  have hKJ : K ≤ J := by
    rw [hcomm]
    apply le_trans (commutator_mono le_rfl ?_) (commutator_le_right K J)
    exact iSup_le fun A => iSup_le fun hA => le_generatedBy_top_of_mem hA.1
  have hN : conjugateClosure K S ≤ J := by
    refine iSup_le fun s => ?_
    rintro x ⟨k, hk, rfl⟩
    exact (inferInstance : J.Normal).conj_mem k (hKJ hk) s
  have hcores (i : Fin d.count) : d.toSolvableFFFactors.factorOddCore i ≤ J := by
    have hi := factorOddCore_mem_conjugateFamily d.toSolvableFFFactors hperm hS hgen hseed i
    exact (conjugate_le_closure K S ⟨_, hi⟩).trans hN
  have he := d.toSolvableFFFactors.stable_generatedBy_eq_of_classifier
    d.ratio_one d.classifier hP
  have hall (i : Fin d.count) : i ∈ d.toSolvableFFFactors.stableFactorSet P :=
    d.toSolvableFFFactors.mem_of_factorOddCore_le_subproduct _ (he ▸ hcores i)
  rw [he, ← d.toSolvableFFFactors.iSup_factor]
  exact le_antisymm (iSup_le fun i => iSup_le fun _ => le_iSup d.factor i)
    (iSup_le fun i => le_iSup_of_le i (le_iSup_of_le (hall i) le_rfl))

/-- Recognition from the literal factor-permutation premise. The construction
in fact needs only the concrete structure, stability, generation, order three,
and the commutator identity; the ambient solvability and reduced-core hypotheses
have already been used to obtain the structural witness. -/
theorem coordinateRecognition (d : SolvableFFStructure ρ)
    (hperm : ∀ (g : G) (i : Fin d.count),
      ∃ j, (d.factor i).map (MulAut.conj g).toMonoidHom = d.factor j)
    {P : Set (Subgroup G)} (hP : IsStable ρ P) (K : Subgroup G) (S : Sylow 2 G)
    (hcard : Nat.card K = 3) (hgen : K ⊔ (S : Subgroup G) = ⊤)
    (hcomm : K = ⁅K, generatedBy P (S : Subgroup G)⁆) :
    Nonempty (CoordinateRecognition d P K (S : Subgroup G)) := by
  classical
  obtain ⟨i₀, hKi, _⟩ := exists_three_coordinate d hP hcard hcomm
  have hseed := d.toSolvableFFFactors.eq_factorOddCore_of_card_three hcard hKi
  have hfamily := conjugateFamily_eq_range_factorOddCore d.toSolvableFFFactors hperm
    S.isPGroup' hgen hseed
  let e : conjugateFamily K (S : Subgroup G) ≃ Fin d.count :=
    (Equiv.setCongr hfamily).trans
      (Equiv.ofInjective d.toSolvableFFFactors.factorOddCore
        d.toSolvableFFFactors.factorOddCore_injective).symm
  have he (c : conjugateFamily K (S : Subgroup G)) :
      d.toSolvableFFFactors.factorOddCore (e c) = (c : Subgroup G) := by
    exact Equiv.apply_ofInjective_symm d.toSolvableFFFactors.factorOddCore_injective
      (Equiv.setCongr hfamily c)
  refine ⟨⟨e, he, generated_eq_of_coordinate d hperm hP S.isPGroup' hgen hcomm hseed, ?_⟩⟩
  intro s c c' hcc
  apply d.toSolvableFFFactors.factor_map_conj_of_oddCore hperm (s : G)
  rw [he, he]
  exact hcc

/-- Apply recognition to the genuine faithful fixed-space image. The only
upstream theorem inputs are the universal solvable FF theorem and literal
factor permutation; all cyclic-three and stable-family premises are discharged
by the source reduction. -/
theorem localImage_coordinateRecognition (structureTheorem : SolvableFFTheorem.{v, v})
    (hf : Function.Injective ρ) (K : Subgroup G) (T : Sylow 2 G)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal)
    (hcard : Nat.card K = 3)
    (hcomm : K = ⁅K, localOffenderSubgroup ρ (T : Subgroup G)⁆)
    (hperm : ∀ d : SolvableFFStructure
        (subspaceImageRepresentation (localRepresentation ρ K (T : Subgroup G))
          (localFixedSpace ρ K (T : Subgroup G))),
      ∀ g (i : Fin d.count),
        ∃ j, (d.factor i).map (MulAut.conj g).toMonoidHom = d.factor j) :
    ∃ d : SolvableFFStructure
        (subspaceImageRepresentation (localRepresentation ρ K (T : Subgroup G))
          (localFixedSpace ρ K (T : Subgroup G))),
      Nonempty (CoordinateRecognition d (localImageFamily ρ K (T : Subgroup G))
        (localImageThree ρ K (T : Subgroup G)) (localImageSylow ρ K T : Subgroup _)) := by
  obtain ⟨d⟩ := localImage_structure ρ structureTheorem hf K (T : Subgroup G)
    hK hcard T.isPGroup' hcomm
  refine ⟨d, coordinateRecognition d (hperm d)
    (localImageFamily_stable ρ hf K (T : Subgroup G) hK hcard T.isPGroup' hcomm)
    (localImageThree ρ K (T : Subgroup G)) (localImageSylow ρ K T)
    (localImageThree_card ρ hf K (T : Subgroup G) hK hcard T.isPGroup')
    (localImageThree_sup_sylow ρ K T) ?_⟩
  exact localImageThree_commutator ρ hf K T hK hcard hcomm

end CFSG.Quasithin.ChapterB.ThreeConjugates
