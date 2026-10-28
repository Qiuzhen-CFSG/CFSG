module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.Transport

/-!
# The faithful section used in the opening assertion of MS93 (4.5.5)

The second orbit layer at c modulo its first orbit layer is the actual
marked doubled-dual section from (4.5.4)(iii). An actor centralizing that
section belongs to Q_c: its inverse-transpose action fixes every vector,
so its matrix is the identity. Only the first of the two factors is needed.

`SeedSection` retains one transporter to the distinguished vertex and the
literal section on the transported seed. Its action uses exactly
`CommonFacts.natural.marking`. It is a quotient witness, not a hypothesis
about noncentrality. The witness belongs to the independent marked-quotient
producer qt-c01-ms93-higher-marked-quotients. The consumer in Noncentrality
uses its faithful action to contradict a central seed commutator.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.4)(iii) and the opening
of (4.5.5), printed pp.898--899. The moving quotient of (4.5.4)(iv), whose
correct orientation is natural, is not used here.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.Noncentrality
open NormalizerTransfer PathCentrality DistanceFour.Linear
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}
  {source : LocalSource L R} {common : CommonFacts R source geometry}

private theorem dual_faithful (g : S) (h : ∀ v : W, dual g v = v) : g = 1 := by
  have hm : (g⁻¹).val.transpose = 1 := by
    ext i j
    have hh := congrFun (h (Pi.single j 1)) i
    simpa only [dual, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply,
      Matrix.one_apply] using hh
  have hi : g⁻¹ = 1 := by
    apply Subtype.ext
    change (g⁻¹).val = 1
    simpa only [Matrix.transpose_transpose, Matrix.transpose_one] using
      congrArg Matrix.transpose hm
  exact inv_eq_one.mp hi

/-- A subgroup centralizing a literal marked doubled-dual section lies in the
actual two-core, because the inverse-transpose matrix action is faithful. -/
theorem actor_le_Q [Finite M] {A N P : Subgroup (FreeAmalgam R)}
    (s : MarkedPairSection source common A N true)
    (hP : P ≤ Mbar R) (hcomm : ⁅P, A⁆ ≤ N) : P ≤ Q R (alpha R) := by
  intro z hz
  obtain ⟨m, hm⟩ := hP hz
  have hmP : embedM R m ∈ P := hm ▸ hz
  have hg : common.natural.marking (source.projection m) = 1 := by
    apply dual_faithful
    intro v
    obtain ⟨x, hx⟩ := s.onto (Multiplicative.ofAdd (v, (0 : W)))
    let y : A := ⟨embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹,
      le_normalizer_iff.mp s.normalized _ (hP hmP) _ x.property⟩
    have hk : y * x⁻¹ ∈ s.quotient.ker := by
      rw [s.kernel]
      exact hcomm (commutator_mem_commutator hmP x.property)
    have he : s.quotient y = s.quotient x := by
      have hh := MonoidHom.mem_ker.mp hk
      rwa [map_mul, map_inv, mul_inv_eq_one] at hh
    have hh := congrArg Prod.fst (s.action m x y rfl)
    simpa only [Bool.true_eq, reduceIte, he, hx, toAdd_ofAdd] using hh.symm
  have hp : source.projection m = 1 := common.natural.marking.injective
    (hg.trans common.natural.marking.map_one.symm)
  have hmcore : m ∈ pCore 2 M := by
    rw [← source.projection_kernel]
    exact hp
  rw [Q_alpha R source.two_group source.core_le]
  exact ⟨m, hmcore, hm⟩

/-- The literal doubled dual section at c, expressed at the distinguished
vertex by one simultaneous transport of all three seed vertices. -/
structure SeedSection (c d e : Vertex R) where
  transport : FreeAmalgam R
  at_base : act R transport c = alpha R
  model : MarkedPairSection source common
    (hatW R (alpha R) (act R transport d) (act R transport e))
    (hatV R (alpha R) (act R transport d)) true

/-- Transport the kernel deduction back to the original seed vertex. All
vertices in both orbit layers use the same conjugating element. -/
theorem SeedSection.le_Q_of_commutator [Finite M] {c d e : Vertex R}
    (s : SeedSection (source := source) (common := common) c d e)
    {P : Subgroup (FreeAmalgam R)} (hP : P ≤ stabilizer R c)
    (hcomm : ⁅P, hatW R c d e⁆ ≤ hatV R c d) : P ≤ Q R c := by
  let f := (MulAut.conj s.transport⁻¹).toMonoidHom
  have hPm : P.map f ≤ Mbar R := by
    have hh := map_mono (f := f) hP
    rw [← stabilizer_act, s.at_base, alpha, stabilizer_m_base] at hh
    exact hh
  have hcm : ⁅P.map f, hatW R (alpha R) (act R s.transport d) (act R s.transport e)⁆ ≤
      hatV R (alpha R) (act R s.transport d) := by
    have hh := map_mono (f := f) hcomm
    rw [map_commutator] at hh
    change ⁅P.map f, rightConjugate (hatW R c d e) s.transport⁆ ≤
      rightConjugate (hatV R c d) s.transport at hh
    simpa only [rightConjugate_hatW, rightConjugate_hatV, s.at_base] using hh
  have hh : P.map f ≤ (Q R c).map f := by
    rw [← Q_act, s.at_base]
    exact actor_le_Q s.model hPm hcm
  intro x hx
  obtain ⟨y, hy, he⟩ := hh (mem_map_of_mem f hx)
  exact (MulAut.conj s.transport⁻¹).injective he ▸ hy

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.Noncentrality
