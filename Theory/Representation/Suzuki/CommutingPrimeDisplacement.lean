module
public import Theory.Representation.Suzuki.SupportMultiplicity
public import Theory.Representation.BinaryPrimeDisplacement
public import Theory.Representation.BinaryOffender.NormalOddSeed

/-!
# Odd-prime displacement under a commuting Suzuki group

A nontrivial odd-prime cyclic action has a simple submodule in its moved
space of degree at least the multiplicative order of two modulo the prime.
The fixed-free commuting Suzuki group forces at least three copies of that
submodule. Its orbit remains inside the same canonical moved space, so the
odd-prime displacement pays three times the binary prime degree.

This bound is used on an exchanged component commutator in Chapter D and
then on the original central Hall quotient-action kernel in Chapter 10.
It assumes neither irreducibility of the full representation nor a faithful
ambient action; only the specified prime element must act nontrivially.
Source: Aschbacher--Smith D.3.9, pp.200--201, and G.7.1, p.347.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace Representation.Suzuki
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A commuting Suzuki group triples the binary odd-prime displacement bound. -/
theorem commuting_prime_triple_displacement
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G)
    (hfix : fixedSpace ρ K = ⊥)
    (m : ℕ) (hm : 0 < m) (e : K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (y : G) (hy : orderOf y = p) (hne : ρ y ≠ 1)
    (hc : K ≤ centralizer (zpowers y : Set G)) :
    3 * orderOf (2 : ZMod p) ≤ fixedCodim ρ (zpowers y) := by
  let : Fact p.Prime := ⟨hp⟩
  let P := zpowers y
  have hcard : Nat.card P = p := (Nat.card_zpowers y).trans hy
  let : IsSimpleGroup P := isSimpleGroup_of_prime_card hcard
  have hodd : Odd (Nat.card P) := hcard ▸ hp.odd_of_ne_two hp2
  let M := subspaceCommutator ρ ⊤ P
  have hPM : P ≤ subspaceStabilizer ρ M :=
    subspaceCommutator_invariant ρ ⊤ P
  let U := invariantSubspace ρ P M hPM
  have hMn : U ≠ ⊥ := by
    intro hz
    have hM0 : M = ⊥ := congrArg Subrepresentation.toSubmodule hz
    have hh := (subspaceCommutator_eq_bot_iff ρ ⊤ P).mp hM0
    apply hne
    ext v
    exact hh Submodule.mem_top ⟨y,mem_zpowers y⟩
  obtain ⟨I,hI,hIU⟩ := (eq_bot_or_exists_atom_le U).resolve_left hMn
  have hi : I.toRepresentation.IsIrreducible := (Subrepresentation.irreducible_iff_isAtom I).mpr hI
  have hcomp : IsCompl (fixedSpace ρ P) M := by
    simpa only [M,RegularCyclicNormalClosure.displacementSpan,subspaceCommutator,eq_comm] using
      (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ) hodd)
  have hf : Function.Injective I.toRepresentation := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rcases I.toRepresentation.normal_ker.eq_bot_or_eq_top with hb | ht
    · exact hb
    · apply False.elim
      apply hI.ne_bot
      apply Subrepresentation.toSubmodule_injective
      apply bot_unique
      intro v hv
      apply Submodule.disjoint_def.mp hcomp.disjoint v
      · intro z
        have hz : z ∈ I.toRepresentation.ker := ht.symm ▸ mem_top z
        exact congrArg Subtype.val (LinearMap.congr_fun hz (⟨v,hv⟩ : I.toSubmodule))
      · exact hIU hv
  have hdeg := BinaryPrimeDegree.orderOf_le_finrank I.toRepresentation hf hp hp2
    (hcard ▸ dvd_refl p)
  have hIR : P ≤ subspaceStabilizer ρ I.toSubmodule := by
    apply le_subspaceStabilizer
    intro x hx v hv
    exact I.apply_mem_toSubmodule ⟨x,hx⟩ hv
  have hir : IsIrreducible (invariantSubspace ρ P I.toSubmodule hIR).toRepresentation := hi
  have ht := commuting_support_triple_degree ρ K hfix m hm e P hc I.toSubmodule hIR hir
  have hKM : K ≤ subspaceStabilizer ρ M :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
      (hc.trans (Subgroup.centralizer_le_normalizer _))
  have hOM : orbitSpan ρ K I.toSubmodule ≤ M := orbitSpan_le ρ hIU hKM
  have hd := Submodule.finrank_mono hOM
  have he := Submodule.finrank_add_eq_of_isCompl hcomp
  have he' := fixedCodim_add_finrank ρ P
  change fixedCodim ρ P + Module.finrank (ZMod 2) (fixedSpace ρ P) = _ at he'
  change 3 * orderOf (2 : ZMod p) ≤ fixedCodim ρ P
  omega
end Representation.Suzuki
