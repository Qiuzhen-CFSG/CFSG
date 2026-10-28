module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.CoreActions
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.RadicalStabilizers.Source

/-!
# Complete orbit and core facts for the deleted S₅ module

The original LT-action has exactly its literal conjugation kernel. The
five-letter core lemma therefore makes O₂(XT) centralize U. Together with
the proved selected orbits and radical stabilizers this constructs the
OrbitFacts used by the original centralizer analysis.

Source: Aschbacher--Smith 13.1.12(1--2) and its proof, pp.872--873.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
open Chapter1 Chapter1.Section02 Chapter12.Section02
open SourceCentralizerStructure.Elimination
namespace SymmetricFiveMarking
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} (d : SymmetricFiveMarking T L)
include d

omit [Finite G] in
/-- The S₅ marking identifies the full original action image, not just L. -/
theorem quotient_kernel : d.quotient.ker =
    (centralizer (normalizerMoved L : Set G)).subgroupOf (L ⊔ (T : Subgroup G)) := by
  ext a
  rw [MonoidHom.mem_ker]
  constructor
  · intro ha u hu
    have he := d.equivariant a ⟨u,hu⟩
    rw [ha,map_one] at he
    have he' := congrArg Subtype.val (d.coordinates.injective he)
    change (a : G) * u * (a : G)⁻¹ = u at he'
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  · intro ha
    apply naturalMulAction_injective_of_odd (Fin 5) (by decide)
    rw [map_one]
    apply MulEquiv.ext
    intro w
    obtain ⟨u,rfl⟩ := d.coordinates.surjective w
    rw [← d.equivariant]
    apply congrArg d.coordinates
    apply Subtype.ext
    change (a : G) * (u : G) * (a : G)⁻¹ = (u : G)
    have hc : (u : G) * (a : G) = (a : G) * (u : G) := ha u u.property
    rw [← hc,mul_inv_cancel_right]

/-- The whole original two-core fixes the deleted module. -/
theorem source_core_centralizes {p : ℕ} [Fact p.Prime] (h : Context T L p) :
    (XiP p L ⊔ (T : Subgroup G)).pCoreIn 2 ≤
      centralizer (normalizerMoved L : Set G) :=
  radicalCore_centralizes_of_five_image h.hypothesis h.many h.maximal
    h.nonquasisimple h.odd h.divides d.quotient d.quotient_kernel d.component

/-- The literal orbit consumer, with all model orbit and core premises discharged. -/
theorem orbitFacts {p : ℕ} [Fact p.Prime] (h : Context T L p) : OrbitFacts T L p where
  irreducible _ hu hne _ := d.radical_irreducible h hu hne
  index u s := (d.centralizer_orbit h.hypothesis h.maximal h.nonquasisimple
    ⟨u,s.mem⟩ (fun he => s.ne_one (congrArg Subtype.val he)) s.local_sylow).1
  core_action _ _ _ := inf_le_left.trans (d.source_core_centralizes h)

/-- The original fixed-core equality for the pushing-up consumer. -/
theorem core_centralizer_eq {p : ℕ} [Fact p.Prime] (h : Context T L p)
    {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G)) :
    centralizerCore T L p u =
      (XiP p L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer (normalizerMoved L : Set G) :=
  h.core_eq_fixed (d.orbitFacts h) s hnt

end SymmetricFiveMarking
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
