module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.SimpleSocle
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.MinimalNormal

/-!
# The simple-socle reduction on the same marked quotient

The characteristic-two marked parabolics and unipotent normal generation
already make O²(X/D) the unique nontrivial minimal normal subgroup. If this
residual is perfect, the finite characteristically-simple theorem gives a
positive simple power. A faithful perfect local factor with the rank-one
Sylow-normalizer properties, normalized by the full specified U, then reduces
that power to one component by SimpleSocle.

The earlier split, local and perfectness premises are explicit; none includes
a recognition conclusion or a classification callback. The source adapter
discharges the local premises from F.1.1 and the original perfect factors.
Only X/D must be finite, so this applies also to the finite geometric quotient
of an infinite universal completion, without any descent to an actual
ambient subgroup. All marked quotient, endpoint and Borel maps are retained.

Source: the minimal-configuration reduction in DGS, Groups and Graphs,
Part II, pp.80–81 and Theorem D on p.224. This proves simplicity of the
residual, not the remaining minimal configuration or marked Lie comparisons.
-/

public noncomputable section
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.MarkedQuotient
variable {X A : Type*} [Group X] [Group A] [Finite A]
  [Nontrivial A] [Group.IsPerfect A] {P : Fin 2 → Subgroup X}

/-- A carrier-general simple-socle reduction for a finite marked quotient.
The numerator X may be an infinite universal completion. -/
theorem twoResidual_isSimple_of_local_factor (d : MarkedQuotient P)
    (split : SplitData d.tits)
    (hc : ∀ i, centralizer (pCore 2 (d.tits.standardParabolic {d.simple i}) :
      Set (d.tits.standardParabolic {d.simple i})) ≤
      pCore 2 (d.tits.standardParabolic {d.simple i}))
    (hgen : split.unipotentClosure = ⊤)
    (hp : Group.IsPerfect (pResidual 2 (X ⧸ d.D)))
    (f : A →* X ⧸ d.D) (hf : Function.Injective f)
    (hfK : f.range ≤ pResidual 2 (X ⧸ d.D))
    (hn : split.U ≤ normalizer (f.range : Set (X ⧸ d.D))) (T : Sylow 2 A)
    (hTU : (T : Subgroup A).map f ≤ split.U)
    (hproper : normalizer (T : Set A) < ⊤)
    (hunique : ∀ M : Subgroup A, (T : Subgroup A) ≤ M → M < ⊤ →
      M ≤ normalizer (T : Set A))
    (hsolv : Group.IsSolvable (normalizer (T : Set A))) :
    IsSimpleGroup (pResidual 2 (X ⧸ d.D)) := by
  obtain ⟨C, hC, _, n, _, ⟨e⟩⟩ := d.twoResidual_simple_power split hc hgen hp
  let := hC
  exact simple_of_simple_power_local_factor _ split.sylow
    (d.normal_subgroup_sup_unipotent split hc hgen _ (d.twoResidual_ne_bot split))
    (fun V hV hn => @twoResidual_le_normal _ _ _ d split hc hgen V hV hn)
    e f hf hfK hn T hTU (local_normalClosure_eq_top T hproper hunique)
    (fun N hN hne => @local_proper_normal_solvable _ _ _ inferInstance T
      hunique hsolv N hN hne)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.MarkedQuotient

