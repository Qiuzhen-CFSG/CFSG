module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.ComponentInputs.Contracts
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.ComponentInputs.KernelNormalization
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.Basic

/-!
# C.2.7 inputs in the characteristic-two Sylow branch

For the contrary overgroup H=KU, put R=O₂(XU) and M_H=H∩N_G(X).
The complete embedding witness is retained, including the original 1.3.4
clauses and the full automorphism-group or exchanged rank-one refinement.
CPU supplies C.2.3 with its genuine relative normal-closure Sylow condition.

In the invariant case the H-normal closure identity makes K normal in H.
In the exchanged case the literal section kernel normalizes the selected
component by the complement-action argument. Both components lie outside
M_H, since containment would put KU and the given outside Y-factor in
N_G(X). Characteristic two passes from K to H and then to the relatively
subnormal selected component. The intrinsic quotient is transported from
the quasisimple clause of the complete embedding output.

`contrary_hypotheses` is the conditional input construction for C.2.7;
it does not prove the embedding alternatives, perform the block sieve,
or assert the final contradiction. `Contracts` supplies the intrinsic KR,
M_K and KR/C_KR(Ω₁(Z(O₂(KR)))) for the downstream application.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
1.3.4, printed pp.509–511; C.2.3 and C.2.7, pp.144–147;
and the characteristic-two paragraph of 15.4.20, p.1164.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.ComponentInputs
universe u
variable {G : Type u} [Group G]

/-- The genuine placed geometry and residual replacement, before the
characteristic-two branch. In particular the source omega-center, Thompson
group, and uniqueness subgroup retain their actual meanings. -/
structure ContraryContext (d : Source.Geometry G) (i j : Bool) (H K U : Subgroup G) where
  placed : EmbeddingReduction.PlacedX d i j H U
  normal_closure : K = EmbeddingReduction.normalClosureIn d.wholeX H
  residual : K = (primeToResidual 3 H).map H.subtype
  generation : K ⊔ U = H
  omega : d.Z = omegaOneCenterAmbient (d.T : Subgroup G)
  thompson : d.J = elementaryAbelianMaxJ (d.T : Subgroup G)
  unique : ∀ N : Subgroup G, IsMaximalTwoLocal N → d.wholeX ⊔ (d.T : Subgroup G) ≤ N → N = d.M₁

/-- The full nonnormal output witness of 1.3.4, together with the two
refinements on p.1164. The `source` field retains every clause of
`XiEmbedding.Conclusion`, including its quasisimple quotient, the actual
plane isomorphism, the split complement and model parameter restrictions.
The embedding/residual owner constructs this input; R-normalization,
characteristic two and the C.2.7 input are not fields of this record. -/
structure EmbeddingWitness (d : Source.Geometry G) (H K U : Subgroup G)
    (P : Sylow 3 d.wholeX) where
  seed : Subgroup G
  source : seed ∈ Chapter1.cComponentsIn H ∧
    IsQuasisimple (Chapter1.XiQuotient seed) ∧
    d.wholeX ≤ componentOrbit seed U ∧
    Chapter1.XiEmbedding.Alternatives 3 U ((P : Subgroup d.wholeX).map d.wholeX.subtype) seed
  refinement :
    (seed = K ∧ ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
        Nonempty ((H ⧸ pCore 2 H) ≃*
          MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) F))) ∨
    ∃ r : G, r ∈ U ∧ r ∉ normalizer (seed : Set G) ∧
      seed ⊔ seed.map (MulAut.conj r).toMonoidHom = K

variable [Finite G]

/-- Retain the entire exchanged alternative, including its split complement,
exact model parameters, and literal component product. The component layer
supplies the normalization needed to turn the join into that product. -/
theorem EmbeddingWitness.exchanged_output
    {d : Source.Geometry G} {H K U : Subgroup G} {P : Sylow 3 d.wholeX}
    (e : EmbeddingWitness d H K U P) (hUH : U ≤ H)
    {r : G} (hr : r ∈ U) (hmove : r ∉ normalizer (e.seed : Set G))
    (hprod : e.seed ⊔ e.seed.map (MulAut.conj r).toMonoidHom = K) :
    Chapter1.XiEmbedding.SwappedFactors U
        ((P : Subgroup d.wholeX).map d.wholeX.subtype) e.seed ∧
      Chapter1.XiEmbedding.SwappedModel 3 (Chapter1.XiQuotient e.seed) ∧
      (K : Set G) = (e.seed : Set G) *
        (e.seed.map (MulAut.conj r).toMonoidHom : Set G) := by
  have hs : Chapter1.XiEmbedding.SwappedFactors U
        ((P : Subgroup d.wholeX).map d.wholeX.subtype) e.seed ∧
      Chapter1.XiEmbedding.SwappedModel 3 (Chapter1.XiQuotient e.seed) := by
    rcases e.source.2.2.2.2 with hs | ⟨hn, _⟩
    · exact hs
    · exact (hmove (hn hr)).elim
  have hn : e.seed.map (MulAut.conj r).toMonoidHom ≤ normalizer (e.seed : Set G) :=
    (le_iSup (fun u : U => e.seed.map (MulAut.conj (u : G)).toMonoidHom) ⟨r, hr⟩).trans
      (Chapter1.XiEmbedding.cComponentOrbit_le_normalizer e.source.1 hUH)
  refine ⟨hs.1, hs.2, ?_⟩
  exact (congrArg (fun S : Subgroup G => (S : Set G)) hprod.symm).trans
    (coe_mul_of_right_le_normalizer_left _ _ hn)

/-- Construct every C.2.7 hypothesis for the component supplied by the
complete embedding output, in both alternatives. Intrinsic quasisimplicity
is transported from the genuine 1.3.4 conclusion; it is not an extra
hypothesis on the characteristic-two branch. CPU constructs C.2.3,
normal closure supplies relative normality of K, subnormal inheritance
supplies characteristic two for the selected component, and the marked
factor action proves the exchanged component's R-invariance. -/
theorem contrary_hypotheses {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    {d : Source.Geometry G} {i j : Bool} {H K U : Subgroup G}
    (c : ContraryContext d i j H K U) (P : Sylow 3 d.wholeX)
    (e : EmbeddingWitness d H K U P)
    (hF : generalizedFitting K = pCore 2 K) :
    let R := (d.wholeX ⊔ U : Subgroup G).pCoreIn 2
    let M := H ⊓ d.M₁
    Hypotheses κ (R.subgroupOf H) (M.subgroupOf H) (e.seed.subgroupOf H) := by
  let X := d.wholeX
  let R := (X ⊔ U : Subgroup G).pCoreIn 2
  let M := H ⊓ d.M₁
  have hXH : X ≤ H := c.placed.whole_le
  have hUH : U ≤ H := c.placed.sylow_image ▸ map_subtype_le (c.placed.sylow : Subgroup H)
  have hUM : U ≤ d.M₁ := c.placed.upper.le.trans c.placed.T_normalizes
  have hXM : X ≤ M := le_inf hXH X.le_normalizer
  have hUMH : U ≤ M := le_inf hUH hUM
  obtain ⟨hsq, hne, hRH, hRp, hrad, hcontrol, hsylow⟩ :=
    contrary_pushing_up_inputs hG d.T c.placed.overgroup.1 hXH
      c.placed.upper.le c.placed.upper_index c.placed.T_normalizes
      c.placed.core_nontrivial c.unique c.placed.sylow c.placed.sylow_image
  change R ≤ H at hRH
  change R ≠ ⊥ at hne
  have hRne : R.subgroupOf H ≠ ⊥ := by
    intro hb
    have he := congrArg (Subgroup.map H.subtype) hb
    exact hne (by simpa only [map_subgroupOf_eq_of_le hRH, Subgroup.map_bot] using he)
  have hsylow' : Chapter1.IsSylowIn 2 (R.subgroupOf H)
      (conjugateModule (M.subgroupOf H) (R.subgroupOf H)) := by
    apply (Chapter1.IsSylowIn.map_iff H.subtype H.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hRH, conjugateModule_subgroupOf_map inf_le_left hRH]
    exact hsylow
  have hcpu : PushingUpHypotheses κ (R.subgroupOf H) (M.subgroupOf H) :=
    ⟨hsq, hRne, hRp.comap_subtype, hrad, hcontrol, hsylow'⟩
  have hKH : K ≤ H := c.normal_closure ▸ EmbeddingReduction.normalClosureIn_le_overgroup X H
  have hKn : (K.subgroupOf H).Normal :=
    c.normal_closure ▸ EmbeddingReduction.normalClosureIn_normal X H
  have hHK : H ≤ normalizer (K : Set G) := (normal_subgroupOf_iff_le_normalizer hKH).mp hKn
  obtain ⟨hKn', hgen, hKF⟩ := source_core_inputs hKH hHK c.placed.sylow
    c.placed.sylow_image c.generation hF
  let _ := hKn'
  have hHF : generalizedFitting H = pCore 2 H :=
    generalizedFitting_eq_twoCore _ c.placed.sylow hgen hKF
  obtain ⟨hL, hq, hXorbit, ha⟩ := e.source
  have hLq : IsQuasisimple ((e.seed.subgroupOf H) ⧸ pCore 2 (e.seed.subgroupOf H)) := by
    let eqv := (subgroupOfEquivOfLe hL.1).symm
    let _ := hq
    exact IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ eqv (pCore_map_iso 2 eqv))
  have hLF : generalizedFitting (e.seed.subgroupOf H) = pCore 2 (e.seed.subgroupOf H) :=
    generalizedFitting_eq_twoCore_of_subnormal _ hL.2.subnormal hHF
  have hYH : d.Y j ≤ H := (d.Y_le_I i j).trans c.placed.overgroup.2
  have houtside : ¬ e.seed ≤ M := by
    rcases e.refinement with ⟨he, _⟩ | ⟨r, hr, _, hprod⟩
    · intro hLM
      have hKM : K ≤ d.M₁ := he ▸ hLM.trans inf_le_right
      have hHM : H ≤ d.M₁ := c.generation ▸ sup_le hKM hUM
      exact c.placed.outside (hYH.trans hHM)
    · exact exchanged_factor_outside c.generation hprod hr hUM hYH c.placed.outside
  have hinvariant : R ≤ normalizer (e.seed : Set G) := by
    rcases e.refinement with ⟨he, _⟩ | ⟨r, hr, hmove, _⟩
    · rw [he]
      exact hRH.trans hHK
    · have hswap : Chapter1.XiEmbedding.SwappedFactors U
          ((P : Subgroup d.wholeX).map d.wholeX.subtype) e.seed ∧
          Chapter1.XiEmbedding.SwappedModel 3 (Chapter1.XiQuotient e.seed) := by
        rcases ha.2 with hs | ⟨hn, _⟩
        · exact hs
        · exact (hmove (hn hr)).elim
      obtain ⟨_, hlocal, _, _⟩ := c.placed.embedding_input hG P
      have hkernel : R = U ⊓ ChapterA.Section04.twoSectionCentralizer X M :=
        contrary_core_eq_section_kernel hXM hUMH inf_le_left inf_le_right
          c.placed.sylow c.placed.sylow_image
      rw [hkernel]
      exact swapped_kernel_normalizes hlocal hL hq hXorbit hswap.1 hswap.2
  refine ⟨hcpu, hL.2, hLq, hLF, ?_, ?_⟩
  · intro hle
    apply houtside
    have hm := map_mono (f := H.subtype) hle
    change (e.seed.subgroupOf H).map H.subtype ≤ (M.subgroupOf H).map H.subtype at hm
    simpa only [map_subgroupOf_eq_of_le hL.1, map_subgroupOf_eq_of_le
      (show M ≤ H from inf_le_left)] using hm
  · intro r hr
    rw [← subgroupOf_normalizer_eq hL.1]
    exact hinvariant hr

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.ComponentInputs
