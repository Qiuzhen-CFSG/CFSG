module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.LinearReciprocal
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.MixedLinearIndices
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.MixedPlaneAction
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.MixedLinearCommutator
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.MixedLinearIndices
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.MixedPlaneAction

/-!
# The actual mixed linear commutator: structure at the original group

The non-FF comparison gives both fixed groups order eight. The original
plane-radical action now supplies the reverse containment in the first
fixed group, so the mixed commutator equals both literal fixed groups.
It has order eight and contains the original distinguished fixed line.

The final application uses the same original H₂,L₂T pair, U=V₀ and
conjugating element g, in every recognized six-dimensional linear row.
Original Hypothesis1331, ChosenModule, CoreMarking, Structural1222 and
Source1332OneTwo remain explicit. MixedLinearStability proves the ensuing
normalization step; the later block, product and graph exclusions remain
with the nonsolvable assembly.
Source: Aschbacher--Smith 13.4.15, printed p.912, refs/quasithin.pdf.

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/MixedLinearCommutator` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 BinaryConjugationCoordinates
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- In a noncommuting mixed pair both literal fixed groups equal the same
commutator, and the original fixed line is contained in it. -/
theorem mixed_nonFF_commutator_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (W : Submodule (ZMod 2) (natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hT : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (H U : Subgroup G) [IsElementaryAbelian 2 U]
    (hHU : H ≤ normalizer (U : Set G))
    (hn : ¬ Representation.BinaryOffender.IsFFModule
      (Representation.BinaryOffender.imageRepresentation (elementaryRepresentation (p := 2)
        (U.normalizerMonoidHom.comp (inclusion hHU)))))
    (hcard : Nat.card U = 64)
    (g : G)
    (h₁ : U.conjBy g ≤ ((L ⊔ (T : Subgroup G)) ⊓ normalizer
      (m.naturalPreimage W : Set G) : Subgroup G).pCoreIn 2)
    (h₂ : V ≤ H.conjBy g)
    (hm : ⁅V,U.conjBy g⁆ ≠ ⊥) :
    ⁅V,U.conjBy g⁆ = V ⊓ centralizer (U.conjBy g : Set G) ∧
      ⁅V,U.conjBy g⁆ = U.conjBy g ⊓ centralizer (V : Set G) ∧
      Nat.card (⁅V,U.conjBy g⁆ : Subgroup G) = 8 ∧ V ⊓ centralizer (L : Set G) ≤ ⁅V,U.conjBy g⁆ := by
  have hBN : ((L ⊔ (T : Subgroup G)) ⊓ normalizer
      (m.naturalPreimage W : Set G) : Subgroup G) ≤ normalizer (L : Set G) :=
    inf_le_left.trans (sup_le L.le_normalizer D.sylow_normalizes_component)
  obtain ⟨_,hi,hcV,hcU,hc⟩ := mixed_nonFF_centralizers_at h structural D m H U hHU hn hcard
    g (h₁.trans ((pCoreIn_le 2 _).trans hBN)) h₂ hm
  obtain ⟨hr,hZ⟩ := original_plane_actor_fixed_le_commutator_at h structural D m W hW hT
    (U.conjBy g) h₁ hi
  have heV := le_antisymm (hc.trans inf_le_left) hr
  have hcommcard : Nat.card (⁅V,U.conjBy g⁆ : Subgroup G) = 8 := by rw [heV,hcV]
  exact ⟨heV,eq_of_le_of_card_ge (hc.trans inf_le_right) (by rw [hcommcard,hcU]),hcommcard,hZ⟩


open Stellmacher Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
variable {A B : Subgroup G}

/-- The literal original H₂,L₂T pair in every linear module row supplies
both commutator equalities and the fixed-line placement in source 13.4.15. -/
theorem original_linear_pair_mixed_commutator_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (hlin : Solvable.LinearAmalgamConclusion T (A ⊔ B))
    (W : Submodule (ZMod 2) (natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)) :
    let X := A ⊔ B
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
    ∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → V ≤ (B.pCoreIn 2).conjBy g →
      ⁅V,U.conjBy g⁆ ≠ ⊥ →
      ⁅V,U.conjBy g⁆ = V ⊓ centralizer (U.conjBy g : Set G) ∧
      ⁅V,U.conjBy g⁆ = U.conjBy g ⊓ centralizer (V : Set G) ∧
      Nat.card (⁅V,U.conjBy g⁆ : Subgroup G) = 8 ∧ V ⊓ centralizer (L : Set G) ≤ ⁅V,U.conjBy g⁆ := by
  obtain ⟨he,hn,hcard,_⟩ := original_linear_pair_module_nonFF_at h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 hlin
  let := he
  dsimp only
  intro g h₁ h₂ hm
  exact mixed_nonFF_commutator_at h structural D m W hW hTW (A ⊔ B)
    (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B))
    (le_normalizer_conjugateSpanBy _ _) hn hcard g (hB ▸ h₁)
    (h₂.trans (map_mono ((pCoreIn_le 2 B).trans le_sup_right))) hm

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
