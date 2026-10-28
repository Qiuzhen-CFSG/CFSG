module
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceNaturalMarking
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceNormalizerProduct
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceSeedNormalizer

/-!
# Source normalizers from the constructed natural marking

The original F.9 action kernel and |U_H|=32 now supply the marked natural
four-space internally. The actual K₂ is a C-component of G₂, both intrinsic
factor maps give G₂/O₂(G₂)≃PSL₃(2)×S₃, and G₂=⟨K₂,L₂,₊,T⟩. The original
I₂ normality, symmetric quotient and transitivity remain the earlier local
inputs. The same construction supplies the literal seed normalizer and the
centralizer index four, without a separate natural-marking premise. The
constructed dual coordinates preserve the same natural point and the
commutator pairing on the original Q_H/H_C.

The compatible exterior and tensor markings, extra-line movement, three
chief factors on H_C/V_H and the full 13.8.31 obstruction remain with the
linear-four owner. These results do not establish full 13.8.28. Earlier
13.8.27 remains with qt-d-138-six-g2-source, and final source assembly with
qt-d-1381-source.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
13.8.29(1--2),13.8.32 and the proof of13.8.28, printed pp.964--966.
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative commutatorElement
open BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]

/-- The original orders construct the natural marking used to identify both G₂ factors. -/
theorem source_normalizer_factors_of_original_order
    (F : ChapterF.Section09.Setup G) (hF : F.Hypothesis)
    [IsElementaryAbelian 2 F.UH]
    (hU : Nat.card F.UH = 32)
    (e₀ : (F.H ⧸ pCore 2 F.H) ≃* LinearGroup 4)
    (V2 L2plus : Subgroup G) (h12 : F.V₁ ≤ V2)
    (h2U : V2 ≤ Source.UH F.H F.Vplus)
    (hT2 : (F.T : Subgroup G) ≤ G2 V2)
    (hH : F.H = normalizer (F.V₁ : Set G))
    (h2 : Nat.card V2 = 4)
    (I : Subgroup (G2 V2)) [I.Normal]
    (eI : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3))
    (hI : I.map (G2 V2).subtype = F.H.pCoreIn 2 ⊔ L2plus)
    (ht : ∀ a b : V2, a ≠ 1 → b ≠ 1 →
      ∃ i : I, ((i : G2 V2) : G) * (a:G) * ((i : G2 V2) : G)⁻¹ = b) :
    ((K2 F.H V2).subgroupOf (G2 V2)).IsCComponent ∧
    G2 V2 = K2 F.H V2 ⊔ L2plus ⊔ (F.T : Subgroup G) ∧
    ∃ (eK : (K2 F.H V2 ⧸ pCore 2 (K2 F.H V2)) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
      (e : (G2 V2 ⧸ pCore 2 (G2 V2)) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) × Equiv.Perm (Fin 3)),
      (∀ k : K2 F.H V2, e (QuotientGroup.mk' (pCore 2 (G2 V2))
        (inclusion ((K2_le_localNormalizer F.H V2).trans inf_le_right) k)) =
        (eK (QuotientGroup.mk' (pCore 2 (K2 F.H V2)) k),1)) ∧
      ∀ i : I, e (QuotientGroup.mk' (pCore 2 (G2 V2)) i) =
        (1,eI (QuotientGroup.mk' (pCore 2 I) i)) := by
  let : IsElementaryAbelian 2 (Source.UH F.H F.Vplus) := ‹IsElementaryAbelian 2 F.UH›
  obtain ⟨ρ,d,π,hker,honto,hnatural,hpoint⟩ :=
    source_natural_point_marking F hF hU e₀ V2 h12 h2U h2
  let φ := (slEquivLinear 4).toMonoidHom.comp π
  have hφ : Function.Surjective φ := (slEquivLinear 4).surjective.comp honto
  have hnat : ∀ h x, ρ h x = φ h x := fun h x =>
    (hnatural h x).trans (slEquivLinear_apply 4 (π h) x).symm
  have hk : IsPGroup 2 φ.ker := by
    dsimp only [φ]
    rw [MonoidHom.ker_comp_of_injective _ _ (slEquivLinear 4).injective,hker]
    exact (isPGroup_pCoreIn 2 F.H).comap_subtype
  have hv : (Pi.single 0 1 : Space 4) ≠ 0 := by
    intro he
    have hh := congrFun he 0
    simp at hh
  exact source_normalizer_factors F hF V2 L2plus h12 h2U hT2 hH
    ρ d φ hφ hnat hk (Pi.single 0 1) hv hpoint I eI hI ht

/-- The actual source seed normalizer needs no supplied natural module marking. -/
theorem source_seed_normalizer_eq_of_original_order
    (F : ChapterF.Section09.Setup G) (hF : F.Hypothesis)
    [IsElementaryAbelian 2 F.UH]
    (hU : Nat.card F.UH = 32)
    (e₀ : (F.H ⧸ pCore 2 F.H) ≃* LinearGroup 4)
    (V2 M G1 : Subgroup G)
    (s : SourceCompletion.NaturalSetup F.T F.L F.V F.V₁ V2 F.Vplus M G1)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple F.T F.L)
    (hHz : F.H ∈ Source.Hz (sourceOne F.L F.T F.V₁) F.T G1 M)
    (hcentral : centralizer (F.Vplus:Set G) ≤ M ⊓ normalizer (F.V:Set G)) :
    F.H ⊓ normalizer (F.Vplus:Set G) = sourceOne F.L F.T F.V₁ ⊔ (F.T:Subgroup G) := by
  let : IsElementaryAbelian 2 (Source.UH F.H F.Vplus) := ‹IsElementaryAbelian 2 F.UH›
  obtain ⟨ρ,d,π,hker,_,hnatural,_⟩ := source_natural_point_marking F hF hU e₀ V2
    s.line_le_plane (s.plane_le_seed.trans (le_conjugateSpanBy _ _)) s.plane_card
  exact source_seed_normalizer_eq s h hHz hcentral ρ d π hker hnatural

/-- The centralizer index follows from the original orders and action kernel. -/
theorem source_seed_centralizer_index_of_original_order
    (F : ChapterF.Section09.Setup G) (hF : F.Hypothesis)
    [IsElementaryAbelian 2 F.UH]
    (hU : Nat.card F.UH = 32)
    (e₀ : (F.H ⧸ pCore 2 F.H) ≃* LinearGroup 4)
    (V2 : Subgroup G) (h12 : F.V₁ ≤ V2) (h2U : V2 ≤ F.UH) (h2 : Nat.card V2 = 4)
    (hseedQ : ⁅F.Vplus,Source.QH F.H⁆ ≠ ⊥) (hseedcard : Nat.card F.Vplus = 8) :
    (Source.QH F.H ⊓ centralizer (F.Vplus:Set G)).relIndex (Source.QH F.H) = 4 := by
  let : IsElementaryAbelian 2 (Source.UH F.H F.Vplus) := ‹IsElementaryAbelian 2 F.UH›
  obtain ⟨ρ,d,π,hker,honto,hnatural,_⟩ := source_natural_point_marking F hF hU e₀ V2 h12 h2U h2
  exact source_seed_centralizer_index_four F hF ρ d π hker honto hnatural hseedQ hseedcard

/-- Construct compatible natural and dual coordinates for the literal commutator pairing. -/
theorem source_natural_dual_marking_of_original_order
    (F : ChapterF.Section09.Setup G) (hF : F.Hypothesis)
    [IsElementaryAbelian 2 F.UH]
    (hU : Nat.card F.UH = 32)
    (e₀ : (F.H ⧸ pCore 2 F.H) ≃* LinearGroup 4)
    (V2 : Subgroup G) (h12 : F.V₁ ≤ V2) (h2U : V2 ≤ F.UH) (h2 : Nat.card V2 = 4)
    (hseedQ : ⁅F.Vplus,Source.QH F.H⁆ ≠ ⊥) :
    ∃ (ρ : Representation (ZMod 2) F.H (Space 4))
      (d : BinaryConjugationSection F.H F.UH F.V₁ ρ)
      (π : F.H →* SL(4,ZMod 2))
      (ddual : BinaryConjugationSection F.H (Source.QH F.H) (Source.HC F.H F.Vplus) ρ.dual),
      π.ker = (Source.QH F.H).subgroupOf F.H ∧ Function.Surjective π ∧
      (∀ h w, ρ h w = Matrix.mulVec (π h).val w) ∧
      d.imageSpace V2 = Submodule.span (ZMod 2) {Pi.single 0 1} ∧
      ∀ (q : Source.QH F.H) (u : F.UH),
        (ddual.coordinates q).toAdd (d.coordinates u).toAdd = 0 ↔ ⁅(q:G),(u:G)⁆ = 1 := by
  let : IsElementaryAbelian 2 (Source.UH F.H F.Vplus) := ‹IsElementaryAbelian 2 F.UH›
  obtain ⟨ρ,d,π,hker,honto,hnatural,hpoint⟩ := source_natural_point_marking F hF hU e₀ V2 h12 h2U h2
  obtain ⟨ddual,hpair⟩ := source_natural_core_duality F hF ρ d π hker honto hnatural hseedQ
  exact ⟨ρ,d,π,ddual,hker,honto,hnatural,hpoint,hpair⟩

end CFSG.Quasithin.Chapter13.Section08.LinearFour
