module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.BorelAction
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Lifting.Transport
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.QuotientAction
public import Theory.SpecificGroups.Suzuki.BorelResidualRigidity
public import Theory.GroupTheory.PCoreImage

/-!
# Full Suzuki Borel fixation on the original terminal section

For a normal local component A contained in H, its two-core lies in O₂(H).
Thus the literal conjugation action on U_H/V₁ factors through A/O₂(A).
The two-residual of the lifted Sylow normalizer covers the entire quotient
Borel. Its proved centralization of the original A₅ module therefore fixes
every V₃ seed in that quotient action. A compatible matrix marking retains
this full-Borel fixation without changing representatives or the kernel.

The source-pair application discharges the residual-centralization premise.
Semisimplicity and the terminal component exclusion are separate consumers.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.6.27 and
Notation 13.5.8, printed pp.918,934–935; F.9.2(3), printed p.318.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
open ChapterF.Source Section08 Ratio
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H A : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]
  (hn : H ≤ normalizer (V₁ : Set G))
  (hk : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H)
  (hAH : A ≤ H) (hHA : H ≤ normalizer (A : Set G))

/-- The actual component quotient acts on the original central section. -/
def componentQuotientRepresentation : Representation (ZMod 2) (A ⧸ pCore 2 A) (Space H V₃ V₁) :=
  QuotientGroup.lift (pCore 2 A)
    ((representation H V₃ V₁ hn).comp (inclusion hAH)) (by
      intro a ha
      have hh := pCoreIn_mono_of_normalizes (p := 2) hAH hHA
        (mem_map_of_mem A.subtype ha)
      obtain ⟨b,hb,he⟩ := hh
      have he' : inclusion hAH a = b := Subtype.ext he.symm
      change inclusion hAH a ∈ (representation H V₃ V₁ hn).ker
      rw [ker_eq_pCore H V₃ V₁ hn hk, he']
      exact hb)

omit [Finite G] in
theorem componentQuotientRepresentation_mk (a : A) :
    componentQuotientRepresentation hn hk hAH hHA (QuotientGroup.mk' (pCore 2 A) a) =
      representation H V₃ V₁ hn (inclusion hAH a) := QuotientGroup.lift_mk _ _ a

/-- A lifted Suzuki Borel residual fixing the original seed fixes it through
its full quotient Borel in the literal U_H/V₁ action. -/
theorem quotient_borel_fixes_seed
    {m : ℕ} (hm : 1 ≤ m)
    (e : (A ⧸ pCore 2 A) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (P : Sylow 2 A)
    (hfix : ((pResidual 2 (normalizer (P : Set A))).map
      (normalizer (P : Set A)).subtype).map A.subtype ≤ centralizer (V₃ : Set G))
    (a : G) (ha : a ∈ V₃)
    (b : A ⧸ pCore 2 A)
    (hb : b ∈ normalizer ((P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 A))) :
      Set (A ⧸ pCore 2 A))) :
    componentQuotientRepresentation hn hk hAH hHA b
      (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))
        ⟨a,le_conjugateSpanBy V₃ H ha⟩)) =
      Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))
        ⟨a,le_conjugateSpanBy V₃ H ha⟩) := by
  rw [← BenderSuzuki.MatrixGroups.suzuki_borelResidual_quotient_image (by omega) e P] at hb
  obtain ⟨r,hr,rfl⟩ := hb
  rw [componentQuotientRepresentation_mk, representation_apply]
  apply congrArg Additive.ofMul
  apply congrArg (QuotientGroup.mk' _)
  apply Subtype.ext
  change r.val * a * r.val⁻¹ = a
  exact mul_inv_eq_iff_eq_mul.mpr
    ((mem_centralizer_iff.mp (hfix (mem_map_of_mem A.subtype hr))) a ha).symm

variable (d : Section05.A5Source.Context T L V V₁ V₂ V₃)

include d in
/-- The full quotient Borel fixation for the actual source pair, with its
residual-fixation premise discharged by the original marked A₅ module. -/
theorem source_pair_quotient_borel_fixes_seed
    (hF : HypothesisF11 ![L,A] (T : Subgroup G))
    {z : G} (hz : zpowers z = V₁) (hAC : A ≤ centralizer ({z} : Set G))
    {m : ℕ} (hm : 1 ≤ m)
    (e : (A ⧸ pCore 2 A) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    ∃ P : Sylow 2 A,
      (P : Subgroup A).map A.subtype = (T : Subgroup G) ⊓ A ∧
      ∀ (a : G) (ha : a ∈ V₃) (b : A ⧸ pCore 2 A),
      b ∈ normalizer ((P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 A))) :
        Set (A ⧸ pCore 2 A)) →
      componentQuotientRepresentation hn hk hAH hHA b
        (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))
          ⟨a,le_conjugateSpanBy V₃ H ha⟩)) =
        Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))
          ⟨a,le_conjugateSpanBy V₃ H ha⟩) := by
  obtain ⟨P,hP⟩ : ∃ P : Sylow 2 A,
      (P : Subgroup A).map A.subtype = (T : Subgroup G) ⊓ A := hF.sylow 1
  refine ⟨P,hP,?_⟩
  apply quotient_borel_fixes_seed hn hk hAH hHA hm e P
  have hNA : (normalizer (P : Set A)).map A.subtype = borel A (T : Subgroup G) := by
    change (sylowNormalizer P).map A.subtype = _
    rw [← borel_subgroupOf_eq_sylowNormalizer A (T : Subgroup G) P hP]
    exact map_subgroupOf_eq_of_le (borel_le _ _)
  rw [map_embedded_pResidual,hNA]
  exact (suzuki_borel_residual_centralizes d A hF hz hAC hm e).trans
    (centralizer_le d.third_le)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation

namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
open ChapterF.Source Section08 Ratio BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H A : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]
  (hn : H ≤ normalizer (V₁ : Set G))
  (hk : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H)
  (hAH : A ≤ H) (hHA : H ≤ normalizer (A : Set G))

/-- The original seed's image in its literal central quotient. -/
def seedVector (a : V₃) : Space H V₃ V₁ :=
  Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))
    ⟨a.val,le_conjugateSpanBy V₃ H a.property⟩)

variable (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d in
/-- A compatible matrix marking makes the full standard Borel fix every
original seed vector, preserving the actual quotient action. -/
theorem source_pair_borel_marking
    (hF : HypothesisF11 ![L,A] (T : Subgroup G))
    {z : G} (hz : zpowers z = V₁) (hAC : A ≤ centralizer ({z} : Set G))
    {m : ℕ} (hm : 1 ≤ m)
    (e : (A ⧸ pCore 2 A) ≃* SuzukiMatrixGroup m) :
    ∃ f : SuzukiMatrixGroup m ≃* (A ⧸ pCore 2 A),
      ∀ a : V₃, ∀ g ∈ SuzukiBorelSubgroup m,
        componentQuotientRepresentation hn hk hAH hHA (f g)
          (seedVector (H := H) (V₁ := V₁) a) = seedVector (H := H) (V₁ := V₁) a := by
  obtain ⟨P,_,hfix⟩ := source_pair_quotient_borel_fixes_seed hn hk hAH hHA d hF hz hAC hm e
  obtain ⟨f,_,hB⟩ := suzukiSylow_aligned_equiv (by omega) e
    (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 A)))
  refine ⟨f,fun a g hg => ?_⟩
  apply hfix a.val a.property
  rw [← hB]
  exact mem_map_of_mem f.toMonoidHom hg

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
