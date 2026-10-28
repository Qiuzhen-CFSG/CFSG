module

public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Quotient
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Constructions

/-!
# The literal substitution used in 15.3.54

In G.2.6 take L=Y, V₁=Z, V=Z-perpendicular and H=C_G(Z). Chapter 15
defines U using Z_S instead of Z-perpendicular. The earlier containments
Z_S ≤ Z-perpendicular ≤ U prove equality of these two normal closures.
Thus the generated group, core, marked intersection and middle layer
below are exactly the Chapter 15 constructions.

The conditional layer application uses the G.2.2 conclusions from
15.3.48, the natural geometry of 15.3.53 and the earlier generation step.
The source model, core product and the further collapse of the middle
layer to V are still independent obligations. In particular the legacy
`G26Witness` record is not used to prove any G.2.6 conclusion.

Source: Aschbacher–Smith, 15.3.53–54, printed pp.1145–1146,
PDF pp.1162–1163, together with G.2.6 on printed p.336.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open Setup
namespace Chapter15
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
variable {G : Type*} [Group G]

/-- Zperp is the perpendicular hyperplane supplied by the actual
orthogonal coordinates in 15.3.53. -/
def setup (Z Zperp Y T : Subgroup G) : Setup G where
  V := Zperp
  V₁ := Z
  L := Y
  T := T
  H := centralizerH Z

/-- The nontrivial closure comparison needed by the printed substitution. -/
theorem closure_eq {Z ZS Zperp Y T : Subgroup G}
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS) :
    (setup Z Zperp Y T).U = closureU Z ZS := by
  apply le_antisymm
  · exact conjugateSpanBy_le hperp (H_normalizes_closureU Z ZS)
  · exact conjugateSpanBy_mono hZS le_rfl

/-- The Chapter G first layer is the original Chapter 15 module. -/
theorem VL_eq {Z Zperp V Y T : Subgroup G} (hspan : localSpan Z Y = V) :
    (setup Z Zperp Y T).VL = V := hspan

theorem I_eq {Z ZS Zperp Y T : Subgroup G} (g : G)
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS) :
    (setup Z Zperp Y T).I g = pairI Z ZS g := by
  change (setup Z Zperp Y T).U ⊔ conjugate (setup Z Zperp Y T).U g = _
  rw [closure_eq hZS hperp]
  rfl

theorem S_eq {Z ZS Zperp Y T : Subgroup G} (g : G)
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS) :
    (setup Z Zperp Y T).S g = pairP Z ZS g := by
  change ((setup Z Zperp Y T).I g).pCoreIn 2 = _
  rw [I_eq g hZS hperp]
  rfl

theorem W_eq {Z ZS Zperp Y T : Subgroup G} (g : G)
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS) :
    (setup Z Zperp Y T).W g = pairW Z ZS g := by
  change (setup Z Zperp Y T).U ⊓ (setup Z Zperp Y T).S g = _
  rw [closure_eq hZS hperp, S_eq g hZS hperp]
  rfl

/-- The G.2.6 denominator is V(U ∩ Uᵍ), before the later Chapter 15
coprime-action argument proves that this is V. -/
theorem S₂_eq {Z ZS Zperp V Y T : Subgroup G} (g : G)
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS)
    (hspan : localSpan Z Y = V) :
    S₂ (setup Z Zperp Y T) g =
      V ⊔ (closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g) := by
  change (setup Z Zperp Y T).VL ⊔
    ((setup Z Zperp Y T).U ⊓ conjugate (setup Z Zperp Y T).U g) = _
  rw [VL_eq hspan, closure_eq hZS hperp]
  rfl

/-- Apply the proved layer argument to the literal Chapter 15 groups.
The invariance and irreducibility inputs are the actual natural action,
and containment in I is discharged by the generation/model branch. -/
theorem normal_layers_application [Finite G]
    {Z ZS Zperp V Y T : Subgroup G} {g : G}
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS)
    (hspan : localSpan Z Y = V)
    (hbase : (setup Z Zperp Y T).BaseHypothesis)
    (hclosure : ClosureConclusions (setup Z Zperp Y T))
    (hg : g ∈ Y) (hV : IsPGroup 2 V) (hVI : V ≤ pairI Z ZS g)
    (hN : pairI Z ZS g ≤ normalizer (V : Set G))
    (hirr : ∀ A : Subgroup G, A ≤ V → pairI Z ZS g ≤ normalizer (A : Set G) →
      A = ⊥ ∨ A = V) :
    let P₀ := V ⊔ (closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g)
    V ≤ P₀ ∧ P₀ ≤ pairP Z ZS g ∧
      (V.subgroupOf (pairI Z ZS g)).Normal ∧ (P₀.subgroupOf (pairI Z ZS g)).Normal ∧
      V ≤ centralizer (pairP Z ZS g : Set G) ∧ ⁅P₀, pairI Z ZS g⁆ ≤ V := by
  let D := setup Z Zperp Y T
  have hi : D.I g = pairI Z ZS g := I_eq g hZS hperp
  have hv : D.VL = V := VL_eq hspan
  have hs : D.S g = pairP Z ZS g := S_eq g hZS hperp
  have he : S₂ D g = V ⊔ (closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g) :=
    S₂_eq g hZS hperp hspan
  have hVp : IsPGroup 2 D.VL := hv.symm ▸ hV
  have hVI' : D.VL ≤ D.I g := by rw [hv, hi]; exact hVI
  have hN' : D.I g ≤ normalizer (D.VL : Set G) := by rw [hv, hi]; exact hN
  have hl := normal_layers hbase hclosure hg hVp hVI' hN'
  have hcentral := central_first_layer hVp hVI' hN' (by
    intro A hA hIA
    rw [hv] at hA ⊢
    rw [hi] at hIA
    exact hirr A hA hIA)
  rw [hv, hi, hs, he] at hl
  rw [hv, hs] at hcentral
  exact ⟨hl.1, hl.2.1, hl.2.2.1, hl.2.2.2.1, hcentral.trans inf_le_right, hl.2.2.2.2⟩

/-- The normalization and commutator assertion of 15.3.54(5) follows
from U normal in T and P ≤ T, without the module decomposition. -/
theorem conjugate_mark_normalizes
    {Z ZS Zperp Y T : Subgroup G} {g : G}
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS)
    (hclosure : ClosureConclusions (setup Z Zperp Y T))
    (hg : g ∈ pairI Z ZS g) (hPT : pairP Z ZS g ≤ T) :
    rightConjugate (pairW Z ZS g) g ≤ normalizer (closureU Z ZS : Set G) ∧
      ⁅rightConjugate (pairW Z ZS g) g, closureU Z ZS⁆ ≤ pairW Z ZS g := by
  let D := setup Z Zperp Y T
  have hu : D.U = closureU Z ZS := closure_eq hZS hperp
  have hi : D.I g = pairI Z ZS g := I_eq g hZS hperp
  have hs : D.S g = pairP Z ZS g := S_eq g hZS hperp
  have hw : D.W g = pairW Z ZS g := W_eq g hZS hperp
  have hTU : T ≤ normalizer (D.U : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hclosure.normal.1).mp hclosure.normal.2
  have hSU : D.S g ≤ normalizer (D.U : Set G) := by
    rw [hs]
    exact hPT.trans hTU
  have hgI : g ∈ D.I g := hi.symm ▸ hg
  have hXS : conjugate (D.W g) g ≤ D.S g := by
    rw [conjugate_W D g hgI]
    exact inf_le_right
  have hn := hXS.trans hSU
  have hc := (commutator_mono hXS le_rfl).trans (core_commutator_U hSU)
  change conjugate (pairW Z ZS g) g ≤ normalizer (closureU Z ZS : Set G) ∧
    ⁅conjugate (pairW Z ZS g) g, closureU Z ZS⁆ ≤ pairW Z ZS g
  simpa only [hu, hw] using And.intro hn hc

end Chapter15
end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
