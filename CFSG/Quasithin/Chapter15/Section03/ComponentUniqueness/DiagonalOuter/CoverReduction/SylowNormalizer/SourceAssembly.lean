module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.SylowNormalizer
public import Theory.GroupTheory.SylowThreeProduct

/-!
# The marked Sylow normalizer from the preceding cover conclusions

This conditional helper takes the actual marked central cover and natural
rank-four action. It constructs the quotient coordinates and the Frattini
section; neither is an input. Normality of O₂(Y) is relative to Y and the
T-action, and the Sylow condition on S inside I proves T ∩ L = S ∩ L.
Consequently the section has precisely L.subgroupOf T as kernel and its
image is the actual N_T(X).

The two plane residuals have common two-core S_L = O₂(Y). Their distinct
fixed planes put their intersection in this core. The Sylow supplement
argument then constructs the multiplication isomorphism X_L × X_D ≃ X,
where both factors are the actual intersections with Y_L and Y_D.

The graph and square-Frobenius recognition calculations and the bound
C_{S_L}(X) ≤ V₁ remain explicit intrinsic cover inputs. Diagonal, graph and
field actions all use the same supplied ProjectiveMarking and its Realizes
equations. The actual diagonal actor in Y_D is retained among the direct
source hypotheses. The center, centralizer and Y₊ identities record the
preceding source paragraph; the present deductions need only part of those
identities.

The source-theorem owner must discharge these preceding local hypotheses
and intrinsic calculations. This helper proves no TI, transfer or nonfusion
assertion. The returned section directly supplies the reflection orders,
t τ t⁻¹ = τ f, w² = f, and the index-two cyclic-four quotient via
Theory.GroupTheory.DihedralRotationQuotient.

Source: Aschbacher--Smith, proof of 15.3.38, combined manuscript
(1 March 2004), printed p.1136, the paragraph beginning “Let X ∈ Syl₃(Y)”.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.SylowNormalizer
variable {G : Type*} [Group G] [Finite G]

/-- The complete conditional Sylow-normalizer paragraph, including the
actual Sylow-factor multiplication isomorphism. The three remaining model
inputs concern the cover centralizer and its two marked automorphism cosets. -/
theorem exists_lift_of_local_cover
    (T : Sylow 2 G) (M I Y Yplus S L YL YD V V₁ V₂ : Subgroup G)
    (a : NaturalOrthogonalAction M V) (hTM : (T : Subgroup G) ≤ M)
    (hYSM : Y ⊔ S ≤ M) (hST : S ≤ T) (hVS : V ≤ S)
    (hMY : M ≤ normalizer (Y : Set G)) (hSI : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = S)
    (_hYplus : Yplus = Y) (c : ProjectiveMarking L 4)
    (_hZcore : center L = pCore 2 L) (hZ : (center L).map L.subtype = V₁)
    (_hCI : I ⊓ centralizer (L : Set G) = V₁)
    (hIprod : (I : Set G) = (L : Set G) * (YD : Set G) * (S : Set G))
    (hSL : S ⊓ L = Y.pCoreIn 2)
    (e : (Y ⧸ pCore 2 Y) ≃* Multiplicative (Fin 2 → ZMod 3))
    (hTK : (T : Subgroup G) ⊓ centralizer (V : Set G) = Y.pCoreIn 2)
    (hYSK : (Y ⊔ S) ⊓ centralizer (V : Set G) = Y.pCoreIn 2)
    (hV₁ : V₁ = a.plane 1) (hV : V = V₁ ⊔ V₂)
    (hS : ∀ t : T, (t : G) ∈ S ↔ (a.actor (inclusion hTM t)).right = 1)
    (y : G) (_hyD : y ∈ YD) (_hy : c.Diagonal y)
    (hYprod : (Y : Set G) = (YL : Set G) * (YD : Set G))
    (hYLcore : YL.pCoreIn 2 = Y.pCoreIn 2)
    (hYDcore : YD.pCoreIn 2 = Y.pCoreIn 2)
    (hYLfix : YL ≤ centralizer (V₁ : Set G))
    (hYDfix : YD ≤ centralizer (V₂ : Set G))
    (hbound : ∀ X : Sylow 3 Y,
      (S ⊓ L) ⊓ centralizer (((X : Subgroup Y).map Y.subtype) : Set G) ≤ V₁)
    (hgraph : ∀ d : NaturalCoordinates T M Y S (Y.pCoreIn 2) V V₁ a hTM hYSM,
      ∀ t : T, d.tProjection t = .sr 0 → c.Graph (t : G))
    (hfield : ∀ d : NaturalCoordinates T M Y S (Y.pCoreIn 2) V V₁ a hTM hYSM,
      ∀ t : T, d.tProjection t = .r 2 → c.Field (t : G)) :
    ∃ b : SylowThreeLift T Y S L c,
      (S ⊓ L) ⊓ centralizer (((b.X : Subgroup Y).map Y.subtype) : Set G) = ⊥ ∧
      S ⊓ normalizer (((b.X : Subgroup Y).map Y.subtype) : Set G) =
        zpowers (b.dihedral.firstReflection : G) ⊔ zpowers (b.dihedral.halfTurn : G) ∧
      (b.dihedral.firstReflection * b.dihedral.halfTurn : G) ∈ centralizer (V₁ : Set G) ∧
      (b.dihedral.firstReflection * b.dihedral.halfTurn : G) ∉ V₁ ∧
      (let P := (b.X : Subgroup Y).map Y.subtype
       ∃ f : ((P ⊓ YL : Subgroup G) × (P ⊓ YD : Subgroup G)) ≃* P,
         ∀ z, (f z : G) = (z.1 : G) * (z.2 : G)) := by
  let R := Y.pCoreIn 2
  have hRY : R ≤ Y := pCoreIn_le 2 Y
  have hcore : R.subgroupOf Y = pCore 2 Y :=
    comap_map_eq_self_of_injective Y.subtype_injective _
  let : (R.subgroupOf Y).Normal := hcore ▸ inferInstance
  let eR : (Y ⧸ R.subgroupOf Y) ≃* Multiplicative (Fin 2 → ZMod 3) :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans e
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) := hTM.trans hMY
  have hYR : Y ≤ normalizer (R : Set G) :=
    Y.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    hTY.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))
  have hLI : L ≤ I := by
    intro l hl
    rw [← SetLike.mem_coe, hIprod]
    exact ⟨l, ⟨l, hl, 1, YD.one_mem, mul_one l⟩, 1, S.one_mem, mul_one l⟩
  obtain ⟨SI, hSI⟩ := hSI
  have hTI : (T : Subgroup G) ⊓ I = S := by
    rw [← hSI]
    exact inf_eq_sylow_map SI T.isPGroup' (hSI ▸ hST)
  have hRL : R.subgroupOf (T : Subgroup G) = L.subgroupOf (T : Subgroup G) := by
    ext t
    change (t : G) ∈ R ↔ (t : G) ∈ L
    change (t : G) ∈ Y.pCoreIn 2 ↔ _
    rw [← hSL]
    exact ⟨And.right, fun ht => ⟨hTI.le ⟨t.property, hLI ht⟩, ht⟩⟩
  have hV₁V : V₁ ≤ V := hV₁ ▸ map_subtype_le _
  have hV₁R : V₁ ≤ R := by
    change V₁ ≤ Y.pCoreIn 2
    rw [← hSL]
    exact le_inf (hV₁V.trans hVS) (hZ ▸ map_subtype_le _)
  obtain ⟨b, hC, hN, hfix, hout⟩ := exists_lift_of_natural_action
    T M Y S L R V V₁ a hTM hYSM hST hRY hYR hTR hTY eR hTK hYSK hRL hV₁R
    hV₁ hS c (fun X => by simpa only [R, ← hSL] using hbound X) hgraph hfield
  have hYLY : YL ≤ Y := by
    intro x hx
    rw [← SetLike.mem_coe, hYprod]
    exact ⟨x, hx, 1, YD.one_mem, mul_one x⟩
  have hYDY : YD ≤ Y := by
    intro x hx
    rw [← SetLike.mem_coe, hYprod]
    exact ⟨1, YL.one_mem, x, hx, one_mul x⟩
  have hAD : YL ⊓ YD ≤ R := by
    intro x hx
    apply hYSK.le
    refine ⟨mem_sup_left (hYLY hx.1), ?_⟩
    have hVC : V ≤ centralizer ({x} : Set G) := by
      rw [hV]
      refine sup_le ?_ ?_
      · intro z hz
        exact mem_centralizer_singleton_iff.mpr (hYLfix hx.1 z hz)
      · intro z hz
        exact mem_centralizer_singleton_iff.mpr (hYDfix hx.2 z hz)
    intro z hz
    exact mem_centralizer_singleton_iff.mp (hVC hz)
  refine ⟨b, hSL.symm ▸ hC, hN, hfix, hout, ?_⟩
  exact SylowThreeNormalizer.exists_product_equiv Y R YL YD hRY hYR eR
    hYLY hYDY (by simpa only [R, ← hYLcore] using pCoreIn_le 2 YL)
    (by simpa only [R, ← hYDcore] using pCoreIn_le 2 YD)
    hAD hYprod b.X (isPGroup_pCoreIn 2 Y)
end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.SylowNormalizer
