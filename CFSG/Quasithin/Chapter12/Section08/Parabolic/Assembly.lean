module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Actions.NaturalCoordinates
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Centers

/-!
# Source assembly of the marked parabolic calculations

This assembles every clause of Aschbacher–Smith 12.8.9–10 on the original
invariant flag and original g ∈ P − H. Generation constructs the actual
S₃ quotient. The literal section O₂(I₂)/E has complementary W/E and X/E
images and a finite natural tensor model, which proves the three marked
fixed/moved identities. The completed coordinate and Frattini calculations
supply the actual hat/tilde action clauses.

For the center calculation, equivariance pulls the first fixed-space equality
back through the canonical section map: a core element whose commutator with
a ∈ U − W lies in E has the coordinates of an element of W, and hence lies
in W because E ≤ W. Restricting the original H-actions to X identifies the
two embedded kernels required by the center theorem. Thus no 12.8.9 result,
model, coordinate witness, product decomposition or center conclusion remains
as an extra premise in the 12.8.10 assembly.

Only precise preceding-source inputs stay explicit. Setup supplies the flag,
the full LT-action and its two-core kernel, and the original g. Preliminary
supplies the commutator/square bounds (12.8.4), the literal local tilde kernel
(12.8.4(4)), nonabelianness, V ∩ Z(U) = V₁ and the plane span (12.8.8(3,6)),
and the evaluated symplectic form on U/Z(U) (12.8.8(2)). Two-perfectness and
T-normalization of L come from 12.8.1; full L-action is used only when n ≥ 3.
The section assembly owner `qt-12-08` retains discharge of these sibling inputs.

The printed H-span in 12.8.9(1) is corrected to the G₂-span proved in the
source. The product condition in 12.8.10(5) remains Z(U)^g ≤ U, and its
conclusion includes the genuine multiplication equivalence. I₂ is never
identified with the whole parabolic P.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemmas 12.8.9–10, printed pp.852–854 (PDF pp.869–871), refs/quasithin.pdf.
-/

public section

open Subgroup
open scoped commutatorElement IsMulCommutative TensorProduct Pointwise
open InvertedCubicTensor

namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- Pull the canonical fixed-space identity of 12.8.9(3) back to the actual
core. This discharges the fixed-space premise of the center theorem without
any choice of tensor basis or involutory lift. -/
theorem binary_source_fixedSpace_pullback (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 V] (hn : 2 ≤ n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G))
    (hfull : Function.Surjective (F.binarySeedAction L hL))
    (hkernel : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1) (hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1)
    (hspan : F.U = conjugateSpanBy (F.Vi 2) F.H) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∀ a ∈ F.U, a ∉ F.W → ∀ z ∈ (F.I₂ L).pCoreIn 2,
      ⁅z, a⁆ ∈ F.E g → z ∈ F.W := by
  obtain ⟨e, hfactor, hPH, hgen, hcore, hindex, _, hquot⟩ :=
    F.binary_source_natural_quotient hn L hL hfull hkernel hcomm hsquare hspan hne
      g hgP hgH
  let := F.binary_source_E_normal_in_core L hL g hgP hgen hcomm
  let := F.binary_source_quotient_elementary L hL g hgP hgen hcore
    (F.binary_core_normalizes_U L hfactor hPH)
    (F.binary_core_factorization L g hgP hfactor hPH hgen e hcore hindex) hcomm hsquare
  obtain ⟨σ, d, _, _, _, hfixed⟩ := hquot
  intro a ha haw z hz hza
  let ai : F.I₂ L := ⟨a, le_conjugateSpanBy F.U (F.P L) ha⟩
  let zs : (F.I₂ L).pCoreIn 2 := ⟨z, hz⟩
  let t : (F.I₂ L).pCoreIn 2 := ⟨a * z * a⁻¹,
    (mem_normalizer_iff.mp (d.normalized ai.property) z).mp hz⟩
  have ht : d.coordinates t = d.coordinates zs := by
    have hc : ⁅a, z⁆ ∈ F.E g := by
      simpa only [commutatorElement_inv] using (F.E g).inv_mem hza
    have he : d.coordinates (t * zs⁻¹) = 1 :=
      (d.coordinates_eq_one_iff _).mpr hc
    rw [map_mul, map_inv, mul_inv_eq_one] at he
    exact he
  have hfixedz : (d.coordinates zs).toAdd ∈
      LinearMap.ker (σ (F.binaryCoreProjection L e ai) - 1) := by
    rw [LinearMap.mem_ker]
    change σ (F.binaryCoreProjection L e ai) (d.coordinates zs).toAdd -
      (d.coordinates zs).toAdd = 0
    exact sub_eq_zero.mpr ((d.equivariant ai zs).symm.trans
      (congrArg Multiplicative.toAdd ht))
  rw [(hfixed ai ha haw).1] at hfixedz
  obtain ⟨w, hw, he⟩ := (d.mem_imageSpace_iff F.W _).mp hfixedz
  have hk : (w : G)⁻¹ * z ∈ F.E g := by
    change w⁻¹ * zs ∈ (F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)
    rw [← d.kernel_eq, MonoidHom.mem_ker, map_mul, map_inv,
      Multiplicative.toAdd.injective he, inv_mul_cancel]
  have hh := F.W.mul_mem hw hk.1
  simpa only [mul_inv_cancel_left] using hh

omit [Finite G] in
private theorem xHatKernel_eq_inf (F : InvariantFlag T V n) (g : G)
    (hg : g ∈ F.Gi 2) :
    F.xHatKernel g hg = F.X g ⊓ F.uhatAction.ker.map F.H.subtype := by
  ext x
  rw [F.mem_xHatKernel]
  constructor
  · rintro ⟨hx, hc⟩
    exact ⟨hx, ⟨⟨x, F.X_le_H g hg hx⟩,
      (F.mem_uhatAction_ker_iff _).mpr hc, rfl⟩⟩
  · rintro ⟨hx, y, hy, rfl⟩
    exact ⟨hx, (F.mem_uhatAction_ker_iff y).mp hy⟩

omit [Finite G] in
private theorem xTildeKernel_eq_inf (F : InvariantFlag T V n) [IsMulCommutative V]
    (g : G) (hg : g ∈ F.Gi 2) :
    F.xTildeKernel g hg =
      F.X g ⊓ (F.localTildeAction F.H le_rfl).ker.map F.H.subtype := by
  ext x
  rw [F.mem_xTildeKernel]
  constructor
  · rintro ⟨hx, hc⟩
    exact ⟨hx, ⟨⟨x, F.X_le_H g hg hx⟩,
      (F.mem_localTildeAction_ker_iff F.H le_rfl _).mpr hc, rfl⟩⟩
  · rintro ⟨hx, y, hy, rfl⟩
    exact ⟨hx, (F.mem_localTildeAction_ker_iff F.H le_rfl y).mp hy⟩

/-- All seven clauses of Lemma 12.8.9 from the exact preceding source
inputs. The first span is the G₂-span proved in the book, correcting the
printed H-span. The actual quotient representation and its complementary
marked subspaces are part of the conclusion, as are all three fixed/moved
identities and the literal hat/tilde action assertions. -/
theorem binary_source_parabolic_calculations (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 V] (hn : 2 ≤ n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G))
    (hfull : Function.Surjective (F.binarySeedAction L hL))
    (hkernel : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1) (hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1)
    (hspan : F.U = conjugateSpanBy (F.Vi 2) F.H) (hne : ¬ IsMulCommutative F.U)
    (hcenter : V ⊓ F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ (e : ((F.I₂ L) ⧸ pCore 2 (F.I₂ L)) ≃* S₃)
      (hfactor : F.P L = (F.P L).pCoreIn 2 ⊔ F.I₂ L)
      (hPH : (F.P L).pCoreIn 2 ≤ F.H)
      (hgen : F.U ⊔ conjugate F.U g = F.I₂ L)
      (hcore : F.I₂ L ⊓ centralizer (F.Vi 2 : Set G) = (F.I₂ L).pCoreIn 2)
      (hindex : F.W.relIndex F.U = 2),
      F.I₂ L = (pResidual 2 (F.P L)).map (F.P L).subtype ⊔ F.U ∧
      F.I₂ L = conjugateSpanBy F.U (F.Gi 2) ∧
      F.I₂ L ≤ F.Gi 2 ∧ ((F.I₂ L).subgroupOf (F.Gi 2)).Normal ∧
      (pResidual 2 (F.P L)).map (F.P L).subtype ≤ F.Gi 2 ∧
      (((pResidual 2 (F.P L)).map (F.P L).subtype).subgroupOf (F.Gi 2)).Normal ∧
      (F.I₂ L).pCoreIn 2 = F.W ⊔ F.X g ∧ ⁅F.E g, F.I₂ L⁆ = F.Vi 2 ∧
      (F.I₂ L : Set G) =
        ((pResidual 2 (F.P L)).map (F.P L).subtype : Set G) * (F.U : Set G) ∧
      ((F.I₂ L).pCoreIn 2 : Set G) = (F.W : Set G) * (F.X g : Set G) ∧
      (∀ (x : F.I₂ L) (v : F.Vi 2),
        ((F.binaryPlaneLabel hn).symm (e (QuotientGroup.mk x)) v : G) =
          (x : G) * (v : G) * (x : G)⁻¹) ∧
    let := F.binary_source_E_normal_in_core L hL g hgP hgen hcomm
    let := F.binary_source_quotient_elementary L hL g hgP hgen hcore
      (F.binary_core_normalizes_U L hfactor hPH)
      (F.binary_core_factorization L g hgP hfactor hPH hgen e hcore hindex) hcomm hsquare
    ∃ (σ : Representation (ZMod 2) S₃
        (Additive (((F.I₂ L).pCoreIn 2) ⧸ (F.E g).subgroupOf ((F.I₂ L).pCoreIn 2))))
      (d : Representation.BinaryConjugationSection (F.I₂ L) ((F.I₂ L).pCoreIn 2)
        (F.E g) (σ.comp (F.binaryCoreProjection L e))),
      (∀ s : (F.I₂ L).pCoreIn 2, (d.coordinates s).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)) s)) ∧
      Finite (multiplicitySpace σ) ∧
      (∃ j : multiplicitySpace σ ⊗[ZMod 2] BinaryPermutation.core (Fin 3) ≃ₗ[ZMod 2]
            Additive (((F.I₂ L).pCoreIn 2) ⧸ (F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)),
          ∀ a z, j ((Representation.tprod (Representation.trivial (ZMod 2) S₃
              (multiplicitySpace σ)) (BinaryPermutation.coreRepresentation (Fin 3))) a z) =
            σ a (j z)) ∧
      IsCompl (d.imageSpace F.W) (d.imageSpace (F.X g)) ∧
      (∀ u : F.I₂ L, (u : G) ∈ F.U → (u : G) ∉ F.W →
          LinearMap.ker (σ (F.binaryCoreProjection L e u) - 1) = d.imageSpace F.W ∧
          LinearMap.range (σ (F.binaryCoreProjection L e u) - 1) = d.imageSpace F.W ∧
          (d.imageSpace (F.X g)).map (σ (F.binaryCoreProjection L e u) - 1) =
            d.imageSpace F.W) ∧
      (∀ y : F.X g, (y : G) ∉ F.W →
        F.tilde F.U ⊓ centralizer ({F.tildeProjection
          ⟨y, F.X_le_H g (F.P_le_G₂ hn L hL hgP) y.property⟩} : Set F.G₁tilde) ≤
            F.tilde F.W) ∧
      (F.xHatKernel g (F.P_le_G₂ hn L hL hgP) = F.E g ∧
        F.xTildeKernel g (F.P_le_G₂ hn L hL hgP) = F.E g) ∧
      (∀ u : F.U, (u : G) ∉ F.W →
        (F.xHatStabilizer g (F.P_le_G₂ hn L hL hgP)
          (QuotientGroup.mk' (center F.U) u) : Set G) ⊆
            (conjugate F.ZU g : Set G) * (F.E g : Set G)) ∧
      conjugate (F.Vi 1) g ⊓ F.ZU = ⊥ := by
  obtain ⟨e, hres, hgen, hGspan, hIG, hIN, hRG, hRN, hfactor, hPH,
    hcore, hindex, heval⟩ :=
    F.binary_generation hn L hL hfull hkernel hcomm hsquare hspan hne g hgP hgH
  have hsplit := F.binary_core_factorization L g hgP hfactor hPH hgen.symm e hcore hindex
  have hEcomm := F.binary_intersection_commutator hn L hL g hgP hgH hgen.symm hcomm hindex
  have hresProduct : (F.I₂ L : Set G) =
      ((pResidual 2 (F.P L)).map (F.P L).subtype : Set G) * (F.U : Set G) := by
    rw [hres]
    exact coe_mul_of_right_le_normalizer_left _ _
      ((F.U_le_G₂_of_commutator hcomm).trans
        ((normal_subgroupOf_iff_le_normalizer hRG).mp hRN))
  have hW : F.U ⊓ (F.I₂ L).pCoreIn 2 = F.W := by
    rw [← hcore, ← inf_assoc,
      inf_eq_left.mpr (show F.U ≤ F.I₂ L from le_conjugateSpanBy _ _)]
    rfl
  have hSW : (F.I₂ L).pCoreIn 2 ≤ normalizer (F.W : Set G) := by
    rw [← hW]
    exact (le_inf (F.binary_core_normalizes_U L hfactor hPH)
      ((F.I₂ L).pCoreIn 2).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hcoreProduct : ((F.I₂ L).pCoreIn 2 : Set G) =
      (F.W : Set G) * (F.X g : Set G) := by
    rw [hsplit]
    exact coe_mul_of_right_le_normalizer_left _ _
      ((le_sup_right.trans hsplit.ge).trans hSW)
  refine ⟨e, hfactor, hPH, hgen.symm, hcore, hindex, hres, hGspan,
    hIG, hIN, hRG, hRN, hsplit, hEcomm, hresProduct, hcoreProduct, heval, ?_⟩
  let := F.binary_source_E_normal_in_core L hL g hgP hgen.symm hcomm
  let := F.binary_source_quotient_elementary L hL g hgP hgen.symm hcore
    (F.binary_core_normalizes_U L hfactor hPH) hsplit hcomm hsquare
  obtain ⟨σ, d, hd, hfinite, hnatural, hfixed⟩ :=
    F.binary_natural_quotient L hL g hgP hfactor hPH hgen.symm e hcore hindex hcomm hsquare
  obtain ⟨hdisplacement, hkernels, hstabilizer⟩ :=
    F.binary_source_parabolic_action_clauses hn L hL hfull hkernel hcomm hsquare hspan hne
      hcenter g hgP hgH
  exact ⟨σ, d, hd, hfinite, hnatural, d.isCompl_imageSpace F.W (F.X g) hsplit rfl,
    hfixed, hdisplacement, hkernels, hstabilizer,
    (F.parabolic_displaced_centers hn L hL hcenter g hgP hgH).1⟩

/-- The two kernels in 12.8.9(5), expressed as intersections with the
embedded kernels of the original H-actions. This is the literal interface
used in all equalities of 12.8.10(6). -/
theorem binary_source_action_kernel_intersections (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 V] (hn : 2 ≤ n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G))
    (hfull : Function.Surjective (F.binarySeedAction L hL))
    (hkernel : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1) (hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1)
    (hspan : F.U = conjugateSpanBy (F.Vi 2) F.H) (hne : ¬ IsMulCommutative F.U)
    (hcenter : V ⊓ F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    (F.X g ⊓ F.uhatAction.ker.map F.H.subtype = F.E g) ∧
    (F.X g ⊓ (F.localTildeAction F.H le_rfl).ker.map F.H.subtype = F.E g) := by
  rw [← F.xHatKernel_eq_inf g (F.P_le_G₂ hn L hL hgP),
    ← F.xTildeKernel_eq_inf g (F.P_le_G₂ hn L hL hgP)]
  exact (F.binary_source_parabolic_action_clauses hn L hL hfull hkernel hcomm hsquare
    hspan hne hcenter g hgP hgH).2.1

/-- All six clauses of Lemma 12.8.10, with every 12.8.9 input proved.
The remaining inputs are precisely the earlier source flag, action, local
kernel and evaluated commutator-form data. The direct product retains its
original conditional antecedent and its actual multiplication equivalence. -/
theorem binary_source_center_calculations
    (F : InvariantFlag T V n) [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat]
    (hn : 2 ≤ n)
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hperfect : IsPPerfect 2 L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hfullLT : Function.Surjective (F.binarySeedAction L hL))
    (hfullL : 3 ≤ n → ∀ a : MulAut V,
      ∃ x ∈ L, ∀ v : V, x * (v : G) * x⁻¹ = (a v : G))
    (hnaturalCore : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hcenter : V ⊓ F.ZU = F.Vi 1) (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1)
    (hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1)
    (hspan : F.U = conjugateSpanBy (F.Vi 2) F.H) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hcore : (F.localTildeAction F.H le_rfl).ker = pCore 2 F.H)
    (B : F.UhatCommutatorForm hcomm) :
    F.ZU ⊓ conjugate F.U g = (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1 ∧
    F.ZU ⊓ conjugate F.ZU g = centerIn (F.I₂ L) ∧
    (F.Vi 1 < F.ZU ⊓ conjugate F.U g →
      sylowOmega T ⊓ centerIn (F.I₂ L) ≠ ⊥) ∧
    (⁅F.W, conjugate F.ZU g⁆ ≤ F.ZU ⊔ F.Vi 2 ∧
      ∀ x : conjugate F.ZU g,
        Group.rank (F.uhatMoved (F.conjugateCenterActor hn L hL g hgP x)) ≤ 2) ∧
    (conjugate F.ZU g ≤ F.U →
      (F.ZU = centerIn (F.I₂ L) ⊔ F.Vi 1 ∧
        Disjoint (centerIn (F.I₂ L)) (F.Vi 1) ∧
        ∃ e : centerIn (F.I₂ L) × F.Vi 1 ≃* F.ZU,
          ∀ a b, (e (a, b) : G) = (a : G) * (b : G)) ∧
      ⁅L, centerIn (F.I₂ L)⁆ = ⊥) ∧
    (conjugate F.ZU g ⊓ F.uhatAction.ker.map F.H.subtype =
        conjugate F.ZU g ⊓ (F.localTildeAction F.H le_rfl).ker.map F.H.subtype ∧
      conjugate F.ZU g ⊓ (F.localTildeAction F.H le_rfl).ker.map F.H.subtype =
        conjugate F.ZU g ⊓ QH F.H ∧
      conjugate F.ZU g ⊓ QH F.H = conjugate F.ZU g ⊓ F.U ∧
      conjugate F.ZU g ⊓ F.U =
        (conjugate F.ZU g ⊓ F.ZU) ⊔ conjugate (F.Vi 1) g ∧
      (conjugate F.ZU g ⊓ F.ZU) ⊔ conjugate (F.Vi 1) g =
        centerIn (F.I₂ L) ⊔ conjugate (F.Vi 1) g ∧
      centerIn (F.I₂ L) ⊔ conjugate (F.Vi 1) g ≤ F.U) := by
  obtain ⟨hhat, htilde⟩ := F.binary_source_action_kernel_intersections hn L hL hfullLT
    hnaturalCore hcomm hsquare hspan hne hcenter g hgP hgH
  exact F.center_calculations_of_binary_source hn L hL hperfect hTL hfullLT hfullL
    hnaturalCore hcenter hcomm hsquare hspan hne g hgP hgH
    (F.binary_source_fixedSpace_pullback hn L hL hfullLT hnaturalCore hcomm hsquare
      hspan hne g hgP hgH) hhat htilde hcore B

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
