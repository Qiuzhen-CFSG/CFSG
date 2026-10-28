module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Actions.FrattiniGeneration
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Actions.NaturalPreimage

/-!
# The quotient-action clauses of Lemma 12.8.9

We assemble (4–6) on the literal marked flag. Natural coordinates give the
fixed space and commutator containment used in (4). Relative normality puts
X inside the supplied Sylow subgroup, and the proved Frattini product then
gives both action kernels in (5). The coordinate inverse-image calculation
gives (6), retaining the original right conjugator and identifying the
subgroup join with the actual product Z(U)^g E.

Only the preceding-source inputs 12.8.4(2), 12.8.8(3,6), the nonabelian
branch and the exact parabolic data of (1–3) remain explicit. In particular,
the marked natural witness is an equivariant isomorphism on the actual
section S/E for the actual S₃ quotient, not an abstract group-family tag.
Its construction and the earlier-source assembly remain with Parabolic.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.8.9(4–6), printed p.853, PDF p.870.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

namespace ParabolicNaturalModule
variable {F : InvariantFlag T V n} {L : Subgroup G} {g : G} {ι : Type*} [Fintype ι]

private theorem commutator_mem_core (M : F.ParabolicNaturalModule L g ι)
    (u : F.U) (s : G) (hs : s ∈ F.W ⊔ F.X g) :
    ⁅s, (u : G)⁆ ∈ F.W ⊔ F.X g :=
  (le_normalizer_iff_commutator_le_left.mp
    ((le_conjugateSpanBy F.U (F.P L)).trans M.core_normalized))
    (commutator_mem_commutator hs u.property)

/-- The natural displacement lies in the marked W-line. -/
theorem commutator_mem_W (M : F.ParabolicNaturalModule L g ι)
    (u : F.U) (hu : (u : G) ∉ F.W) (s : G) (hs : s ∈ F.W ⊔ F.X g) :
    ⁅s, (u : G)⁆ ∈ F.W := by
  let c : ↥(F.W ⊔ F.X g) := ⟨⁅s, (u : G)⁆, M.commutator_mem_core u s hs⟩
  apply (M.W_marking c).mpr
  intro j
  have hc := M.commutator_coordinates u hu ⟨s, hs⟩ c rfl j
  rw [hc]
  simp [BinaryPermutation.coreRepresentation_apply, BinaryPermutation.representation_apply,
    Equiv.swap_apply_def]

/-- The fixed-space assertion of (3), pulled back along the actual
coordinate homomorphism with kernel E. -/
theorem fixedSpace_commutator (M : F.ParabolicNaturalModule L g ι)
    (u : F.U) (hu : (u : G) ∉ F.W) (s : G) (hs : s ∈ F.W ⊔ F.X g) :
    ⁅s, (u : G)⁆ ∈ F.E g ↔ s ∈ F.W :=
  M.commutator_mem_E_iff u hu ⟨s, hs⟩
    ⟨⁅s, (u : G)⁆, M.commutator_mem_core u s hs⟩ rfl

/-- Recover the literal quotient fixed-space interface used by (4). -/
theorem fixedSpace (M : F.ParabolicNaturalModule L g ι)
    [((F.E g).subgroupOf (F.I₂ L)).Normal] : F.ParabolicFixedSpace L g := by
  intro u hu
  let I := F.I₂ L
  let q := QuotientGroup.mk' ((F.E g).subgroupOf I)
  let ui : I := ⟨u, le_conjugateSpanBy F.U (F.P L) u.property⟩
  ext a
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, hc⟩
    have hcomm : ⁅(s : G), (u : G)⁆ ∈ F.E g := by
      have he : q ⁅s, ui⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr
          (hc (q ui) (Set.mem_singleton _)).symm
      exact (QuotientGroup.eq_one_iff ⁅s, ui⁆).mp he
    exact ⟨s, (M.fixedSpace_commutator u hu s hs).mp hcomm, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    have hsS : (s : G) ∈ F.W ⊔ F.X g := (le_sup_left : F.W ≤ F.W ⊔ F.X g) hs
    refine ⟨⟨s, hsS, rfl⟩, ?_⟩
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    have he : q ⁅s, ui⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr
      ((M.fixedSpace_commutator u hu s hsS).mpr hs)
    rw [map_commutatorElement] at he
    exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm

end ParabolicNaturalModule

/-- The point stabilizer for the literal action on U/Z(U), embedded in G. -/
def xHatStabilizer (F : InvariantFlag T V n) (g : G) (hg : g ∈ F.Gi 2)
    (a : F.Uhat) : Subgroup G :=
  ((MulAction.stabilizer (MulAut F.Uhat) a).comap (F.xHatAction g hg)).map (F.X g).subtype

theorem mem_xHatStabilizer (F : InvariantFlag T V n) (g : G) (hg : g ∈ F.Gi 2)
    (a : F.Uhat) (x : G) :
    x ∈ F.xHatStabilizer g hg a ↔ ∃ hx : x ∈ F.X g, F.xHatAction g hg ⟨x, hx⟩ a = a := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩
  · rintro ⟨hx, hfix⟩
    exact ⟨⟨x, hx⟩, hfix, rfl⟩

/-- Clause (5), with the Sylow placement, fixed space and Frattini
product discharged from (1–3) and the stated earlier source inputs. -/
theorem parabolic_action_kernels_eq [Finite G] (F : InvariantFlag T V n)
    [IsMulCommutative V] (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hn : 2 ≤ n) (g : G) (hgP : g ∈ F.P L)
    {ι : Type*} [Fintype ι] (M : F.ParabolicNaturalModule L g ι)
    [((F.I₂ L).subgroupOf (F.Gi 2)).Normal]
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1) (hcenter : V ⊓ F.ZU = F.Vi 1)
    (hspan : F.U = conjugateSpanBy (F.Vi 2) F.H) (hnonab : ¬ IsMulCommutative F.U) :
    F.xHatKernel g (F.P_le_G₂ hn L hL hgP) = F.E g ∧
      F.xTildeKernel g (F.P_le_G₂ hn L hL hgP) = F.E g := by
  have hIG : F.I₂ L ≤ F.Gi 2 := conjugateSpanBy_le (F.U_le_G₂_of_commutator hcomm)
    ((F.P_le_G₂ hn L hL).trans (F.Gi 2).le_normalizer)
  exact F.action_kernels_eq_of_source_frattini L hL hn g hgP hcomm hcenter hspan hnonab
    (F.X_le_T_of_core L g hIG M.core_eq)
    (fun u hu huw s hs hc => (M.fixedSpace_commutator ⟨u, hu⟩ huw s hs).mp hc)

/-- Clause (6) as a subgroup bound on the literal point stabilizer.
The commutator containment and the natural inverse image are proved,
with the original g in P − H. -/
theorem parabolic_hat_stabilizer_le (F : InvariantFlag T V n)
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G)) (hn : 2 ≤ n)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    {ι : Type*} [Fintype ι] (M : F.ParabolicNaturalModule L g ι)
    (hfactor : F.P L = (F.P L).pCoreIn 2 ⊔ F.I₂ L)
    (hPH : (F.P L).pCoreIn 2 ≤ F.H)
    (hcore : F.I₂ L ⊓ centralizer (F.Vi 2 : Set G) = (F.I₂ L).pCoreIn 2)
    [((F.E g).subgroupOf (F.I₂ L)).Normal]
    (u : F.U) (hu : (u : G) ∉ F.W) :
    F.xHatStabilizer g (F.P_le_G₂ hn L hL hgP) (QuotientGroup.mk' (center F.U) u) ≤
      conjugate F.ZU g ⊔ F.E g := by
  have hWI : F.W ≤ F.I₂ L := (show F.W ≤ F.U from inf_le_left).trans
    (le_conjugateSpanBy _ _)
  let : ((F.E g).subgroupOf F.W).Normal := normal_subgroupOf_of_le_normalizer
    (hWI.trans (le_normalizer_of_normal_subgroupOf
      ((show F.E g ≤ F.W from inf_le_left).trans hWI)))
  rintro x hx
  obtain ⟨hxX, hfix⟩ := (F.mem_xHatStabilizer g (F.P_le_G₂ hn L hL hgP) _ x).mp hx
  exact F.hat_stabilizer_le_of_natural_module L hL hn g hgP hgH M hfactor hPH hcore
    u hu (fun y hy => M.commutator_mem_W u hu y
      ((le_sup_right : F.X g ≤ F.W ⊔ F.X g) hy)) ⟨x, hxX⟩ hfix

/-- Relative normality in I₂ makes the displayed join the literal source
product Z(U)^g E. No normality of E in the ambient group is asserted. -/
theorem conjugate_ZU_sup_E_eq_product (F : InvariantFlag T V n)
    (L : Subgroup G) (g : G) (hgP : g ∈ F.P L)
    [((F.E g).subgroupOf (F.I₂ L)).Normal] :
    ((conjugate F.ZU g ⊔ F.E g : Subgroup G) : Set G) = (conjugate F.ZU g : Set G) * (F.E g : Set G) := by
  have hWI : F.W ≤ F.I₂ L := (show F.W ≤ F.U from inf_le_left).trans
    (le_conjugateSpanBy _ _)
  have hXI : F.X g ≤ F.I₂ L :=
    (map_mono (show F.W ≤ F.U from inf_le_left)).trans
      (le_sup_right.trans (F.U_sup_conjugate_le_I₂ L g hgP))
  have hnorm : F.I₂ L ≤ normalizer (F.E g : Set G) :=
    le_normalizer_of_normal_subgroupOf ((show F.E g ≤ F.W from inf_le_left).trans hWI)
  exact coe_mul_of_left_le_normalizer_right _ _ ((F.conjugate_ZU_le_X g).trans (hXI.trans hnorm))

/-- All three quotient-action clauses of 12.8.9 on the actual marked flag.
The hypotheses are the nonabelian branch, [U,U] ≤ V₁ from 12.8.4(2),
V ∩ Z(U) = V₁ and U = ⟨V₂ᴴ⟩ from 12.8.8(3,6), and the preceding
parabolic data (1–3). No clause of (4–6), fixed vector, Frattini product,
commutator-image assertion or inverse-image identity is a premise.

The parent parabolic assembly constructs the marked natural-module witness
and discharges these earlier-source inputs. -/
theorem parabolic_action_clauses [Finite G] (F : InvariantFlag T V n)
    [IsMulCommutative V] (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hn : 2 ≤ n) (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    {ι : Type*} [Fintype ι] (M : F.ParabolicNaturalModule L g ι)
    [((F.I₂ L).subgroupOf (F.Gi 2)).Normal]
    [((F.E g).subgroupOf (F.I₂ L)).Normal]
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1) (hcenter : V ⊓ F.ZU = F.Vi 1)
    (hspan : F.U = conjugateSpanBy (F.Vi 2) F.H) (hnonab : ¬ IsMulCommutative F.U)
    (hfactor : F.P L = (F.P L).pCoreIn 2 ⊔ F.I₂ L)
    (hPH : (F.P L).pCoreIn 2 ≤ F.H)
    (hcore : F.I₂ L ⊓ centralizer (F.Vi 2 : Set G) = (F.I₂ L).pCoreIn 2) :
    (∀ y : F.X g, (y : G) ∉ F.W →
      F.tilde F.U ⊓ centralizer ({F.tildeProjection
        ⟨y, F.X_le_H g (F.P_le_G₂ hn L hL hgP) y.property⟩} : Set F.G₁tilde) ≤
          F.tilde F.W) ∧
    (F.xHatKernel g (F.P_le_G₂ hn L hL hgP) = F.E g ∧
      F.xTildeKernel g (F.P_le_G₂ hn L hL hgP) = F.E g) ∧
    (∀ u : F.U, (u : G) ∉ F.W →
      (F.xHatStabilizer g (F.P_le_G₂ hn L hL hgP)
        (QuotientGroup.mk' (center F.U) u) : Set G) ⊆
          (conjugate F.ZU g : Set G) * (F.E g : Set G)) := by
  refine ⟨?_, F.parabolic_action_kernels_eq L hL hn g hgP M hcomm hcenter hspan hnonab, ?_⟩
  · exact fun y hy => F.parabolic_tilde_centralizer_le L hL hn g hgP M.fixedSpace y hy
  · intro u hu
    rw [← F.conjugate_ZU_sup_E_eq_product L g hgP]
    exact F.parabolic_hat_stabilizer_le L hL hn g hgP hgH M hfactor hPH hcore u hu

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
