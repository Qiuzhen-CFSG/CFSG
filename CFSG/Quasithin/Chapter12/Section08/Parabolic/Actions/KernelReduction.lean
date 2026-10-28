module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Actions.Displacement
public import Theory.GroupAction.CommonFixedNormalizer
public import Theory.GroupTheory.SylowNormalizerOvergroup

/-!
# The remaining kernel arguments on the actual marked flag

The two-core and normality clauses of 12.8.9 place X in the supplied
ambient Sylow subgroup. Nonabelianness and 12.8.8(6) make W proper in U.
Thus the Frattini product Ũ = C_{Ũ}(C_T(Û)) Z̃(U), once constructed,
produces a fixed vector outside W̃ and finishes the action-kernel equality.
The product is an explicit pending premise, not an assumed source theorem.

Source: Aschbacher–Smith, Lemma 12.8.9(4–6), printed p.853.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The Sylow containment used in the last sentence of the source proof
follows from (1–2); it is not an extra placement assumption on X. -/
theorem X_le_T_of_core (F : InvariantFlag T V n) (L : Subgroup G) (g : G)
    (hIG : F.I₂ L ≤ F.Gi 2) [((F.I₂ L).subgroupOf (F.Gi 2)).Normal]
    (hcore : (F.I₂ L).pCoreIn 2 = F.W ⊔ F.X g) : F.X g ≤ (T : Subgroup G) := by
  have hnorm : (T : Subgroup G) ≤ normalizer ((F.I₂ L).pCoreIn 2 : Set G) :=
    (F.invariant 2).trans (((normal_subgroupOf_iff_le_normalizer hIG).mp inferInstance).trans
      (normalizer_le_normalizer_characteristic_image (F.I₂ L) (pCore 2 (F.I₂ L))))
  have hST := (isPGroup_pCoreIn 2 (F.I₂ L)).le_sylow_of_normalized T hnorm
  rw [hcore] at hST
  exact le_sup_right.trans hST

/-- W is proper because its plane generates the nonabelian group U under H. -/
theorem U_not_le_W (F : InvariantFlag T V n)
    (hspan : F.U = conjugateSpanBy (F.Vi 2) F.H)
    (hnonab : ¬ IsMulCommutative F.U) : ¬ F.U ≤ F.W := by
  intro hUW
  have hplane : F.Vi 2 ≤ F.ZU := by
    rw [ZU, centerIn_eq_inf_centralizer]
    exact le_inf ((F.le_seed 2).trans (le_conjugateSpanBy V F.H))
      (le_centralizer_iff.mp (hUW.trans inf_le_right))
  have hUZ : F.U ≤ F.ZU := by
    rw [hspan]
    exact conjugateSpanBy_le hplane F.H_normalizes_ZU
  exact hnonab (le_centralizer_iff_isMulCommutative.mp
    (hUZ.trans (centerIn_le_centralizer F.U)))

/-- The source R = C_T(Û), expressed as a subgroup of H. -/
def rHat (F : InvariantFlag T V n) : Subgroup F.H :=
  (T : Subgroup G).subgroupOf F.H ⊓ F.uhatAction.ker

/-- The source Ṽ₀, with the literal action on the image in H/V₁. -/
def rFixedTilde (F : InvariantFlag T V n) : Subgroup (F.tilde F.U) :=
  (F.localTildeAction F.H le_rfl).commonFixed F.rHat

/-- The Frattini product supplies the required vector; the vector itself
is not assumed. Establishing the product is the independent remaining step. -/
theorem exists_rFixedTilde_outside_W (F : InvariantFlag T V n) [IsMulCommutative V]
    (hproper : ¬ F.U ≤ F.W)
    (hgen : F.rFixedTilde ⊔ (F.tilde F.ZU).subgroupOf (F.tilde F.U) = ⊤) :
    ∃ a : F.tilde F.U, a ∈ F.rFixedTilde ∧ (a : F.G₁tilde) ∉ F.tilde F.W := by
  classical
  by_contra h
  push Not at h
  have hfixed : F.rFixedTilde ≤ (F.tilde F.W).subgroupOf (F.tilde F.U) := h
  have hcent : (F.tilde F.ZU).subgroupOf (F.tilde F.U) ≤
      (F.tilde F.W).subgroupOf (F.tilde F.U) := by
    intro a ha
    exact map_mono (comap_mono F.ZU_le_W) ha
  have hall : (⊤ : Subgroup (F.tilde F.U)) ≤
      (F.tilde F.W).subgroupOf (F.tilde F.U) := by
    rw [← hgen]
    exact sup_le hfixed hcent
  apply hproper
  intro u hu
  have hm := hall (show F.tildeMap F.U F.U_le_H ⟨u, hu⟩ ∈
      (⊤ : Subgroup (F.tilde F.U)) from mem_top _)
  exact (F.mem_tilde_iff_of_point_le F.W ((F.le_seed 1).trans F.seed_le_W)
    ⟨u, F.U_le_H hu⟩).mp hm

/-- Finish (5) from the Frattini product. This conditional assembly retains
that product as an unproved premise, to be discharged by its construction. -/
theorem action_kernels_eq_of_frattini_product (F : InvariantFlag T V n)
    [IsMulCommutative V] (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hn : 2 ≤ n) (g : G) (hgP : g ∈ F.P L)
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1)
    (hspan : F.U = conjugateSpanBy (F.Vi 2) F.H) (hnonab : ¬ IsMulCommutative F.U)
    (hXT : F.X g ≤ (T : Subgroup G))
    (hfixed : ∀ u ∈ F.U, u ∉ F.W → ∀ s ∈ F.W ⊔ F.X g,
      ⁅s, u⁆ ∈ F.E g → s ∈ F.W)
    (hgen : F.rFixedTilde ⊔ (F.tilde F.ZU).subgroupOf (F.tilde F.U) = ⊤) :
    F.xHatKernel g (F.P_le_G₂ hn L hL hgP) = F.E g ∧
      F.xTildeKernel g (F.P_le_G₂ hn L hL hgP) = F.E g := by
  let hg := F.P_le_G₂ hn L hL hgP
  have hinc := F.E_le_action_kernels (by omega) g hg hcomm
  have hhat : F.xHatKernel g hg ≤ F.E g := by
    intro x hx
    obtain ⟨hxX, hc⟩ := (F.mem_xHatKernel g hg x).mp hx
    obtain ⟨a, ha, houtside⟩ := F.exists_rFixedTilde_outside_W (F.U_not_le_W hspan hnonab) hgen
    have hxR : (⟨x, F.X_le_H g hg hxX⟩ : F.H) ∈ F.rHat :=
      ⟨hXT hxX, (F.mem_uhatAction_ker_iff _).mpr hc⟩
    have hxa := (MonoidHom.mem_commonFixed _ _ a).mp ha _ hxR
    have hxa' : F.xTildeAction g hg ⟨x, hxX⟩ a = a := by
      apply Subtype.ext
      exact congrArg Subtype.val hxa
    have hxW : x ∈ F.W := by
      by_contra hxW
      exact houtside (F.tilde_displacement L hL hn g hgP hfixed ⟨x, hxX⟩ hxW a hxa')
    exact ⟨hxW, hxX⟩
  exact ⟨le_antisymm hhat (hinc.1.trans hinc.2),
    le_antisymm (hinc.2.trans hhat) hinc.1⟩

/-- The final use of the inverse-image calculation, retaining the actual
point stabilizer in U/Z(U). The natural-module identification is still a premise. -/
theorem hat_stabilizer_le_of_commutator_preimage (F : InvariantFlag T V n)
    (g : G) (hg : g ∈ F.Gi 2) (u : F.U)
    [((F.E g).subgroupOf F.W).Normal]
    (hcomm : ∀ x ∈ F.X g, ⁅x, (u : G)⁆ ∈ F.W)
    (habel : ⁅F.W ⊔ F.X g, F.W ⊔ F.X g⁆ ≤ F.E g)
    (hpreimage : ∀ x : F.X g,
      F.parabolicCommutator g u hcomm habel x ∈
        (F.ZU.subgroupOf F.W).map (QuotientGroup.mk' ((F.E g).subgroupOf F.W)) →
      (x : G) ∈ conjugate F.ZU g ⊔ F.E g)
    (x : F.X g)
    (hx : F.xHatAction g hg x (QuotientGroup.mk' (center F.U) u) =
      QuotientGroup.mk' (center F.U) u) :
    (x : G) ∈ conjugate F.ZU g ⊔ F.E g := by
  apply hpreimage
  rw [F.parabolicCommutator_preimage]
  exact (le_sup_left : F.ZU ≤ F.ZU ⊔ F.E g)
    ((F.xHatAction_fixed_iff g hg x u).mp hx)

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
