module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.SourceInterfaces
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.FixedPoints
public import Theory.GroupAction.RegularCentralizerEmbedding

/-!
# The linear centralizer action on moved cosets

The earlier centralizer-closure theorem identifies the fixed cosets of an
involution u in D with the base orbit of L. Thus J=C_G(L) fixes those
cosets pointwise and acts faithfully on their complement. The PSL₂ order
formula gives |Γᵤ|=|L|, so freeness of the L-action implies regularity.
Inverse evaluation then constructs an actual injective homomorphism J →* L.

This module proves the action and cardinality steps of Lemma 12.14, keeping
freeness explicit. The final assembly must supply its prime-stabilizer proof.
Source: GLS IV, Chapter 2, Lemmas 12.10 and 12.14,
refs/KGroup/GLS4/Chapter2.tex.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d

/-- The order of the originally marked linear model. -/
public theorem Context.card_residualGenerated :
    Nat.card (residualGenerated M z t) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  rw [Nat.card_congr d.model.toEquiv]
  have hc := External.huppert614_card_psl_mul_center (K := BinaryGaloisField n)
  rw [External.huppert614_card_center_of_neg_one_eq_one
    (show (-1 : BinaryGaloisField n) = 1 from CharTwo.neg_eq _),
    GaloisField.card 2 n (by have := d.parameter; omega), mul_one] at hc
  exact hc

/-- The degree and fixed-point count give precisely the order of L moved points. -/
public theorem Context.card_movedPoints {u : G}
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u) :
    Nat.card {beta : G ⧸ M // u • beta ≠ beta} = Nat.card (residualGenerated M z t) := by
  classical
  let : Fintype (G ⧸ M) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    d.degree_and_fixed.1, d.degree_and_fixed.2 u huD hu, d.card_residualGenerated]
  rw [Nat.add_sub_add_right, Nat.mul_sub_left_distrib, mul_one]
  congr 1
  ring

/-- Every pair-stabilizer involution fixes exactly the local base orbit. -/
public theorem Context.fixedPoints_eq_local_baseOrbit {u : G}
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u) :
    {beta : G ⧸ M | u • beta = beta} =
      MulAction.orbit (residualGenerated M z t) (QuotientGroup.mk 1 : G ⧸ M) := by
  have hlocal := proper_residualGenerated_centralizer_local_data d.minimal d.reduction
    d.action d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.even_pair
  have hh := pair_involution_fixedPoints_eq_centralizerClosure_orbit
    d.reduction hlocal huD hu
  rwa [d.centralizer_closure huD hu] at hh

/-- The centralizer of `L` fixes every point fixed by the pair-stabilizer involution. -/
public theorem Context.centralizer_fixes_involution_fixedPoints {u j : G}
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (hj : j ∈ centralizer (residualGenerated M z t : Set G))
    {beta : G ⧸ M} (hbeta : u • beta = beta) : j • beta = beta := by
  have hjD := centralizer_residualGenerated_le_pairStabilizer
    d.minimal.disconnected d.z_mem d.z_mem_M hj
  have hjfix : j • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk 1 := by
    change j ∈ MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M)
    rw [baseCoset_stabilizer]
    exact hjD.1
  have hbeta' : beta ∈ MulAction.orbit (residualGenerated M z t)
      (QuotientGroup.mk 1 : G ⧸ M) := by
    rw [← d.fixedPoints_eq_local_baseOrbit huD hu]
    exact hbeta
  obtain ⟨l, rfl⟩ := MulAction.mem_orbit_iff.mp hbeta'
  change j • ((l : G) • (QuotientGroup.mk 1 : G ⧸ M)) = _
  rw [← mul_smul, ← mem_centralizer_iff.mp hj l l.property, mul_smul, hjfix]
  rfl

/-- Simplicity and properness make the action on the literal cosets faithful. -/
public theorem Context.coset_action_faithful {g : G}
    (hg : ∀ beta : G ⧸ M, g • beta = beta) : g = 1 := by
  have hc : M.normalCore = ⊥ := by
    rcases d.reduction.simple.eq_bot_or_eq_top_of_normal M.normalCore inferInstance with h | h
    · exact h
    · exact (d.minimal.disconnected.proper (top_le_iff.mp (h ▸ M.normalCore_le))).elim
  have hgker : g ∈ (MulAction.toPermHom G (G ⧸ M)).ker := by
    apply Equiv.Perm.ext
    exact hg
  rw [← M.normalCore_eq_ker, hc] at hgker
  exact hgker

/-- The centralizer preserves the complement of the involution fixed-point set. -/
public theorem Context.centralizer_preserves_movedPoints {u j : G}
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (hj : j ∈ centralizer (residualGenerated M z t : Set G))
    {beta : G ⧸ M} (hbeta : u • beta ≠ beta) : u • (j • beta) ≠ j • beta := by
  intro he
  have hjfix := d.centralizer_fixes_involution_fixedPoints huD hu hj he
  have hh : j • beta = beta := (MulAction.injective j) hjfix
  exact hbeta (hh ▸ he)

/-- The action of the centralizer on the moved cosets is faithful. -/
public theorem Context.centralizer_moved_action_faithful {u j : G}
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (hj : j ∈ centralizer (residualGenerated M z t : Set G))
    (hfix : ∀ beta : G ⧸ M, u • beta ≠ beta → j • beta = beta) : j = 1 := by
  apply d.coset_action_faithful
  intro beta
  by_cases hb : u • beta = beta
  · exact d.centralizer_fixes_involution_fixedPoints huD hu hj hb
  · exact hfix beta hb

/-- The actual injective centralizer homomorphism in Lemma 12.14(b), conditional on part (a). -/
public theorem Context.centralizer_embedding_of_regular {u : G}
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (hregular : ∀ a b : G ⧸ M, u • a ≠ a → u • b ≠ b →
      ∃! x : residualGenerated M z t, (x : G) • a = b) :
    ∃ f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t,
      Function.Injective f := by
  have hpos : 0 < Nat.card {beta : G ⧸ M // u • beta ≠ beta} := by
    rw [d.card_movedPoints huD hu]
    exact Nat.card_pos
  have hn : Nonempty {beta : G ⧸ M // u • beta ≠ beta} := Nat.card_pos_iff.mp hpos |>.1
  obtain ⟨a, ha⟩ := hn
  apply MulAction.exists_injective_hom_of_commuting_regular_action
    {beta : G ⧸ M | u • beta ≠ beta} a ha
  · intro b hb c hc
    exact hregular b c hb hc
  · intro j beta hbeta
    exact d.centralizer_preserves_movedPoints huD hu j.property hbeta
  · intro l j beta
    change (l : G) • ((j : G) • beta) = (j : G) • ((l : G) • beta)
    rw [← mul_smul, mem_centralizer_iff.mp j.property l l.property, mul_smul]
  · intro j hj
    apply Subtype.ext
    exact d.centralizer_moved_action_faithful huD hu j.property hj

/-- The source cardinalities turn freeness on the moved cosets into regularity. -/
public theorem Context.regular_on_moved_of_free {u : G}
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (hfree : ∀ x : residualGenerated M z t, ∀ beta : G ⧸ M,
      u • beta ≠ beta → (x : G) • beta = beta → x = 1)
    {a b : G ⧸ M} (ha : u • a ≠ a) (hb : u • b ≠ b) :
    ∃! x : residualGenerated M z t, (x : G) • a = b := by
  classical
  let L := residualGenerated M z t
  have huJ := d.pair_involution_centralizes huD hu
  let f : L → {beta : G ⧸ M // u • beta ≠ beta} := fun x =>
    ⟨(x : G) • a, by
      intro he
      apply ha
      apply MulAction.injective (x : G)
      change (x : G) • (u • a) = (x : G) • a
      rw [← mul_smul, mem_centralizer_iff.mp huJ x x.property, mul_smul]
      exact he⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have he : (x : G) • a = (y : G) • a := congrArg Subtype.val hxy
    have hfix : ((y⁻¹ * x : L) : G) • a = a := by
      simp only [coe_mul, coe_inv, mul_smul, he, inv_smul_smul]
    exact (inv_mul_eq_one.mp (hfree (y⁻¹ * x) a ha hfix)).symm
  have hbij : Function.Bijective f := (Nat.bijective_iff_injective_and_card f).mpr
    ⟨hf, (d.card_movedPoints huD hu).symm⟩
  obtain ⟨x, hx⟩ := hbij.surjective ⟨b, hb⟩
  refine ⟨x, congrArg Subtype.val hx, ?_⟩
  intro y hy
  exact hf (Subtype.ext (hy.trans (congrArg Subtype.val hx).symm))

/-- A distinguished involution fixes at most one literal coset. -/
public theorem Context.distinguished_fixedPoint_unique
    {x : G} (hxZ : x ∈ Z) {a b : G ⧸ M}
    (hxa : x • a = a) (hxb : x • b = b) : a = b := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (d.reduction.one_class z d.z_mem x hxZ)
  have hzfix (beta : G ⧸ M) (hb : x • beta = beta) :
      z • (g⁻¹ • beta) = g⁻¹ • beta := by
    calc
      _ = g⁻¹ • ((g * z * g⁻¹) • beta) := by
        simp only [mul_smul, inv_smul_smul]
      _ = g⁻¹ • beta := by rw [hg, hb]
  apply MulAction.injective g⁻¹
  exact (action_fixedPoint_eq_base d.minimal.disconnected d.z_mem d.z_mem_M (hzfix a hxa)).trans
    (action_fixedPoint_eq_base d.minimal.disconnected d.z_mem d.z_mem_M (hzfix b hxb)).symm

/-- The involution branch in the freeness proof of Lemma 12.14(a). -/
public theorem Context.involution_not_fix_movedPoint {u x : G}
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (hxL : x ∈ residualGenerated M z t) (hx : PFAppendixIII.IsInvolution x)
    {beta : G ⧸ M} (hbeta : u • beta ≠ beta) : x • beta ≠ beta := by
  intro hxfix
  have hxZ := (isInvolution_iff_mem_Z_in_proper_residualGenerated d.minimal.disconnected
    d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper hxL).mp hx
  have huJ := d.pair_involution_centralizes huD hu
  have hother : x • (u • beta) = u • beta := by
    rw [← mul_smul, mem_centralizer_iff.mp huJ x hxL, mul_smul, hxfix]
  exact hbeta (d.distinguished_fixedPoint_unique hxZ hother hxfix)

end BenderSuzuki.ZD.LinearExclusion
