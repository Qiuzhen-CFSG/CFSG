module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Linear.Placement.Transport
public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.SpecificGroups.PSL3.ProjectionKernel
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# Scalar covers in the binary PSL₃ branch

The only earlier-source input retained here is the universal multiplier
calculation from I.1.3: cyclic three or trivial in the ordinary cases, and
C₄ × C₄ × C₃ over the four-element field. `UniversalMultiplierInput` states
this for actual universal perfect central covers, with no identification of
such a cover with SL₃.

Construct the universal cover and compare it with both SL₃ and the given
quasisimple group Q. Perfectness makes both comparison maps surjective.
The actual scalar kernel of SL₃ has the ordinary multiplier order, so the
kernel of the comparison to SL₃ has order one, or sixteen when f = 2.
Its image in Q is a normal two-group and vanishes because O₂(Q) = 1.
The comparison to Q therefore descends to a surjection SL₃ → Q commuting
with the chosen projections. No geometric placement assumption is used.

Source: Aschbacher–Smith, I.1.1 and I.1.3, printed p.407 (PDF p.418),
as used in the proof of Proposition 1.3.4, printed p.511 (PDF p.528),
`refs/quasithin.pdf`. Proving the retained multiplier input belongs to the
source-theorem assembly; the cover comparison itself is proved here.
-/

public section
open Subgroup PerfectCentralCovering
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear.Placement.ScalarCover
universe u v

/-- The binary degree-three part of source I.1.3, stated for actual universal
perfect central covers. The exceptional multiplier is C₄ × C₄ × C₃;
otherwise it is C₃ or trivial according to the field-order congruence.
This is an explicit earlier-source input, not an assertion that SL₃ is universal. -/
@[expose] def UniversalMultiplierInput (F : Type u) [Field F] [Finite F] (f : ℕ) : Prop :=
  ∀ (U : Type u) [Group U] [Finite U] (c : Cover U PSL(3,F)),
    IsUniversal.{u,u,u} c →
    (f = 2 → Nonempty (c.toMonoidHom.ker ≃*
      ((Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ×
        Multiplicative (ZMod 3)))) ∧
    (2 < f → Nonempty (c.toMonoidHom.ker ≃*
      Multiplicative (ZMod (if Nat.card F % 3 = 1 then 3 else 1))))

private theorem card_ker_mul_of_surjective {A B : Type*} [Group A] [Group B]
    (a : A →* B) (ha : Function.Surjective a) :
    Nat.card a.ker * Nat.card B = Nat.card A := by
  simpa only [index_ker, MonoidHom.range_eq_top.mpr ha, card_top]
    using a.ker.card_mul_index

private theorem card_comparison_kernel {A B C : Type*}
    [Group A] [Group B] [Group C] [Finite C]
    (a : A →* B) (b : B →* C) (c : A →* C)
    (ha : Function.Surjective a) (hb : Function.Surjective b)
    (hc : Function.Surjective c) :
    Nat.card a.ker * Nat.card b.ker = Nat.card c.ker := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := C))
  calc
    (Nat.card a.ker * Nat.card b.ker) * Nat.card C =
        Nat.card a.ker * Nat.card B := by
      rw [mul_assoc, card_ker_mul_of_surjective b hb]
    _ = Nat.card A := card_ker_mul_of_surjective a ha
    _ = Nat.card c.ker * Nat.card C := (card_ker_mul_of_surjective c hc).symm

/-- A commuting comparison from a universal cover to SL₃ is surjective. Its
kernel has order one in the ordinary cases and sixteen over the four-element field. -/
theorem comparison_kernel_card {F : Type u} [Field F] [Finite F]
    {f : ℕ} (hf : 2 ≤ f) (hF : Nat.card F = 2^f)
    (hI : UniversalMultiplierInput F f)
    {U : Type u} [Group U] [Finite U] (c : Cover U PSL(3,F))
    (hc : IsUniversal.{u,u,u} c)
    (a : U →* SL(3,F)) (ha : (Matrix.PSL3.projection F).comp a = c.toMonoidHom) :
    Function.Surjective a ∧ Nat.card a.ker = if f = 2 then 16 else 1 := by
  let _ := Atlas.sl_perfect (F := F) 3 (by decide)
  have hsurj : Function.Surjective a :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      (Matrix.PSL3.projection F) a (ha ▸ c.surjective)
      (by rw [Matrix.PSL3.projection_ker])
  refine ⟨hsurj, ?_⟩
  have hcount := card_comparison_kernel a (Matrix.PSL3.projection F) c.toMonoidHom
    hsurj (Matrix.PSL3.projection_surjective F) c.surjective
  obtain ⟨hex, hord⟩ := hI U c hc
  by_cases hf2 : f = 2
  · obtain ⟨e⟩ := hex hf2
    have he := Nat.card_congr e.toEquiv
    change Nat.card c.toMonoidHom.ker = Nat.card ((ZMod 4 × ZMod 4) × ZMod 3) at he
    norm_num [Nat.card_prod, Nat.card_zmod] at he
    change Nat.card c.toMonoidHom.ker = 48 at he
    rw [Matrix.PSL3.card_projectionKernel, hF, hf2, he] at hcount
    norm_num at hcount
    rw [if_pos hf2]
    change Nat.card a.ker * 3 = 48 at hcount
    omega
  · obtain ⟨e⟩ := hord (by omega)
    have he := Nat.card_congr e.toEquiv
    change Nat.card c.toMonoidHom.ker =
      Nat.card (ZMod (if Nat.card F % 3 = 1 then 3 else 1)) at he
    rw [Nat.card_zmod] at he
    have hscalar : Nat.card (Matrix.PSL3.projection F).ker =
        if Nat.card F % 3 = 1 then 3 else 1 := by
      split_ifs with hm
      · have hh := Nat.card_congr (Matrix.PSL3.projectionKernelEquivThree F hm).toEquiv
        change Nat.card (Matrix.PSL3.projection F).ker = Nat.card (ZMod _) at hh
        simpa only [Nat.card_zmod] using hh
      · have hh := Nat.card_congr (Matrix.PSL3.projectionKernelEquivOne F hm).toEquiv
        change Nat.card (Matrix.PSL3.projection F).ker = Nat.card (ZMod _) at hh
        simpa only [Nat.card_zmod] using hh
    rw [hscalar, he] at hcount
    split_ifs at hcount <;> simp_all

/-- The actual commuting scalar-cover surjection needed by placement. The only
extra premise is the explicitly stated universal multiplier implication of I.1.3. -/
theorem exists_scalar_cover {Q : Type v} [Group Q] [Finite Q]
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    {F : Type u} [Field F] [Finite F] {f : ℕ}
    (hf : 2 ≤ f) (hF : Nat.card F = 2^f)
    (hI : UniversalMultiplierInput F f)
    (e : Q ⧸ center Q ≃* PSL(3,F)) :
    ∃ k : SL(3,F) →* Q, Function.Surjective k ∧
      (modelProjection e).comp k = Matrix.PSL3.projection F := by
  let _ := h.quasisimple
  let _ := Atlas.sl_perfect (F := F) 3 (by decide)
  let _ := Atlas.psl_perfect (F := F) 3 (by decide)
  let c := universalCover PSL(3,F)
  have hc : IsUniversal.{u,u,u} c := universalCover_isUniversal
  obtain ⟨a, ha, _⟩ := hc SL(3,F)
    { toMonoidHom := Matrix.PSL3.projection F
      surjective := Matrix.PSL3.projection_surjective F
      isPerfect := inferInstance
      ker_le_center := by rw [Matrix.PSL3.projection_ker] }
  obtain ⟨b, hb, _⟩ := universalProjection_existsUnique_lift
    (modelProjection e) (modelProjection_surjective e) (by rw [modelProjection_ker])
  have hbsurj : Function.Surjective b :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      (modelProjection e) b (hb ▸ c.surjective) (by rw [modelProjection_ker])
  obtain ⟨hasurj, hak⟩ := comparison_kernel_card hf hF hI c hc a ha
  have hp : IsPGroup 2 a.ker := by
    by_cases hf2 : f = 2
    · apply IsPGroup.of_card (n := 4)
      simpa [hf2] using hak
    · apply IsPGroup.of_card (n := 0)
      simpa [hf2] using hak
  have hmap : a.ker.map b ≤ pCore 2 Q :=
    le_sSup ⟨Subgroup.Normal.map inferInstance b hbsurj, hp.map b⟩
  have hkill : a.ker ≤ b.ker := by
    rw [h.twoCore] at hmap
    intro x hx
    exact Subgroup.mem_bot.mp (hmap (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
  let k : SL(3,F) →* Q := a.liftOfSurjective hasurj ⟨b, hkill⟩
  have hk : k.comp a = b := MonoidHom.liftOfRightInverse_comp _ _ _ _
  refine ⟨k, ?_, ?_⟩
  · intro q
    obtain ⟨x, rfl⟩ := hbsurj q
    exact ⟨a x, DFunLike.congr_fun hk x⟩
  · apply (MonoidHom.cancel_right hasurj).mp
    rw [MonoidHom.comp_assoc, hk, hb]
    exact ha.symm

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear.Placement.ScalarCover
