module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.CubicControl
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# The solvable envelope of two component projections

For disjoint commuting factors B and C and Y contained in their product,
B ∩ YC and C ∩ YB are the images of Y under the two coordinate projections.
Their product is therefore solvable when Y is solvable. If Y is generated
by elements of order three, so are both images and their product. Nontrivial
commutator generation of each factor makes both images nontrivial, and the
order of their direct product is divisible by nine.

The intrinsic intersection formula also proves invariance whenever the actor
normalizes Y and permutes the two factors. This constructs the whole solvable
envelope; its two-core is not assumed trivial. The component-orbit argument
must still supply the two factors and their product containment.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1144,
the application of (j) and (b) to the possible L₃(2) orbit.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.OrbitClosure
variable {D : Type*} [Group D]

private theorem factorization_of_normalizes (Y C : Subgroup D)
    (hn : Y ≤ normalizer (C : Set D)) {x : D} (hx : x ∈ Y ⊔ C) :
    ∃ y ∈ Y, ∃ c ∈ C, y * c = x := by
  let J := Y ⊔ C
  have hc : (C.subgroupOf J).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_right).mpr (sup_le hn C.le_normalizer)
  let := hc
  have ht : Y.subgroupOf J ⊔ C.subgroupOf J = ⊤ := (codisjoint_subgroupOf_sup Y C).eq_top
  have hx' : (⟨x, hx⟩ : J) ∈ Y.subgroupOf J ⊔ C.subgroupOf J := ht ▸ mem_top _
  obtain ⟨y, hy, c, hc, he⟩ := mem_sup_of_normal_right.mp hx'
  exact ⟨y, hy, c, hc, congrArg Subtype.val he⟩

private theorem exists_projection (B C Y : Subgroup D)
    (hd : Disjoint B C) (hc : B ≤ centralizer (C : Set D)) (hY : Y ≤ B ⊔ C) :
    ∃ f : Y →* D, f.range = B ⊓ (Y ⊔ C) := by
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting B C hd hc
  let r : Y →* B × C := e.symm.toMonoidHom.comp (inclusion hY)
  let f : Y →* D := B.subtype.comp ((MonoidHom.fst B C).comp r)
  have hr (y : Y) : ((r y).1 : D) * (r y).2 = y :=
    (he (r y).1 (r y).2).symm.trans (congrArg Subtype.val (e.apply_symm_apply (inclusion hY y)))
  refine ⟨f, le_antisymm ?_ ?_⟩
  · rintro x ⟨y, rfl⟩
    refine ⟨(r y).1.property, ?_⟩
    have hy : f y = (y : D) * ((r y).2 : D)⁻¹ := by
      change ((r y).1 : D) = _
      rw [← hr y, mul_inv_cancel_right]
    rw [hy]
    exact (Y ⊔ C).mul_mem (mem_sup_left y.property) (mem_sup_right (C.inv_mem (r y).2.property))
  · intro x hx
    have hn : Y ≤ normalizer (C : Set D) :=
      hY.trans (sup_le (hc.trans (Subgroup.centralizer_le_normalizer _)) C.le_normalizer)
    obtain ⟨y, hy, c, hc', heq⟩ := factorization_of_normalizes Y C hn hx.2
    let y' : Y := ⟨y, hy⟩
    have hh : (⟨x, hx.1⟩, (1 : C)) = ((r y').1, (r y').2 * ⟨c, hc'⟩) := by
      apply mul_injective_of_disjoint hd
      change x * 1 = ((r y').1 : D) * (((r y').2 : D) * c)
      rw [mul_one, ← mul_assoc, hr y']
      exact heq.symm
    exact ⟨y', (congrArg (fun z : B × C => (z.1 : D)) hh).symm⟩

private theorem projection_nontrivial (B C Y : Subgroup D)
    (hd : Disjoint B C) (hc : B ≤ centralizer (C : Set D)) (hY : Y ≤ B ⊔ C)
    (hb : B ≠ ⊥) (hg : B = ⁅B, Y⁆) : B ⊓ (Y ⊔ C) ≠ ⊥ := by
  intro hz
  have hYC : Y ≤ C := by
    intro y hy
    obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting B C hd hc
    obtain ⟨⟨b, c⟩, hbc⟩ := e.surjective ⟨y, hY hy⟩
    have heq : (b : D) * c = y := (he b c).symm.trans (congrArg Subtype.val hbc)
    have hbmem : (b : D) ∈ B ⊓ (Y ⊔ C) := by
      refine ⟨b.property, ?_⟩
      have heq' : (b : D) = y * (c : D)⁻¹ := by rw [← heq, mul_inv_cancel_right]
      rw [heq']
      exact (Y ⊔ C).mul_mem (mem_sup_left hy) (mem_sup_right (C.inv_mem c.property))
    have hb1 : (b : D) = 1 := mem_bot.mp (hz ▸ hbmem)
    rw [hb1, one_mul] at heq
    exact heq ▸ c.property
  exact hb (hg.trans (commutator_eq_bot_iff_le_centralizer.mpr
    (hc.trans (centralizer_le hYC))))

/-- The product of the two coordinate projections of Y onto B and C. -/
def projectionEnvelope (B C Y : Subgroup D) : Subgroup D :=
  (B ⊓ (Y ⊔ C)) ⊔ (C ⊓ (Y ⊔ B))

private theorem projectionEnvelope_normalized (B C Y S : Subgroup D)
    (hY : S ≤ normalizer (Y : Set D))
    (hpair : ∀ s ∈ S,
      (B.map (MulAut.conj s).toMonoidHom = B ∧ C.map (MulAut.conj s).toMonoidHom = C) ∨
      (B.map (MulAut.conj s).toMonoidHom = C ∧ C.map (MulAut.conj s).toMonoidHom = B)) :
    S ≤ normalizer (projectionEnvelope B C Y : Set D) := by
  intro s hs
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (projectionEnvelope B C Y).map (MulAut.conj s).toMonoidHom = projectionEnvelope B C Y
  have hy := mem_normalizer_iff_map_conj_eq.mp (hY hs)
  change Y.map (MulAut.conj s).toMonoidHom = Y at hy
  simp only [projectionEnvelope, Subgroup.map_sup, Subgroup.map_inf _ _ (MulAut.conj s).toMonoidHom (MulAut.conj s).injective, hy]
  rcases hpair s hs with ⟨hb, hc⟩ | ⟨hb, hc⟩
  · rw [hb, hc]
  · rw [hb, hc, sup_comm]

/-- Both projection images contribute a cubic factor to the invariant solvable envelope. -/
theorem projectionEnvelope_properties (B C Y S : Subgroup D) [Group.IsSolvable Y]
    (hd : Disjoint B C) (hc : B ≤ centralizer (C : Set D))
    (hY : Y ≤ B ⊔ C) (ht : theta Y = Y)
    (hb : B ≠ ⊥) (hcne : C ≠ ⊥) (hbg : B = ⁅B, Y⁆) (hcg : C = ⁅C, Y⁆)
    (hYn : S ≤ normalizer (Y : Set D))
    (hpair : ∀ s ∈ S,
      (B.map (MulAut.conj s).toMonoidHom = B ∧ C.map (MulAut.conj s).toMonoidHom = C) ∨
      (B.map (MulAut.conj s).toMonoidHom = C ∧ C.map (MulAut.conj s).toMonoidHom = B)) :
    Group.IsSolvable (projectionEnvelope B C Y) ∧ theta (projectionEnvelope B C Y) = projectionEnvelope B C Y ∧
      S ≤ normalizer (projectionEnvelope B C Y : Set D) ∧ 9 ∣ Nat.card (projectionEnvelope B C Y) := by
  let P := B ⊓ (Y ⊔ C)
  let Q := C ⊓ (Y ⊔ B)
  obtain ⟨f, hf⟩ := exists_projection B C Y hd hc hY
  obtain ⟨g, hg⟩ := exists_projection C B Y hd.symm (le_centralizer_iff.mp hc) (hY.trans_eq (sup_comm B C))
  change f.range = P at hf
  change g.range = Q at hg
  have hp : theta P = P := hf ▸ theta_range_eq_self Y ht f
  have hq : theta Q = Q := hg ▸ theta_range_eq_self Y ht g
  let : Group.IsSolvable P := hf ▸ Group.isSolvable_of_surjective f.rangeRestrict_surjective
  let : Group.IsSolvable Q := hg ▸ Group.isSolvable_of_surjective g.rangeRestrict_surjective
  have hpq : Disjoint P Q := hd.mono inf_le_left inf_le_left
  have hpc : P ≤ centralizer (Q : Set D) := inf_le_left.trans (hc.trans (centralizer_le inf_le_left))
  obtain ⟨e, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting P Q hpq hpc
  have he : projectionEnvelope B C Y = P ⊔ Q := rfl
  refine ⟨Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective, ?_, projectionEnvelope_normalized B C Y S hYn hpair, ?_⟩
  · apply le_antisymm (theta_le _) (sup_le ?_ ?_)
    · exact hp.symm.le.trans (theta_mono le_sup_left)
    · exact hq.symm.le.trans (theta_mono le_sup_right)
  · obtain ⟨x, hx, hx3⟩ := exists_cubic_of_theta P hp (projection_nontrivial B C Y hd hc hY hb hbg)
    obtain ⟨z, hz, hz3⟩ := exists_cubic_of_theta Q hq (projection_nontrivial C B Y hd.symm
      (le_centralizer_iff.mp hc) (hY.trans_eq (sup_comm B C)) hcne hcg)
    have hp3 : 3 ∣ Nat.card P := by
      rw [← hx3, Subgroup.orderOf_coe (⟨x, hx⟩ : P)]
      exact orderOf_dvd_natCard _
    have hq3 : 3 ∣ Nat.card Q := by
      rw [← hz3, Subgroup.orderOf_coe (⟨z, hz⟩ : Q)]
      exact orderOf_dvd_natCard _
    rw [he, ← Nat.card_congr e.toEquiv, Nat.card_prod]
    exact Nat.mul_dvd_mul hp3 hq3
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.OrbitClosure
