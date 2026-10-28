module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex
public import BenderSuzuki.External.Huppert.XI.theorem_3_6
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder

/-!
# Cubic automorphisms detected by Suzuki Borel displacements

Root-valued displacements on the standard Borel force a cubic automorphism
to be identity. Root and torus normalization reduce the one-factor statement
to coordinate rigidity and the three-free group order. In the product, the
diagonal maps are automorphisms by simplicity, and commuting factors kill
the off-diagonal maps. No factor preservation is assumed.

Adapted from the intrinsic proof in
`CFSG/Quasithin/Chapter15/Section03/ComponentUniqueness/Candidates/SuzukiExclusion/ConcreteAction.lean`,
without its chapter interfaces. The normalization source is GLS III,
Theorem 2.5.12(b--f). Application: Aschbacher--Smith, 13.6.6, printed p.927.
-/

public section
open Subgroup BenderSuzuki BenderSuzuki.PFAppendixIII
namespace BenderSuzuki.MatrixGroups

private theorem root_le_borel (m : ℕ) : SuzukiRootSubgroup m ≤ SuzukiBorelSubgroup m := by
  rw [suzukiBorelSubgroup_eq_sup]; exact le_sup_left

private theorem torus_le_borel (m : ℕ) : SuzukiSplitTorus m ≤ SuzukiBorelSubgroup m := by
  rw [suzukiBorelSubgroup_eq_sup]; exact le_sup_right

/-- The action on the Borel modulo its two-core detects cubic automorphisms
of a single concrete Suzuki group. -/
theorem suzuki_cubic_eq_one_of_borel_displacement (m : ℕ) (hm : 0 < m)
    (α : MulAut (SuzukiMatrixGroup m)) (hα : α ^ 3 = 1)
    (hcomm : ∀ b ∈ SuzukiBorelSubgroup m,
      α b * b⁻¹ ∈ SuzukiRootSubgroup m) : α = 1 := by
  have hc (b : SuzukiMatrixGroup m) (hb : b ∈ SuzukiBorelSubgroup m) :
      α b * b⁻¹ ∈ SuzukiRootSubgroup m := by
    exact hcomm b hb
  have hU : (SuzukiRootSubgroup m).map α.toMonoidHom = SuzukiRootSubgroup m := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨u, hu, rfl⟩
      change α u ∈ SuzukiRootSubgroup m
      simpa only [inv_mul_cancel_right] using
        (SuzukiRootSubgroup m).mul_mem (hc u (root_le_borel m hu)) hu
    · exact (Subgroup.card_map_of_injective α.injective).ge
  obtain ⟨r, hrU, hrT⟩ := suzukiAut_normalize_split m hm α hU
  let β := MulAut.conj (r : SuzukiMatrixGroup m) * α
  have hβ (t : SuzukiSplitTorus m) : β t = t := by
    have htU : (t : SuzukiMatrixGroup m) * (r : SuzukiMatrixGroup m)⁻¹ *
        (t : SuzukiMatrixGroup m)⁻¹ ∈ SuzukiRootSubgroup m :=
      (Subgroup.mem_normalizer_iff.mp (suzukiSplitTorus_le_normalizer_root m t.property) _).mp
        ((SuzukiRootSubgroup m).inv_mem r.property)
    have hdiff : β t * (t : SuzukiMatrixGroup m)⁻¹ ∈ SuzukiRootSubgroup m := by
      convert (SuzukiRootSubgroup m).mul_mem
        ((SuzukiRootSubgroup m).mul_mem r.property (hc t (torus_le_borel m t.property))) htU using 1
      simp [β, MulAut.mul_apply, MulAut.conj_apply, mul_assoc]
    have hβt : β t ∈ SuzukiSplitTorus m := by
      have ht := Subgroup.mem_map_of_mem β.toMonoidHom t.property
      change β t ∈ (SuzukiSplitTorus m).map
        (MulAut.conj (r : SuzukiMatrixGroup m) * α).toMonoidHom at ht
      rwa [hrT] at ht
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp
      ((suzukiRootSubgroup_disjoint_splitTorus m hm).le_bot
        ⟨hdiff, (SuzukiSplitTorus m).mul_mem hβt ((SuzukiSplitTorus m).inv_mem t.property)⟩))
  obtain ⟨s, hsU, hsT, hsw⟩ := suzukiAut_normalize_weyl m hm β hrU hrT
  let γ := MulAut.conj (s : SuzukiMatrixGroup m) * β
  obtain ⟨σ, hσ⟩ := suzukiAut_eq_fieldAut_of_normalized m hm γ hsU hsT hsw
  have hγ (t : SuzukiSplitTorus m) : γ t = t := by
    let := suzukiSplitTorus_isCyclic m hm
    let := IsCyclic.commGroup (α := SuzukiSplitTorus m)
    have hst : (s : SuzukiMatrixGroup m) * t = t * s :=
      congrArg Subtype.val (mul_comm s t)
    simp only [γ, MulAut.mul_apply, MulAut.conj_apply, hβ, hst, mul_inv_cancel_right]
  have hfield (x : (BinaryGaloisField (2 * m + 1))ˣ) :
      σ (x : BinaryGaloisField (2 * m + 1)) ^ (2 ^ m) =
        (x : BinaryGaloisField (2 * m + 1)) ^ (2 ^ m) := by
    let t : SuzukiSplitTorus m :=
      ⟨⟨SuzukiTorusGL m x, Subgroup.subset_closure (Or.inr (Or.inl ⟨x, rfl⟩))⟩,
        (mem_suzukiSplitTorus_iff m _).mpr ⟨x, rfl⟩⟩
    have he := congrArg (fun g : SuzukiMatrixGroup m => g.val (1 : Fin 4) (1 : Fin 4)) (hγ t)
    rw [hσ, suzukiFieldAut_apply_entry] at he
    simpa [t, SuzukiTorusGL, SuzukiTorusMatrix] using he
  have hσone : σ = 1 := by
    ext x
    change σ x = x
    by_cases hx : x = 0
    · simp [hx]
    · have he := hfield (Units.mk0 x hx)
      exact (iterateFrobenius_inj _ 2 m) (by simpa only [iterateFrobenius_def, Units.val_mk0] using he)
  have hγone : γ = 1 := by
    rw [hσ, hσone, ← suzukiFieldAutHom_apply, map_one]
  have hinner : α = MulAut.conj (((s : SuzukiMatrixGroup m) * r)⁻¹) := by
    have he : MulAut.conj ((s : SuzukiMatrixGroup m) * r) * α = 1 := by
      simpa only [map_mul, mul_assoc, γ, β] using hγone
    exact eq_inv_of_mul_eq_one_right he |>.trans (map_inv _ _).symm
  apply (pow_eq_one_iff_of_coprime
    ((Nat.prime_three.coprime_iff_not_dvd).mpr (suzukiMatrixGroup_three_free m hm))).mp
  refine ⟨hα, ?_⟩
  rw [hinner, ← map_pow, pow_card_eq_one', map_one]

private theorem diagonal_bijective {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (B U : Subgroup G) (hne : ¬ B ≤ U) (f : G →* G)
    (hf : ∀ b ∈ B, f b * b⁻¹ ∈ U) : Function.Bijective f := by
  have hi : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
    · exact h
    · have hf1 : f = 1 := MonoidHom.ker_eq_top_iff.mp h
      exfalso
      apply hne
      intro b hb
      have hh := hf b hb
      simp only [hf1, MonoidHom.one_apply, one_mul] at hh
      exact (U).inv_mem_iff.mp hh
  exact ⟨hi, Finite.surjective_of_injective hi⟩

private theorem detector_prod {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hz : center G = ⊥) (B U : Subgroup G) (hne : ¬ B ≤ U)
    (hd : ∀ a : MulAut G, a ^ 3 = 1 → (∀ b ∈ B, a b * b⁻¹ ∈ U) → a = 1)
    (α : MulAut (G × G)) (hα : α ^ 3 = 1)
    (hcomm : ∀ x ∈ B.prod B, α x * x⁻¹ ∈ U.prod U) : α = 1 := by
  have hc (x : G × G) (hx : x ∈ B.prod B) :
      α x * x⁻¹ ∈ (U).prod (U) := by
    exact hcomm x hx
  let f : G →* G := ((MonoidHom.fst G G).comp α.toMonoidHom).comp (MonoidHom.inl G G)
  let g : G →* G := ((MonoidHom.snd G G).comp α.toMonoidHom).comp (MonoidHom.inr G G)
  have hf (b : G) (hb : b ∈ B) : f b * b⁻¹ ∈ U :=
    (hc (b, 1) ⟨hb, B.one_mem⟩).1
  have hg (b : G) (hb : b ∈ B) : g b * b⁻¹ ∈ U :=
    (hc (1, b) ⟨B.one_mem, hb⟩).2
  let a : MulAut G := MulEquiv.ofBijective f (diagonal_bijective B U hne f hf)
  let b : MulAut G := MulEquiv.ofBijective g (diagonal_bijective B U hne g hg)
  have hleft (x : G) : α (x, 1) = (a x, 1) := by
    apply Prod.ext
    · rfl
    · apply Subgroup.mem_bot.mp
      rw [← hz]
      apply mem_center_iff.mpr
      intro z
      obtain ⟨y, rfl⟩ := b.surjective z
      exact (congrArg Prod.snd
        (((MonoidHom.commute_inl_inr x y).map α).eq)).symm
  have hright (y : G) : α (1, y) = (1, b y) := by
    apply Prod.ext
    · apply Subgroup.mem_bot.mp
      rw [← hz]
      apply mem_center_iff.mpr
      intro z
      obtain ⟨x, rfl⟩ := a.surjective z
      exact congrArg Prod.fst (((MonoidHom.commute_inl_inr x y).map α).eq)
    · rfl
  have hsplit (x : G × G) : α x = (a x.1, b x.2) := by
    calc
      α x = α ((x.1, 1) * (1, x.2)) := by rw [Prod.fst_mul_snd]
      _ = _ := by rw [map_mul, hleft, hright]; simp
  have ha3 : a ^ 3 = 1 := by
    ext x
    have he := congrArg (fun c : MulAut (G × G) => (c (x, 1)).1) hα
    simpa only [pow_succ, pow_zero, mul_one, MulAut.mul_apply, hsplit,
      MulAut.one_apply] using he
  have hb3 : b ^ 3 = 1 := by
    ext y
    have he := congrArg (fun c : MulAut (G × G) => (c (1, y)).2) hα
    simpa only [pow_succ, pow_zero, mul_one, MulAut.mul_apply, hsplit,
      MulAut.one_apply] using he
  have ha1 : a = 1 := hd a ha3 hf
  have hb1 : b = 1 := hd b hb3 hg
  apply MulEquiv.ext
  intro x
  change α x = x
  simpa only [ha1, hb1, MulAut.one_apply, Prod.mk.eta] using hsplit x

private theorem suzuki_center_eq_bot (m : ℕ) (hm : 0 < m) :
    center (SuzukiMatrixGroup m) = ⊥ := by
  let := (External.huppert_blackburn_XI_3_6 m hm).1
  rcases (inferInstance : (center (SuzukiMatrixGroup m)).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (External.suzukiMatrixGroup_not_isSolvable m hm
      (Group.isSolvable_of_comm (fun x y => by
        have hx : x ∈ center (SuzukiMatrixGroup m) := h ▸ mem_top x
        exact (mem_center_iff.mp hx y).symm))).elim

private theorem suzuki_borel_not_le_root (m : ℕ) (hm : 0 < m) :
    ¬ SuzukiBorelSubgroup m ≤ SuzukiRootSubgroup m := by
  intro h
  have he : SuzukiSplitTorus m = ⊥ := le_bot_iff.mp (by
    intro t ht
    exact (suzukiRootSubgroup_disjoint_splitTorus m hm).le_bot
      ⟨h (torus_le_borel m ht), ht⟩)
  have hc := suzukiSplitTorus_card m hm
  rw [he, Subgroup.card_bot] at hc
  have hq : 2 ^ 3 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- The product Borel detects cubic automorphisms, including possible factor mixing. -/
theorem suzuki_pair_cubic_eq_one_of_borel_displacement (m : ℕ) (hm : 0 < m)
    (α : MulAut (SuzukiMatrixGroup m × SuzukiMatrixGroup m)) (hα : α ^ 3 = 1)
    (hcomm : ∀ x ∈ (SuzukiBorelSubgroup m).prod (SuzukiBorelSubgroup m),
      α x * x⁻¹ ∈ (SuzukiRootSubgroup m).prod (SuzukiRootSubgroup m)) : α = 1 := by
  let := (External.huppert_blackburn_XI_3_6 m hm).1
  exact detector_prod (suzuki_center_eq_bot m hm) (SuzukiBorelSubgroup m)
    (SuzukiRootSubgroup m) (suzuki_borel_not_le_root m hm)
    (suzuki_cubic_eq_one_of_borel_displacement m hm) α hα hcomm

end BenderSuzuki.MatrixGroups
