module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Linear
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Field.ZMod

/-!
# The binary plane fixer and its contragredient fixed line

An order-four subgroup fixing a natural plane in SL₃(2) is its full
pointwise fixer. Evaluation on a vector outside the plane embeds the fixer
in the plane, and the given order makes the actor's displacement map onto.
The dot-product pairing then identifies the dual fixed space with the
annihilator. Separation supplies a nonzero covector; evaluation on the same
outside vector proves that the annihilator is exactly a binary line.

These are model facts for the doubled-dual neighboring quotient used in
Meierfrankenfeld--Stellmacher (1993), (4.5.4)--(4.5.5), printed pp.898--899.
The actual local actors and quotient markings are supplied separately.
-/

@[expose] public section

open Matrix
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Linear
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.NeighborAction.Linear

private theorem binary : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

private theorem neg_vector (v : W) : -v = v := by
  funext i
  exact CharTwo.neg_eq (v i)

private theorem natural_inv (g : S) (v : W) : g.val.mulVec ((g⁻¹).val.mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
  exact Matrix.one_mulVec v

private theorem dot_ext {v w : W} (h : ∀ x : W, v ⬝ᵥ x = w ⬝ᵥ x) : v = w := by
  funext i
  simpa using h (Pi.single i 1)

private theorem plane_cosets (P : Submodule (ZMod 2) W) (hP : Nat.card P = 4) :
    ∃ t : W, t ∉ P ∧ ∀ v : W, v + t ∈ P ∨ v ∈ P := by
  have h := P.toAddSubgroup.card_mul_index
  have hW : Nat.card W = 8 := by simp [W, Nat.card_eq_fintype_card]
  change Nat.card P * P.toAddSubgroup.index = Nat.card W at h
  rw [hP, hW] at h
  exact (AddSubgroup.index_eq_two_iff_exists_notMem_and (H := P.toAddSubgroup)).mp (by omega)

/-- The subgroup fixing every vector of the indicated natural plane. -/
def planeFixer (P : Submodule (ZMod 2) W) : Subgroup S where
  carrier := {g | ∀ v ∈ P, g.val.mulVec v = v}
  one_mem' := by intro v hv; exact one_mulVec v
  mul_mem' := by
    intro g h hg hh v hv
    rw [Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hh v hv, hg v hv]
  inv_mem' := by
    intro g hg v hv
    have h := natural_inv g⁻¹ v
    simpa only [inv_inv, hg v hv] using h

/-- Covectors vanishing on the literal natural plane. -/
def annihilator (P : Submodule (ZMod 2) W) : Submodule (ZMod 2) W where
  carrier := {v | ∀ p ∈ P, v ⬝ᵥ p = 0}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw p hp; simp [add_dotProduct, hv p hp, hw p hp]
  smul_mem' := by intro c v hv p hp; simp [smul_dotProduct, hv p hp]

private theorem outside_image {P : Submodule (ZMod 2) W} {t : W} (ht : t ∉ P)
    {g : S} (hg : g ∈ planeFixer P) : g.val.mulVec t ∉ P := by
  intro hm
  have h := (planeFixer P).inv_mem hg _ hm
  have hi : (g⁻¹).val.mulVec (g.val.mulVec t) = t := by
    simpa only [inv_inv] using natural_inv g⁻¹ t
  rw [hi] at h
  exact ht (h.symm ▸ hm)

private theorem evaluation_injective {P : Submodule (ZMod 2) W} {t : W}
    (hc : ∀ v : W, v + t ∈ P ∨ v ∈ P) :
    Function.Injective (fun g : planeFixer P => g.val.val.mulVec t) := by
  intro g h he
  change g.val.val.mulVec t = h.val.val.mulVec t at he
  apply Subtype.ext
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext v
  rcases hc v with hv | hv
  · have eg := g.property (v + t) hv
    have eh := h.property (v + t) hv
    rw [mulVec_add] at eg eh
    exact add_right_cancel (eg.trans eh.symm |>.trans (by rw [he]))
  · exact (g.property v hv).trans (h.property v hv).symm

/-- For every vector in the plane, some actor has that displacement on an outside vector. -/
theorem plane_displacement_surjective (K : Subgroup S) (P : Submodule (ZMod 2) W)
    (hK : Nat.card K = 4) (hP : Nat.card P = 4) (hfix : K ≤ planeFixer P) :
    ∃ t : W, t ∉ P ∧ ∀ p ∈ P, ∃ k ∈ K, k.val.mulVec t - t = p := by
  obtain ⟨t, ht, hc⟩ := plane_cosets P hP
  have hm (k : K) : k.val.val.mulVec t - t ∈ P := by
    rcases hc (k.val.val.mulVec t) with h | h
    · simpa only [sub_eq_add_neg, neg_vector] using h
    · exact (outside_image ht (hfix k.property) h).elim
  let f : K → P := fun k => ⟨k.val.val.mulVec t - t, hm k⟩
  have hinj : Function.Injective f := by
    intro k l h
    have he : k.val.val.mulVec t = l.val.val.mulVec t :=
      (sub_left_inj).mp (congrArg Subtype.val h)
    have hh := evaluation_injective hc (a₁ := ⟨k.val, hfix k.property⟩)
      (a₂ := ⟨l.val, hfix l.property⟩) he
    apply Subtype.ext
    exact congrArg (fun q : planeFixer P => (q : S)) hh
  have hs := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, hK.trans hP.symm⟩).2
  refine ⟨t, ht, fun p hp => ?_⟩
  obtain ⟨k, hk⟩ := hs ⟨p, hp⟩
  exact ⟨k, k.property, congrArg Subtype.val hk⟩

/-- The order-four actor is the whole pointwise fixer, not just a subgroup of it. -/
theorem eq_planeFixer (K : Subgroup S) (P : Submodule (ZMod 2) W)
    (hK : Nat.card K = 4) (hP : Nat.card P = 4) (hfix : K ≤ planeFixer P) :
    K = planeFixer P := by
  obtain ⟨t, ht, hc⟩ := plane_cosets P hP
  have hm (g : planeFixer P) : g.val.val.mulVec t + t ∈ P :=
    (hc _).resolve_right (outside_image ht g.property)
  let f : planeFixer P → P := fun g => ⟨g.val.val.mulVec t + t, hm g⟩
  have hinj : Function.Injective f := by
    intro g h he
    exact evaluation_injective hc (add_right_cancel (congrArg Subtype.val he))
  have hle := Nat.card_le_card_of_injective f hinj
  rw [hP, ← hK] at hle
  have hs := (Subgroup.inclusion_injective hfix).bijective_of_nat_card_le hle
  apply le_antisymm hfix
  intro g hg
  obtain ⟨k, hk⟩ := hs.2 ⟨g, hg⟩
  have he : (k : S) = g := congrArg Subtype.val hk
  exact he ▸ k.property

/-- Fixed covectors are exactly those annihilating the fixed natural plane. -/
theorem dual_fixed_iff (K : Subgroup S) (P : Submodule (ZMod 2) W)
    (hK : Nat.card K = 4) (hP : Nat.card P = 4) (hfix : K ≤ planeFixer P) (v : W) :
    (∀ k ∈ K, dual k v = v) ↔ v ∈ annihilator P := by
  constructor
  · intro hv p hp
    obtain ⟨t, ht, hs⟩ := plane_displacement_surjective K P hK hP hfix
    obtain ⟨k, hk, he⟩ := hs p hp
    have heval := congrArg (fun w : W => t ⬝ᵥ w) (hv k⁻¹ (K.inv_mem hk))
    simp only [dual, inv_inv, dotProduct_transpose_mulVec] at heval
    rw [dotProduct_comm t v] at heval
    rw [← he, dotProduct_sub, heval, sub_self]
  · intro hv k hk
    apply dot_ext
    intro x
    obtain ⟨t, ht, hc⟩ := plane_cosets P hP
    have hm : (k⁻¹).val.mulVec x - x ∈ P := by
      rcases hc x with hx | hx
      · have hi := hfix (K.inv_mem hk) (x + t) hx
        have hi' : (k⁻¹).val.mulVec t + t ∈ P :=
          (hc _).resolve_right (outside_image ht (hfix (K.inv_mem hk)))
        have eq : (k⁻¹).val.mulVec x - x = t - (k⁻¹).val.mulVec t := by
          apply sub_eq_sub_iff_add_eq_add.mpr
          simpa only [mulVec_add, add_comm] using hi
        rw [eq, sub_eq_add_neg, neg_vector, add_comm]
        exact hi'
      · rw [hfix (K.inv_mem hk) x hx, sub_self]
        exact P.zero_mem
    have hh := hv _ hm
    rw [dotProduct_sub, sub_eq_zero] at hh
    rw [dotProduct_comm (dual k v) x, dual, dotProduct_transpose_mulVec]
    exact hh

/-- Every dual displacement annihilates the pointwise fixed natural plane. -/
theorem dual_displacement_mem (K : Subgroup S) (P : Submodule (ZMod 2) W)
    (hfix : K ≤ planeFixer P) {k : S} (hk : k ∈ K) (v : W) :
    v - dual k v ∈ annihilator P := by
  intro p hp
  rw [sub_dotProduct]
  have hh : dual k v ⬝ᵥ p = v ⬝ᵥ p := by
    rw [dotProduct_comm, dual, dotProduct_transpose_mulVec, hfix (K.inv_mem hk) p hp]
  rw [hh, sub_self]

/-- The annihilator is an actual binary line. -/
theorem annihilator_line (P : Submodule (ZMod 2) W) (hP : Nat.card P = 4) :
    ∃ n : W, n ≠ 0 ∧ ∀ v : W, v ∈ annihilator P ↔ v = 0 ∨ v = n := by
  obtain ⟨t, ht, hc⟩ := plane_cosets P hP
  have hinj {v w : W} (hv : v ∈ annihilator P) (hw : w ∈ annihilator P)
      (he : v ⬝ᵥ t = w ⬝ᵥ t) : v = w := by
    apply dot_ext
    intro x
    rcases hc x with hx | hx
    · have hh := (hv _ hx).trans (hw _ hx).symm
      rw [dotProduct_add, dotProduct_add, he] at hh
      exact add_right_cancel hh
    · rw [hv x hx, hw x hx]
  have hproper : P < ⊤ := lt_top_iff_ne_top.mpr (by
    intro he
    apply ht
    rw [he]
    exact Submodule.mem_top)
  obtain ⟨f, hf, hp⟩ := Submodule.exists_le_ker_of_lt_top
    (K := ZMod 2) (V := W) P hproper
  let n : W := (dotProductEquiv (ZMod 2) (Fin 3)).symm f
  have hn : n ≠ 0 := by
    intro hn
    apply hf
    have he := (dotProductEquiv (ZMod 2) (Fin 3)).apply_symm_apply f
    change (dotProductEquiv (ZMod 2) (Fin 3)) n = f at he
    rw [hn, map_zero] at he
    exact he.symm
  have hnP : n ∈ annihilator P := by
    intro p hp'
    have he := LinearMap.congr_fun ((dotProductEquiv (ZMod 2) (Fin 3)).apply_symm_apply f) p
    exact he.trans (hp hp')
  have hnt : n ⬝ᵥ t = 1 := (binary _).resolve_left (fun h => hn (hinj hnP
    (annihilator P).zero_mem (by simpa using h)))
  refine ⟨n, hn, fun v => ⟨fun hv => ?_, ?_⟩⟩
  · rcases binary (v ⬝ᵥ t) with hv0 | hv1
    · exact Or.inl (hinj hv (annihilator P).zero_mem (by simpa using hv0))
    · exact Or.inr (hinj hv hnP (hv1.trans hnt.symm))
  · rintro (rfl | rfl)
    · exact (annihilator P).zero_mem
    · exact hnP

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.NeighborAction.Linear
