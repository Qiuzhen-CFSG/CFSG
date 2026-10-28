module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Glauberman.BlockConstruction.Basic
public import Theory.Representation.BinaryDihedralSplitting

/-!
# Plane support of an odd conjugate pair

Two rank-one involutions with nonidentity odd-order product move a binary
plane. Odd-order splitting decomposes the product support into the two
reflection supports; neither vanishes, and each has dimension at most one.
The full reflection supports therefore lie in this plane, forcing the
product's fixed complement to be fixed by both reflections.

This supplies the linear part of Kurzweil–Stellmacher 9.3.3 and the splitting
argument of 9.3.6, printed pp.241–242 and245 of `refs/original/kurzweil.pdf`.
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.Glauberman.BlockConstruction.PairRecognition
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

lemma moved_mono {W U : Submodule (ZMod 2) V} {A B : Subgroup G}
    (hWU : W ≤ U) (hAB : A ≤ B) :
    subspaceCommutator ρ W A ≤ subspaceCommutator ρ U B := by
  apply Submodule.span_mono
  rintro _ ⟨a, ha, w, hw, rfl⟩
  exact ⟨a, hAB ha, w, hWU hw, rfl⟩

private lemma moved_sup (A B : Subgroup G) :
    subspaceCommutator ρ ⊤ (A ⊔ B) =
      subspaceCommutator ρ ⊤ A ⊔ subspaceCommutator ρ ⊤ B := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, v, _, rfl⟩
    have hh : ∀ v : V, ρ g v - v ∈
        subspaceCommutator ρ ⊤ A ⊔ subspaceCommutator ρ ⊤ B := by
      rw [Subgroup.sup_eq_closure] at hg
      induction hg using Subgroup.closure_induction with
      | mem a ha =>
        intro v
        rcases ha with ha | ha
        · exact (le_sup_left : subspaceCommutator ρ ⊤ A ≤ _) (Submodule.subset_span ⟨a, ha, v, Submodule.mem_top, rfl⟩)
        · exact (le_sup_right : subspaceCommutator ρ ⊤ B ≤ _) (Submodule.subset_span ⟨a, ha, v, Submodule.mem_top, rfl⟩)
      | one => intro v; simp
      | mul a b _ _ ha hb =>
        intro v
        have hh := (subspaceCommutator ρ ⊤ A ⊔ subspaceCommutator ρ ⊤ B).add_mem
          (ha (ρ b v)) (hb v)
        simpa only [map_mul, Module.End.mul_apply, sub_add_sub_cancel] using hh
      | inv a _ ha =>
        intro v
        have hh := (subspaceCommutator ρ ⊤ A ⊔ subspaceCommutator ρ ⊤ B).neg_mem
          (ha (ρ a⁻¹ v))
        simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_apply, neg_sub] using hh
    exact hh v
  · exact sup_le (moved_mono ρ le_rfl le_sup_left) (moved_mono ρ le_rfl le_sup_right)

private lemma fixed_sup (A B : Subgroup G) :
    fixedSpace ρ (A ⊔ B) = fixedSpace ρ A ⊓ fixedSpace ρ B := by
  ext v
  constructor
  · intro hv
    exact ⟨fun a => hv ⟨a, (le_sup_left : A ≤ A ⊔ B) a.property⟩,
      fun b => hv ⟨b, (le_sup_right : B ≤ A ⊔ B) b.property⟩⟩
  · rintro ⟨ha, hb⟩ ⟨g, hg⟩
    change ρ g v = v
    rw [Subgroup.sup_eq_closure] at hg
    induction hg using Subgroup.closure_induction with
    | mem a h =>
      rcases h with h | h
      · exact ha ⟨a, h⟩
      · exact hb ⟨a, h⟩
    | one => simp
    | mul a b _ _ ha hb => simp only [map_mul, Module.End.mul_apply, ha, hb]
    | inv a _ ha =>
      have h := congrArg (ρ a⁻¹) ha
      simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply] using h.symm

variable [Finite G] [FiniteDimensional (ZMod 2) V]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private lemma odd_moved_ne_bot (hρ : Function.Injective ρ) {t u : G} (hne : t * u ≠ 1) :
    subspaceCommutator ρ ⊤ (zpowers (t * u)) ≠ ⊥ := by
  intro hbot
  apply hne
  apply hρ
  ext v
  rw [map_one, Module.End.one_apply]
  exact (mem_fixedSpace_zpowers_iff ρ (t * u) v).mp
    ((subspaceCommutator_eq_bot_iff ρ ⊤ _).mp hbot Submodule.mem_top)

lemma odd_pair_plane (hρ : Function.Injective ρ) (t u : G)
    (ht : t * t = 1) (hu : u * u = 1) (hne : t * u ≠ 1)
    (hodd : Odd (orderOf (t * u)))
    (hdt : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (zpowers t)) = 1)
    (hdu : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (zpowers u)) = 1) :
    let E := zpowers t ⊔ zpowers u
    let R := zpowers (t * u)
    subspaceCommutator ρ ⊤ R = subspaceCommutator ρ ⊤ E ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ E) = 2 ∧
      IsCompl (subspaceCommutator ρ ⊤ E) (fixedSpace ρ E) := by
  let W := subspaceCommutator ρ ⊤ (zpowers (t * u))
  let T := subspaceCommutator ρ W (zpowers t)
  let U := subspaceCommutator ρ W (zpowers u)
  have hsplit := Representation.BinaryDihedralSplitting.splitting_of_odd_product ρ t u ht hu hodd
  change IsCompl W (fixedSpace ρ (zpowers (t * u))) ∧ Disjoint T U ∧
    T ⊔ U = W ∧ W ⊓ fixedSpace ρ (zpowers t) = T at hsplit
  have hWne : W ≠ ⊥ := odd_moved_ne_bot ρ hρ hne
  have hTne : T ≠ ⊥ := by
    intro he
    have hfix : W ≤ fixedSpace ρ (zpowers t) :=
      (subspaceCommutator_eq_bot_iff ρ W _).mp he
    have hz := hsplit.2.2.2
    rw [inf_eq_left.mpr hfix, he] at hz
    exact hWne hz
  have hrev : u * t = (t * u)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht, inv_eq_of_mul_eq_one_right hu]
  have hswap : subspaceCommutator ρ ⊤ (zpowers (u * t)) = W := by
    have he : u * t = (t * u)⁻¹ := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht, inv_eq_of_mul_eq_one_right hu]
    rw [he, zpowers_inv]
  have hsplit' := Representation.BinaryDihedralSplitting.splitting_of_odd_product ρ u t hu ht
    (by rwa [hrev, orderOf_inv])
  rw [hswap] at hsplit'
  have hUne : U ≠ ⊥ := by
    intro he
    have hfix : W ≤ fixedSpace ρ (zpowers u) :=
      (subspaceCommutator_eq_bot_iff ρ W _).mp he
    have hz : W ⊓ fixedSpace ρ (zpowers u) = U := hsplit'.2.2.2
    rw [inf_eq_left.mpr hfix, he] at hz
    exact hWne hz
  have hTle := moved_mono ρ (show W ≤ ⊤ from le_top) (show zpowers t ≤ zpowers t from le_rfl)
  have hUle := moved_mono ρ (show W ≤ ⊤ from le_top) (show zpowers u ≤ zpowers u from le_rfl)
  have hdT : Module.finrank (ZMod 2) T = 1 := by
    have hle : Module.finrank (ZMod 2) T ≤ 1 := hdt ▸ Submodule.finrank_mono hTle
    have hpos := mt Submodule.finrank_eq_zero.mp hTne
    omega
  have hdU : Module.finrank (ZMod 2) U = 1 := by
    have hle : Module.finrank (ZMod 2) U ≤ 1 := hdu ▸ Submodule.finrank_mono hUle
    have hpos := mt Submodule.finrank_eq_zero.mp hUne
    omega
  have hTe : T = subspaceCommutator ρ ⊤ (zpowers t) :=
    Submodule.eq_of_le_of_finrank_eq hTle (hdT.trans hdt.symm)
  have hUe : U = subspaceCommutator ρ ⊤ (zpowers u) :=
    Submodule.eq_of_le_of_finrank_eq hUle (hdU.trans hdu.symm)
  have hWE : W = subspaceCommutator ρ ⊤ (zpowers t ⊔ zpowers u) := by
    rw [moved_sup, ← hTe, ← hUe, hsplit.2.2.1]
  have hdW : Module.finrank (ZMod 2) W = 2 := by
    have hr := Submodule.finrank_sup_add_finrank_inf_eq T U
    rw [hsplit.2.1.eq_bot, finrank_bot, hsplit.2.2.1, hdT, hdU] at hr
    omega
  have hC : fixedSpace ρ (zpowers (t * u)) = fixedSpace ρ (zpowers t ⊔ zpowers u) := by
    rw [fixed_sup]
    apply le_antisymm
    · intro v hv
      have hv' := (mem_fixedSpace_zpowers_iff ρ (t * u) v).mp hv
      have huv : ρ u v = ρ t v := by
        have hh := congrArg (ρ t) hv'
        simpa only [← Module.End.mul_apply, ← map_mul, ← mul_assoc, ht, one_mul] using hh
      have htfix : ρ t v = v := by
        have hw : ρ t v - v ∈ W := by
          apply (show T ≤ W from hsplit.2.2.1 ▸ le_sup_left)
          rw [hTe]
          exact Submodule.subset_span ⟨t, mem_zpowers t, v, Submodule.mem_top, rfl⟩
        have hc : ρ t v - v ∈ fixedSpace ρ (zpowers (t * u)) := by
          apply (mem_fixedSpace_zpowers_iff ρ (t * u) _).mpr
          have hutf : ρ u (ρ t v) = v := by
            rw [← huv, ← Module.End.mul_apply, ← map_mul, hu, map_one, Module.End.one_apply]
          rw [map_sub, hv']
          rw [map_mul, Module.End.mul_apply, hutf]
        exact sub_eq_zero.mp (Submodule.disjoint_def.mp hsplit.1.disjoint _ hw hc)
      exact ⟨(mem_fixedSpace_zpowers_iff ρ t v).mpr htfix,
        (mem_fixedSpace_zpowers_iff ρ u v).mpr (huv.trans htfix)⟩
    · intro v hv
      apply (mem_fixedSpace_zpowers_iff ρ (t * u) v).mpr
      rw [map_mul, Module.End.mul_apply,
        (mem_fixedSpace_zpowers_iff ρ u v).mp hv.2,
        (mem_fixedSpace_zpowers_iff ρ t v).mp hv.1]
  exact ⟨hWE, hWE ▸ hdW, by rw [← hWE, ← hC]; exact hsplit.1⟩

end CFSG.Quasithin.ChapterB.Glauberman.BlockConstruction.PairRecognition
