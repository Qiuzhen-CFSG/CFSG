module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Naturality.Movement.Inputs
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Calculations
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

/-!
# Core displacement in a binary parabolic pencil

For the literal point parabolic P of SL₃(2), let V be its translation
four-group. A pencil consists of a P-invariant layer U containing [W,V]
and an incident-core-fixed seed whose P-translates span W. We prove that
if the preimage of C_(W/U)(P) is V-fixed, then [W,V] is P-fixed.

For a seed vector s, the cubic norm n = s + r*s + r²*s is fixed by the
cubic r and the incident involution t. The core-displacement hypothesis
makes n fixed modulo U by the remaining generator k. Applying k-1 to
its resulting core-fixedness gives r*d + r²*d = 0, where d = a*s - s
is the other translation displacement. In characteristic two this forces
d to be r-fixed; the seed relations make it t- and k-fixed as well.
Normality of V then extends the calculation to the full orbit span.

The matrix relations use small coordinate certificates. Generation uses
short upper-triangular words and the existing binary Bruhat decomposition.
No enumeration of representations is involved.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank
two* (1993), proof of (4.6.8), printed p.907, the binary D/core paragraph.
The source action and its application are assembled separately.
-/

open Subgroup Representation.BinaryOffender Matrix.PSL3Two
open Matrix.PSL3Two.MarkedAutomorphisms
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.CoreMovement
namespace PencilCalculation

private def r : Actor := ⟨cubic, pointA_le cubic_mem⟩
private def t : Actor := ⟨Bruhat.upper 4, (Bruhat.upper_mem 4).1⟩
private def a : Actor := ⟨Bruhat.upper 1, (Bruhat.upper_mem 1).1⟩
private def k : Actor := ⟨Bruhat.upper 2, (Bruhat.upper_mem 2).1⟩

private theorem r_cube : r ^ 3 = 1 := by
  apply Subtype.ext
  exact cubic_cube
private theorem t_seed : t ∈ incidentCore := by change Bruhat.upper 4 ∈ lineV; decide +kernel
private theorem k_seed : k ∈ incidentCore := by change Bruhat.upper 2 ∈ lineV; decide +kernel
private theorem a_core : a ∈ modelCore := by change Bruhat.upper 1 ∈ pointV; decide +kernel
private theorem k_core : k ∈ modelCore := by change Bruhat.upper 2 ∈ pointV; decide +kernel
private theorem k_a : k * a = a * k := by apply Subtype.ext; decide +kernel
private theorem t_a : t * a = a * k * t := by apply Subtype.ext; decide +kernel
private theorem t_r : t * r = r ^ 2 * t := by apply Subtype.ext; decide +kernel
private theorem t_r2 : t * r ^ 2 = r * t := by apply Subtype.ext; decide +kernel
private theorem k_r : k * r = r * a * k := by apply Subtype.ext; decide +kernel
private theorem k_r2 : k * r ^ 2 = r ^ 2 * a := by apply Subtype.ext; decide +kernel
private theorem a_word : a = r * k * r⁻¹ := by apply Subtype.ext; decide +kernel

private def translation (u v : ZMod 2) : SL :=
  ⟨!![1, u, v; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

private theorem core_cases (x : Actor) (hx : x ∈ modelCore) :
    x = 1 ∨ x = a ∨ x = k ∨ x = a * k := by
  change pointCorePred x.val at hx
  dsimp only [pointCorePred] at hx
  rcases hx with ⟨h00, h10, h20, h11, h12, h21, h22⟩
  have he : x.val = translation (x.val.val 0 1) (x.val.val 0 2) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      first | exact h00 | exact h10 | exact h20 | exact h11 |
              exact h12 | exact h21 | exact h22 | rfl
  have hc : ∀ u v : ZMod 2,
      translation u v = 1 ∨ translation u v = Bruhat.upper 1 ∨
      translation u v = Bruhat.upper 2 ∨
      translation u v = Bruhat.upper 1 * Bruhat.upper 2 := by decide +kernel
  rcases hc (x.val.val 0 1) (x.val.val 0 2) with h | h | h | h
  · exact Or.inl (Subtype.ext (he.trans h))
  · exact Or.inr (Or.inl (Subtype.ext (he.trans h)))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext (he.trans h))))
  · exact Or.inr (Or.inr (Or.inr (Subtype.ext (he.trans h))))

private def upperWords : Fin 8 → List (Fin 3) :=
  ![[], [0], [1], [0, 1], [2], [1, 0, 2], [1, 2], [0, 2]]

private def upperGenerators : Fin 3 → SL :=
  ![Bruhat.upper 1, Bruhat.upper 2, Bruhat.upper 4]

private theorem upper_word : ∀ i : Fin 8,
    ((upperWords i).map upperGenerators).prod = Bruhat.upper i := by decide +kernel

private theorem upper_mem_of_generators (J : Subgroup SL)
    (ha : Bruhat.upper 1 ∈ J) (hk : Bruhat.upper 2 ∈ J) (ht : Bruhat.upper 4 ∈ J)
    (i : Fin 8) : Bruhat.upper i ∈ J := by
  rw [← upper_word i]
  apply J.list_prod_mem
  intro g hg
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
  fin_cases j
  · exact ha
  · exact hk
  · exact ht

private theorem perm_point : ∀ j : Fin 6,
    (Bruhat.perm j).val 1 0 = 0 ∧ (Bruhat.perm j).val 2 0 = 0 → j = 0 ∨ j = 1 := by
  decide +kernel

private theorem perm_zero : Bruhat.perm 0 = 1 := by decide +kernel
private theorem perm_one : Bruhat.perm 1 = cubic * Bruhat.upper 4 := by decide +kernel

private theorem parabolic_le (J : Subgroup SL) (hr : cubic ∈ J)
    (ha : Bruhat.upper 1 ∈ J) (hk : Bruhat.upper 2 ∈ J) (ht : Bruhat.upper 4 ∈ J) :
    pointParabolicSL ≤ J := by
  intro g hg
  obtain ⟨i, j, l, he⟩ := Bruhat.decomposition g
  have hp : Bruhat.perm j ∈ pointParabolicSL := by
    have h1 := pointParabolicSL.mul_mem (pointParabolicSL.inv_mem (Bruhat.upper_mem i).1) hg
    rw [he, ← mul_assoc, inv_mul_cancel_left] at h1
    exact (pointParabolicSL.mul_mem_cancel_right (Bruhat.upper_mem l).1).mp h1
  have hjJ : Bruhat.perm j ∈ J := by
    rcases perm_point j ((mem_pointParabolicSL_iff _).mp hp) with rfl | rfl
    · rw [perm_zero]; exact J.one_mem
    · rw [perm_one]; exact J.mul_mem hr ht
  rw [he]
  exact J.mul_mem (J.mul_mem (upper_mem_of_generators J ha hk ht i) hjJ)
    (upper_mem_of_generators J ha hk ht l)

private theorem generates (H : Subgroup Actor) (hr : r ∈ H) (ht : t ∈ H)
    (hk : k ∈ H) : H = ⊤ := by
  have ha : a ∈ H := by
    rw [a_word]
    exact H.mul_mem (H.mul_mem hr hk) (H.inv_mem hr)
  have hj := parabolic_le (H.map Actor.subtype) ⟨r, hr, rfl⟩
    ⟨a, ha, rfl⟩ ⟨k, hk, rfl⟩ ⟨t, ht, rfl⟩
  apply top_unique
  intro g _
  obtain ⟨g', hg', he'⟩ := hj g.property
  exact (Subtype.ext he' : g' = g) ▸ hg'

private theorem r_a : r * a * r⁻¹ = a * k := by apply Subtype.ext; decide +kernel
private theorem t_k : t * k = k * t := by apply Subtype.ext; decide +kernel

private theorem core_normalizer (g : Actor)
    (ha : g * a * g⁻¹ ∈ modelCore) (hk : g * k * g⁻¹ ∈ modelCore) :
    g ∈ Subgroup.normalizer (modelCore : Set Actor) := by
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  rcases core_cases x hx with rfl | rfl | rfl | rfl
  · change g * 1 * g⁻¹ ∈ modelCore
    rw [mul_one, mul_inv_cancel]
    exact modelCore.one_mem
  · exact ha
  · exact hk
  · have he : g * (a * k) * g⁻¹ = (g * a * g⁻¹) * (g * k * g⁻¹) := by group
    rw [he]
    exact modelCore.mul_mem ha hk

private theorem core_normal : modelCore.Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply generates
  · apply core_normalizer
    · rw [r_a]; exact modelCore.mul_mem a_core k_core
    · rw [← a_word]; exact a_core
  · apply core_normalizer
    · rw [t_a, mul_inv_cancel_right]; exact modelCore.mul_mem a_core k_core
    · rw [t_k, mul_inv_cancel_right]; exact k_core
  · exact modelCore.le_normalizer k_core

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) Actor W)

private def moduloStabilizer (U : Submodule (ZMod 2) W)
    (hU : ∀ g : Actor, U ≤ U.comap (ρ g)) (v : W) : Subgroup Actor where
  carrier := {g | ρ g v - v ∈ U}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change ρ (g * h) v - v ∈ U
    have hm := U.add_mem (hU g hh) hg
    change ρ g (ρ h v - v) + (ρ g v - v) ∈ U at hm
    simpa only [map_sub, sub_add_sub_cancel, map_mul, Module.End.mul_apply] using hm
  inv_mem' := by
    intro g hg
    change ρ g⁻¹ v - v ∈ U
    have hm := U.neg_mem (hU g⁻¹ hg)
    change -(ρ g⁻¹ (ρ g v - v)) ∈ U at hm
    simpa only [map_sub, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply, neg_sub] using hm

private theorem fixedModulo_of_generators (U : Submodule (ZMod 2) W)
    (hU : ∀ g : Actor, U ≤ U.comap (ρ g)) (v : W)
    (hr : ρ r v - v ∈ U) (ht : ρ t v - v ∈ U) (hk : ρ k v - v ∈ U) :
    v ∈ fixedModulo ρ U := by
  have he := generates (moduloStabilizer ρ U hU v) hr ht hk
  apply (mem_fixedModulo ρ U v).mpr
  intro g
  exact (show g ∈ moduloStabilizer ρ U hU v from he.symm ▸ Subgroup.mem_top g)

private theorem fixed_of_generators (v : W)
    (hr : ρ r v = v) (ht : ρ t v = v) (hk : ρ k v = v) :
    v ∈ fixedSpace ρ ⊤ := by
  have hf := fixedModulo_of_generators ρ ⊥ (fun _ => bot_le) v
    (by simp [hr])
    (by simp [ht]) (by simp [hk])
  intro g
  exact sub_eq_zero.mp ((mem_fixedModulo ρ ⊥ v).mp hf g)

private theorem add_self (v : W) : v + v = 0 := by
  have h := @two_smul (ZMod 2) W _ _ _ v
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [htwo, zero_smul] at h
  exact h.symm

private theorem neg_self (v : W) : -v = v :=
  neg_eq_iff_add_eq_zero.mpr (add_self v)

private theorem norm_r (s : W) :
    ρ r (s + ρ r s + ρ (r ^ 2) s) = s + ρ r s + ρ (r ^ 2) s := by
  have h1 : r * r = r ^ 2 := (pow_two _).symm
  have h2 : r * r ^ 2 = 1 := by rw [← pow_succ', r_cube]
  simp only [map_add, ← Module.End.mul_apply, ← map_mul, h1, h2,
    map_one, Module.End.one_apply]
  abel

private theorem norm_t (s : W) (hs : ρ t s = s) :
    ρ t (s + ρ r s + ρ (r ^ 2) s) = s + ρ r s + ρ (r ^ 2) s := by
  have h1 : ρ t (ρ r s) = ρ (r ^ 2) s := by
    rw [← Module.End.mul_apply, ← map_mul, t_r, map_mul, Module.End.mul_apply, hs]
  have h2 : ρ t (ρ (r ^ 2) s) = ρ r s := by
    rw [← Module.End.mul_apply, ← map_mul, t_r2, map_mul, Module.End.mul_apply, hs]
  simp only [map_add, hs, h1, h2]
  abel

private theorem seed_displacement_fixed {U : Submodule (ZMod 2) W}
    (pencil : Pencil ρ U) (h : fixedModulo ρ U ≤ fixedSpace ρ modelCore)
    (s : W) (hs : s ∈ pencil.seed) : ρ a s - s ∈ fixedSpace ρ ⊤ := by
  have ht : ρ t s = s := pencil.seed_fixed hs ⟨t, t_seed⟩
  have hk : ρ k s = s := pencil.seed_fixed hs ⟨k, k_seed⟩
  let n := s + ρ r s + ρ (r ^ 2) s
  -- The quotient-fixed preimage is taken for the full parabolic.
  have hn : n ∈ fixedModulo ρ U := by
    apply fixedModulo_of_generators ρ U pencil.invariant
    · rw [norm_r, sub_self]; exact U.zero_mem
    · rw [norm_t ρ s ht, sub_self]; exact U.zero_mem
    · exact pencil.core_displacement (Submodule.subset_span ⟨k, k_core, n, trivial, rfl⟩)
  have hkn : ρ k n = n := h hn ⟨k, k_core⟩
  let d := ρ a s - s
  have hk1 : ρ k (ρ r s) = ρ r (ρ a s) := by
    rw [← Module.End.mul_apply, ← map_mul, k_r, map_mul, Module.End.mul_apply,
      hk, map_mul, Module.End.mul_apply]
  have hk2 : ρ k (ρ (r ^ 2) s) = ρ (r ^ 2) (ρ a s) := by
    rw [← Module.End.mul_apply, ← map_mul, k_r2, map_mul, Module.End.mul_apply]
  -- This is the displacement of the cubic norm by the incident translation.
  have hd : ρ r d + ρ (r ^ 2) d = 0 := by
    calc
      _ = ρ k n - n := by
        dsimp only [d, n]
        simp only [map_add, map_sub, hk, hk1, hk2]
        abel
      _ = 0 := sub_eq_zero.mpr hkn
  have he : ρ r d = ρ (r ^ 2) d := by
    exact (eq_neg_of_add_eq_zero_left hd).trans (neg_self _)
  have hr : ρ r d = d := by
    have hv := congrArg (ρ (r ^ 2)) he
    have h3 : r ^ 2 * r = 1 := by rw [← pow_succ, r_cube]
    have h4 : r ^ 2 * r ^ 2 = r := by
      calc _ = r ^ 3 * r := by group
           _ = r := by rw [r_cube, one_mul]
    simpa only [← Module.End.mul_apply, ← map_mul, h3, h4, map_one,
      Module.End.one_apply] using hv.symm
  apply fixed_of_generators ρ d hr
  · dsimp only [d]
    rw [map_sub, ht]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, t_a, map_mul, Module.End.mul_apply,
      ht, map_mul, Module.End.mul_apply, hk]
  · dsimp only [d]
    rw [map_sub, hk]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, k_a, map_mul, Module.End.mul_apply, hk]

private theorem seed_core_displacement_fixed {U : Submodule (ZMod 2) W}
    (pencil : Pencil ρ U) (h : fixedModulo ρ U ≤ fixedSpace ρ modelCore)
    (s : W) (hs : s ∈ pencil.seed) (c : Actor) (hc : c ∈ modelCore) :
    ρ c s - s ∈ fixedSpace ρ ⊤ := by
  have hk : ρ k s = s := pencil.seed_fixed hs ⟨k, k_seed⟩
  rcases core_cases c hc with rfl | rfl | rfl | rfl
  · simpa only [map_one, Module.End.one_apply, sub_self] using (fixedSpace ρ ⊤).zero_mem
  · exact seed_displacement_fixed ρ pencil h s hs
  · simpa only [hk, sub_self] using (fixedSpace ρ ⊤).zero_mem
  · simpa only [map_mul, Module.End.mul_apply, hk] using
      seed_displacement_fixed ρ pencil h s hs

end PencilCalculation
open PencilCalculation

/-- The binary parabolic pencil calculation: if the preimage of the full
actor's quotient-fixed space is core-fixed, every core displacement is fixed
by the full actor. No finiteness hypothesis on the module is needed. -/
public theorem pencil_core_displacement_fixed
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) Actor W) (U : Submodule (ZMod 2) W)
    (pencil : Pencil ρ U)
    (h : fixedModulo ρ U ≤ fixedSpace ρ modelCore) :
    subspaceCommutator ρ ⊤ modelCore ≤ fixedSpace ρ ⊤ := by
  apply Submodule.span_le.mpr
  rintro v ⟨c, hc, w, _, rfl⟩
  have hw : (⊤ : Submodule (ZMod 2) W) ≤ (fixedSpace ρ ⊤).comap (ρ c - 1) := by
    rw [← pencil.generated]
    apply iSup_le
    intro g
    rintro _ ⟨s, hs, rfl⟩
    change ρ c (ρ g s) - ρ g s ∈ fixedSpace ρ ⊤
    let b := g⁻¹ * c * g
    have hb : b ∈ modelCore := by
      simpa only [inv_inv] using core_normal.conj_mem c hc g⁻¹
    have hf := seed_core_displacement_fixed ρ pencil h s hs b hb
    have he : ρ c (ρ g s) - ρ g s = ρ g (ρ b s - s) := by
      rw [map_sub]
      congr 1
      simp only [← Module.End.mul_apply, ← map_mul]
      congr 1
      dsimp only [b]
      group
    have hfix : ρ g (ρ b s - s) = ρ b s - s := hf ⟨g, Subgroup.mem_top g⟩
    rw [he, hfix]
    exact hf
  exact hw Submodule.mem_top

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.CoreMovement
