module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.Semilinear
public import Theory.AtlasPort.LinearGroups.G2.SylowNormalizer
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.RootElements
public import Theory.GroupAction.SylowPointwiseInner

/-!
# Automorphisms fixing a Sylow subgroup in even G₂

Assuming coverage by the actual inner–field action, every pointwise Sylow
fixer is conjugation by an element of that Sylow subgroup. No order bound is
needed. In the standard marking, Sylow normalization places the inner factor
in the Borel. The two simple-root coordinates kill its torus part, and the
highest-root parameters then kill its field part. The Sylow-center calculation
identifies the remaining conjugating element with a highest-root element.
For involutions this gives the long-root conclusion in every Sylow marking.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, 16.1.6,
printed p.1172. The only unproved automorphism-classification premise is the
explicit surjectivity of `semilinearAction`; its owner discharges it separately.
No central-cover lifting is asserted here. The root and torus formulas come
from the licensed ATLAS port; see LICENSES/ATLAS.txt.
-/

public section

open Subgroup
set_option maxHeartbeats 800000
namespace Atlas.G2.EvenInvolutionGeometry
open LieParabolicSetup LieAutomorphismExtensions
variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
private theorem map_eq_of_pointwise (r : MulAut (Model F))
    (hr : ∀ x ∈ unipotent, r x = x) :
    unipotent.map r.toMonoidHom = unipotent := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    change r x ∈ unipotent
    rw [hr x hx]
    exact hx
  · intro x hx
    exact ⟨x,hx,hr x hx⟩

omit [CharP F 2] in
private theorem borel_conj_fixing_simple_roots {g : Model F}
    (hg : g ∈ borel) (hE : MulAut.conj g (rootE 1) = rootE 1)
    (hF : MulAut.conj g (rootF 1) = rootF 1) : g ∈ unipotent := by
  obtain ⟨⟨u,t⟩,hp⟩ := (borelProductEquiv (K := F)).surjective ⟨g,hg⟩
  have hp' : u.val * t.val = g := congrArg Subtype.val hp
  obtain ⟨t,⟨⟨l,m⟩,rfl⟩⟩ := t
  obtain ⟨u,hu⟩ := u
  rw [unipotent_eq_range] at hu
  obtain ⟨v,rfl⟩ := hu
  change unipotentProduct v * torus l m = g at hp'
  subst g
  have hc (x y : Model F) (h : MulAut.conj (unipotentProduct v * torus l m) x = y) :
      unipotentProduct v * (torus l m * x * (torus l m)⁻¹) =
        y * unipotentProduct v := by
    have := congrArg (fun z => z * unipotentProduct v) h
    simpa [MulAut.conj_apply, mul_assoc] using this
  have he := hc _ _ hE
  have hf := hc _ _ hF
  rw [torus_rootE, mul_one] at he
  rw [torus_rootF, mul_one] at hf
  have re (a : F) : rootE a = unipotentProduct ![0,0,0,0,a,0] := by
    simp [unipotentProduct]
  have rf (a : F) : rootF a = unipotentProduct ![0,0,0,0,0,a] := by
    simp [unipotentProduct]
  rw [re, re, unipotentProduct_mul, unipotentProduct_mul] at he
  rw [rf, rf, unipotentProduct_mul, unipotentProduct_mul] at hf
  have he' : (m : F)^2 / l = 1 := by
    have := congrFun (unipotentProduct_injective he) 4
    simpa [unipotentProductParameters, add_comm] using this
  have hf' : (l : F) / m = 1 := by
    have := congrFun (unipotentProduct_injective hf) 5
    simpa [unipotentProductParameters, add_comm] using this
  have hlm : (l : F) = m := (div_eq_one_iff_eq (Units.ne_zero m)).mp hf'
  have hm : m = 1 := by
    apply Units.ext
    have hmm : (m : F) * m = 1 * m := by
      simpa only [pow_two, hlm] using (div_eq_iff (Units.ne_zero l)).mp he'
    exact (mul_right_cancel₀ (Units.ne_zero m) hmm)
  have hl : l = 1 := Units.ext (hlm.trans (congrArg Units.val hm))
  have ht : torus (1 : Fˣ) 1 = 1 := (torusHom (K := F)).map_one
  rw [hl, hm, ht, mul_one]
  exact unipotentProduct_mem v

private theorem semilinear_fixing_unipotent (z : Model F ⋊[fieldAction] (F ≃+* F))
    (hz : ∀ x ∈ unipotent, semilinearAction z x = x) :
    ∃ a : F, semilinearAction z = MulAut.conj (rootA a) := by
  have hn : z.left ∈ borel := by
    rw [← SylowNormalizer.normalizer_unipotent]
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hm := map_eq_of_pointwise (semilinearAction z) hz
    change unipotent.map ((MulAut.conj z.left).toMonoidHom.comp
      (fieldEquiv z.right).toMonoidHom) = unipotent at hm
    rwa [← map_map, SylowNormalizer.field_map_unipotent] at hm
  have hE : MulAut.conj z.left (rootE 1) = rootE 1 := by
    have h := hz (rootE 1) (subset_closure (by simp))
    change MulAut.conj z.left (fieldEquiv z.right (rootE 1)) = rootE 1 at h
    have hroot : fieldEquiv z.right (rootE 1) = rootE 1 := by
      have h := long_field_unipotentProduct z.right (![0,0,0,0,1,0] : Fin 6 → F)
      simpa [unipotentProduct, Function.comp_def] using h
    simpa only [hroot] using h
  have hF : MulAut.conj z.left (rootF 1) = rootF 1 := by
    have h := hz (rootF 1) (subset_closure (by simp))
    change MulAut.conj z.left (fieldEquiv z.right (rootF 1)) = rootF 1 at h
    have hroot : fieldEquiv z.right (rootF 1) = rootF 1 := by
      have h := long_field_unipotentProduct z.right (![0,0,0,0,0,1] : Fin 6 → F)
      simpa [unipotentProduct, Function.comp_def] using h
    simpa only [hroot] using h
  have hu := borel_conj_fixing_simple_roots hn hE hF
  have hr : z.right = 1 := by
    apply RingEquiv.ext
    intro a
    have h := hz (rootA a) (subset_closure (by simp))
    change MulAut.conj z.left (fieldEquiv z.right (rootA a)) = rootA a at h
    rw [fieldEquiv_rootA] at h
    have hu' := hu
    rw [unipotent_eq_range] at hu'
    obtain ⟨v,hv⟩ := hu'
    rw [← hv, MulAut.conj_apply,
      (unipotentProduct_commute_rootA v (z.right a)).eq, mul_inv_cancel_right] at h
    exact rootA_injective h
  have he : semilinearAction z = MulAut.conj z.left := by
    rw [semilinearAction_apply, hr, map_one, mul_one]
  have hc : z.left ∈ highestRoot := by
    rw [← unipotent_center]
    refine ⟨⟨z.left,hu⟩,mem_center_iff.mpr ?_,rfl⟩
    intro x
    apply Subtype.ext
    have h := hz x.val x.property
    rw [he, MulAut.conj_apply] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  obtain ⟨a,ha⟩ := hc
  exact ⟨a.toAdd, he.trans (congrArg MulAut.conj ha.symm)⟩

/-- Standard Sylow fixers are inner, with a conjugating element in that Sylow. -/
theorem fixing_standard_sylow_inner [Finite F]
    (hcover : Function.Surjective (semilinearAction (F := F)))
    (r : MulAut (Model F)) (hr : ∀ x ∈ sylow (F := F), r x = x) :
    ∃ x ∈ sylow (F := F), r = MulAut.conj x := by
  obtain ⟨z,rfl⟩ := hcover r
  obtain ⟨a,ha⟩ := semilinear_fixing_unipotent z hr
  exact ⟨rootA a, subset_closure (by simp), ha⟩

/-- Every Sylow pointwise fixer is inner; in particular this covers all two-elements. -/
theorem fixing_sylow_inner [Finite F]
    (hcover : Function.Surjective (semilinearAction (F := F)))
    (S : Sylow 2 (Model F)) (r : MulAut (Model F))
    (hr : ∀ x ∈ S, r x = x) : ∃ x ∈ S, r = MulAut.conj x :=
  MulAut.fixing_inner_sylow sylow S (fixing_standard_sylow_inner hcover) r hr

/-- The involutory Sylow fixers are induced by genuine long-root elements. -/
theorem fixing_sylow_involution_longRoot [Finite F] (hq : 2 < Nat.card F)
    (hcover : Function.Surjective (semilinearAction (F := F)))
    (S : Sylow 2 (Model F)) (r : MulAut (Model F))
    (hr : ∀ x ∈ S, r x = x) (hsq : r ^ 2 = 1) (hne : r ≠ 1) :
    ∃ x ∈ S, r = MulAut.conj x ∧ IsLongRootElement x := by
  obtain ⟨x,hx,he⟩ := fixing_sylow_inner hcover S r hr
  refine ⟨x,hx,he,central_involution_isLongRoot S hx ?_ ?_ ?_⟩
  · apply Theory.GroupTheory.conj_injective_of_center_eq_bot (model_center_eq_bot hq)
    rw [map_pow, ← he, hsq, map_one]
  · intro y hy
    have h := hr y hy
    rw [he, MulAut.conj_apply] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  · intro hxone
    apply hne
    rw [he, hxone, map_one]

end Atlas.G2.EvenInvolutionGeometry
