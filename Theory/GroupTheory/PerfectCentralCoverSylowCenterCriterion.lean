module

public import Theory.GroupTheory.PerfectCentralCoverSylowTransfer
public import Theory.GroupTheory.PerfectCentralCoverAbelianSylow
public import Theory.GroupTheory.CentralExtensionInvariantPairing
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# A local action criterion for centers of covering Sylow subgroups

Let a finite perfect central double cover project a Sylow P onto T. If the
normalizer of T is transitive on the nonidentity elements of Z(T), the image
of Z(P) is either trivial or all of Z(T). In the latter case the full preimage
of Z(T) is central. An abelian T contradicts transfer immediately. Otherwise
an odd-period normalizer element, fixed-point-free on Z(T), produces a norm
retraction and an invariant binary commutator pairing; the absence of such
pairings again contradicts transfer. Hence Z(P) is exactly the covering kernel.

Only intrinsic data on the actual base subgroup and its normalizer are inputs.
One model Sylow suffices, by postcomposing the original cover with the model
isomorphism and an inner automorphism. This retains the covering kernel and P.

Source: the Sylow-center and automorphism conclusions in GLS4, Chapter 4,
Lemma 2.8(c). This alternative proof does not classify the covering groups.
-/

namespace PerfectCentralCovering
open Subgroup
open scoped IsMulCommutative
variable {E B : Type*} [Group E] [Group B]

/-- Intrinsic base-group action data for the direct central-cover argument.
The action is the actual conjugation action of the subgroup normalizer. -/
public structure SylowCenterAction (T : Subgroup B) : Prop where
  transitive : ∀ z w : center T, z ≠ 1 → w ≠ 1 →
    ∃ h : (normalizer (T : Set B)), centerCongr (T.normalizerMonoidHom h) z = w
  obstruction : IsMulCommutative T ∨
    (commutator T ≤ center T ∧ ∃ (h : (normalizer (T : Set B))) (r : ℕ),
      Odd r ∧ h ^ r = 1 ∧
      (∀ z ∈ center T, T.normalizerMonoidHom h z = z → z = 1) ∧
      (∀ c : T →* (T →* Multiplicative (ZMod 2)),
        (∀ x y, c (T.normalizerMonoidHom h x) (T.normalizerMonoidHom h y) = c x y) →
        c = 1))

public theorem Cover.lift_mem_sylow_normalizer
    (f : Cover E B) (hcard : Nat.card f.toMonoidHom.ker = 2) (P : Sylow 2 E)
    {t : E} (ht : f.toMonoidHom t ∈ (normalizer (((P : Subgroup E).map f.toMonoidHom) : Set B))) :
    t ∈ (normalizer (P : Set E)) := by
  change t ∈ normalizer ((P : Subgroup E) : Set E)
  rw [← f.comap_map_sylow hcard P]
  intro x
  change f.toMonoidHom x ∈ (P : Subgroup E).map f.toMonoidHom ↔
    f.toMonoidHom (t * x * t⁻¹) ∈ (P : Subgroup E).map f.toMonoidHom
  rw [map_mul, map_mul, map_inv]
  exact ht (f.toMonoidHom x)

public theorem Cover.sylow_center_eq_kernel_of_action
    [Finite E] (f : Cover E B) (hcard : Nat.card f.toMonoidHom.ker = 2)
    (P : Sylow 2 E)
    (hact : SylowCenterAction ((P : Subgroup E).map f.toMonoidHom)) :
    (center P).map (P : Subgroup E).subtype = f.toMonoidHom.ker := by
  let T := (P : Subgroup E).map f.toMonoidHom
  let F : P →* T := f.toMonoidHom.subgroupMap (P : Subgroup E)
  have hF : Function.Surjective F := f.toMonoidHom.subgroupMap_surjective _
  have hk : F.ker ≤ center P := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact mem_center_iff.mp (f.ker_le_center (show f.toMonoidHom (x : E) = 1 from
      congrArg Subtype.val hx)) y
  have hkc : Nat.card F.ker = 2 := by
    have he : F.ker = f.toMonoidHom.ker.subgroupOf (P : Subgroup E) := by
      ext x
      change (⟨f.toMonoidHom x, _⟩ : T) = 1 ↔ f.toMonoidHom x = 1
      exact Subtype.ext_iff
    rw [he, Nat.card_congr (subgroupOfEquivOfLe (f.ker_le_sylow hcard P)).toEquiv, hcard]
  have hkd : F.ker ≤ commutator P := by
    intro x hx
    have hxD := f.ker_le_sylow_commutator hcard P
      (show f.toMonoidHom (x : E) = 1 from congrArg Subtype.val hx)
    rw [← map_subtype_commutator] at hxD
    obtain ⟨y, hy, he⟩ := hxD
    have hxy : y = x := Subtype.ext he
    exact hxy ▸ hy
  have himage : (center P).map F ≤ center T := by
    rintro _ ⟨z, hz, rfl⟩
    apply mem_center_iff.mpr
    intro t
    obtain ⟨y, rfl⟩ := hF t
    rw [← map_mul, ← map_mul, mem_center_iff.mp hz y]
  have lift_action (h : (normalizer (T : Set B))) :
      ∃ a : MulAut P, ∀ x, F (a x) = T.normalizerMonoidHom h (F x) := by
    obtain ⟨t, ht⟩ := f.surjective (h : B)
    have htn : t ∈ (normalizer (P : Set E)) :=
      f.lift_mem_sylow_normalizer hcard P (ht ▸ h.property)
    refine ⟨(P : Subgroup E).normalizerMonoidHom ⟨t, htn⟩, ?_⟩
    intro x
    apply Subtype.ext
    change f.toMonoidHom (t * (x : E) * t⁻¹) =
      (h : B) * f.toMonoidHom (x : E) * (h : B)⁻¹
    rw [map_mul, map_mul, map_inv, ht]
  have hdich : (center P).map F = ⊥ ∨ (center P).map F = center T := by
    by_cases hi : (center P).map F = ⊥
    · exact Or.inl hi
    right
    apply le_antisymm himage
    obtain ⟨z, hz, hzne⟩ := ((center P).map F).bot_or_exists_ne_one.resolve_left hi
    intro w hw
    by_cases hw1 : w = 1
    · exact hw1 ▸ ((center P).map F).one_mem
    obtain ⟨h, hzw⟩ := hact.transitive ⟨z, himage hz⟩ ⟨w, hw⟩
      (fun he => hzne (congrArg Subtype.val he))
      (fun he => hw1 (congrArg Subtype.val he))
    obtain ⟨a, ha⟩ := lift_action h
    obtain ⟨v, hv, hvz⟩ := hz
    refine ⟨a v, (centerCongr a ⟨v,hv⟩).property, ?_⟩
    rw [ha, hvz]
    exact congrArg Subtype.val hzw
  apply le_antisymm _ (f.ker_le_sylow_center hcard P)
  rcases hdich with hi | hi
  · rintro _ ⟨z, hz, rfl⟩
    have hz1 : F z = 1 := mem_bot.mp (hi ▸ mem_map_of_mem F hz)
    exact congrArg Subtype.val hz1
  · have hpre : (center T).comap F = center P := by
      rw [← hi, comap_map_eq_self hk]
    rcases hact.obstruction with habel | ⟨hdT, h, r, hodd, hr, hfixed, hforms⟩
    · have hcent : center P = ⊤ := by
        rw [← hpre, @center_eq_top T _ habel, comap_top]
      have habP : IsMulCommutative P := center_eq_top_iff.mp hcent
      let := f.isPerfect
      exact False.elim (not_dvd_card_kernel_of_abelian_sylow f.toMonoidHom
        f.ker_le_center P habP (by simp only [hcard]; exact dvd_refl 2))
    · have hdP : commutator P ≤ center P := by
        rw [← hpre]
        apply map_le_iff_le_comap.mp
        rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hF]
        exact hdT
      obtain ⟨t, ht, htr⟩ := f.exists_odd_order_lift hcard (h : B) r hodd
        (congrArg Subtype.val hr)
      have htn : t ∈ (normalizer (P : Set E)) :=
        f.lift_mem_sylow_normalizer hcard P (ht ▸ h.property)
      let a : MulAut P := (P : Subgroup E).normalizerMonoidHom ⟨t, htn⟩
      have ha : ∀ x, F (a x) = T.normalizerMonoidHom h (F x) := by
        intro x
        apply Subtype.ext
        change f.toMonoidHom (t * (x : E) * t⁻¹) =
          (h : B) * f.toMonoidHom (x : E) * (h : B)⁻¹
        rw [map_mul, map_mul, map_inv, ht]
      have har : a ^ r = 1 := by
        change ((P : Subgroup E).normalizerMonoidHom ⟨t, htn⟩) ^ r = 1
        rw [← map_pow]
        have he : (⟨t, htn⟩ : (normalizer (P : Set E))) ^ r = 1 := Subtype.ext htr
        rw [he, map_one]
      have hak : ∀ x ∈ F.ker, a x = x := by
        intro x hx
        apply Subtype.ext
        change t * (x : E) * t⁻¹ = x
        have hxc := f.ker_le_center (show f.toMonoidHom (x : E) = 1 from
          congrArg Subtype.val hx)
        rw [mem_center_iff.mp hxc t, mul_inv_cancel_right]
      exact (CentralExtension.false_of_invariant_pairings_trivial F hF hk hkc hkd hdP
        a (T.normalizerMonoidHom h) ha hak r har hodd hfixed hforms).elim
end PerfectCentralCovering

namespace PerfectCentralCovering
open Subgroup
variable {E B D : Type*} [Group E] [Finite E] [Group B] [Group D] [Finite D]

/-- One actual model Sylow suffices. Postcomposition retains the original
covering kernel and Sylow subgroup in the covering group. -/
public theorem Cover.sylow_center_eq_kernel_of_model_sylow
    (f : Cover E B) (hcard : Nat.card f.toMonoidHom.ker = 2)
    (e : B ≃* D) (Q : Sylow 2 D) (hQ : SylowCenterAction (Q : Subgroup D))
    (P : Sylow 2 E) :
    (center P).map (P : Subgroup E).subtype = f.toMonoidHom.ker := by
  let q : E →* D := e.toMonoidHom.comp f.toMonoidHom
  have hq : Function.Surjective q := e.surjective.comp f.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D (P.mapSurjective hq) Q
  let p : E →* D := (MulAut.conj g).toMonoidHom.comp q
  have hpker : p.ker = f.toMonoidHom.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective,
      MonoidHom.ker_comp_of_injective _ _ e.injective]
  let f' : Cover E D := {
    toMonoidHom := p
    surjective := (MulAut.conj g).surjective.comp hq
    isPerfect := f.isPerfect
    ker_le_center := hpker ▸ f.ker_le_center }
  have hmap : (P : Subgroup E).map p = Q := by
    have he := congrArg (fun R : Sylow 2 D => (R : Subgroup D)) hg
    change ((P.mapSurjective hq : Subgroup D).map (MulAut.conj g).toMonoidHom) = Q at he
    rw [Sylow.coe_mapSurjective, map_map] at he
    exact he
  have hh : SylowCenterAction ((P : Subgroup E).map p) := hmap ▸ hQ
  exact (f'.sylow_center_eq_kernel_of_action (by change Nat.card p.ker = 2; rw [hpker, hcard]) P hh).trans hpker
end PerfectCentralCovering
