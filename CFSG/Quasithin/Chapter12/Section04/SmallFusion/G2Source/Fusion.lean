module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.Setup
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleG2Fusion

/-!
# Fusion from binary G₂ Sylow representatives

The Weyl calculation supplies two independent pieces of data: the fixed
involution is weakly closed in the chosen module, and every other nonidentity
vector is conjugate under `N_G(L)` to one centralized by `T`.  Sylow conjugacy
then changes a global transporter into an `N_G(T)`-transporter; the source
normalizer inclusion puts it back in `N_G(L)`.  This is the precise normalizer
fusion interface used in 12.4.7.  It does not use the 12.2.13 `NoEscape`
assumption.

Source: Aschbacher--Smith 12.2.16, pp.799--800, and 12.4.7, p.814.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source

universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-! The fixed involution is weakly closed once the Sylow-central representatives
are available.  This is the short source argument behind the G₂ row of
12.4.7: the original `T` centralizes `z`, and both the `N_G(L)`- and
`N_G(T)`-transporters centralize it. -/

/-- A Sylow-central representative family forces weak closure of the fixed line.

The only normalizer input is `N_G(T) ≤ N_G(L)`.  In particular, this lemma
does not use the contrary `NoEscape` assumption from 12.2.13. -/
theorem weakly_closed_of_sylow_central_representatives
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G)) {z : G}
    (_hz : z ∈ V) (_hz1 : z ≠ 1)
    (hM : normalizer (L : Set G) = centralizer ({z} : Set G))
    (hzOmega : z ∈ omegaOneAmbient
      ((center (T : Subgroup G)).map (T : Subgroup G).subtype))
    (hcentral : ∀ x ∈ V, x ≠ 1 → x ≠ z →
      ∃ m ∈ normalizer (L : Set G),
        (T : Subgroup G) ≤ centralizer ({m * x * m⁻¹} : Set G)) :
    ∀ g : G, MulAut.conj g z ∈ V → MulAut.conj g z = z := by
  have hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
    have hz' : z ∈ (center (T : Subgroup G)).map (T : Subgroup G).subtype :=
      (omegaOneAmbient_le _) hzOmega
    rcases Subgroup.mem_map.mp hz' with ⟨zt, hzt, rfl⟩
    intro t ht
    exact mem_centralizer_singleton_iff.mpr
      (congrArg (fun v : T => (v : G))
        ((mem_center_iff.mp hzt) ⟨t, ht⟩))
  intro g hg
  have hconj1 : MulAut.conj g z ≠ 1 := by
    intro he
    exact _hz1 ((MulAut.conj g).map_eq_one_iff.mp he)
  by_cases hconjz : MulAut.conj g z = z
  · exact hconjz
  obtain ⟨b, hb, hby⟩ := hcentral (MulAut.conj g z) hg hconj1 hconjz
  have hzy : IsConj z (b * (MulAut.conj g z) * b⁻¹) :=
    (isConj_iff.mpr ⟨g, rfl⟩).trans (isConj_iff.mpr ⟨b, rfl⟩)
  let S := T.subtype hTz
  have hST : (S : Subgroup (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype = (T : Subgroup G) := by
    exact map_subgroupOf_eq_of_le hTz
  obtain ⟨c, hcN, hcy⟩ := exists_normalizer_conjugator_of_centralizer_sylow
    z (b * (MulAut.conj g z) * b⁻¹) S (hST ▸ hby) hzy
  rw [hST] at hcN
  have hcM : c ∈ normalizer (L : Set G) := hNT hcN
  have hcZ : MulAut.conj c z = z := by
    change c * z * c⁻¹ = z
    exact mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_singleton_iff.mp (hM ▸ hcM))
  have hbZ : MulAut.conj b z = z := by
    change b * z * b⁻¹ = z
    exact mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_singleton_iff.mp (hM ▸ hb))
  have hbyz : b * (MulAut.conj g z) * b⁻¹ = z := hcy.symm.trans hcZ
  apply (MulAut.conj b).injective
  change b * (MulAut.conj g z) * b⁻¹ = b * z * b⁻¹
  calc
    b * (MulAut.conj g z) * b⁻¹ = z := hbyz
    _ = b * z * b⁻¹ := hbZ.symm

/-- Convert Sylow-central representatives into `N_G(L)`-controlled fusion on `V`.
The distinguished fixed involution is handled by the supplied weak-closure
callback; all other vectors use the common-centralizer Sylow adjustment. -/
theorem fusion_of_sylow_central_representatives
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G)) {z : G}
    (_hz : z ∈ V) (_hz1 : z ≠ 1)
    (hweak : ∀ g : G, MulAut.conj g z ∈ V → MulAut.conj g z = z)
    (hcentral : ∀ x ∈ V, x ≠ 1 → x ≠ z →
      ∃ m ∈ normalizer (L : Set G),
        (T : Subgroup G) ≤ centralizer ({m * x * m⁻¹} : Set G)) :
    ∀ x ∈ V, ∀ y ∈ V, IsConj x y →
      ∃ m ∈ normalizer (L : Set G), MulAut.conj m x = y := by
  intro x hx y hy hxy
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  change MulAut.conj g x = y at hg
  by_cases hxz : x = z
  · subst x
    have hyz := hweak g (hg.symm ▸ hy)
    have hyz' : y = z := hg.symm.trans hyz
    exact ⟨1, (normalizer (L : Set G)).one_mem, by simp [hyz']⟩
  have hyz : y ≠ z := by
    intro he
    have hback : MulAut.conj g⁻¹ z = x := by
      calc
        MulAut.conj g⁻¹ z = MulAut.conj g⁻¹ (MulAut.conj g x) := by rw [hg, he]
        _ = x := by simp [MulAut.conj_apply, mul_assoc]
    have hx' := hweak g⁻¹ (hback.symm ▸ hx)
    exact hxz (hback.symm.trans hx')
  by_cases hx1 : x = 1
  · have hy1 : y = 1 := by
      exact hg.symm.trans (by simp [hx1])
    exact ⟨1, (normalizer (L : Set G)).one_mem, by simp [hx1, hy1]⟩
  have hy1 : y ≠ 1 := by
    intro he
    have hconj : MulAut.conj g x ≠ 1 := by
      intro hconj
      exact hx1 ((MulAut.conj g).map_eq_one_iff.mp hconj)
    exact hconj (he ▸ hg)
  obtain ⟨a, ha, hax⟩ := hcentral x hx hx1 hxz
  obtain ⟨b, hb, hby⟩ := hcentral y hy hy1 hyz
  let x' := a * x * a⁻¹
  let y' := b * y * b⁻¹
  let S := T.subtype hax
  have hST : (S : Subgroup (centralizer ({x'} : Set G))).map
      (centralizer ({x'} : Set G)).subtype = (T : Subgroup G) := by
    exact map_subgroupOf_eq_of_le hax
  have hxy' : IsConj x' y' :=
    (isConj_iff.mpr ⟨a, rfl⟩).symm.trans
      (hxy.trans (isConj_iff.mpr ⟨b, rfl⟩))
  obtain ⟨c, hcN, he⟩ := exists_normalizer_conjugator_of_centralizer_sylow
    x' y' S (hST ▸ hby) hxy'
  rw [hST] at hcN
  have hb' : b⁻¹ ∈ normalizer (L : Set G) :=
    (normalizer (L : Set G)).inv_mem hb
  refine ⟨b⁻¹ * c * a, mul_mem (mul_mem hb' (hNT hcN)) ha, ?_⟩
  have he' : c * (a * x * a⁻¹) * c⁻¹ = b * y * b⁻¹ := he
  calc
    (b⁻¹ * c * a) * x * (b⁻¹ * c * a)⁻¹ =
        b⁻¹ * (c * (a * x * a⁻¹) * c⁻¹) * b := by group
    _ = b⁻¹ * (b * y * b⁻¹) * b := by rw [he']
    _ = y := by group

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
