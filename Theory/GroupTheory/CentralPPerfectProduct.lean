module

public import Theory.GroupTheory.CentralPPerfectCoprime
public import Mathlib.Algebra.Group.Subgroup.Pointwise
/-!
# Injectivity on a product with a p-perfect factor

A map with central p-group kernel is injective on a p-perfect subgroup
whose image is abelian of exponent coprime to p. If that subgroup and a
normalizing p-subgroup generate the domain, injectivity on the latter
forces injectivity everywhere: their images have trivial intersection.
The central-extension argument is supplied by `CentralPPerfectCoprime`;
no complement or coprime order of the first factor is assumed.

Source: the central-kernel step in Aschbacher–Smith G.2.6, printed p.336.
-/

public section
open Subgroup
open scoped Pointwise

/-- Eliminate a central p-kernel from a product with a p-perfect factor. -/
theorem MonoidHom.injective_of_isPPerfect_product {E H : Type*} [Group E] [Group H]
    {p : ℕ} [Fact p.Prime] (f : E →* H) (A B : Subgroup E)
    (hc : f.ker ≤ center E) (hp : IsPGroup p f.ker)
    (hA : IsPPerfect p A) (hB : IsPGroup p B)
    (hBA : B ≤ normalizer (A : Set E)) (hgen : A ⊔ B = ⊤)
    (hBi : Function.Injective (f.domRestrict B))
    (hcomm : ∀ a b : A, Commute (f a) (f b))
    {n : ℕ} (hn : Nat.Coprime p n) (hexp : ∀ a : A, f a ^ n = 1) :
    Function.Injective f := by
  have hcA : (f.domRestrict A).ker ≤ center A := by
    intro a ha
    exact mem_center_iff.mpr fun b => Subtype.ext (mem_center_iff.mp (hc ha) b)
  have hpA : IsPGroup p (f.domRestrict A).ker := by
    rw [MonoidHom.ker_domRestrict]
    exact hp.comap_subtype
  have hAi := MonoidHom.injective_of_isPPerfect_of_coprime_abelian_image hA
    (f.domRestrict A) hcA hpA hcomm hn hexp
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply bot_unique
  intro x hx
  have hxAB : x ∈ (A ⊔ B : Subgroup E) := hgen.symm ▸ mem_top x
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left A B hBA] at hxAB
  obtain ⟨a, ha, b, hb, rfl⟩ := hxAB
  have he : f a * f b = 1 := by simpa only [MonoidHom.mem_ker, map_mul] using hx
  have he' : f b = (f a)⁻¹ := by
    calc
      f b = (f a)⁻¹ * (f a * f b) := by simp
      _ = (f a)⁻¹ := by rw [he, mul_one]
  have hbpow : f b ^ n = 1 := by rw [he', inv_pow, hexp ⟨a, ha⟩, inv_one]
  have hb1 : f b = 1 := by
    let y : B.map f := ⟨f b, mem_map.mpr ⟨b, hb, rfl⟩⟩
    have hy : y = 1 := (hB.map f).powEquiv hn |>.injective (Subtype.ext (by simpa using hbpow))
    exact congrArg Subtype.val hy
  have ha1 : f a = 1 := by simpa only [hb1, mul_one] using he
  have ha' : a = 1 := congrArg Subtype.val (hAi (by simpa using ha1 : f.domRestrict A ⟨a, ha⟩ = f.domRestrict A 1))
  have hb' : b = 1 := congrArg Subtype.val (hBi (by simpa using hb1 : f.domRestrict B ⟨b, hb⟩ = f.domRestrict B 1))
  simp [ha', hb']
