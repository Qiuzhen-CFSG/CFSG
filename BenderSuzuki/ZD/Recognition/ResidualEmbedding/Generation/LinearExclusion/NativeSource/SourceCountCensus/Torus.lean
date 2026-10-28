module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.SourceCountCensus.Geometry

/-!
# The torus family of nonsquare elements

Starting with x²≠1, central A-translates of the K-conjugates of x retain
nontrivial squares. Freeness on R₁/AU separates their A-cosets. This gives
the q(q-1) complementary elements in the source census without prescribing
the order of U.

Source: GLS4, Chapter 2, Lemma 15.6, counting paragraph.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion.SourceCount.Census
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
local notation "A" => closure (Z ∩ (M : Set G))
local notation "U" => twoCore M z t
local notation "R" => sourceNormalizer Z M z t
local notation "K" => residualCommutator M t
include d

public theorem torus_translate_square (hg : NormalizerData d)
    {x : G} (hx : x ∈ R) (k : K) (a : A) :
    (MulAut.conj (k : G) x * a) ^ 2 = MulAut.conj (k : G) (x ^ 2) := by
  rw [((distinguished_commutes d (source_conj_mem d hg
    (torus_le_point d k.property) hx) a.property).symm).mul_pow,
    distinguished_square d a.property, mul_one, map_pow]

public theorem torus_translate_nonsquare (hg : NormalizerData d)
    {x : G} (hx : x ∈ R) (hx2 : x ^ 2 ≠ 1) (k : K) (a : A) :
    (MulAut.conj (k : G) x * a) ^ 2 ≠ 1 := by
  rw [torus_translate_square d hg hx]
  exact fun he => hx2 ((MulAut.conj (k : G)).injective (he.trans (map_one _).symm))

/-- Freeness of the actual AU-cosets separates all pairs of torus and A factors. -/
public theorem torus_translate_injective (hs : CentralizerLocalTwoData d)
    (hg : NormalizerData d) {x : G} (hx : x ∈ R) (hx2 : x ^ 2 ≠ 1) :
    Function.Injective (fun p : K × A => MulAut.conj (p.1 : G) x * p.2) := by
  rintro ⟨k,a⟩ ⟨l,b⟩ he
  dsimp only at he
  have hy : MulAut.conj (l : G) x ∈ R :=
    source_conj_mem d hg (torus_le_point d l.property) hx
  have hy2 : (MulAut.conj (l : G) x) ^ 2 ≠ 1 := by
    rw [← map_pow]
    exact fun he => hx2 ((MulAut.conj (l : G)).injective (he.trans (map_one _).symm))
  have hyAU : MulAut.conj (l : G) x ∉ A ⊔ U := fun h => hy2 (sup_square d hs h)
  have hkl : (k : G) * (l : G)⁻¹ = 1 := by
    by_contra hkl
    apply hg.torus_free _ ((K).mul_mem k.property ((K).inv_mem l.property)) hkl _ hy hyAU
    have hc : MulAut.conj ((k : G) * (l : G)⁻¹) (MulAut.conj (l : G) x) *
        (MulAut.conj (l : G) x)⁻¹ = (b : G) * (a : G)⁻¹ := by
      have hh := congrArg (fun y : G => y * (a : G)⁻¹) he
      simp only [mul_inv_cancel_right] at hh
      have hc := (distinguished_commutes d hy
        ((A).mul_mem b.property ((A).inv_mem a.property))).eq
      calc
        _ = MulAut.conj (k : G) x * (MulAut.conj (l : G) x)⁻¹ := by
          simp only [MulAut.conj_apply]
          group
        _ = (MulAut.conj (l : G) x * ((b : G) * (a : G)⁻¹)) *
            (MulAut.conj (l : G) x)⁻¹ := by rw [hh]; group
        _ = ((b : G) * (a : G)⁻¹ * MulAut.conj (l : G) x) *
            (MulAut.conj (l : G) x)⁻¹ := by rw [hc]
        _ = (b : G) * (a : G)⁻¹ := by group
    rw [hc]
    exact (show A ≤ A ⊔ U from le_sup_left) ((A).mul_mem b.property ((A).inv_mem a.property))
  have hke : k = l := Subtype.ext (mul_inv_eq_one.mp hkl)
  subst l
  exact Prod.ext rfl (Subtype.ext (mul_left_cancel he))

end BenderSuzuki.ZD.LinearExclusion.SourceCount.Census
