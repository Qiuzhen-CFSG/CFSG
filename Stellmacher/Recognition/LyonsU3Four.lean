module

public import Stellmacher.Recognition.LyonsU3Four.Basic
public import Stellmacher.Recognition.LyonsU3Four.Arithmetic
public import Theory.Comparator.Defs

/-!
# The final strong-embedding step in Lyons's order-64 branch

For a Sylow subgroup satisfying the intrinsic hypotheses of Theorem 2, the
centralizer equality implies strong embedding of the center normalizer.
Every involution of that normalizer lies in the center, by Sylow conjugacy.
Burnside's fusion lemma then adjusts an intersection conjugator by a Sylow
normalizer element to centralize an involution. The centralizer equality
puts the adjusted conjugator in the center normalizer.

The arithmetic in `LyonsU3Four.Arithmetic` isolates the final contradiction
between the fourth-power action index, equation (4.1), and Schur's bound.
The local and character-theoretic inputs remain explicit in the assembly;
this module does not assume a trivial local odd core.

Source: Lyons, *A Characterization of the Group U₃(4)*, §5, p. 386.
-/

namespace Stellmacher.Recognition.LyonsU3Four

/-- The centralizer equality obtained in Lyons's §5 suffices for strong
embedding; no additional fusion or local odd-core hypothesis is required. -/
public theorem stronglyEmbedded_of_centralizer_eq
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S)
    (hcent : ∀ z ∈ centerImage S, z ≠ 1 →
      Subgroup.centralizer ({z} : Set G) =
        Subgroup.centralizer (centerImage S : Set G)) :
    IsStronglyEmbedded (Subgroup.normalizer (centerImage S : Set G)) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Z := centerImage S
  let N := Subgroup.normalizer (Z : Set G)
  let _ : IsElementaryAbelian 2 Z := centerImage_elementary S h
  have hZC : Z ≤ Subgroup.centralizer (S : Set G) :=
    Subgroup.le_centralizer_iff.mp (sylow_le_centralizer_centerImage S)
  have hCN : Subgroup.centralizer (Z : Set G) ≤ N :=
    Subgroup.centralizer_le_normalizer _
  obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (centerImage_ne_bot S h)
  have hzG : (z : G) ≠ 1 := fun heq => hz (Subtype.ext heq)
  refine ⟨normalizer_centerImage_ne_top S h,
    ⟨z, Z.le_normalizer z.property, hzG,
      elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : G) z.property⟩, ?_⟩
  intro g hg x hx hxinv
  obtain ⟨y, hyN, hyx⟩ := hx.2
  change g * y * g⁻¹ = x at hyx
  have hyinv : IsInvolution y := by
    constructor
    · intro hy
      apply hxinv.1
      simpa [hy] using hyx.symm
    · apply (MulAut.conj g).injective
      simpa only [map_pow, map_one, MulAut.conj_apply, hyx] using hxinv.2
  have hxZ : x ∈ Z := square_one_mem_centerImage_of_mem_normalizer S h hx.1 hxinv.2
  have hyZ : y ∈ Z := square_one_mem_centerImage_of_mem_normalizer S h hyN hyinv.2
  obtain ⟨n, hn, hny⟩ := S.conj_eq_normalizer_conj_of_mem_centralizer y g⁻¹
    (hZC hyZ) (by simpa only [inv_inv, hyx] using hZC hxZ)
  simp only [inv_inv] at hny
  have hconj : (n * g) * y * (n * g)⁻¹ = y := by
    calc
      (n * g) * y * (n * g)⁻¹ = n * (g * y * g⁻¹) * n⁻¹ := by group
      _ = y := by rw [hny]; group
  have hcentral : n * g ∈ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hconj)
  have hng : n * g ∈ N := hCN (by rwa [← hcent y hyZ hyinv.1])
  have hnN : n ∈ N := normalizer_sylow_le_normalizer_centerImage S hn
  exact hg (by simpa using N.mul_mem (N.inv_mem hnN) hng)

end Stellmacher.Recognition.LyonsU3Four
