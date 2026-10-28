module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.OddSupplement.HallTransfer
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.QuotientLifting
public import Theory.GroupTheory.PCoreActionSplitting

/-!
# Applying odd Hall transfer to the original centralizer

The source index [C₀:J] is a power of two. An odd complement to the
actual two-core of J is consequently Hall odd in C₀. For every nontrivial
subgroup P of that complement, the source normalizer equality
N_C₀(P)=A N_J(P) makes its normalizer centralize it. Primewise Burnside
transfer makes the two-core of C₀ a complement to Y.

Since C₀ is normal in M and contains O₂(M), its two-core maps exactly to
O₂(M). The final result is the literal carrier product C₀=O₂(M)Y used in
GLS IV, Chapter 2, Lemma 15.5. The only intermediate inputs below concern
the actual complement inside J; the neighboring intrinsic model proof
constructs them from nontriviality of O₂(J).
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d
local notation "A" => closure (Z ∩ (M : Set G))
local notation "L" => residualGenerated M z t
local notation "J" => (centralizer (L : Set G) : Subgroup G)
local notation "C₀" => (M ⊓ centralizer (A : Set G) : Subgroup G)
local notation "U" => Subgroup.map (Subgroup.subtype J) (pCore 2 J)
local notation "V" => Subgroup.map M.subtype (pCore 2 M)

private theorem embedded_centralizer_core_eq : (pCore 2 C₀).map (C₀).subtype = V := by
  let C : Subgroup M := (C₀).subgroupOf M
  let : C.Normal := d.centralizer_normal
  have hVC : pCore 2 M ≤ C := by
    intro v hv
    exact d.point_twoCore_le_distinguished_centralizer ⟨v, hv, rfl⟩
  have hh := pCore_eq_map_of_normal_of_le 2 C hVC
  have hm := congrArg (map M.subtype) hh
  change V = ((pCore 2 C).map C.subtype).map M.subtype at hm
  let e : C ≃* C₀ := subgroupOfEquivOfLe (show C₀ ≤ M from inf_le_left)
  have hc : M.subtype.comp C.subtype = (C₀).subtype.comp e.toMonoidHom := rfl
  rw [map_map, hc, ← map_map, pCore_map_iso 2 e] at hm
  exact hm.symm

private theorem odd_complement_hall_in_centralizer (Y : Subgroup G)
    (hYJ : Y ≤ J) (hodd : Odd (Nat.card Y))
    (hprod : (J : Set G) = (U : Set G) * (Y : Set G)) :
    IsHallSubgroup OddHall.oddPrimes (Y.subgroupOf C₀) := by
  have hYnorm : Y ≤ normalizer (U : Set G) := by
    have hn : J ≤ normalizer (U : Set G) := by
      simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
        (pCore 2 J).le_normalizer_map (J).subtype
    exact hYJ.trans hn
  have hjoin : U ⊔ Y = J := SetLike.coe_injective
    ((coe_mul_of_right_le_normalizer_left U Y hYnorm).trans hprod.symm)
  have hyJ := OddHall.oddHall_of_normalized_sup (pCore_isPGroup.map (J).subtype)
    hodd.coprime_two_left hYnorm hjoin
  have hYC := hYJ.trans d.centralizer_le_distinguished_centralizer
  refine ⟨?_, ?_⟩
  · intro p hp hp2
    have hcard : Nat.card (Y.subgroupOf C₀) = Nat.card Y :=
      Nat.card_congr (subgroupOfEquivOfLe hYC).toEquiv
    rw [hcard, hp2] at hp
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hp)
  · intro p hp hp2
    change p.val ∣ Y.relIndex C₀ at hp
    have hi := relIndex_mul_relIndex Y J C₀ hYJ d.centralizer_le_distinguished_centralizer
    rw [← hi] at hp
    rcases p.property.dvd_mul.mp hp with hp | hp
    · exact hyJ.p_in_pi_of_p_dvd_index p hp hp2
    · have hpd := hp.trans d.centralizer_index_dvd
      exact hp2 (Nat.prime_eq_prime_of_dvd_pow p.property Nat.prime_two
        (p.property.dvd_of_dvd_pow hpd))

/-- The original C₀=VY product from an actual odd complement inside J and
its intrinsic normalizers. This consumes no later counting assertion. -/
public theorem Context.centralizer_product_of_odd_complement
    (Y : Subgroup G) (hYJ : Y ≤ J) (hodd : Odd (Nat.card Y))
    (hprod : (J : Set G) = (U : Set G) * (Y : Set G))
    (hcyc : IsCyclic Y)
    (hn : ∀ P : Subgroup G, P ≤ Y → P ≠ ⊥ → J ⊓ normalizer (P : Set G) = Y) :
    (C₀ : Set G) = (V : Set G) * (Y : Set G) := by
  let : IsCyclic Y := hcyc
  let Y₀ := Y.subgroupOf C₀
  have hYC := hYJ.trans d.centralizer_le_distinguished_centralizer
  have hHall := odd_complement_hall_in_centralizer d Y hYJ hodd hprod
  have hnormalizers (P : Subgroup C₀) (hPY : P ≤ Y₀) (hP : P ≠ ⊥) :
      normalizer (P : Set C₀) ≤ centralizer (P : Set C₀) := by
    let P₁ := P.map (C₀).subtype
    have hP₁Y : P₁ ≤ Y := by
      rintro _ ⟨p, hp, rfl⟩
      exact hPY hp
    have hP₁ : P₁ ≠ ⊥ := fun he => hP ((P.map_eq_bot_iff_of_injective (C₀).subtype_injective).mp he)
    have hCJ : C₀ ⊓ normalizer (P₁ : Set G) = A ⊔ Y := by
      rw [d.odd_subgroup_normalizer_in_distinguished_centralizer P₁
        (hP₁Y.trans hYJ) hP₁, hn P₁ hP₁Y hP₁]
    intro c hc p hp
    have hcG : (c : G) ∈ normalizer (P₁ : Set G) := by
      exact P.le_normalizer_map (C₀).subtype (mem_map_of_mem _ hc)
    have hcAY : (c : G) ∈ A ⊔ Y := hCJ ▸ ⟨c.property, hcG⟩
    have hcentral : A ⊔ Y ≤ centralizer (P₁ : Set G) := by
      apply sup_le
      · exact le_centralizer_iff.mp ((hP₁Y.trans hYJ).trans (centralizer_le d.distinguished_le))
      · exact le_centralizer_iff.mp (hP₁Y.trans (by
          apply le_centralizer_iff_isMulCommutative.mpr
          infer_instance))
    exact Subtype.ext (mem_centralizer_iff.mp (hcentral hcAY) p (mem_map_of_mem _ hp))
  have hcomp := OddSupplement.twoCore_complement_of_oddHall_normalizers Y₀ hHall hnormalizers
  apply Set.Subset.antisymm
  · intro c hc
    obtain ⟨v, hv, y, hy, he⟩ := Set.mem_mul.mp (hcomp.mul_eq ▸ Set.mem_univ (⟨c,hc⟩ : C₀))
    refine ⟨v, ?_, y, hy, congrArg Subtype.val he⟩
    rw [← embedded_centralizer_core_eq d]
    exact mem_map_of_mem _ hv
  · rintro _ ⟨v, hv, y, hy, rfl⟩
    exact (C₀).mul_mem (d.point_twoCore_le_distinguished_centralizer hv) (hYC hy)

end BenderSuzuki.ZD.LinearExclusion
