module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.BaumannNormalization.Alternating
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.BaumannNormalization.Restriction
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.BaumannNormalization.Natural

/-!
# Baumann normalization of a commuting chi-zero family

For A3 and A5, the short layer has trivial fixed kernel. For a natural
SL2 block, restrict to its normalizer in R: the actual block Sylow
intersection is still Sylow in that extension, and Thompson heredity
retains J(R). The natural fixed-witness calculation then applies. The
omega-center argument prevents movement to any distinct commuting block.
No bound on the number of blocks or characteristic-two assumption is
needed beyond the supplied genuine block and Sylow data.

Source: Aschbacher--Smith C.1.16(2) and C.5.4(1), pp.125--126,155.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BaumannNormalization
open Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]

theorem normalizes_chiZero {ι : Type*} (R : Subgroup G)
    (K : ι → Subgroup G)
    (hperm : ∀ g ∈ R, ∀ i, ∃ j, (K i).map (MulAut.conj g).toMonoidHom = K j)
    (hcomm : Pairwise fun i j => ⁅K i,K j⁆ = ⊥)
    (i : ι) (hR : IsPGroup 2 R)
    (hUR : (blockU (K i)).map (K i).subtype ≤ R)
    (hmoved : K i = ⁅K i,elementaryAbelianMaxJ R⁆)
    (h : IsChiZeroBlock (K i))
    (P : Sylow 2 (K i)) (hP : (P : Subgroup (K i)).map (K i).subtype = R ⊓ K i) :
    ChapterB.baumann R ≤ normalizer (K i) := by
  rcases h with ⟨n,hn,hs,F,hField,hFinite,hcard,hq,τ,⟨m⟩,hτ⟩ | hA
  · let := hField
    let := hFinite
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    let : Algebra (ZMod 2) F := ZMod.algebra F 2
    let T : Subgroup G := R ⊓ normalizer (K i)
    have hJ : elementaryAbelianMaxJ T = elementaryAbelianMaxJ R :=
      thompson_normalizer_intersection R (K i) hmoved
    obtain ⟨S,hS⟩ := normalizer_intersection_sylow R (K i) hR P hP
    have hUT : U (K i) ≤ T := le_inf hUR ((map_subtype_le _).trans (K i).le_normalizer)
    have hf := natural_fixed_noncentral (K i) T hs (hR.to_le inf_le_left) inf_le_right
      S hS hUT (hJ.symm ▸ hmoved) τ m hτ (by
        rw [hcard]
        exact lt_of_le_of_lt (by decide : 2 ≤ 2^1) (pow_lt_pow_right₀ (by decide) hn))
    rw [hJ] at hf
    let : IsElementaryAbelian 2 (blockU (K i)) := hs.elementary
    let : IsElementaryAbelian 2 ((blockU (K i)).map (K i).subtype) :=
      IsElementaryAbelian.map (K i).subtype
    exact normalizes_of_fixed_witness R K hperm hcomm i _ hUR (map_subtype_le _) hf
  · exact normalizes_alternating R K hperm hcomm i hR hUR hmoved hA
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BaumannNormalization
