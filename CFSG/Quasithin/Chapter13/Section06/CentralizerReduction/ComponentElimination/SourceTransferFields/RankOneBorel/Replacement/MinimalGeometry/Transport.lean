module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement

/-!
# Comparing the replacement's native plus quotient

Once equal star images have been established, the literal star-to-plus map
shows that K₀ surjects onto the original K⁺. Equality of W_K₀ and W_K then
identifies the kernels of the two component maps on K₀. Their first-isomorphism
maps give an equivalence from K₀'s native plus image to K⁺, compatible with
both component maps and with conjugation on the actual W_K.

The final model comparison composes this equivalence with the original model.
It is a transport result: equality of star images remains an explicit premise,
not an assertion that the full minimal-local choice has that equality.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.18, printed p.931 (PDF p.948), and the action quotients on p.929.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.MinimalGeometry
open Subgroup Theory.GroupTheory ComponentSelection
variable {G : Type*} [Group G]

/-- The native component map has the literal relative centralizer as kernel. -/
theorem componentMap_ker (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    (componentMap K L T z v hL hz).ker =
      (centralizer (WK K L T z v : Set G)).subgroupOf K := by
  ext k
  change componentMap K L T z v hL hz k = 1 ↔ _
  rw [Subtype.ext_iff]
  change inclusion (K_le_plusActor K L T v) k ∈ (plusMk K L T z v hL hz).ker ↔ _
  rw [plusMk_ker]
  rfl

/-- Equal star images have equal images in the original plus quotient. -/
theorem plusImage_eq_of_starImage_eq (K₀ K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ≤ Gv v) (hle : K₀ ≤ K)
    (he : starImage z v K₀ = starImage z v K) :
    plusImage K L T z v hL hz K₀ = plusImage K L T z v hL hz K := by
  rw [← starToPlus_image K L T z v hK hL hz K₀
      (hle.trans (K_le_plusActor K L T v)), he,
    starToPlus_image K L T z v hK hL hz K (K_le_plusActor K L T v)]

/-- Restriction to K₀ still covers the original plus image of K. -/
theorem restricted_componentMap_surjective (K₀ K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ≤ Gv v) (hle : K₀ ≤ K)
    (he : starImage z v K₀ = starImage z v K) :
    Function.Surjective ((componentMap K L T z v hL hz).comp (inclusion hle)) := by
  intro a
  have ha : (a : Gplus K L T z v hL hz) ∈ plusImage K L T z v hL hz K₀ :=
    (plusImage_eq_of_starImage_eq K₀ K L T z v hL hz hK hle he).ge a.property
  obtain ⟨x, hx, hxa⟩ := ha
  exact ⟨⟨x, hx⟩, Subtype.ext hxa⟩

private theorem exists_common_quotient_equiv
    {D A B : Type*} [Group D] [Group A] [Group B]
    (f : D →* A) (g : D →* B) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hk : f.ker = g.ker) : ∃ e : A ≃* B, ∀ x, e (f x) = g x := by
  let a := QuotientGroup.quotientKerEquivOfSurjective f hf
  let b := QuotientGroup.quotientKerEquivOfSurjective g hg
  refine ⟨(a.symm.trans (QuotientGroup.quotientMulEquivOfEq hk)).trans b, ?_⟩
  intro x
  have hm : a.symm (f x) = QuotientGroup.mk x := by
    apply a.injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  change b (QuotientGroup.quotientMulEquivOfEq hk (a.symm (f x))) = g x
  rw [hm]
  rfl

private theorem nativePlusExists (K₀ K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ≤ Gv v) (hle : K₀ ≤ K)
    (he : starImage z v K₀ = starImage z v K)
    (hW : WK K₀ L T z v = WK K L T z v) :
    ∃ e : plusImage K₀ L T z v hL hz K₀ ≃* plusImage K L T z v hL hz K,
      ∀ k : K₀, e (componentMap K₀ L T z v hL hz k) =
        componentMap K L T z v hL hz (inclusion hle k) := by
  apply exists_common_quotient_equiv (componentMap K₀ L T z v hL hz)
    ((componentMap K L T z v hL hz).comp (inclusion hle))
    (componentMap_surjective K₀ L T z v hL hz)
    (restricted_componentMap_surjective K₀ K L T z v hL hz hK hle he)
  rw [← MonoidHom.comap_ker, componentMap_ker, componentMap_ker, hW]
  rfl

/-- Compare the native plus images through their common representatives in K₀.
The first-isomorphism construction is encapsulated in its proved specification
so downstream action proofs do not unfold the two quotient implementations. -/
noncomputable def nativePlusEquiv (K₀ K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ≤ Gv v) (hle : K₀ ≤ K)
    (he : starImage z v K₀ = starImage z v K)
    (hW : WK K₀ L T z v = WK K L T z v) :
    plusImage K₀ L T z v hL hz K₀ ≃* plusImage K L T z v hL hz K :=
  Classical.choose (nativePlusExists K₀ K L T z v hL hz hK hle he hW)

/-- The comparison preserves the specified quotient maps on every representative. -/
theorem nativePlusEquiv_mk (K₀ K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ≤ Gv v) (hle : K₀ ≤ K)
    (he : starImage z v K₀ = starImage z v K)
    (hW : WK K₀ L T z v = WK K L T z v) (k : K₀) :
    nativePlusEquiv K₀ K L T z v hL hz hK hle he hW
      (componentMap K₀ L T z v hL hz k) =
        componentMap K L T z v hL hz (inclusion hle k) :=
  Classical.choose_spec (nativePlusExists K₀ K L T z v hL hz hK hle he hW) k

/-- Corresponding vectors have the same conjugates. The vector comparison is
stated in the original ambient group, without transporting group instances. -/
theorem nativePlusEquiv_action (K₀ K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ≤ Gv v) (hle : K₀ ≤ K)
    (he : starImage z v K₀ = starImage z v K)
    (hW : WK K₀ L T z v = WK K L T z v)
    (a : plusImage K₀ L T z v hL hz K₀)
    (w₀ : WK K₀ L T z v) (w : WK K L T z v) (hw : (w₀ : G) = (w : G)) :
    ((plusAction K₀ L T z v hL hz a w₀ : WK K₀ L T z v) : G) =
      ((plusAction K L T z v hL hz
        (nativePlusEquiv K₀ K L T z v hL hz hK hle he hW a) w : WK K L T z v) : G) := by
  obtain ⟨k, hk⟩ := componentMap_surjective K₀ L T z v hL hz a
  calc
    _ = ((plusAction K₀ L T z v hL hz
        (componentMap K₀ L T z v hL hz k) w₀ : WK K₀ L T z v) : G) :=
      (congrArg (fun b : plusImage K₀ L T z v hL hz K₀ =>
        ((plusAction K₀ L T z v hL hz b w₀ : WK K₀ L T z v) : G)) hk).symm
    _ = (k : G) * (w₀ : G) * (k : G)⁻¹ :=
      plusAction_mk_apply K₀ L T z v hL hz (inclusion (K_le_plusActor K₀ L T v) k) w₀
    _ = (k : G) * (w : G) * (k : G)⁻¹ := congrArg (fun x : G => (k : G) * x * (k : G)⁻¹) hw
    _ = ((plusAction K L T z v hL hz
        (componentMap K L T z v hL hz (inclusion hle k)) w : WK K L T z v) : G) :=
      (plusAction_mk_apply K L T z v hL hz
        (inclusion (K_le_plusActor K L T v) (inclusion hle k)) w).symm
    _ = _ := congrArg (fun b : plusImage K L T z v hL hz K =>
      ((plusAction K L T z v hL hz b w : WK K L T z v) : G))
        ((nativePlusEquiv_mk K₀ K L T z v hL hz hK hle he hW k).symm.trans
          (congrArg (nativePlusEquiv K₀ K L T z v hL hz hK hle he hW) hk))

/-- Transport an actual model isomorphism to the native plus quotient of K₀. -/
noncomputable def modelOfEqualStarImage (K₀ K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ≤ Gv v) (hle : K₀ ≤ K)
    (hn₀ : Tv T v ≤ normalizer (K₀ : Set G))
    (hnK : Tv T v ≤ normalizer (K : Set G))
    (he : starImage z v K₀ = starImage z v K)
    {M : Type*} [Group M] (e : plusImage K L T z v hL hz K ≃* M) :
    plusImage K₀ L T z v hL hz K₀ ≃* M :=
  (nativePlusEquiv K₀ K L T z v hL hz hK hle he
    (Replacement.WK_eq_of_starImage_eq K₀ K L T z v (hle.trans hK) hK hn₀ hnK he)).trans e

/-- The transported model uses the original marking on every element of K₀. -/
theorem modelOfEqualStarImage_mk (K₀ K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ≤ Gv v) (hle : K₀ ≤ K)
    (hn₀ : Tv T v ≤ normalizer (K₀ : Set G))
    (hnK : Tv T v ≤ normalizer (K : Set G))
    (he : starImage z v K₀ = starImage z v K)
    {M : Type*} [Group M] (e : plusImage K L T z v hL hz K ≃* M) (k : K₀) :
    modelOfEqualStarImage K₀ K L T z v hL hz hK hle hn₀ hnK he e
      (componentMap K₀ L T z v hL hz k) =
        e (componentMap K L T z v hL hz (inclusion hle k)) := by
  exact congrArg e (nativePlusEquiv_mk K₀ K L T z v hL hz hK hle he _ k)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.MinimalGeometry

end
