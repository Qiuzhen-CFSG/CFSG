module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.Models
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.SylowNormalIntersection
/-!
# The source actor, Sylow intersection, and parabolic product

The source T normalizes K, so a Sylow two-subgroup T of KT restricts to
T∩K and then maps onto a Sylow subgroup of the actual block quotient.
The image of L_v remains two-perfect and T-invariant. A two-group kernel
preserves the factor three in its order. All maps use the specified actor;
the last identity retains P=L_v(T∩K) as the original subgroup product.

Source: Aschbacher–Smith, Lemma 13.6.22, printed p.932.
-/

@[expose] public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.SourceActors
variable {G A W : Type*} [Group G] [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  {K U D T : Subgroup G} {ρ : Representation (ZMod 2) A W}

/-- The source residual maps to its literal image in the chosen block actor. -/
def imageMap (f : K →* A) (hDK : D ≤ K) : D →* (D.subgroupOf K).map f where
  toFun d := ⟨f ⟨d, hDK d.property⟩, mem_map_of_mem f d.property⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul f (⟨a, hDK a.property⟩ : K) (⟨b, hDK b.property⟩ : K)

theorem imageMap_surjective (f : K →* A) (hDK : D ≤ K) :
    Function.Surjective (imageMap f hDK) := by
  rintro ⟨a, k, hk, rfl⟩
  exact ⟨⟨k, hk⟩, rfl⟩

theorem image_perfect (f : K →* A) (hDK : D ≤ K) (hD : IsPPerfect 2 D) :
    IsPPerfect 2 ((D.subgroupOf K).map f) :=
  hD.of_surjective (imageMap f hDK) (imageMap_surjective f hDK)

theorem image_normalizes (f : K →* A) (hn : T ≤ normalizer (D : Set G)) :
    (T.subgroupOf K).map f ≤ normalizer ((D.subgroupOf K).map f : Set A) := by
  apply le_trans (map_mono (f := f) ?_) (le_normalizer_map f)
  intro t ht
  apply mem_normalizer_iff.mpr
  intro d
  exact mem_normalizer_iff.mp (hn ht) d

/-- A kernel of two-power order cannot remove the source factor three. -/
theorem three_dvd_image [Finite G] (f : K →* A) (hDK : D ≤ K)
    (hk : IsPGroup 2 f.ker) (h3 : 3 ∣ Nat.card D) :
    3 ∣ Nat.card ((D.subgroupOf K).map f) := by
  let q := imageMap f hDK
  let i : q.ker →* f.ker := {
    toFun := fun d => ⟨⟨d.val, hDK d.val.property⟩, congrArg Subtype.val d.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hi : Function.Injective i := by
    intro a b he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : f.ker => (x.val : G)) he
  obtain ⟨n, hn⟩ := (hk.of_injective i hi).exists_card_eq
  have hcard := q.ker.card_mul_index
  rw [index_ker, q.range_eq_top_of_surjective (imageMap_surjective f hDK),
    Nat.card_congr (topEquiv : (⊤ : Subgroup ((D.subgroupOf K).map f)) ≃* _).toEquiv,
    hn] at hcard
  rw [← hcard] at h3
  exact (Nat.Prime.dvd_mul (by decide : Nat.Prime 3)).mp h3 |>.resolve_left
    (by intro hh; have := (Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3)) hh; norm_num at this)

/-- The earlier Sylow intersection is mapped through the actual core quotient. -/
theorem sylow_image [Finite G] (f : K →* A) (hf : Function.Surjective f)
    (S : Sylow 2 K) (hS : (S : Subgroup K) = T.subgroupOf K) :
    ((S.mapSurjective hf : Sylow 2 A) : Subgroup A) = (T.subgroupOf K).map f := by
  rw [Sylow.coe_mapSurjective, hS]

/-- The source product P=L_v(T_v∩K) retains its exact image. -/
theorem parabolic_image (f : K →* A) (hDK : D ≤ K) :
    ((D ⊔ (T ⊓ K)).subgroupOf K).map f =
      (D.subgroupOf K).map f ⊔ (T.subgroupOf K).map f := by
  rw [subgroupOf_sup hDK inf_le_right, Subgroup.map_sup]
  congr 1
  congr 1
  ext x
  exact and_iff_left x.property
/-- Correct T-invariance of K gives the literal Sylow intersection in K. -/
theorem exists_source_sylow [Finite G] (hTK : T ≤ normalizer (K : Set G))
    (S : Sylow 2 ↥(K ⊔ T)) (hS : (S : Subgroup ↥(K ⊔ T)) = T.subgroupOf (K ⊔ T)) :
    ∃ R : Sylow 2 K, (R : Subgroup K) = T.subgroupOf K := by
  let N := K.subgroupOf (K ⊔ T)
  have : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hTK)
  obtain ⟨R, hR⟩ := S.exists_subgroupOf_eq_of_normal N
  let e : N ≃* K := subgroupOfEquivOfLe (le_sup_left : K ≤ K ⊔ T)
  have he : Function.Surjective e.toMonoidHom := e.surjective
  refine ⟨R.mapSurjective he, ?_⟩
  ext x
  rw [Sylow.coe_mapSurjective, mem_map_equiv, hR, hS]
  rfl
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.SourceActors
