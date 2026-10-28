module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.Displacement
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.DualOffender.NaturalCard
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.DualOffender.AlternatingCard

/-!
# C.5.13 displacement on the literal moved module

The proved source identity [V₁,K]=U bounds every original K actor on
I=[V₁,L], with its actual image in N/C_N(V₁). In the proper-enlargement
source types L₂(4) and A₅ the full central-cover orders give fixed
codimension at most six, hence less than eight. No irreducibility or
model for I is assumed.
Source: Aschbacher–Smith C.5.13, printed p.163.
-/
public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]

/-- The original source maps give a bound by the binary rank of U. -/
theorem noncubic_source_moved_displacement (K T X : Subgroup G)
    (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (k : G) (hk : k ∈ K) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    let : IsElementaryAbelian 2 V := hs.1
    let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
    let hKN : K ≤ N := le_inf (le_sup_left.trans hAX)
      (le_sup_left.trans ((K ⊔ T).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (K ⊔ T) (pCore 2 (K ⊔ T : Subgroup G)))))
    let a : closureImage (V.subgroupOf N) (K.subgroupOf N) :=
      ⟨QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N)) ⟨k,hKN hk⟩,
        mem_map_of_mem _ (le_normalClosure hk)⟩
    fixedCodim (movedRepresentation (V.subgroupOf N) (K.subgroupOf N)) (zpowers a) ≤
      Nat.log 2 (Nat.card (U K)) := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  have hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let : IsElementaryAbelian 2 V := hs.1
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
  have hKN : K ≤ N := le_inf (le_sup_left.trans hAX)
    (le_sup_left.trans ((K ⊔ T).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (K ⊔ T) (pCore 2 (K ⊔ T : Subgroup G)))))
  have hUN : U K ≤ N := (map_subtype_le _).trans hKN
  have hc : ⁅V.subgroupOf N,K.subgroupOf N⁆ ≤ (U K).subgroupOf N := by
    apply map_le_map_iff_of_injective N.subtype_injective |>.mp
    rw [map_commutator,map_subgroupOf_eq_of_le hs.2.1,map_subgroupOf_eq_of_le hKN,
      map_subgroupOf_eq_of_le hUN]
    exact hs.2.2.2.2.2.2.2.le
  have hd := moved_displacement_le_card (V.subgroupOf N) (K.subgroupOf N)
    ((U K).subgroupOf N) hc ⟨k,hKN hk⟩ hk
  have he : Nat.card ((U K).subgroupOf N) = Nat.card (U K) :=
    Nat.card_congr (subgroupOfEquivOfLe hUN).toEquiv
  rw [he] at hd
  exact hd
/-- The actual natural-four marking bounds the entire original U, including
its central kernel, and discharges the strict-eight displacement bound. -/
theorem natural_four_source_moved_displacement_lt_eight (K T X : Subgroup G)
    (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {F : Type*} [Field F] (h : Setup T K F) (hn : IsL2EvenBlock K 2)
    (k : G) (hk : k ∈ K) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    let : IsElementaryAbelian 2 V := hs.1
    let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
    let hKN : K ≤ N := le_inf (le_sup_left.trans hAX)
      (le_sup_left.trans ((K ⊔ T).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (K ⊔ T) (pCore 2 (K ⊔ T : Subgroup G)))))
    let a : closureImage (V.subgroupOf N) (K.subgroupOf N) :=
      ⟨QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N)) ⟨k,hKN hk⟩,
        mem_map_of_mem _ (le_normalClosure hk)⟩
    fixedCodim (movedRepresentation (V.subgroupOf N) (K.subgroupOf N)) (zpowers a) < 8 := by
  have hd := noncubic_source_moved_displacement K T X hK h3 hT hUT hTK P hP hA hAX S hS k hk
  have hc := natural_module_card_le h hn
  rw [natural_coordinate_card h hn] at hc
  have hl := Nat.log_monotone (b := 2) hc
  norm_num at hl
  exact lt_of_le_of_lt hd (by omega)

/-- The actual A₅ marking similarly discharges the displacement bound. -/
theorem alternating_five_source_moved_displacement_lt_eight (K T X : Subgroup G)
    (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {J : Subgroup G} (h : ConjugateSource.AlternatingPairSetup T K J)
    (k : G) (hk : k ∈ K) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    let : IsElementaryAbelian 2 V := hs.1
    let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
    let hKN : K ≤ N := le_inf (le_sup_left.trans hAX)
      (le_sup_left.trans ((K ⊔ T).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (K ⊔ T) (pCore 2 (K ⊔ T : Subgroup G)))))
    let a : closureImage (V.subgroupOf N) (K.subgroupOf N) :=
      ⟨QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N)) ⟨k,hKN hk⟩,
        mem_map_of_mem _ (le_normalClosure hk)⟩
    fixedCodim (movedRepresentation (V.subgroupOf N) (K.subgroupOf N)) (zpowers a) < 8 := by
  have hd := noncubic_source_moved_displacement K T X hK h3 hT hUT hTK P hP hA hAX S hS k hk
  have hc : Nat.card (U K) = 16 := h.module_card
  rw [hc] at hd
  exact lt_of_le_of_lt hd (by decide)

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
