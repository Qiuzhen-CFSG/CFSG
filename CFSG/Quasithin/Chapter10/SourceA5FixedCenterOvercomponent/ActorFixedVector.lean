module
public import Theory.SpecificGroups.AlternatingFiveSolvableResidualNormalizer
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.NormalizerFixedLine
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.LayerClosureRatio
/-!
# Solvable residuals fix the original A₅ Sylow vector

A solvable two-perfect subgroup normalizes a Sylow two-subgroup of a normal
A₅ actor whenever that Sylow subgroup normalizes it. Pulling this conclusion
through the action kernel makes the Sylow commutators fix the prescribed
vector. The original A₅ fixed space has at most two elements, so the whole
residual fixes the vector.

Source: the rank-one exclusion in Aschbacher–Smith 10.2.1, printed p.743.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter10
variable {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
theorem solvable_twoPerfect_actor_fixes_of_alternatingFive_image (V R Y B : Subgroup G) (f : G →* A)
    (e : B.map f ≃* alternatingGroup (Fin 5))
    (P : Sylow 2 (B.map f))
    (hP : (P:Subgroup (B.map f)).map (B.map f).subtype = R.map f)
    [Group.IsSolvable Y] (hp : IsPPerfect 2 Y)
    (hYA : Y.map f ≤ normalizer (B.map f : Set A))
    (hRY : R ≤ normalizer (Y:Set G))
    (hYV : Y ≤ normalizer (V:Set G))
    (hk : f.ker ≤ centralizer (V:Set G))
    (hsmall : Nat.card (V ⊓ centralizer (R:Set G) : Subgroup G) ≤ 2)
    {v : G} (hv : v ∈ V) (hvR : v ∈ centralizer (R:Set G)) :
    Y ≤ centralizer ({v}:Set G) := by
  let : Group.IsSolvable (Y.map f) := Group.isSolvable_of_surjective (f.subgroupMap_surjective Y)
  have hnorm : Y.map f ≤ normalizer (R.map f:Set A) := by
    rw [←hP]
    apply Theory.SpecificGroups.alternatingFive_solvable_residual_normalizes_sylow
      (B.map f) e P (Y.map f)
      (hp.of_surjective (f.subgroupMap Y) (f.subgroupMap_surjective Y)) hYA
    rw [hP]
    exact (map_mono hRY).trans ((Y).le_normalizer_map f)
  apply normalizer_fixes_of_small_fixed_commutator V R Y hYV hsmall hv hvR
  have hc : ⁅R,Y⁆ ≤ R ⊔ f.ker := by
    have hh := le_normalizer_iff_commutator_le_left.mp hnorm
    rw [←map_commutator] at hh
    have hh' := map_le_iff_le_comap.mp hh
    rwa [comap_map_eq] at hh'
  apply hc.trans
  apply sup_le
  · intro r hr
    exact mem_centralizer_singleton_iff.mpr (hvR r hr)
  · exact hk.trans (centralizer_le (Set.singleton_subset_iff.mpr hv))
end CFSG.Quasithin.Chapter10

namespace CFSG.Quasithin.Chapter10
open ChapterC
variable {G : Type*} [Group G] [Finite G]
theorem alternatingFive_actor_fixes_sylow_vector (L I R Y V : Subgroup G) [I.Normal] [V.Normal]
    (hL : IsAlternatingBlock L 5) (hLI : L ≤ I)
    (hV : V = (blockU L).map L.subtype)
    (ha : Nonempty ((I ⧸ centralizer (V.subgroupOf I:Set I)) ≃* alternatingGroup (Fin 5)))
    (hR : Chapter1.IsSylowIn 2 R L)
    [Group.IsSolvable Y] (hp : IsPPerfect 2 Y)
    (hRY : R ≤ normalizer (Y:Set G))
    {v : G} (hv : v ∈ V) (hvR : v ∈ centralizer (R:Set G)) :
    Y ≤ centralizer ({v}:Set G) := by
  let q := QuotientGroup.mk' (centralizer (V:Set G))
  have hVI : V ≤ I := hV ▸ (map_subtype_le _).trans hLI
  have hker : (q.subgroupMap I).ker = centralizer (V.subgroupOf I:Set I) := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    ext i
    change (i:G) ∈ centralizer (V:Set G) ↔ _
    constructor
    · intro hi x hx
      exact Subtype.ext (hi x hx)
    · intro hi x hx
      exact congrArg Subtype.val (hi ⟨x,hVI hx⟩ hx)
  obtain ⟨ea⟩ := ha
  let eI : I.map q ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientKerEquivOfSurjective (q.subgroupMap I)
      (q.subgroupMap_surjective I)).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hker).trans ea)
  obtain ⟨eL⟩ := hL.layer_split_quotient_image L V hV.symm.le
    (by rw [hV,sup_eq_left.mpr inf_le_left]) q (QuotientGroup.ker_mk' _)
  have heq : L.map q = I.map q := eq_of_le_of_card_ge (map_mono hLI)
    ((Nat.card_congr eI.toEquiv).trans (Nat.card_congr eL.toEquiv).symm).le
  let : (I.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hYA : Y.map q ≤ normalizer (L.map q:Set _) := by
    rw [heq]
    exact le_normalizer_of_normal
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_map hR q
  have hsmall : Nat.card (V ⊓ centralizer (R:Set G) : Subgroup G) ≤ 2 := by
    obtain ⟨S,hS⟩ := hR
    let f : (V ⊓ centralizer (R:Set G) : Subgroup G) →
        (blockU L ⊓ centralizer (S:Set L) : Subgroup L) := fun x =>
      ⟨⟨x,(hV ▸ map_subtype_le (blockU L)) x.property.1⟩,by
        refine ⟨?_,?_⟩
        · have hx : (x:G) ∈ (blockU L).map L.subtype := hV.le x.property.1
          obtain ⟨l,hl,he⟩ := hx
          exact (Subtype.ext he : l=⟨x,_⟩) ▸ hl
        · intro s hs
          exact Subtype.ext (x.property.2 s (hS ▸ mem_map_of_mem L.subtype hs))⟩
    have hf : Function.Injective f := by
      intro x y he
      exact Subtype.ext (congrArg (fun z : (blockU L ⊓ centralizer (S:Set L) : Subgroup L) =>
        ((z:L):G)) he)
    exact (Nat.card_le_card_of_injective f hf).trans (hL.sylow_fixed_card_le_two S)
  exact solvable_twoPerfect_actor_fixes_of_alternatingFive_image V R Y L q eL P hP hp
    hYA hRY le_normalizer_of_normal (by rw [QuotientGroup.ker_mk']) hsmall hv hvR
end CFSG.Quasithin.Chapter10
