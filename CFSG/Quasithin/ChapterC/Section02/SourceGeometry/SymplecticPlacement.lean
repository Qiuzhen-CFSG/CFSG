module

public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.ThompsonPlacement
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.StarSylow
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.SylowBlocks
public import Theory.SpecificGroups.SymplecticFour.RadicalParabolics.Exact
public import Theory.SpecificGroups.SymplecticFour.BorelActionGeometry.Normalizers

/-!
# The marked symplectic parabolic from the Thompson image

Apply the exact intrinsic radical theorem to the original R*∩K*. In the
case J(R)* ≤ K*, its normalizer lies in M_K*. A point or plane parabolic
is maximal, and M_K* is proper, so these subgroups coincide after the same
model conjugation. The other intrinsic alternative lifts to R∈Syl₂(KR),
where the genuine C.1.29 source theorem makes K a chi-zero block.

No marked-parabolic or normalizer-placement premise is supplied. The
remaining case where J(R)* acts externally remains a separate source branch.
Source: Aschbacher--Smith C.2.7(3), printed pp.146--147.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H K R M : Subgroup G}
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem star_symplectic_thompson_placement_or_sylow
    (h : Input κ H R M K) [(K.subgroupOf H).Normal]
    (hinner : starImage K R (Stellmacher.elementaryAbelianMaxJ R) ≤ starImage K R K)
    (e : starImage K R K ≃* Sp F) :
    (∃ g : Sp F,
      (((starM K R M).subgroupOf (starImage K R K)).map e.toMonoidHom).map
          (MulAut.conj g).toMonoidHom = pointParabolic ∨
      (((starM K R M).subgroupOf (starImage K R K)).map e.toMonoidHom).map
          (MulAut.conj g).toMonoidHom = planeParabolic) ∨
      Chapter1.IsSylowIn 2 R (K ⊔ R) := by
  let C := starImage K R K
  let U := (starImage K R R).subgroupOf C
  let P := (starM K R M).subgroupOf C
  have hu : (U.map e.toMonoidHom).IsPRadical 2 :=
    (star_intersection_radical_of_thompson_inner h hinner).map_equiv e
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨n,_,hcard⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2 ^ (n : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hn : 1 ≤ (n : ℕ) := by
    have hpos := Finite.one_lt_card (α := F)
    by_contra hn
    have hn0 : (n : ℕ) = 0 := by omega
    rw [hF,hn0,pow_zero] at hpos
    omega
  rcases radical_normalizer_parabolic_or_sylow (U.map e.toMonoidHom) hu hF hn with
    ⟨g,hg⟩ | ⟨S,hS⟩
  · let a := MulAut.conj g
    let Q := (P.map e.toMonoidHom).map a.toMonoidHom
    have hPQ : Q ≠ ⊤ := by
      intro he
      have hproper : P ≠ ⊤ := fun hp =>
        (star_thompson_intersection_of_normal_input h).2.not_ge (subgroupOf_eq_top.mp hp)
      apply hproper
      have h₁ := congrArg (comap a.toMonoidHom) he
      have h₂ : P.map e.toMonoidHom = ⊤ := by
        simpa only [Q,comap_map_eq_self_of_injective (f := a.toMonoidHom) a.injective,comap_top] using h₁
      have h₃ := congrArg (comap e.toMonoidHom) h₂
      simpa only [comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective,comap_top] using h₃
    have hNQ : (normalizer (U.map e.toMonoidHom : Set (Sp F))).map a.toMonoidHom ≤ Q := by
      rw [←map_equiv_normalizer_eq]
      exact map_mono (map_mono (star_intersection_normalizer_control_of_thompson_inner h hinner))
    left
    refine ⟨g,?_⟩
    rcases hg with hp | hp
    · exact Or.inl ((BorelActionGeometry.pointParabolic_isCoatom.le_iff_eq hPQ).mp (hp ▸ hNQ))
    · exact Or.inr ((BorelActionGeometry.planeParabolic_isCoatom.le_iff_eq hPQ).mp (hp ▸ hNQ))
  · let S' := S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hs' : (S' : Subgroup C) = U := by
      change (S : Subgroup (Sp F)).map e.symm.toMonoidHom = U
      rw [hS]
      ext x
      constructor
      · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
        simpa using hz
      · intro hx
        exact ⟨e x,⟨x,hx,rfl⟩,e.symm_apply_apply x⟩
    have hSR : (S' : Subgroup C).map C.subtype ≤ starImage K R R := by
      rw [hs',subgroupOf_map_subtype]
      exact inf_le_left
    obtain ⟨T,hT⟩ := radical_sylow_of_star_component_sylow h S' hSR
    right
    refine ⟨T,?_⟩
    rw [hT,map_subgroupOf_eq_of_le (show R ≤ K ⊔ R from le_sup_right)]

theorem star_symplectic_thompson_placement_or_chiZero
    (h : Input KnownSimple.IsKnownSimple H R M K) [(K.subgroupOf H).Normal]
    (hinner : starImage K R (Stellmacher.elementaryAbelianMaxJ R) ≤ starImage K R K)
    (e : starImage K R K ≃* Sp F) :
    (∃ g : Sp F,
      (((starM K R M).subgroupOf (starImage K R K)).map e.toMonoidHom).map
          (MulAut.conj g).toMonoidHom = pointParabolic ∨
      (((starM K R M).subgroupOf (starImage K R K)).map e.toMonoidHom).map
          (MulAut.conj g).toMonoidHom = planeParabolic) ∨
      IsBlock (K.subgroupOf H) ∧ IsChiZeroBlock K := by
  rcases star_symplectic_thompson_placement_or_sylow h hinner e with hp | hs
  · exact Or.inl hp
  · exact Or.inr (source_chiZero_of_sylow_input h hs)

end CFSG.Quasithin.ChapterC.C27Source
