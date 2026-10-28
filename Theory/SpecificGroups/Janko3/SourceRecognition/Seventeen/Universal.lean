module
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Triangle

/-!
# Faithful completions are universal

The two intersections in H₃ generate H₃: their orders are 24 and 12,
while H₃ has order 120 and the H₁–H₂ intersection has order 30.
For arbitrary compatible homomorphisms on the three local groups, take
their graphs in H × K. These graphs form another faithful source amalgam.
Lemma 2.7 gives order 8160 to both completions, so projection onto H is
bijective. Its inverse followed by the second projection is the unique
extension of the compatible maps. This proves the universal mapping
property, including for noninjective maps into an arbitrary group.

Source: Baumeister, *A geometry for groups of J₃-type* (2007),
Corollary 2.8, printed p.498.
-/

public noncomputable section
open Subgroup
namespace Sporadic.Janko3.SourceRecognition.Seventeen
namespace SourceData
variable {G : Type*} [Group G] (S : SourceData G)

theorem third_card : Nat.card S.H3 = 120 := by
  rw [Nat.card_congr S.triangleEquiv.toEquiv, Nat.card_prod, nat_card_alternatingGroup]
  norm_num [Nat.card_fin, Nat.factorial, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative]

theorem third_generated :
    S.H1.subgroupOf S.H3 ⊔ S.H2.subgroupOf S.H3 = ⊤ := by
  let : Finite S.H3 := Nat.finite_of_card_ne_zero (by rw [S.third_card]; decide)
  let A := S.H1.subgroupOf S.H3
  let B := S.H2.subgroupOf S.H3
  have ha : Nat.card A = 24 := by
    change Nat.card (S.H1.subgroupOf S.H3) = 24
    rw [← inf_subgroupOf_right, Nat.card_congr (subgroupOfEquivOfLe
      (show S.H1 ⊓ S.H3 ≤ S.H3 from inf_le_right)).toEquiv]
    exact S.point_third_overlap_card
  have hb : Nat.card B = 12 := by
    change Nat.card (S.H2.subgroupOf S.H3) = 12
    rw [← inf_subgroupOf_right, Nat.card_congr (subgroupOfEquivOfLe
      (show S.H2 ⊓ S.H3 ≤ S.H3 from inf_le_right)).toEquiv]
    exact S.third_overlap_card
  have hi : A.index = 5 := by
    have hh := A.card_mul_index
    rw [ha, S.third_card] at hh
    omega
  have hd : (A ⊔ B).index ∣ 5 := hi ▸ index_dvd_of_le (show A ≤ A ⊔ B from le_sup_left)
  rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with h | h
  · exact index_eq_one.mp h
  · have he : A ⊔ B = A := by
      apply (eq_of_le_of_card_ge (show A ≤ A ⊔ B from le_sup_left) ?_).symm
      have hm := (A ⊔ B).card_mul_index
      rw [h, S.third_card] at hm
      omega
    have hBA : B ≤ A := he ▸ (show B ≤ A ⊔ B from le_sup_right)
    have hle : S.H2 ⊓ S.H3 ≤ S.H1 ⊓ S.H2 := by
      intro x hx
      exact ⟨hBA (show (⟨x, hx.2⟩ : S.H3) ∈ B from hx.1), hx.1⟩
    have hh := card_dvd_of_le hle
    rw [S.third_overlap_card, S.overlap_card] at hh
    norm_num at hh

abbrev family : Fin 3 → Subgroup G
  | 0 => S.H1
  | 1 => S.H2
  | 2 => S.H3

end SourceData

variable {G : Type*} [Group G] (S : SourceData G)
/-- Maps on the three actual subgroups agreeing on all their literal overlaps. -/
structure CompatibleMaps (K : Type*) [Group K] where
  map : (i : Fin 3) → S.family i →* K
  compatible : ∀ (i j : Fin 3) (x : S.family i) (y : S.family j),
    (x : G) = (y : G) → map i x = map j y

namespace CompatibleMaps
variable {S} {K : Type*} [Group K] (F : CompatibleMaps S K)

@[expose] def graphMap (i : Fin 3) : S.family i →* G × K := (S.family i).subtype.prod (F.map i)

@[expose] def completion : Subgroup (G × K) := (F.graphMap 0).range ⊔ (F.graphMap 1).range

private theorem graph_third_le : (F.graphMap 2).range ≤ F.completion := by
  have hh : (S.H1.subgroupOf S.H3) ⊔ (S.H2.subgroupOf S.H3) ≤
      F.completion.comap (F.graphMap 2) := by
    apply sup_le
    · intro x hx
      have he : F.graphMap 2 x = F.graphMap 0 ⟨x, hx⟩ := by
        refine Prod.ext rfl ?_
        exact F.compatible 2 0 x ⟨x, hx⟩ rfl
      rw [mem_comap, he]
      exact (show (F.graphMap 0).range ≤ F.completion from le_sup_left) (show F.graphMap 0 ⟨x, hx⟩ ∈ (F.graphMap 0).range from ⟨_, rfl⟩)
    · intro x hx
      have he : F.graphMap 2 x = F.graphMap 1 ⟨x, hx⟩ := by
        refine Prod.ext rfl ?_
        exact F.compatible 2 1 x ⟨x, hx⟩ rfl
      rw [mem_comap, he]
      exact (show (F.graphMap 1).range ≤ F.completion from le_sup_right) (show F.graphMap 1 ⟨x, hx⟩ ∈ (F.graphMap 1).range from ⟨_, rfl⟩)
  rw [S.third_generated] at hh
  rintro y ⟨x, rfl⟩
  exact hh (mem_top x)

private theorem graph_le (i : Fin 3) : (F.graphMap i).range ≤ F.completion := by
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right
  · exact graph_third_le F

@[expose] def lift (i : Fin 3) : S.family i →* F.completion :=
  (F.graphMap i).codRestrict F.completion (fun x => by exact graph_le F i ⟨x, rfl⟩)

@[expose] def projection : F.completion →* G := (MonoidHom.fst G K).comp F.completion.subtype

@[simp] theorem projection_lift (i : Fin 3) (x : S.family i) :
    F.projection (F.lift i x) = x := rfl

theorem lift_injective (i : Fin 3) : Function.Injective (F.lift i) := by
  intro x y he
  exact Subtype.ext (congrArg F.projection he)

abbrev localGroup (i : Fin 3) := (F.lift i).range

def localEquiv (i : Fin 3) : F.localGroup i ≃* S.family i :=
  (MonoidHom.ofInjective (F.lift_injective i)).symm

theorem localEquiv_coe (i : Fin 3) (x : F.localGroup i) :
    (F.localEquiv i x : G) = F.projection x := by
  obtain ⟨y, hy⟩ := x.property
  have he : x = (MonoidHom.ofInjective (F.lift_injective i)) y := Subtype.ext hy.symm
  rw [he]
  change ((MonoidHom.ofInjective (F.lift_injective i)).symm
    ((MonoidHom.ofInjective (F.lift_injective i)) y) : G) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem projection_injective (i : Fin 3) :
    Function.Injective (fun x : F.localGroup i => F.projection x) := by
  intro x y he
  apply (F.localEquiv i).injective
  apply Subtype.ext
  simpa only [F.localEquiv_coe] using he

private def intersectionMap (i j : Fin 3) :
    (F.localGroup i ⊓ F.localGroup j : Subgroup F.completion) →*
      (S.family i ⊓ S.family j : Subgroup G) :=
  (F.projection.comp (F.localGroup i ⊓ F.localGroup j).subtype).codRestrict _ (fun x => by
    obtain ⟨a, ha⟩ := x.property.1
    obtain ⟨b, hb⟩ := x.property.2
    change F.projection x ∈ S.family i ⊓ S.family j
    exact ⟨by rw [← ha, F.projection_lift]; exact a.property,
      by rw [← hb, F.projection_lift]; exact b.property⟩)

def intersectionEquiv (i j : Fin 3) :
    (F.localGroup i ⊓ F.localGroup j : Subgroup F.completion) ≃*
      (S.family i ⊓ S.family j : Subgroup G) :=
  by
  exact MulEquiv.ofBijective (intersectionMap F i j) ⟨by
    intro x y he
    have he' : (⟨x, x.property.1⟩ : F.localGroup i) = ⟨y, y.property.1⟩ :=
      F.projection_injective i (congrArg Subtype.val he)
    exact Subtype.ext (congrArg (fun z : F.localGroup i => (z : F.completion)) he'), by
    intro x
    let a : S.family i := ⟨x, x.property.1⟩
    let b : S.family j := ⟨x, x.property.2⟩
    have he : F.lift i a = F.lift j b := by
      apply Subtype.ext
      exact Prod.ext rfl (F.compatible i j a b rfl)
    refine ⟨⟨F.lift i a, ⟨⟨a, rfl⟩, ⟨b, he.symm⟩⟩⟩, ?_⟩
    rfl⟩

theorem generated : F.localGroup 0 ⊔ F.localGroup 1 = ⊤ := by
  apply Subgroup.map_injective F.completion.subtype_injective
  rw [Subgroup.map_sup, ← MonoidHom.range_comp, ← MonoidHom.range_comp]
  change (F.graphMap 0).range ⊔ (F.graphMap 1).range = (⊤ : Subgroup F.completion).map _
  rw [← MonoidHom.range_eq_map, range_subtype]
  rfl

private theorem core_transport {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hc : centralizer (pCore 2 B : Set B) = pCore 2 B) :
    centralizer (pCore 2 A : Set A) = pCore 2 A := by
  have he (x : A) : e x ∈ pCore 2 B ↔ x ∈ pCore 2 A := by
    rw [← pCore_map_iso 2 e, mem_map_equiv]
    simp only [MulEquiv.symm_apply_apply]
  ext x
  constructor
  · intro hx
    apply (he x).mp
    rw [← hc]
    intro y hy
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg e (hx y ((he y).mp hy))
  · intro hx y hy
    have hx' : e x ∈ centralizer (pCore 2 B : Set B) := hc.symm ▸ (he x).mpr hx
    apply e.injective
    rw [map_mul, map_mul]
    exact hx' (e y) ((he y).mpr hy)

def source : SourceData F.completion where
  H1 := F.localGroup 0
  H2 := F.localGroup 1
  H3 := F.localGroup 2
  generated := F.generated
  action := S.action
  pointEquiv := (F.localEquiv 0).trans S.pointEquiv
  pairEquiv := (F.localEquiv 1).trans S.pairEquiv
  triangleEquiv := (F.localEquiv 2).trans S.triangleEquiv
  core_centralizer := by exact core_transport (F.localEquiv 0) S.core_centralizer
  overlap12 := (F.intersectionEquiv 0 1).trans S.overlap12
  overlap13 := (F.intersectionEquiv 0 2).trans S.overlap13
  overlap23 := (F.intersectionEquiv 1 2).trans S.overlap23

theorem projection_surjective : Function.Surjective F.projection := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← S.generated]
  apply sup_le
  · intro x hx
    exact ⟨F.lift 0 ⟨x, hx⟩, rfl⟩
  · intro x hx
    exact ⟨F.lift 1 ⟨x, hx⟩, rfl⟩

theorem projection_bijective : Function.Bijective F.projection := by
  let : Finite F.completion := Nat.finite_of_card_ne_zero (by rw [F.source.group_card]; decide)
  exact F.projection_surjective.bijective_of_nat_card_le (by
    rw [S.group_card, F.source.group_card])

def extension : G →* K :=
  ((MonoidHom.snd G K).comp F.completion.subtype).comp
    (MulEquiv.ofBijective F.projection F.projection_bijective).symm.toMonoidHom

theorem extension_apply (i : Fin 3) (x : S.family i) : F.extension x = F.map i x := by
  have he : (MulEquiv.ofBijective F.projection F.projection_bijective).symm x = F.lift i x := by
    apply (MulEquiv.ofBijective F.projection F.projection_bijective).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  change ((MulEquiv.ofBijective F.projection F.projection_bijective).symm x).val.2 = _
  rw [he]
  rfl

theorem existsUnique_extension :
    ∃! f : G →* K, ∀ (i : Fin 3) (x : S.family i), f x = F.map i x := by
  refine ⟨F.extension, F.extension_apply, ?_⟩
  intro f hf
  have he : S.H1 ⊔ S.H2 ≤ f.eqLocus F.extension := by
    apply sup_le
    · intro x hx
      exact (hf 0 ⟨x, hx⟩).trans (F.extension_apply 0 ⟨x, hx⟩).symm
    · intro x hx
      exact (hf 1 ⟨x, hx⟩).trans (F.extension_apply 1 ⟨x, hx⟩).symm
  ext x
  exact he (S.generated ▸ mem_top x)

end CompatibleMaps

namespace SourceData
variable {G : Type*} [Group G] (S : SourceData G)

/-- Corollary 2.8: every faithful completion has the order and universal mapping property. -/
theorem corollary_2_8 {K : Type*} [Group K] (F : CompatibleMaps S K) :
    Nat.card G = 8160 ∧
      ∃! f : G →* K, ∀ (i : Fin 3) (x : S.family i), f x = F.map i x :=
  ⟨S.group_card, F.existsUnique_extension⟩

end SourceData
end Sporadic.Janko3.SourceRecognition.Seventeen
