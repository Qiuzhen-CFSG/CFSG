module
public import Theory.SpecificGroups.SL2.TwoCoreBorel
public import Theory.SpecificGroups.SL2.PairSylowSolvability

/-!
# Multiplicative coordinates on a binary SL₂ pair Borel

The two factor diagonal characters on a Sylow normalizer have the product
Sylow as common kernel. Pulling them through a surjection whose kernel lies
in the original Sylow preserves this kernel description. Restriction to an
odd subgroup is injective, since an odd subgroup intersects a two-group
trivially.

This supplies the torus coordinates before the field-factor elimination in
Aschbacher--Smith, 10.2.3, printed p.745. It does not identify the centralizer
of the omega-center with the norm-one subtorus.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem exists_pair_sylowNormalizer_diagonal
    (S : Sylow 2 (SL(2,F) × SL(2,F))) :
    ∃ d : normalizer (S : Set (SL(2,F) × SL(2,F))) →* Fˣ × Fˣ,
      ∀ x, d x = 1 ↔ (x : SL(2,F) × SL(2,F)) ∈ S := by
  let f := MonoidHom.fst SL(2,F) SL(2,F)
  let g := MonoidHom.snd SL(2,F) SL(2,F)
  let S1 := S.mapSurjective (f := f) (fun x => ⟨(x,1),rfl⟩)
  let S2 := S.mapSurjective (f := g) (fun x => ⟨(1,x),rfl⟩)
  have hp : IsPGroup 2 ((S1 : Subgroup SL(2,F)).prod (S2 : Subgroup SL(2,F))) := by
    obtain ⟨m,hm⟩ := S1.isPGroup'.exists_card_eq
    obtain ⟨n,hn⟩ := S2.isPGroup'.exists_card_eq
    apply IsPGroup.of_card (n := m+n)
    rw [Nat.card_congr (prodEquiv (S1 : Subgroup SL(2,F)) (S2 : Subgroup SL(2,F))).toEquiv,
      Nat.card_prod,hm,hn,pow_add]
  have he : (S1 : Subgroup SL(2,F)).prod (S2 : Subgroup SL(2,F)) = (S : Subgroup (SL(2,F) × SL(2,F))) :=
    S.is_maximal' hp (by
      intro x hx
      exact ⟨mem_map_of_mem f hx,mem_map_of_mem g hx⟩)
  obtain ⟨d1,_,h1⟩ := exists_sylowNormalizer_diagonal (MonoidHom.id SL(2,F))
    Function.surjective_id S1 (by simp)
  obtain ⟨d2,_,h2⟩ := exists_sylowNormalizer_diagonal (MonoidHom.id SL(2,F))
    Function.surjective_id S2 (by simp)
  let N := normalizer (S : Set (SL(2,F) × SL(2,F)))
  let N1 := normalizer (S1 : Set SL(2,F))
  let N2 := normalizer (S2 : Set SL(2,F))
  have hf : N.map f ≤ N1 := le_normalizer_map f
  have hg : N.map g ≤ N2 := le_normalizer_map g
  let f1 : N →* N1 := (f.comp N.subtype).codRestrict N1
    (fun x => hf (mem_map_of_mem f x.property))
  let f2 : N →* N2 := (g.comp N.subtype).codRestrict N2
    (fun x => hg (mem_map_of_mem g x.property))
  refine ⟨(d1.comp f1).prod (d2.comp f2),?_⟩
  intro x
  change (d1 (f1 x),d2 (f2 x)) = (1,1) ↔ _
  rw [Prod.mk.injEq,h1,h2]
  change (x : SL(2,F) × SL(2,F)) ∈ (S1 : Subgroup SL(2,F)).prod (S2 : Subgroup SL(2,F)) ↔
    (x : SL(2,F) × SL(2,F)) ∈ (S : Subgroup (SL(2,F) × SL(2,F)))
  rw [he]

variable {A : Type*} [Group A] [Finite A]
theorem exists_pair_sylowNormalizer_diagonal_of_two_kernel
    (q : A →* SL(2,F) × SL(2,F)) (hq : Function.Surjective q)
    (P : Sylow 2 A) (hk : q.ker ≤ (P : Subgroup A)) :
    ∃ d : normalizer (P : Set A) →* Fˣ × Fˣ,
      ∀ x, d x = 1 ↔ (x : A) ∈ P := by
  let S := P.mapSurjective hq
  obtain ⟨d,hd⟩ := exists_pair_sylowNormalizer_diagonal S
  let N := normalizer (P : Set A)
  let Nq := normalizer (S : Set (SL(2,F) × SL(2,F)))
  have hN : N.map q ≤ Nq := le_normalizer_map q
  let f : N →* Nq := (q.comp N.subtype).codRestrict Nq
    (fun x => hN (mem_map_of_mem q x.property))
  refine ⟨d.comp f,?_⟩
  intro x
  change d (f x) = 1 ↔ _
  rw [hd]
  change (x : A) ∈ ((P : Subgroup A).map q).comap q ↔ _
  rw [comap_map_eq_self hk]
  rfl

theorem exists_odd_subgroup_pair_sylowNormalizer_embedding
    (q : A →* SL(2,F) × SL(2,F)) (hq : Function.Surjective q)
    (P : Sylow 2 A) (hk : q.ker ≤ (P : Subgroup A))
    (C : Subgroup A) (hC : C ≤ normalizer (P : Set A))
    (ho : Odd (Nat.card C)) :
    ∃ d : C →* Fˣ × Fˣ, Function.Injective d := by
  obtain ⟨d,hd⟩ := exists_pair_sylowNormalizer_diagonal_of_two_kernel q hq P hk
  let i : C →* normalizer (P : Set A) := inclusion hC
  refine ⟨d.comp i,?_⟩
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨n,hn⟩ := P.isPGroup'.exists_card_eq
  have hdis : Disjoint (P : Subgroup A) C := disjoint_of_coprime_natCard (by
    rw [hn]
    exact (Nat.coprime_two_left.mpr ho).pow_left n)
  apply Subtype.ext
  exact disjoint_def.mp hdis ((hd (i x)).mp hx) x.property

end Matrix.SpecialLinearGroup
