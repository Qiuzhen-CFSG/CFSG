module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Parabolic

/-!
# The original cubic residual retains unique maximality

A cubic image and a kernel inside the two-core/Frattini preimage give a
unique maximal overgroup of each Sylow two-subgroup. Apply this to the
original two-residual, inside its join with the original Baumann subgroup.
The latter join is normal in the full minimal parabolic; this preserves the
subnormality needed by the fixed-pair block consumer.

The action centralizer is allowed its original odd Frattini kernel.
Source: Aschbacher--Smith B.6.8 and C.1.26--28, printed pp.114--117,132--134.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.Single
open ChapterB
variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]

omit [Finite Q] in
private theorem two_group_eq_bot_of_card_three
    (hQ : Nat.card Q = 3) (A : Subgroup Q) (hA : IsPGroup 2 A) : A = ⊥ := by
  apply le_bot_iff.mp
  intro a ha
  have hc := hA.orderOf_coprime (by decide : Nat.Coprime 2 3) (⟨a,ha⟩ : A)
  have hd : orderOf (⟨a,ha⟩ : A) ∣ 3 := by
    rw [←Subgroup.orderOf_coe]
    simpa only [hQ] using orderOf_dvd_natCard a
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hc dvd_rfl hd))

/-- Unique maximality through the actual cubic residual action, with its
full two-core/Frattini kernel. -/
theorem cubic_unique_of_coreFrattini_kernel
    (f : G →* Q) (hf : Function.Surjective f) (hQ : Nat.card Q = 3)
    (hk : f.ker ≤ (frattini (G ⧸ pCore 2 G)).comap (QuotientGroup.mk' (pCore 2 G)))
    (S : Sylow 2 G) : Order.HasUniqueMaximalOver (S : Subgroup G) ⊤ := by
  have hc : pCore 2 G ≤ f.ker := (Subgroup.map_eq_bot_iff _).mp
    (two_group_eq_bot_of_card_three hQ _ (pCore_isPGroup.map f))
  let q := QuotientGroup.mk' (pCore 2 G)
  let g := QuotientGroup.lift (pCore 2 G) f hc
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x,rfl⟩ := hf y
    exact ⟨q x,rfl⟩
  have hgk : g.ker ≤ frattini (G ⧸ pCore 2 G) := by
    intro x hx
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 G) x
    exact hk hx
  let Sq := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G))
  have he : (Sq : Subgroup (G ⧸ pCore 2 G)).map g = ⊥ :=
    two_group_eq_bot_of_card_three hQ _ (Sq.isPGroup'.map g)
  have hu : Order.HasUniqueMaximalOver ((Sq : Subgroup (G ⧸ pCore 2 G)).map g) ⊤ := by
    rw [he]
    let : Fact (Nat.card Q).Prime := ⟨hQ ▸ Nat.prime_three⟩
    let : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    have hb : IsCoatom (⊥ : Subgroup Q) := by
      refine ⟨bot_ne_top,fun M hM => ?_⟩
      exact M.eq_bot_or_eq_top_of_prime_card.resolve_left hM.ne'
    refine ⟨hb.lt_top,⊥,⟨le_rfl,hb.covBy_top⟩,?_⟩
    intro M hM
    exact M.eq_bot_or_eq_top_of_prime_card.resolve_right hM.2.ne
  have hh := hasUniqueMaximalOver_of_frattini_kernel g hg hgk hu
  apply hasUniqueMaximalOver_of_surjective q (QuotientGroup.mk'_surjective _) ?_ hh
  rw [QuotientGroup.ker_mk']
  exact pCore_isPGroup.le_sylow_of_normal S

/-- The selected group is the whole normal residual--Baumann join. Its
Sylow is the original Baumann subgroup, and its maximality is derived from
the cubic image of the original residual. -/
theorem selected_baumann_unique_of_cubic_residual
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* Q) (hk : q.ker = centralizer (U : Set G))
    (hc : Nat.card ((pResidual 2 G).map q) = 3)
    (hs : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      (pResidual 2 G ⊔ baumann (T : Subgroup G))) :
    ∃ S : Sylow 2 (pResidual 2 G ⊔ baumann (T : Subgroup G) : Subgroup G),
      (S : Subgroup (pResidual 2 G ⊔ baumann (T : Subgroup G) : Subgroup G)).map (pResidual 2 G ⊔ baumann (T : Subgroup G)).subtype =
        baumann (T : Subgroup G) ∧ Order.HasUniqueMaximalOver (S : Subgroup (pResidual 2 G ⊔ baumann (T : Subgroup G) : Subgroup G)) ⊤ := by
  let X := pResidual 2 G
  let B := baumann (T : Subgroup G)
  let N := X ⊔ B
  let A := X.subgroupOf N
  let i : A ≃* X := subgroupOfEquivOfLe (show X ≤ N from le_sup_left)
  let f : A →* X.map q := (q.subgroupMap X).comp i.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective X).comp i.surjective
  have hfr := RankOneBaumann.residual_centralizer_le_coreFrattini T hP U hU hJ
  have hfker : f.ker ≤ (frattini (A ⧸ pCore 2 A)).comap (QuotientGroup.mk' (pCore 2 A)) := by
    have hik : IsPGroup 2 i.toMonoidHom.ker := by
      rw [(MonoidHom.ker_eq_bot_iff i.toMonoidHom).mpr i.injective]
      exact IsPGroup.of_subsingleton 2 _
    rw [←i.toMonoidHom.comap_frattini_pCore_of_pKernel i.surjective hik]
    intro a ha
    have hqa : q (i a : G) = 1 := congrArg Subtype.val ha
    have hca : (i a : G) ∈ centralizer (U : Set G) := hk ▸ hqa
    obtain ⟨x,hx,he⟩ := hfr ⟨(i a).property,hca⟩
    change i a ∈ (frattini (X ⧸ pCore 2 X)).comap (QuotientGroup.mk' (pCore 2 X))
    exact (show x = i a from Subtype.ext he) ▸ hx
  obtain ⟨S,hS⟩ := hs
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal A
  have hu := cubic_unique_of_coreFrattini_kernel f hf hc hfker R
  have huA := hasUniqueMaximalOver_map_subtype hu
  rw [hR,subgroupOf_map_subtype,inf_comm] at huA
  have huN := hasUniqueMaximalOver_sup_of_normalizes
    (show (S : Subgroup N) ≤ normalizer (A : Set N) from le_normalizer_of_normal) huA
  have hgen : A ⊔ (S : Subgroup N) = ⊤ := by
    apply map_injective N.subtype_injective
    rw [Subgroup.map_sup,hS,map_subgroupOf_eq_of_le (show X ≤ N from le_sup_left),
      ←MonoidHom.range_eq_map,range_subtype]
  rw [hgen] at huN
  exact ⟨S,hS,huN⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.Single
