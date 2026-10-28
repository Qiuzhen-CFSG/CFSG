module
public import Theory.GroupTheory.ExchangedPairSelection
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallCubic
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairSymmetric.NoStrong
public import Theory.Representation.BinaryOffender.ProductSplitting
public import Theory.Representation.NormalComponentConstituents
public import Theory.GroupTheory.SylowNormalIntersection
/-!
# Cubic selection for the paired natural five-action

A sharp offender in the faithful paired natural chief action lies in the
S₅ × S₅ base and splits into its coordinate offenders. The natural S₅ cubic
selection in an active coordinate is transported through the literal marked
pair. Keeping the passive coordinate in the selected rank-two subgroup and
using the source Sylow exchanger yields the exact cubic, normalization,
commutator and generation data needed by the original Thompson selection.

Source: Aschbacher–Smith 3.1.9(5), 15.1.12(4), and E.2.3(3), pp.216–217.
-/
public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource SourceInduction BinaryPermutation
set_option backward.isDefEq.respectTransparency false
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]

private theorem sylow_eq_prod (S : Sylow 2 (D × D)) :
    (S : Subgroup (D × D)) = ((S : Subgroup _).map (MonoidHom.fst D D)).prod
      ((S : Subgroup _).map (MonoidHom.snd D D)) := by
  let S₁ := S.mapSurjective (show Function.Surjective (MonoidHom.fst D D) from fun g => ⟨(g,1),rfl⟩)
  let S₂ := S.mapSurjective (show Function.Surjective (MonoidHom.snd D D) from fun g => ⟨(1,g),rfl⟩)
  change (S : Subgroup _) = (S₁ : Subgroup D).prod (S₂ : Subgroup D)
  apply Eq.symm
  apply S.is_maximal'
  · obtain ⟨a,ha⟩ := S₁.isPGroup'.exists_card_eq
    obtain ⟨b,hb⟩ := S₂.isPGroup'.exists_card_eq
    apply IsPGroup.of_card (n := a+b)
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,Nat.card_prod,ha,hb,pow_add]
  · intro x hx
    exact ⟨mem_map_of_mem _ hx,mem_map_of_mem _ hx⟩

omit [Finite D] in
private theorem map_prod_swap (A B : Subgroup D) :
    (A.prod B).map (MulEquiv.prodComm : D × D ≃* D × D).toMonoidHom = B.prod A := by
  ext x
  exact ⟨by rintro ⟨y,hy,rfl⟩; exact ⟨hy.2,hy.1⟩,
    fun hx => ⟨(x.2,x.1),⟨hx.2,hx.1⟩,rfl⟩⟩

omit [Finite G] [Finite D] in
private theorem selection_of_product_actor
    (j : D × D →* G) (hj : Function.Injective j)
    (S : Subgroup G) (A₁ A₂ : Subgroup D) (P₁ P₂ : Sylow 2 D)
    (hAS : (A₁.prod A₂).map j ≤ S)
    (hPS : ((P₁ : Subgroup D).prod (P₂ : Subgroup D)).map j ≤ S)
    (hbase : j.range ⊔ S = ⊤)
    (hex : ∃ t ∈ S,
      (((⊤ : Subgroup D).prod (⊥ : Subgroup D)).map j).map
        (MulAut.conj t).toMonoidHom = ((⊥ : Subgroup D).prod (⊤ : Subgroup D)).map j ∧
      (((⊥ : Subgroup D).prod (⊤ : Subgroup D)).map j).map
        (MulAut.conj t).toMonoidHom = ((⊤ : Subgroup D).prod (⊥ : Subgroup D)).map j)
    (hgeom : (∃ R L : Subgroup D, R ≤ A₁ ∧ A₁ ≤ normalizer (R : Set D) ∧
      L ≤ normalizer (R : Set D) ∧ A₁ ≤ normalizer (L : Set D) ∧
      R.relIndex A₁ = 2 ∧ L = ⁅L,A₁⁆ ∧ L ⊔ (P₁ : Subgroup D) = ⊤) ∨
      (∃ R L : Subgroup D, R ≤ A₂ ∧ A₂ ≤ normalizer (R : Set D) ∧
      L ≤ normalizer (R : Set D) ∧ A₂ ≤ normalizer (L : Set D) ∧
      R.relIndex A₂ = 2 ∧ L = ⁅L,A₂⁆ ∧ L ⊔ (P₂ : Subgroup D) = ⊤)) :
    ∃ R L : Subgroup G,
      R ≤ S ∧ (A₁.prod A₂).map j ≤ normalizer (R : Set G) ∧
      L ≤ normalizer (R : Set G) ∧
      (A₁.prod A₂).map j ≤ normalizer (L : Set G) ∧
      R.relIndex ((A₁.prod A₂).map j) = 2 ∧
      L = ⁅L,(A₁.prod A₂).map j⁆ ∧ L ⊔ S = ⊤ := by
  rcases hgeom with ⟨R,L,hRA,hAR,hLR,hAL,hidx,hcomm,hgen⟩ | ⟨R,L,hRA,hAR,hLR,hAL,hidx,hcomm,hgen⟩
  · exact exchanged_pair_selection j hj S A₁ A₂ R L P₁ hRA hAS
      ((map_mono (prod_mono le_rfl bot_le)).trans hPS) hAR hLR hAL hidx hcomm hgen
      hbase (by obtain ⟨t,ht,h₁,_⟩ := hex; exact ⟨t,ht,h₁⟩)
  · let s : D × D ≃* D × D := MulEquiv.prodComm
    let k := j.comp s.toMonoidHom
    have hm (A B : Subgroup D) : (A.prod B).map k = (B.prod A).map j := by
      rw [show k = j.comp s.toMonoidHom from rfl,←map_map,map_prod_swap]
    have hkr : k.range = j.range := by
      ext x
      exact ⟨by rintro ⟨a,rfl⟩; exact ⟨s a,rfl⟩,
        by rintro ⟨a,rfl⟩; exact ⟨s.symm a,by simp [k]⟩⟩
    have hexk : ∃ t ∈ S,
        (((⊤ : Subgroup D).prod (⊥ : Subgroup D)).map k).map
          (MulAut.conj t).toMonoidHom = ((⊥ : Subgroup D).prod (⊤ : Subgroup D)).map k := by
      obtain ⟨t,ht,_,h₂⟩ := hex
      exact ⟨t,ht,by rw [hm,hm]; exact h₂⟩
    have hASk : (A₂.prod A₁).map k ≤ S := by rw [hm]; exact hAS
    have hPSk : ((P₂ : Subgroup D).prod (⊥ : Subgroup D)).map k ≤ S := by
      rw [hm]
      exact (map_mono (prod_mono bot_le le_rfl)).trans hPS
    obtain ⟨R',L',hh⟩ := exchanged_pair_selection k (hj.comp s.injective) S A₂ A₁ R L P₂
      hRA hASk hPSk hAR hLR hAL hidx hcomm hgen (by rw [hkr]; exact hbase) hexk
    rw [hm] at hh
    exact ⟨R',L',hh⟩
end CFSG.Quasithin.ChapterB
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource SourceInduction BinaryPermutation
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem paired_five_action_cubic_selection
    (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ]
    (hf : Function.Injective ρ) (T : Sylow 2 G)
    (hP : IsMinimalParabolicOver T ⊤) (hff : IsFFModule ρ)
    (hcore : pCore 2 G = ⊥)
    (d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5)))
    (A : Subgroup G) (hAT : A ≤ (T : Subgroup G)) (hA : IsOffender ρ A) :
    ∃ R L : Subgroup G,
      R ≤ (T : Subgroup G) ∧ A ≤ normalizer (R : Set G) ∧
      L ≤ normalizer (R : Set G) ∧ A ≤ normalizer (L : Set G) ∧
      R.relIndex A = 2 ∧ L = ⁅L,A⁆ ∧ L ⊔ (T : Subgroup G) = ⊤ := by
  let Y := offenderSubgroup ρ
  let := offenderSubgroup_normal ρ
  let e := c.action.groupEquiv
  let j := Y.subtype.comp e.symm.toMonoidHom
  have hj : Function.Injective j := Y.subtype_injective.comp e.symm.injective
  have hstrong := c.symmetric_not_strong ρ d
  have hbest := (isBestOffender_iff_of_not_strong ρ hstrong A).mpr
    ⟨hA.1,le_antisymm hA.2 (Nat.le_of_not_gt (fun h => hstrong ⟨A,hA.1,h⟩))⟩
  have hAY : A ≤ Y := hbest.le_offenderSubgroup ρ
  let B := (A.subgroupOf Y).map e.toMonoidHom
  have hBmap : B.map j = A := by
    rw [show B = (A.subgroupOf Y).map e.toMonoidHom from rfl,map_map]
    have he : j.comp e.toMonoidHom = Y.subtype := by ext x; simp [j]
    rw [he,map_subgroupOf_eq_of_le hAY]
  let : Nontrivial Y := e.symm.injective.nontrivial
  have hfix : Representation.invariants (ρ.comp Y.subtype) = ⊥ :=
    fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf inferInstance Y
      (Y.nontrivial_iff_ne_bot.mp inferInstance)
  have hfi : Function.Injective c.quotientMap :=
    LinearMap.ker_eq_bot.mp (c.quotientMap_ker.trans hfix)
  let f := LinearEquiv.ofBijective c.quotientMap ⟨hfi,c.quotientMap_surjective⟩
  let τ := naturalRepresentation (Fin 5)
  let π := Representation.prod
    (τ.comp (MonoidHom.fst (Equiv.Perm (Fin 5)) (Equiv.Perm (Fin 5))))
    (τ.comp (MonoidHom.snd (Equiv.Perm (Fin 5)) (Equiv.Perm (Fin 5))))
  have hB : IsOffender π B :=
    ((hbest.subgroupOf ρ hAY).isOffender _).map_equivariant _ _ e.toMonoidHom e.injective f
      c.quotientMap_action
  have hnostrong : ¬ IsStrongFFModule τ := by
    rintro ⟨B,hB⟩
    exact Offenders.Odd.not_isStrongOffender_natural (Or.inl rfl) B hB
  obtain ⟨hsplit,h₁,h₂⟩ := offender_product_of_not_strong τ τ hnostrong hnostrong hB
  let A₁ := B.map (MonoidHom.fst _ _)
  let A₂ := B.map (MonoidHom.snd _ _)
  have hAprod : (A₁.prod A₂).map j = A := by rw [←hsplit]; exact hBmap
  obtain ⟨U,hU⟩ := T.exists_subgroupOf_eq_of_normal Y
  let P := U.mapSurjective (f := e.toMonoidHom) e.surjective
  let P₁ := P.mapSurjective (f := MonoidHom.fst _ _) (fun g => ⟨(g,1),rfl⟩)
  let P₂ := P.mapSurjective (f := MonoidHom.snd _ _) (fun g => ⟨(1,g),rfl⟩)
  have hBP : B ≤ (P : Subgroup _) := by
    apply map_mono
    rw [hU]
    exact fun x hx => hAT hx
  have hA₁P : A₁ ≤ (P₁ : Subgroup _) := map_mono hBP
  have hA₂P : A₂ ≤ (P₂ : Subgroup _) := map_mono hBP
  have hPS : ((P₁ : Subgroup _).prod (P₂ : Subgroup _)).map j ≤ (T : Subgroup G) := by
    have hp : (P : Subgroup (Equiv.Perm (Fin 5) × Equiv.Perm (Fin 5))) =
        (P₁ : Subgroup (Equiv.Perm (Fin 5))).prod (P₂ : Subgroup (Equiv.Perm (Fin 5))) :=
      sylow_eq_prod P
    rw [←hp]
    change ((U : Subgroup Y).map e.toMonoidHom).map j ≤ _
    rw [map_map]
    have he : j.comp e.toMonoidHom = Y.subtype := by ext x; simp [j]
    rw [he,hU,subgroupOf_map_subtype]
    exact inf_le_left
  have hbase : j.range ⊔ (T : Subgroup G) = ⊤ := by
    have hjrange : j.range = Y := by
      ext x
      constructor
      · rintro ⟨y,rfl⟩
        exact (e.symm y).property
      · intro hx
        refine ⟨e ⟨x,hx⟩,?_⟩
        simp [j]
    rw [hjrange]
    exact (offender_generation T hP ρ hff hcore).2
  have hmfirst : ((⊤ : Subgroup (Equiv.Perm (Fin 5))).prod ⊥).map j = d.first.map Y.subtype := by
    rw [show j = Y.subtype.comp e.symm.toMonoidHom from rfl,←map_map,c.first_eq]
  have hmsecond : ((⊥ : Subgroup (Equiv.Perm (Fin 5))).prod ⊤).map j = d.second.map Y.subtype := by
    rw [show j = Y.subtype.comp e.symm.toMonoidHom from rfl,←map_map,c.second_eq]
  have hex : ∃ t ∈ (T : Subgroup G),
      (((⊤ : Subgroup (Equiv.Perm (Fin 5))).prod ⊥).map j).map
        (MulAut.conj t).toMonoidHom = ((⊥ : Subgroup _).prod ⊤).map j ∧
      (((⊥ : Subgroup (Equiv.Perm (Fin 5))).prod ⊤).map j).map
        (MulAut.conj t).toMonoidHom = ((⊤ : Subgroup _).prod ⊥).map j := by
    obtain ⟨t,ht₁,ht₂⟩ := source_offender_two_factor_exists_sylow_exchange ρ T hP hff hcore d
    refine ⟨t,t.property,?_,?_⟩
    · rw [hmfirst,hmsecond,map_map]
      have hc : (MulAut.conj (t:G)).toMonoidHom.comp Y.subtype =
          Y.subtype.comp (MulAut.conjNormal (t:G)).toMonoidHom := by ext x; rfl
      rw [hc,←map_map,ht₁]
    · rw [hmfirst,hmsecond,map_map]
      have hc : (MulAut.conj (t:G)).toMonoidHom.comp Y.subtype =
          Y.subtype.comp (MulAut.conjNormal (t:G)).toMonoidHom := by ext x; rfl
      rw [hc,←map_map,ht₂]
  have hgeom : (∃ R L : Subgroup (Equiv.Perm (Fin 5)), R ≤ A₁ ∧ A₁ ≤ normalizer (R : Set _) ∧
      L ≤ normalizer (R : Set _) ∧ A₁ ≤ normalizer (L : Set _) ∧
      R.relIndex A₁ = 2 ∧ L = ⁅L,A₁⁆ ∧ L ⊔ (P₁ : Subgroup _) = ⊤) ∨
      (∃ R L : Subgroup (Equiv.Perm (Fin 5)), R ≤ A₂ ∧ A₂ ≤ normalizer (R : Set _) ∧
      L ≤ normalizer (R : Set _) ∧ A₂ ≤ normalizer (L : Set _) ∧
      R.relIndex A₂ = 2 ∧ L = ⁅L,A₂⁆ ∧ L ⊔ (P₂ : Subgroup _) = ⊤) := by
    have hselect (P : Sylow 2 (Equiv.Perm (Fin 5))) (C : Subgroup (Equiv.Perm (Fin 5)))
        (hCP : C ≤ (P : Subgroup _)) (hC : IsOffender τ C) :
        ∃ R L : Subgroup (Equiv.Perm (Fin 5)), R ≤ C ∧ C ≤ normalizer (R : Set _) ∧
          L ≤ normalizer (R : Set _) ∧ C ≤ normalizer (L : Set _) ∧
          R.relIndex C = 2 ∧ L = ⁅L,C⁆ ∧ L ⊔ (P : Subgroup _) = ⊤ := by
      let : IsElementaryAbelian 2 C := hC.1.2
      obtain ⟨L,R,_,_,hRC,hidx,hCR,hLR,hCL,hcomm,hgen⟩ :=
        Theory.SpecificGroups.SymmetricFive.CubicSelection.exists_outer_actor_selection P C hCP
          (natural_five_offender_outer C hC)
      exact ⟨R,L,hRC,hCR,hLR.trans (Subgroup.centralizer_le_normalizer _),hCL,hidx,hcomm,hgen⟩
    rcases h₁ with hb₁ | hoff₁
    · rcases h₂ with hb₂ | hoff₂
      · have hzero : B = ⊥ := by rw [hsplit,hb₁,hb₂,bot_prod_bot]
        exact (hB.1.1 hzero).elim
      · exact Or.inr (hselect P₂ A₂ hA₂P hoff₂)
    · exact Or.inl (hselect P₁ A₁ hA₁P hoff₁)
  obtain ⟨R,L,hh⟩ := selection_of_product_actor j hj T A₁ A₂ P₁ P₂
    (by rw [hAprod]; exact hAT) hPS hbase hex hgeom
  rw [hAprod] at hh
  exact ⟨R,L,hh⟩
end CFSG.Quasithin.ChapterB
