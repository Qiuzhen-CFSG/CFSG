module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalElementarySource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.UnitaryFourSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallUnitarySolvability

/-!
# The elementary source profile on the literal reduced pair

The two Chapter 11 linear markings define surjections from O₂(B)Lᵢ to
binary SL₂. Their kernels are exactly the full reduced parabolic two-cores,
via the original graph inclusion. Restricting these maps to O₂(B) makes
both core quotients elementary. The source identity Q_alpha=Z_alpha and
the strictly smaller beta-center order give the remaining core clauses.
The neighbor counts retain the full Borel and the same square-field relation.

Thus (11.7) constructs every field of the existing U₄ recognition profile.
Its application produces a marked reduced amalgam comparison, preserving
both endpoint maps and the whole Borel. Nonsolvable original parabolics
also discharge both enlarged local catalogues. In the unrestricted source
case those catalogues remain inputs. The marked split quotient and rotation
order four remain earlier Chapter 14 inputs; no unconditional recognition
or unrestricted order-144 exclusion is asserted here.

Source: DGS, Groups and Graphs (1985), (11.5)--(11.7), pp.172--175,
Theorem D, p.224, and Fong--Seitz II (8B), pp.201--202. The concrete U₄
presentation and model comparison are reused from UnitaryFourSource.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open CommutingNontrivial NoncommutingProfile Subgroup.CosetGeometry.RankTwo Reduction
open Theory.GroupTheory RankTwoAmalgam OriginalExtension SuzukiContainment
open FongSeitzBinary
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F₀" => reducedFamily L S
local notation "G₀" => Reduction.G₀ L S
local notation "R" => reducedSylow L S
local notation:max "M" b:arg => (Subgroup.map (Subgroup.subtype G₀) (graphLocalGroup F₀ (base F₀ b)))
local notation:max "P" i:arg => parabolic L R i

private theorem source_actor_image (h : HypothesisF11 L S) (b : Bool) :
    M b = R ⊔ L (if b then 1 else 0) := by
  rw [reduced_graphLocalGroup_image h]
  have hi (i : Fin 2) : enlargedEndpoint L S i = R ⊔ L i := by
    change ((parabolic L S i).pCoreIn 2 ⊔ L i) ⊔ R = _
    have hc : (parabolic L S i).pCoreIn 2 ≤ R := parabolic_core_le_reducedSylow h i
    rw [sup_right_comm, sup_eq_right.mpr hc]
  cases b
  · exact hi 0
  · exact hi 1

private theorem source_actor_core (h : HypothesisF11 L S) (b : Bool) :
    (M b).pCoreIn 2 = (P (if b then 1 else 0)).pCoreIn 2 := by
  rw [reduced_graphLocalGroup_image h]
  cases b <;> exact (enlargedEndpoint_core h _).trans (reduced_parabolic_core h _).symm

private theorem source_core_image (h : HypothesisF11 L S) (b : Bool) :
    (Q F₀ (base F₀ b)).map (G₀).subtype = (P (if b then 1 else 0)).pCoreIn 2 :=
  (reduced_base_Q_map h b).trans (reduced_parabolic_core h _).symm

private theorem source_linear_actor (h : HypothesisF11 L S) (b : Bool)
    {k : Type} [Field k] [Finite k] [CharP k 2]
    (e : (M b ⧸ pCore 2 (M b)) ≃* SL(2,k)) :
    ∃ f : (R ⊔ L (if b then 1 else 0)).subgroupOf (P (if b then 1 else 0)) →* SL(2,k),
      Function.Surjective f ∧ f.ker = (pCore 2 (P (if b then 1 else 0))).subgroupOf
        ((R ⊔ L (if b then 1 else 0)).subgroupOf (P (if b then 1 else 0))) := by
  let i : Fin 2 := if b then 1 else 0
  let A := (R ⊔ L i).subgroupOf (P i)
  have hAP : R ⊔ L i ≤ P i := sup_le (le_sup_right.trans le_sup_left) (le_sup_left.trans le_sup_left)
  let a : A ≃* M b := (subgroupOfEquivOfLe hAP).trans
    (MulEquiv.subgroupCongr (source_actor_image h b).symm)
  let f : A →* SL(2,k) := e.toMonoidHom.comp ((QuotientGroup.mk' _).comp a.toMonoidHom)
  refine ⟨f,e.surjective.comp ((QuotientGroup.mk'_surjective _).comp a.surjective),?_⟩
  ext x
  change e (QuotientGroup.mk' _ (a x)) = 1 ↔ x.val ∈ pCore 2 (P i)
  rw [e.map_eq_one_iff]
  change QuotientGroup.mk (a x) = (1 : M b ⧸ pCore 2 (M b)) ↔ x.val ∈ pCore 2 (P i)
  rw [QuotientGroup.eq_one_iff]
  have hx : (a x : G) = x.val.val := rfl
  rw [←mem_map_iff_mem (M b).subtype_injective]
  change (a x : G) ∈ (M b).pCoreIn 2 ↔ _
  rw [hx,source_actor_core h b]
  exact mem_map_iff_mem (P i).subtype_injective

private theorem source_linear_sylow_elementary (b : Bool)
    {k : Type} [Field k] [Finite k] [CharP k 2]
    (f : (R ⊔ L (if b then 1 else 0)).subgroupOf (P (if b then 1 else 0)) →* SL(2,k))
    (hk : f.ker = (pCore 2 (P (if b then 1 else 0))).subgroupOf
      ((R ⊔ L (if b then 1 else 0)).subgroupOf (P (if b then 1 else 0)))) :
    letI := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := R) (if b then 1 else 0)
    IsElementaryAbelian 2 (R ⧸ ((P (if b then 1 else 0)).pCoreIn 2).subgroupOf R) := by
  let i : Fin 2 := if b then 1 else 0
  let := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := R) i
  let A := (R ⊔ L i).subgroupOf (P i)
  let j : R →* A := {
    toFun x := ⟨⟨x.val,(show R ≤ P i from le_sup_right.trans le_sup_left) x.property⟩,
      (show R ≤ R ⊔ L i from le_sup_left) x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let g := f.comp j
  have hg : g.ker = ((P i).pCoreIn 2).subgroupOf R := by
    ext x
    change j x ∈ f.ker ↔ x.val ∈ (P i).pCoreIn 2
    rw [hk]
    change (j x).val ∈ pCore 2 (P i) ↔ ((j x).val : G) ∈ (P i).pCoreIn 2
    exact (mem_map_iff_mem (P i).subtype_injective).symm
  have ht : IsPGroup 2 g.range :=
    (isPGroup_pCoreIn 2 (commonBorel L S)).of_surjective g.rangeRestrict g.rangeRestrict_surjective
  obtain ⟨T,hT⟩ := ht.exists_le_sylow
  let : Fintype k := Fintype.ofFinite k
  obtain ⟨n,_,hn⟩ := FiniteField.card k 2
  have he : ClassicalGroup.IsPSL SL(2,k) 2 (2^(n:ℕ)) :=
    ⟨k,inferInstance,inferInstance,by simpa only [Nat.card_eq_fintype_card] using hn,
      ⟨Atlas.RankOneFieldAutomorphisms.slEquivPSL⟩⟩
  let := linear_model_sylow_elementary he T
  let : IsElementaryAbelian 2 g.range :=
    IsElementaryAbelian.of_injective (inclusion hT) (inclusion_injective _)
  let a := (QuotientGroup.quotientMulEquivOfEq hg.symm).trans (QuotientGroup.quotientKerEquivRange g)
  exact IsElementaryAbelian.of_injective a.toMonoidHom a.injective

private theorem source_neighbor_index (h : HypothesisF11 L S) (b : Bool) :
    Nat.card ((graph F₀).neighborSet (base F₀ b)) =
      (commonBorel L R).relIndex (P (if b then 1 else 0)) := by
  rw [←B₀_eq_source h,←P₀_eq_source h]
  have ht := (reduced_triple h).intersection
  cases b
  · rw [card_neighbor_base]
    change ((P₀ L S 1).subgroupOf G₀).relIndex ((P₀ L S 0).subgroupOf G₀) = _
    rw [←inf_relIndex_right,inf_comm,ht]
    exact relIndex_subgroupOf (show P₀ L S 0 ≤ G₀ from le_sup_left)
  · rw [card_neighbor_base]
    change ((P₀ L S 0).subgroupOf G₀).relIndex ((P₀ L S 1).subgroupOf G₀) = _
    rw [←inf_relIndex_right,ht]
    exact relIndex_subgroupOf (show P₀ L S 1 ≤ G₀ from le_sup_right)


/-- The literal quadratic profile consumed by the U₄ presentation theorem.
The actors, their kernels and both Sylow quotients are constructed on the
reduced pair over the whole original Borel two-core. -/
theorem original_elementary_marked_profile_of_linear
    (h : HypothesisF11 L S)
    (hc : IsCriticalPair F₀ (base F₀ false) (base F₀ true))
    (hb : DGS85.b F₀ = 1)
    (hcomm : ⁅Z F₀ (base F₀ false),Z F₀ (base F₀ true)⁆ = ⊥)
    {kₐ kᵦ : Type} [Field kₐ] [Finite kₐ] [CharP kₐ 2]
    [Field kᵦ] [Finite kᵦ] [CharP kᵦ 2]
    {m : ℕ} (hm : 0 < m) (hka : Nat.card kₐ = 2^(2*m)) (hkb : Nat.card kᵦ = 2^m)
    (ea : (M false ⧸ pCore 2 (M false)) ≃* SL(2,kₐ))
    (eb : (M true ⧸ pCore 2 (M true)) ≃* SL(2,kᵦ)) :
    Nonempty (Assembly.UnitaryFourSource.Profile L R kₐ kᵦ false) := by
  have ma : ClassicalGroup.IsPSL (M false ⧸ pCore 2 (M false)) 2 (2^(2*m)) :=
    ⟨kₐ,inferInstance,inferInstance,hka,⟨ea.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL⟩⟩
  have mb : ClassicalGroup.IsPSL (M true ⧸ pCore 2 (M true)) 2 (2^m) :=
    ⟨kᵦ,inferInstance,inferInstance,hkb,⟨eb.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL⟩⟩
  let d := reducedFullEarlierLocalTheorems h
  obtain ⟨_,hQa,hZb,hca,hcb,_⟩ := original_reduced_linear_linear_profile h d hc hb hcomm
    (2*m) m (by omega) hm ma mb
  have hcent := (original_linear_beta_span_and_center h hc hb hcomm
    (.linear (2*m) (by omega) ma) hm mb).2
  have hcore0 : (Q F₀ (base F₀ false)).map (G₀).subtype = (P 0).pCoreIn 2 := source_core_image h false
  have hcore1 : (Q F₀ (base F₀ true)).map (G₀).subtype = (P 1).pCoreIn 2 := source_core_image h true
  have hlarge : IsElementaryAbelian 2 ((P 0).pCoreIn 2) := by
    rw [←hcore0,hQa]
    let : IsElementaryAbelian 2 (Z F₀ (base F₀ false)) :=
      source_center_elementary (reduced_triple h) (base F₀ false)
    exact IsElementaryAbelian.map (G₀).subtype
  have hnon : ⁅(P 1).pCoreIn 2,(P 1).pCoreIn 2⁆ ≠ ⊥ := by
    rw [←hcore1]
    intro he
    have hself := commutator_eq_bot_iff_le_centralizer.mp he
    have hcz : centerIn ((Q F₀ (base F₀ true)).map (G₀).subtype) =
        (Q F₀ (base F₀ true)).map (G₀).subtype := by
      exact inf_eq_left.mpr hself
    have heq := hcent.symm.trans hcz
    have hn := congrArg (fun H : Subgroup G => Nat.card H) heq
    rw [hZb,hcb] at hn
    have hq : 1 < (2:ℕ)^(2*m) := one_lt_pow₀ (by decide) (by omega)
    have hp : 0 < (2:ℕ)^m := pow_pos (by decide) _
    have hlt := Nat.mul_lt_mul_of_pos_right (one_lt_pow₀ hq (by decide : 2 ≠ 0)) hp
    rw [one_mul] at hlt
    omega
  obtain ⟨fa,hfa,hfka⟩ := source_linear_actor h false ea
  obtain ⟨fb,hfb,hfkb⟩ := source_linear_actor h true eb
  refine ⟨{
    largeActor := fa
    smallActor := fb
    large_surjective := hfa
    small_surjective := hfb
    large_kernel := hfka
    small_kernel := hfkb
    fields := ?_
    large_index := ?_
    small_index := ?_
    large_core_elementary := hlarge
    large_sylow_elementary := source_linear_sylow_elementary false fa hfka
    small_sylow_elementary := source_linear_sylow_elementary true fb hfkb
    small_core_nonabelian := hnon }⟩
  · rw [hka,hkb,←pow_mul,Nat.mul_comm m 2]
  · have hv := original_reduced_linear_neighbor_cards h d (n := 2*m) (by omega) hm ma mb (base F₀ false)
    change Nat.card ((graph F₀).neighborSet (base F₀ false)) = 2^(2*m)+1 at hv
    rw [←hka] at hv
    exact (source_neighbor_index h false).symm.trans hv
  · have hv := original_reduced_linear_neighbor_cards h d (n := 2*m) (by omega) hm ma mb (base F₀ true)
    change Nat.card ((graph F₀).neighborSet (base F₀ true)) = 2^m+1 at hv
    rw [←hkb] at hv
    exact (source_neighbor_index h true).symm.trans hv


variable (h : HypothesisF11 L S)
    (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) (base (reducedFamily L S) true))
    (hb : DGS85.b (reducedFamily L S) = 1)
    (hcomm : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),Z (reducedFamily L S) (base (reducedFamily L S) true)⁆ = ⊥)
    (Ma : IsRankOneModel ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) false)).map (Reduction.G₀ L S).subtype ⧸
      pCore 2 ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) false)).map (Reduction.G₀ L S).subtype)))
    (Mb : IsRankOneModel ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map (Reduction.G₀ L S).subtype ⧸
      pCore 2 ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map (Reduction.G₀ L S).subtype)))
    (helem : letI := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := reducedSylow L S) 1
      IsElementaryAbelian 2 (reducedSylow L S ⧸
        ((parabolic L (reducedSylow L S) 1).pCoreIn 2).subgroupOf (reducedSylow L S)))
include h hc hb hcomm Ma Mb helem

/-- Source (11.7) constructs the full U₄ recognition profile, including its
actual two actor maps. Neither linear marking nor a profile is an input. -/
theorem original_borel_elementary_marked_profile :
    ∃ m : ℕ, 0 < m ∧
      ∃ (kₐ : Type) (_ : Field kₐ) (_ : Finite kₐ) (_ : CharP kₐ 2)
        (kᵦ : Type) (_ : Field kᵦ) (_ : Finite kᵦ) (_ : CharP kᵦ 2),
        Nat.card kₐ = 2^(2*m) ∧ Nat.card kᵦ = 2^m ∧
          Nonempty (Assembly.UnitaryFourSource.Profile L R kₐ kᵦ false) := by
  have he : ∃ hN : (((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf R).Normal,
      letI := hN
      IsElementaryAbelian 2 (R ⧸ ((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf R) := by
    have hq : (Q F₀ (base F₀ true)).map (G₀).subtype = (P 1).pCoreIn 2 := source_core_image h true
    rw [hq]
    exact ⟨QuadrangleStructure.original_core_normal_in_sylow 1,helem⟩
  obtain ⟨m,hm,mb⟩ := original_borel_elementary_linear_beta h hc hb hcomm Ma Mb he
  have ma := original_linear_beta_alpha_marking h hc hb hcomm Ma hm mb
  obtain ⟨kₐ,hFa,hfina,hka,⟨ea⟩⟩ := ma
  obtain ⟨kᵦ,hFb,hfinb,hkb,⟨eb⟩⟩ := mb
  let : Fintype kₐ := Fintype.ofFinite kₐ
  let : Fintype kᵦ := Fintype.ofFinite kᵦ
  let : CharP kₐ 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hka)
  let : CharP kᵦ 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hkb)
  exact ⟨m,hm,kₐ,hFa,hfina,inferInstance,kᵦ,hFb,hfinb,inferInstance,hka,hkb,
    original_elementary_marked_profile_of_linear h hc hb hcomm hm hka hkb
      (ea.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm)
      (eb.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm)⟩

open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates

/-- The constructed elementary profile feeds the actual marked U₄
recognition theorem. The Chapter 14 quotient, splitness and its rotation
order remain explicit; the entire profile premise has been discharged. -/
theorem original_elementary_reduced_comparison
    {X : Type*} [Group X] {endpoints : Fin 2 → Subgroup X}
    (quot : MarkedQuotient endpoints)
    (e : Iso (reducedAmalgam L S) quot.standardAmalgam)
    (split : SplitData quot.tits) (hrot : rotationOrder quot = 4) :
    ∃ (m : ℕ) (hm : 0 < m), Nonempty (Iso (reducedAmalgam L S)
      (UnitaryFourNative.amalgam m hm false)) := by
  obtain ⟨m,hm,kₐ,hFa,hfina,hcha,kᵦ,hFb,hfinb,hchb,_,hkb,⟨profile⟩⟩ :=
    original_borel_elementary_marked_profile h hc hb hcomm Ma Mb helem
  let : NeZero m := ⟨by omega⟩
  exact ⟨m,hm,⟨Assembly.UnitaryFourSource.reducedComparison h quot e split hrot false profile m hkb⟩⟩


omit Ma Mb in
/-- The actual nonsolvable source parabolics supply both local catalogues,
including exclusion of the order-144 enlargement. The elementary branch
therefore has no additional local-structure or profile premise. -/
theorem original_nonsolvable_elementary_reduced_comparison
    (hns : ∀ i : Fin 2, ¬ Group.IsSolvable (parabolic L S i))
    {X : Type*} [Group X] {endpoints : Fin 2 → Subgroup X}
    (quot : MarkedQuotient endpoints)
    (e : Iso (reducedAmalgam L S) quot.standardAmalgam)
    (split : SplitData quot.tits) (hrot : rotationOrder quot = 4) :
    ∃ (m : ℕ) (hm : 0 < m), Nonempty (Iso (reducedAmalgam L S)
      (UnitaryFourNative.amalgam m hm false)) := by
  have model (b : Bool) : IsRankOneModel (M b ⧸ pCore 2 (M b)) := by
    let a := (graphLocalGroup F₀ (base F₀ b)).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
    exact (reduced_actor_models_of_nonsolvable_parabolics h hns (base F₀ b)).of_equiv
      (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm
  exact original_elementary_reduced_comparison h hc hb hcomm (model false) (model true) helem
    quot e split hrot

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
