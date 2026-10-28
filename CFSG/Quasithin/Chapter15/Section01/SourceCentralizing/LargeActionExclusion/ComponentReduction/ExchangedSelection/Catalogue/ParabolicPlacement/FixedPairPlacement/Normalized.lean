module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.FixedPairPlacement.Closure
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.FixedPairPlacement.MovingBlock
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.CubicResidual
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.MaximalSylow
public import Theory.GroupTheory.WreathTwoCoreQuotient
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Same-pair placement when the Sylow subgroup normalizes the component

Here the literal source quotient is the quotient of P₀=⟨P,S⟩ itself.
It makes P₀ minimal parabolic. An actual A₃ block in P₀ would generate
its two-residual through its Sylow orbit; pulling the commuting factors
back to P contradicts the source exclusion. Thus the one universal
characteristic pair has a central or normal alternative for every P,
which places P in M ∩ L or M_L.

This proves the normalizing branch of (*), not the branch where S
permutes components. Neither p=3 nor p=5 is singled out.
Source: Aschbacher--Smith, 15.1.22(*), printed pp.1098--1099.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterB ChapterC.GlaubermanNiles ChapterC.RankOne.ChiProduct
open Section03 Section03.InitialSource ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem minimal_of_small_core_quotient
    (R : Sylow 2 G)
    (he : Nonempty ((G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty ((G ⧸ pCore 2 G) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))) :
    IsMinimalParabolicOver R ⊤ := by
  rcases he with he | he
  · obtain ⟨e⟩ := he
    have hi := SymmetricThreeTwoCore.sylow_index_three e R
    have hmax : IsCoatom (R : Subgroup G) := by
      refine ⟨?_,?_⟩
      · intro h
        simp [h] at hi
      · intro U hU
        have hd : U.index ∣ 3 := (Subgroup.index_dvd_of_le hU.le).trans (dvd_of_eq hi)
        rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd with h | h
        · exact Subgroup.index_eq_one.mp h
        · have hmul := Subgroup.relIndex_mul_index hU.le
          rw [hi,h] at hmul
          exact (hU.not_ge (Subgroup.relIndex_eq_one.mp (by omega))).elim
    apply isMinimalParabolicOver_of_sylow_isCoatom R hmax
    intro hn
    let := hn
    exact hmax.ne_top ((SymmetricThreeTwoCore.sylow_self_normalizing e R).symm.trans
      (normalizer_eq_top (H := (R : Subgroup G))))
  · obtain ⟨e⟩ := he
    obtain ⟨eSL⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
    let ew := e.trans (RegularWreathProduct.congr eSL.symm
      (MulEquiv.refl (Multiplicative (ZMod 2))))
    exact isMinimalParabolicOver_of_sylow_isCoatom R
      (WreathTwoResidual.sylow_isCoatom_of_core_quotient R ew)
      (WreathTwoResidual.sylow_not_normal_of_core_quotient R ew)

theorem IsSourceParabolic.closure_minimal_of_sylow_normalizes
    {d : CaseIComponentData T M Mc V} {P : Subgroup G} (hP : d.IsSourceParabolic P)
    (hn : d.S ≤ normalizer (d.L : Set G))
    (R : Sylow 2 (d.parabolicClosure P)) : IsMinimalParabolicOver R ⊤ := by
  apply minimal_of_small_core_quotient R
  have he : d.sylowNormalizer = d.S := inf_eq_left.mpr hn
  have hq := hP.quotient
  change Nonempty (((P ⊔ d.sylowNormalizer : Subgroup G) ⧸ pCore 2 (P ⊔ d.sylowNormalizer : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∨ Nonempty (((P ⊔ d.sylowNormalizer : Subgroup G) ⧸ pCore 2 (P ⊔ d.sylowNormalizer : Subgroup G)) ≃* RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) at hq
  rw [he] at hq
  exact hq


private theorem residual_product_pullback {H : Type*} [Group H] [Finite H]
    (f : G →* H) (hf : Function.Injective f)
    (F : Set (Subgroup H))
    (hb : ∀ B ∈ F, ChapterC.IsBlock B ∧ ChapterC.IsAlternatingBlock B 3)
    (hc : F.Pairwise (fun B C => ⁅B,C⁆ = ⊥))
    (hgen : sSup F = (pResidual 2 G).map f) :
    ∃ E : Set (Subgroup G),
      (∀ A ∈ E, ChapterC.IsBlock A ∧ ChapterC.IsAlternatingBlock A 3) ∧
      E.Pairwise (fun A B => ⁅A,B⁆ = ⊥) ∧ sSup E = pResidual 2 G := by
  let E := (fun B : Subgroup H => B.comap f) '' F
  have hm (B : Subgroup H) (hB : B ∈ F) : (B.comap f).map f = B :=
    map_comap_eq_self ((le_sSup hB).trans (hgen.le.trans (map_le_range _ _)))
  have ha (B : Subgroup H) (hB : B ∈ F) :
      ChapterC.IsAlternatingBlock (B.comap f) 3 := by
    let e : B.comap f ≃* B :=
      ((B.comap f).equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr (hm B hB))
    exact ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv e.symm (hb B hB).2
  refine ⟨E,?_,?_,?_⟩
  · rintro A ⟨B,hB,rfl⟩
    exact ⟨⟨inferInstance,(ha B hB).2.1,(hb B hB).1.subnormal.comap f⟩,ha B hB⟩
  · rintro A ⟨B,hB,rfl⟩ C ⟨D,hD,rfl⟩ hne
    apply (map_eq_bot_iff_of_injective _ hf).mp
    rw [map_commutator,hm B hB,hm D hD]
    exact hc hB hD (fun he => hne (congrArg (comap f) he))
  · apply (map_injective hf)
    apply le_antisymm
    · apply map_le_iff_le_comap.mpr
      apply sSup_le
      rintro A ⟨B,hB,rfl⟩
      apply map_le_iff_le_comap.mp
      rw [hm B hB,←hgen]
      exact le_sSup hB
    · rw [←hgen]
      apply sSup_le
      intro B hB
      rw [←hm B hB]
      exact map_mono (le_sSup (show B.comap f ∈ E from ⟨B,hB,rfl⟩))


theorem IsSourceParabolic.residual_closure_of_sylow_normalizes
    {d : CaseIComponentData T M Mc V} {P : Subgroup G} (hP : d.IsSourceParabolic P)
    (hL : d.L ∈ Chapter1.L G d.S)
    (hn : d.S ≤ normalizer (d.L : Set G)) :
    (pResidual 2 (d.parabolicClosure P)).map (d.parabolicClosure P).subtype =
      (pResidual 2 P).map P.subtype := by
  let E := (pResidual 2 P).map P.subtype
  have hNS : d.sylowNormalizer = d.S := inf_eq_left.mpr hn
  have hPS : d.S ≤ normalizer (P : Set G) := hNS ▸ hP.normalized
  have hES : d.S ≤ normalizer (E : Set G) :=
    hPS.trans (normalizer_le_normalizer_characteristic_image P (pResidual 2 P))
  have hgen : E ⊔ d.S = d.parabolicClosure P := by
    have hs := hP.residual_sup_sylow_intersection hL
    rw [←twoResidual_eq_primeToResidual_three hP.twoThree] at hs
    change E ⊔ (d.S ⊓ P) = P at hs
    change E ⊔ d.S = P ⊔ d.S
    calc
      E ⊔ d.S = (E ⊔ (d.S ⊓ P)) ⊔ d.S := by
        rw [sup_assoc, sup_eq_right.mpr (show d.S ⊓ P ≤ d.S from inf_le_left)]
      _ = P ⊔ d.S := congrArg (· ⊔ d.S) hs
  rw [←hgen]
  exact embedded_pResidual_join_pGroup E d.S
    ((isPPerfect_pResidual 2).of_surjective
      ((pResidual 2 P).equivMapOfInjective P.subtype P.subtype_injective).toMonoidHom
      ((pResidual 2 P).equivMapOfInjective P.subtype P.subtype_injective).surjective) (T.isPGroup'.to_le d.S_le_T) hES

theorem PreExclusionSource.no_moving_block_of_sylow_normalizes
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {P : Subgroup G} (hP : d.IsSourceParabolic P)
    (hn : d.S ≤ normalizer (d.L : Set G))
    (R : Sylow 2 (d.parabolicClosure P)) :
    ¬ HasMovingAThreeBlock (d.parabolicClosure P) R := by
  rintro ⟨A,hb,ha,_⟩
  obtain ⟨F,_,hF,hcomm,hgen⟩ := alternatingThree_residual_product
    (s.parabolicClosure_fitting (h := h) hP)
    ((hP.closure_sqtk hG h).stronglyQuasithin 3 Nat.prime_three (by decide))
    R (hP.closure_minimal_of_sylow_normalizes hn R) A hb ha
  have hr := hP.residual_closure_of_sylow_normalizes s.local_component hn
  let f : P →* d.parabolicClosure P := inclusion (show P ≤ d.parabolicClosure P from le_sup_left)
  have he : (pResidual 2 P).map f = pResidual 2 (d.parabolicClosure P) := by
    apply map_injective (d.parabolicClosure P).subtype_injective
    rw [map_map,hr]
    rfl
  exact hP.not_aThree_product
    (residual_product_pullback f (inclusion_injective _) F hF hcomm (hgen.trans he.symm))

/-- The normalizing branch of (*), using one universal characteristic
pair chosen before the parabolic. No fixed-pair escape premise remains. -/
theorem PreExclusionSource.parabolic_placement_of_sylow_normalizes
    {d : CaseIComponentData T M Mc V} {p : ℕ}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (s : d.PreExclusionSource h.normalized p)
    (hnL : d.S ≤ normalizer (d.L : Set G)) :
    ∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML := by
  obtain ⟨D,hD,_⟩ := FixedPair.exists_uniform_pair.{u,u}
    T (MainForward.sylow_ne_bot hG T)
  have hB := (h.caseI_marked_thompson_control hG T hM hJ d.Z1_le_fixed).2.1
  intro P hP
  change d.IsSourceParabolic P at hP
  obtain ⟨R,hR⟩ := s.parabolicClosure_sylow (h := h) hP
  have hi : ParabolicClosureStructure (d.parabolicClosure P) R :=
    ⟨hP.closure_minimal_of_sylow_normalizes hnL R,
      s.parabolicClosure_fitting (h := h) hP,hP.closure_solvable⟩
  by_cases hc : FixedPair.firstSeed R (d.localPair D (d.parabolicClosure P) R hR hB) ≤
      center (d.parabolicClosure P)
  · exact d.placement_of_localPair_alternative hG hM hJ hu h D
      (d.parabolicClosure P) P le_sup_left hP.le_component R hR hB (Or.inl hc)
  by_cases hn : ((d.localPair D (d.parabolicClosure P) R hR hB).second.map
      (baumann (R : Subgroup (d.parabolicClosure P))).subtype).Normal
  · exact d.placement_of_localPair_alternative hG hM hJ hu h D
      (d.parabolicClosure P) P le_sup_left hP.le_component R hR hB (Or.inr hn)
  exact (s.no_moving_block_of_sylow_normalizes (h := h) hG hP hnL R
    (hP.moving_block_of_no_pair_alternative hG h R hR hB D hD hi hc hn)).elim

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
