module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.SeedFrame
public import Theory.GroupTheory.PerfectSimpleImageOrder
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary

/-!
# Equality of the original seed with the marked parabolic local

The original seed has the same simple two-core quotient as the marked local.
The simple-section order argument forces its projection onto that local
quotient to be surjective. The full inner Sylow normalizes the seed and
contains the local two-core, so the seed is normal in the local. The local
is perfect and its quotient by the seed is a two-group; hence they are equal.
The same marking then identifies the entire seed normalizer with the parabolic.

All six local choices in SL₃, Sp₄ and G₂ are retained, including the SL₃
covering center. Classification.lean applies this equality to the literal
chosen flag without an extra seed-identification premise. Inner radical
placement, strict omega-center containment and final 11.4.2 assembly remain
with qt-d-1222-shadow-component-comparison; earlier-source discharge remains
with qt-d-1222-shadow-components.
Source: Aschbacher--Smith 11.4.2, printed p.777. The imported G₂ calculations
retain LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.SeedFrame

private theorem seed_eq_local {G : Type*} [Group G] [Finite G]
    (B P L : Subgroup G) [Group.IsPerfect B] [Nontrivial B] [Group.IsPerfect L]
    [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hBL : B ≤ L) (hPL : P ≤ normalizer (L : Set G))
    (S : Sylow 2 G) (hSP : (S : Subgroup G) ≤ P)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L)) : B = L := by
  let q := QuotientGroup.mk' (pCore 2 B)
  let f := e.symm.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 L)).comp (inclusion hBL))
  let : Group.IsSolvable q.ker := by
    change Group.IsSolvable (QuotientGroup.mk' (pCore 2 B)).ker
    rw [QuotientGroup.ker_mk']
    let := (pCore_isPGroup (p := 2) (G := B)).isNilpotent
    infer_instance
  have hsur : Function.Surjective f := by
    rcases hom_eq_one_or_surjective_of_simple_quotient q (QuotientGroup.mk'_surjective _) f with hz | hs
    · have hbq : B ≤ L.pCoreIn 2 := by
        intro b hb
        have hh := DFunLike.congr_fun hz (⟨b,hb⟩ : B)
        have hh' : QuotientGroup.mk' (pCore 2 L) (inclusion hBL ⟨b,hb⟩) = 1 :=
          e.symm.injective (by simpa only [f,MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.one_apply, map_one] using hh)
        exact ⟨inclusion hBL ⟨b,hb⟩,(QuotientGroup.eq_one_iff _).mp hh',rfl⟩
      let := ((isPGroup_pCoreIn 2 L).to_le hbq).isNilpotent
      exact (Group.IsPerfect.not_isSolvable B inferInstance).elim
    · exact hs
  have hQB : L.pCoreIn 2 ≤ normalizer (B : Set G) :=
    ((isPGroup_pCoreIn 2 L).le_sylow_of_normalized S
      (hSP.trans (hPL.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))))).trans hSB
  have hLB : L ≤ normalizer (B : Set G) := by
    intro l hl
    obtain ⟨b,hb⟩ := hsur (e.symm (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩))
    have hbl : QuotientGroup.mk' (pCore 2 L) (inclusion hBL b) =
        QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩ := e.symm.injective hb
    have hk : (inclusion hBL b)⁻¹ * (⟨l,hl⟩ : L) ∈ pCore 2 L := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (pCore 2 L) _ = 1
      rw [map_mul,map_inv,hbl,inv_mul_cancel]
    have hn := (normalizer (B : Set G)).mul_mem (B.le_normalizer b.property)
      (hQB (show (b : G)⁻¹ * l ∈ L.pCoreIn 2 from ⟨_,hk,rfl⟩))
    simpa only [mul_inv_cancel_left] using hn
  let B' := B.subgroupOf L
  let : B'.Normal := (normal_subgroupOf_iff_le_normalizer hBL).mpr hLB
  have hgen : B' ⊔ pCore 2 L = ⊤ := by
    apply top_unique
    intro l _
    obtain ⟨b,hb⟩ := hsur (e.symm (QuotientGroup.mk' (pCore 2 L) l))
    have hbl : QuotientGroup.mk' (pCore 2 L) (inclusion hBL b) =
        QuotientGroup.mk' (pCore 2 L) l := e.symm.injective hb
    have hk : (inclusion hBL b)⁻¹ * l ∈ pCore 2 L := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (pCore 2 L) _ = 1
      rw [map_mul,map_inv,hbl,inv_mul_cancel]
    have hm := (B' ⊔ pCore 2 L).mul_mem
      (mem_sup_left (show inclusion hBL b ∈ B' from b.property)) (mem_sup_right hk)
    simpa only [mul_inv_cancel_left] using hm
  let := (isPGroup_quotient_of_sup_eq_top B' (pCore 2 L) pCore_isPGroup hgen).isNilpotent
  have ht : B' = ⊤ := top_unique (le_of_isPerfect_of_solvable_quotient (⊤ : Subgroup L) B')
  exact le_antisymm hBL (subgroupOf_eq_top.mp ht)

open Classification
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- A single component marking identifies both the entire seed and its
normalizer with the corresponding local and full parabolic. -/
def FullParabolicFrame : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ E.input.field.degree ∧
    ((∃ e : componentImage E ≃* SL(3,F),
      ((normalizer (innerSeed E : Set (componentImage E))).map e.toMonoidHom =
          Matrix.PSL3.LinearThree.pointParabolicSL F ∧
        (innerSeed E).map e.toMonoidHom = Matrix.PSL3.LinearThree.pointLocalSL F) ∨
      ((normalizer (innerSeed E : Set (componentImage E))).map e.toMonoidHom =
          Matrix.PSL3.LinearThree.lineParabolicSL F ∧
        (innerSeed E).map e.toMonoidHom = Matrix.PSL3.LinearThree.lineLocalSL F)) ∨
    (∃ e : componentImage E ≃* Theory.SpecificGroups.SymplecticFour.Sp F,
      ((normalizer (innerSeed E : Set (componentImage E))).map e.toMonoidHom =
          Theory.SpecificGroups.SymplecticFour.pointParabolic ∧
        (innerSeed E).map e.toMonoidHom = Theory.SpecificGroups.SymplecticFour.pointLocal) ∨
      ((normalizer (innerSeed E : Set (componentImage E))).map e.toMonoidHom =
          Theory.SpecificGroups.SymplecticFour.planeParabolic ∧
        (innerSeed E).map e.toMonoidHom = Theory.SpecificGroups.SymplecticFour.planeLocal)) ∨
    (∃ e : componentImage E ≃* Atlas.G2.Model F,
      ((normalizer (innerSeed E : Set (componentImage E))).map e.toMonoidHom =
          Atlas.G2.LieParabolicSetup.parabolic₁ ∧
        (innerSeed E).map e.toMonoidHom = Atlas.G2.LieParabolicSetup.local₁) ∨
      ((normalizer (innerSeed E : Set (componentImage E))).map e.toMonoidHom =
          Atlas.G2.LieParabolicSetup.parabolic₂ ∧
        (innerSeed E).map e.toMonoidHom = Atlas.G2.LieParabolicSetup.local₂)))

private theorem marked_seed_eq_local
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (e₁ : (E.L₁ ⧸ pCore 2 E.L₁) ≃* PSL(2,E.input.field.Carrier))
    (hT : (T : Subgroup G) ≤ E.G₁)
    {M : Type*} [Group M] [Finite M] (a : componentImage E ≃* M)
    (P J : Subgroup M) [Group.IsPerfect J]
    (hN : (normalizer (innerSeed E : Set (componentImage E))).map a.toMonoidHom ≤ P)
    (hB : (innerSeed E).map a.toMonoidHom ≤ J)
    (hres : (solvableResidual P).map P.subtype = J)
    (ej : (J ⧸ pCore 2 J) ≃* PSL(2,E.input.field.Carrier)) :
    (normalizer (innerSeed E : Set (componentImage E))).map a.toMonoidHom = P ∧
      (innerSeed E).map a.toMonoidHom = J := by
  let B := (innerSeed E).map a.toMonoidHom
  let es : B ≃* seed E := (a.subgroupMap (innerSeed E)).symm.trans
    (subgroupOfEquivOfLe (AlternatingSeven.seedImage_le_componentImage E))
  let eb := (QuotientGroup.congr _ _ es (pCore_map_iso 2 es)).trans
    (seedQuotientEquiv E h hf hne hstar hcent e₁)
  obtain ⟨hp,hn⟩ := seed_perfect_nontrivial E h hf hne hstar hcent e₁
  let := hp
  let := hn
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := es.symm.toMonoidHom) es.symm.surjective
  let : Nontrivial B := es.toEquiv.nontrivial
  have hlarge : 3 < Nat.card E.input.field.Carrier := by
    rw [E.input.field.card_eq]
    have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) E.input.nonbinary
    omega
  let : IsSimpleGroup PSL(2,E.input.field.Carrier) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := eb.isSimpleGroup
  obtain ⟨S,hS⟩ := exists_inner_sylow E h hT
  have hnB : (S : Subgroup (componentImage E)).map a.toMonoidHom ≤ normalizer (B : Set M) := by
    rw [←map_equiv_normalizer_eq]
    exact map_mono hS
  have hPJ : P ≤ normalizer (J : Set M) := by
    rw [←hres]
    exact P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (solvableResidual P))
  have he : B = J := seed_eq_local B P J hB hPJ
    (S.mapSurjective (f := a.toMonoidHom) a.surjective)
    ((map_mono hS).trans hN) hnB (eb.trans ej.symm)
  refine ⟨le_antisymm hN ?_,he⟩
  rw [map_equiv_normalizer_eq]
  change P ≤ normalizer (B : Set M)
  rwa [he]

/-- The original seed is the full marked local, and its normalizer is the full
parabolic, in each of the three surviving image rows. -/
theorem full_parabolic_frame (h : EarlierGeometry E)
    (hf : V ⊓ centralizer (L : Set G) = ⊥) (hne : E.Kz ≠ E.K)
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (e₁ : (E.L₁ ⧸ pCore 2 E.L₁) ≃* PSL(2,E.input.field.Carrier))
    (hT : (T : Subgroup G) ≤ E.G₁) (hm : RankTwoModel E) : FullParabolicFrame E := by
  obtain ⟨F,_,_,hF,hframe⟩ := parabolic_frame E h hf hne hstar hcent e₁ hT hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let : Fintype F := Fintype.ofFinite F
  let : Fintype E.input.field.Carrier := Fintype.ofFinite E.input.field.Carrier
  let ef : F ≃+* E.input.field.Carrier := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card] using hF.trans E.input.field.card_eq.symm)
  let ep := Atlas.fieldEquivPSL 2 ef
  let el := Atlas.RankOneFieldAutomorphisms.slEquivPSL.trans ep
  have hlarge : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) E.input.nonbinary
  refine ⟨F,inferInstance,inferInstance,hF,?_⟩
  rcases hframe with ⟨a,ha⟩ | ⟨a,ha⟩ | ⟨a,ha⟩
  · left
    refine ⟨a,?_⟩
    rcases ha with ⟨hN,hB⟩ | ⟨hN,hB⟩
    · let := Matrix.PSL3.LinearThree.pointLocalSL_isPerfect F hlarge
      exact Or.inl (marked_seed_eq_local E h hf hne hstar hcent e₁ hT a _ _ hN hB
        (Matrix.PSL3.LinearThree.pointParabolicSL_residual F hlarge)
        ((Matrix.PSL3.LinearThree.pointLocalSLCoreQuotientEquiv F).trans el))
    · let := Matrix.PSL3.LinearThree.lineLocalSL_isPerfect F hlarge
      exact Or.inr (marked_seed_eq_local E h hf hne hstar hcent e₁ hT a _ _ hN hB
        (Matrix.PSL3.LinearThree.lineParabolicSL_residual F hlarge)
        ((Matrix.PSL3.LinearThree.lineLocalSLCoreQuotientEquiv F).trans el))
  · right; left
    refine ⟨a,?_⟩
    rcases ha with ⟨hN,hB⟩ | ⟨hN,hB⟩
    · let := Theory.SpecificGroups.SymplecticFour.pointLocal_perfect hF E.input.nonbinary
      exact Or.inl (marked_seed_eq_local E h hf hne hstar hcent e₁ hT a _ _ hN hB
        (Theory.SpecificGroups.SymplecticFour.pointParabolic_solvableResidual_eq hF E.input.nonbinary)
        ((Theory.SpecificGroups.SymplecticFour.pointLocalCoreQuotientEquiv hF E.input.nonbinary).trans el))
    · let := Theory.SpecificGroups.SymplecticFour.planeLocal_perfect hF E.input.nonbinary
      exact Or.inr (marked_seed_eq_local E h hf hne hstar hcent e₁ hT a _ _ hN hB
        (Theory.SpecificGroups.SymplecticFour.planeParabolic_solvableResidual_eq hF E.input.nonbinary)
        ((Theory.SpecificGroups.SymplecticFour.planeLocalCoreQuotientEquiv hF E.input.nonbinary).trans el))
  · right; right
    refine ⟨a,?_⟩
    rcases ha with ⟨hN,hB⟩ | ⟨hN,hB⟩
    · let := Atlas.G2.LieParabolicSetup.local₁_isPerfect (F := F) (by omega)
      exact Or.inl (marked_seed_eq_local E h hf hne hstar hcent e₁ hT a _ _ hN hB
        (Atlas.G2.HigherFieldResiduals.parabolic₁_residual (by omega))
        (Atlas.G2.LieParabolicSetup.local₁CoreQuotientEquivPSL.trans ep))
    · let := Atlas.G2.LieParabolicSetup.local₂_isPerfect (F := F) (by omega)
      exact Or.inr (marked_seed_eq_local E h hf hne hstar hcent e₁ hT a _ _ hN hB
        (Atlas.G2.HigherFieldResiduals.parabolic₂_residual (by omega))
        (Atlas.G2.LieParabolicSetup.local₂CoreQuotientEquivPSL.trans ep))

/-- The symplectic row retains its specified model and field while identifying
both the whole seed and its full normalizer in one conjugate marking. -/
theorem sp4_full_parabolic_frame (h : EarlierGeometry E)
    (hf : V ⊓ centralizer (L : Set G) = ⊥) (hne : E.Kz ≠ E.K)
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (e₁ : (E.L₁ ⧸ pCore 2 E.L₁) ≃* PSL(2,E.input.field.Carrier))
    (hT : (T : Subgroup G) ≤ E.G₁)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2^E.input.field.degree)
    (e : componentImage E ≃* Theory.SpecificGroups.SymplecticFour.Sp F) :
    ∃ a : componentImage E ≃* Theory.SpecificGroups.SymplecticFour.Sp F,
      ((normalizer (innerSeed E : Set (componentImage E))).map a.toMonoidHom =
          Theory.SpecificGroups.SymplecticFour.pointParabolic ∧
        (innerSeed E).map a.toMonoidHom = Theory.SpecificGroups.SymplecticFour.pointLocal) ∨
      ((normalizer (innerSeed E : Set (componentImage E))).map a.toMonoidHom =
          Theory.SpecificGroups.SymplecticFour.planeParabolic ∧
        (innerSeed E).map a.toMonoidHom = Theory.SpecificGroups.SymplecticFour.planeLocal) := by
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (show 2^1 < 2^E.input.field.degree from
      Nat.pow_lt_pow_right (by decide) E.input.nonbinary)
  obtain ⟨g,hg⟩ := sp4_seed_normalizer_parabolic E h hf hne hstar hcent e₁ hT hlarge e
  let a := e.trans (MulAut.conj g)
  obtain ⟨hp,_⟩ := seed_perfect_nontrivial E h hf hne hstar hcent e₁
  let := hp
  let ei := subgroupOfEquivOfLe (AlternatingSeven.seedImage_le_componentImage E)
  let : Group.IsPerfect (innerSeed E) := Group.IsPerfect.ofSurjective
    (f := ei.symm.toMonoidHom) ei.symm.surjective
  let : Group.IsPerfect ((innerSeed E).map a.toMonoidHom) := Group.IsPerfect.map _
  let : Fintype F := Fintype.ofFinite F
  let : Fintype E.input.field.Carrier := Fintype.ofFinite E.input.field.Carrier
  let ef : F ≃+* E.input.field.Carrier := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card] using hF.trans E.input.field.card_eq.symm)
  let el := Atlas.RankOneFieldAutomorphisms.slEquivPSL.trans (Atlas.fieldEquivPSL 2 ef)
  refine ⟨a,?_⟩
  rcases hg with hg | hg
  · let := Theory.SpecificGroups.SymplecticFour.pointLocal_perfect hF E.input.nonbinary
    have hres := Theory.SpecificGroups.SymplecticFour.pointParabolic_solvableResidual_eq hF E.input.nonbinary
    have hB := le_map_solvableResidual_of_isPerfect ((innerSeed E).map a.toMonoidHom) _
      ((map_mono (f := a.toMonoidHom) (innerSeed E).le_normalizer).trans hg)
    exact Or.inl (marked_seed_eq_local E h hf hne hstar hcent e₁ hT a _ _ hg (hres ▸ hB) hres
      ((Theory.SpecificGroups.SymplecticFour.pointLocalCoreQuotientEquiv hF E.input.nonbinary).trans el))
  · let := Theory.SpecificGroups.SymplecticFour.planeLocal_perfect hF E.input.nonbinary
    have hres := Theory.SpecificGroups.SymplecticFour.planeParabolic_solvableResidual_eq hF E.input.nonbinary
    have hB := le_map_solvableResidual_of_isPerfect ((innerSeed E).map a.toMonoidHom) _
      ((map_mono (f := a.toMonoidHom) (innerSeed E).le_normalizer).trans hg)
    exact Or.inr (marked_seed_eq_local E h hf hne hstar hcent e₁ hT a _ _ hg (hres ▸ hB) hres
      ((Theory.SpecificGroups.SymplecticFour.planeLocalCoreQuotientEquiv hF E.input.nonbinary).trans el))

/-- The special linear row retains its specified model and field while identifying
both the whole seed and its full normalizer in one conjugate marking. -/
theorem sl3_full_parabolic_frame (h : EarlierGeometry E)
    (hf : V ⊓ centralizer (L : Set G) = ⊥) (hne : E.Kz ≠ E.K)
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (e₁ : (E.L₁ ⧸ pCore 2 E.L₁) ≃* PSL(2,E.input.field.Carrier))
    (hT : (T : Subgroup G) ≤ E.G₁)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2^E.input.field.degree)
    (e : componentImage E ≃* SL(3,F)) :
    ∃ a : componentImage E ≃* SL(3,F),
      ((normalizer (innerSeed E : Set (componentImage E))).map a.toMonoidHom =
          Matrix.PSL3.LinearThree.pointParabolicSL F ∧
        (innerSeed E).map a.toMonoidHom = Matrix.PSL3.LinearThree.pointLocalSL F) ∨
      ((normalizer (innerSeed E : Set (componentImage E))).map a.toMonoidHom =
          Matrix.PSL3.LinearThree.lineParabolicSL F ∧
        (innerSeed E).map a.toMonoidHom = Matrix.PSL3.LinearThree.lineLocalSL F) := by
  have hlarge : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) E.input.nonbinary
  obtain ⟨a,hg⟩ := sl3_seed_normalizer_parabolic E h hf hne hstar hcent e₁ hT hF e
  obtain ⟨hp,_⟩ := seed_perfect_nontrivial E h hf hne hstar hcent e₁
  let := hp
  let ei := subgroupOfEquivOfLe (AlternatingSeven.seedImage_le_componentImage E)
  let : Group.IsPerfect (innerSeed E) := Group.IsPerfect.ofSurjective
    (f := ei.symm.toMonoidHom) ei.symm.surjective
  let : Group.IsPerfect ((innerSeed E).map a.toMonoidHom) := Group.IsPerfect.map _
  let : Fintype F := Fintype.ofFinite F
  let : Fintype E.input.field.Carrier := Fintype.ofFinite E.input.field.Carrier
  let ef : F ≃+* E.input.field.Carrier := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card] using hF.trans E.input.field.card_eq.symm)
  let el := Atlas.RankOneFieldAutomorphisms.slEquivPSL.trans (Atlas.fieldEquivPSL 2 ef)
  refine ⟨a,?_⟩
  rcases hg with hg | hg
  · let := Matrix.PSL3.LinearThree.pointLocalSL_isPerfect F hlarge
    have hres := Matrix.PSL3.LinearThree.pointParabolicSL_residual F hlarge
    have hB := le_map_solvableResidual_of_isPerfect ((innerSeed E).map a.toMonoidHom) _
      ((map_mono (f := a.toMonoidHom) (innerSeed E).le_normalizer).trans hg)
    exact Or.inl (marked_seed_eq_local E h hf hne hstar hcent e₁ hT a _ _ hg (hres ▸ hB) hres
      ((Matrix.PSL3.LinearThree.pointLocalSLCoreQuotientEquiv F).trans el))
  · let := Matrix.PSL3.LinearThree.lineLocalSL_isPerfect F hlarge
    have hres := Matrix.PSL3.LinearThree.lineParabolicSL_residual F hlarge
    have hB := le_map_solvableResidual_of_isPerfect ((innerSeed E).map a.toMonoidHom) _
      ((map_mono (f := a.toMonoidHom) (innerSeed E).le_normalizer).trans hg)
    exact Or.inr (marked_seed_eq_local E h hf hne hstar hcent e₁ hT a _ _ hg (hres ▸ hB) hres
      ((Matrix.PSL3.LinearThree.lineLocalSLCoreQuotientEquiv F).trans el))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.SeedFrame
