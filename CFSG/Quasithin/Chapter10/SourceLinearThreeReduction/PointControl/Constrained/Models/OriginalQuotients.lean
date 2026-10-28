module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.Placement
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.ComponentModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryIntrinsicQuotients
public import Theory.SpecificGroups.Classical.BinaryLinearThreeRank

/-!
# Original quotients recovered from the containing local component

The smaller image in the literal VI action preserves L/O₂(L). In each
rank-two Lie-type containing model its parabolic placement identifies that
quotient with SL₂ over the same field. For SL₄(2) and SL₅(2), intrinsic local
quotient classification gives SL_m(2); the original odd-prime rank bound
forces m = 3. All equivalences use the actual local image and two-core.
These facts remove the group-quotient recognition premises from the source
model analysis; action markings remain with the final constrained owner.

Source: Aschbacher--Smith 10.2.9, printed p.751, cases (a) and (c).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterA.Section03
open ChapterA.Section03.SourceEmbeddings.FiveLocalFF

private theorem linear_three_local_quotient
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n)
    (S : Sylow 2 SL(3,F)) (B : Subgroup SL(3,F))
    (hl : B ∈ localCComponents S) (hp : B ≠ ⊤) :
    Nonempty ((B ⧸ pCore 2 B) ≃* SL(2,F)) := by
  obtain ⟨g,hg⟩ := special_linear_three_local_placement hF hn S B hl hp
  let a := (MulAut.conj g).subgroupMap B
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  apply Nonempty.map (fun e => aq.trans e)
  change Nonempty (((B.map (MulAut.conj g).toMonoidHom) ⧸
    pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F))
  rcases hg with hp | hp
  · rw [hp]
    exact ⟨Matrix.PSL3.LinearThree.pointLocalSLCoreQuotientEquiv F⟩
  · rw [hp]
    exact ⟨Matrix.PSL3.LinearThree.lineLocalSLCoreQuotientEquiv F⟩

private theorem symplectic_four_local_quotient
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n)
    (S : Sylow 2 (Matrix.symplecticGroup (Fin 2) F))
    (B : Subgroup (Matrix.symplecticGroup (Fin 2) F))
    (hl : B ∈ localCComponents S) (hp : B ≠ ⊤) :
    Nonempty ((B ⧸ pCore 2 B) ≃* SL(2,F)) := by
  obtain ⟨g,hg⟩ := symplectic_local_placement hF hn S B hl hp
  let a := (MulAut.conj g).subgroupMap B
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  apply Nonempty.map (fun e => aq.trans e)
  change Nonempty (((B.map (MulAut.conj g).toMonoidHom) ⧸
    pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F))
  rcases hg with hp | hp
  · rw [hp]
    exact ⟨Theory.SpecificGroups.SymplecticFour.pointLocalCoreQuotientEquiv hF hn⟩
  · rw [hp]
    exact ⟨Theory.SpecificGroups.SymplecticFour.planeLocalCoreQuotientEquiv hF hn⟩

private theorem g2_local_quotient
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (S : Sylow 2 (Atlas.G2.Model F)) (B : Subgroup (Atlas.G2.Model F))
    (hl : B ∈ localCComponents S) (hp : B ≠ ⊤) :
    Nonempty ((B ⧸ pCore 2 B) ≃* SL(2,F)) := by
  obtain ⟨g,hg⟩ := G2.local_placement hF S B hl hp
  let a := (MulAut.conj g).subgroupMap B
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  apply Nonempty.map (fun e => aq.trans e)
  change Nonempty (((B.map (MulAut.conj g).toMonoidHom) ⧸
    pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F))
  rcases hg with hp | hp
  · rw [hp]
    exact ⟨(QuotientGroup.quotientMulEquivOfEq Atlas.G2.LieParabolicSetup.local₁_intrinsic_pCore).trans
      Atlas.G2.LieParabolicSetup.local₁RadicalQuotientEquivSL⟩
  · rw [hp]
    exact ⟨(QuotientGroup.quotientMulEquivOfEq Atlas.G2.LieParabolicSetup.local₂_pCore).trans
      Atlas.G2.LieParabolicSetup.local₂RadicalQuotientEquivSL⟩

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The smaller local image retains the original two-core quotient. -/
theorem Context.small_local_quotient (c : Context D t v I) (a : ActionFacts c) :
    letI := c.reduced.normal
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    let B := ((L.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))).subgroupOf A
    Nonempty ((B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L)) := by
  let H := pointJoin T v I
  let U := internalModule D v I
  let := c.reduced.normal
  let q := actionMk U
  let A := (I.subgroupOf H).map q
  let B₀ := (L.subgroupOf H).map q
  let B := B₀.subgroupOf A
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    fun h => c.escaping.t_not_normalizes (h c.escaping.t_mem)
  let := D.quasisimple
  let : IsSimpleGroup (L ⧸ pCore 2 L) := Selection.ModuleChoice.component_quotient_simple D hn
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    rcases (inferInstance : (center (L ⧸ pCore 2 L)).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative (L ⧸ pCore 2 L) (center_eq_top_iff.mp h)).elim
  obtain ⟨_,⟨e₀⟩⟩ := c.small_image_twoCore a hz
  have hBA : B₀ ≤ A := map_mono (comap_mono c.escaping.strict.le)
  let b : B ≃* B₀ := subgroupOfEquivOfLe hBA
  exact ⟨(QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans e₀⟩

private theorem local_quotient_of_equiv
    {A M J : Type*} [Group A] [Finite A] [Group M] [Group J]
    (E : A ≃* M) (S : Sylow 2 A) (B : Subgroup A)
    (hl : B ∈ localCComponents S) (hp : B ≠ ⊤)
    (h : ∀ (S : Sylow 2 M) (B : Subgroup M), B ∈ localCComponents S → B ≠ ⊤ →
      Nonempty ((B ⧸ pCore 2 B) ≃* J)) : Nonempty ((B ⧸ pCore 2 B) ≃* J) := by
  let : Group.IsSolvable E.toMonoidHom.ker := by
    rw [E.toMonoidHom.ker_eq_bot_iff.mpr E.injective]
    exact Group.isSolvable_of_comm (fun _ _ => Subsingleton.elim _ _)
  have hl' := Chapter1.Section02.localCComponents_map_of_solvable_ker
    (G := A) (G' := M) (B := B) (S := (S : Subgroup A)) hl E.toMonoidHom

  have hp' : B.map E.toMonoidHom ≠ ⊤ := by
    intro he
    exact hp (map_injective E.injective (he.trans (map_top_of_surjective _ E.surjective).symm))
  obtain ⟨e⟩ := h (S.mapSurjective (f := E.toMonoidHom) E.surjective) _ hl' hp'
  let b := E.subgroupMap B
  exact ⟨(QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans e⟩

private theorem original_quotient_of_local_model (c : Context D t v I) (a : ActionFacts c)
    {M J : Type*} [Group M] [Group J] :
    letI := c.reduced.normal
    ∀ (_E : ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))) ≃* M),
      (∀ (S : Sylow 2 M) (B : Subgroup M), B ∈ localCComponents S → B ≠ ⊤ →
        Nonempty ((B ⧸ pCore 2 B) ≃* J)) → Nonempty ((L ⧸ pCore 2 L) ≃* J) := by
  let := c.reduced.normal
  intro E h
  obtain ⟨e⟩ := c.small_local_quotient a
  obtain ⟨hp,R,_,hl⟩ := a.small_local
  obtain ⟨b⟩ := local_quotient_of_equiv E
    (R.mapSurjective ((actionMk (internalModule D v I)).subgroupMap_surjective
      (I.subgroupOf (pointJoin T v I)))) _ hl hp.ne h
  exact ⟨e.symm.trans b⟩

/-- A containing SL₃ action recovers the original rank-one quotient over the same field. -/
theorem Context.rank_one_quotient_of_linear_three (c : Context D t v I) (a : ActionFacts c)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n) :
    letI := c.reduced.normal
    ∀ (_E : ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))) ≃* SL(3,F)),
      Nonempty ((L ⧸ pCore 2 L) ≃* SL(2,F)) := by
  let := c.reduced.normal
  intro E
  exact original_quotient_of_local_model c a E (linear_three_local_quotient hF hn)

/-- The symplectic containing action has the same original rank-one quotient. -/
theorem Context.rank_one_quotient_of_symplectic_four (c : Context D t v I) (a : ActionFacts c)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n) :
    letI := c.reduced.normal
    ∀ (_E : ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))) ≃*
      Matrix.symplecticGroup (Fin 2) F), Nonempty ((L ⧸ pCore 2 L) ≃* SL(2,F)) := by
  let := c.reduced.normal
  intro E
  exact original_quotient_of_local_model c a E (symplectic_four_local_quotient hF hn)

/-- The G₂ containing action recovers the original rank-one quotient. -/
theorem Context.rank_one_quotient_of_g2 (c : Context D t v I) (a : ActionFacts c)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F) :
    letI := c.reduced.normal
    ∀ (_E : ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))) ≃*
      Atlas.G2.Model F), Nonempty ((L ⧸ pCore 2 L) ≃* SL(2,F)) := by
  let := c.reduced.normal
  intro E
  exact original_quotient_of_local_model c a E (g2_local_quotient hF)

private theorem binary_three_quotient_of_local
    {A : Type*} [Group A] [Finite A] {d : ℕ} (hd : d ≤ 5)
    (E : A ≃* SL(d,ZMod 2)) (S : Sylow 2 A) (B : Subgroup A)
    (hlocal : B ∈ localCComponents S) (hr : primeRank 3 (B ⧸ pCore 2 B) ≤ 1) :
    Nonempty ((B ⧸ pCore 2 B) ≃* SL(3,ZMod 2)) := by
  let f := E.trans (_root_.BinaryLinear.OuterCyclic.slEquivLinear d)
  let C := B.map f.toMonoidHom
  let bC : B ≃* C := B.equivMapOfInjective f.toMonoidHom f.injective
  let : Group.IsSolvable f.toMonoidHom.ker := by
    rw [f.toMonoidHom.ker_eq_bot_iff.mpr f.injective]
    exact Group.isSolvable_of_comm (fun _ _ => Subsingleton.elim _ _)
  have hC := Chapter1.Section02.localCComponents_map_of_solvable_ker
    (G := A) (G' := _root_.BinaryLinear.OuterCyclic.LinearGroup d)
    (B := B) (S := (S : Subgroup A)) hlocal f.toMonoidHom

  obtain ⟨m,hm,hmn,⟨eC⟩⟩ := SourceEmbeddings.BinaryIntrinsic.local_twoCore_quotient d
    hd (S.mapSurjective (f := f.toMonoidHom) f.surjective) C hC
  let e : (B ⧸ pCore 2 B) ≃* SL(m,ZMod 2) :=
    ((QuotientGroup.congr _ _ bC (pCore_map_iso 2 bC)).trans eC).trans
      (_root_.BinaryLinear.OuterCyclic.slEquivLinear m).symm
  have hm3 : m = 3 := by
    by_contra hm3
    have hfour : 4 ≤ m := by omega
    have hlow := Theory.SpecificGroups.Classical.BinaryLinearThreeRank.two_le_primeRank hfour
    rw [← primeRank_equiv 3 e] at hlow
    omega
  subst m
  exact ⟨e⟩


/-- A binary containing actor of degree four or five forces the original SL₃(2) quotient. -/
theorem Context.binary_three_quotient_of_binary_containing (c : Context D t v I)
    (a : ActionFacts c) {d : ℕ} (hd : d = 4 ∨ d = 5)
    : letI := c.reduced.normal
      ∀ (_E : ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))) ≃*
        SL(d,ZMod 2)), Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) := by
  let H := pointJoin T v I
  let U := internalModule D v I
  let := c.reduced.normal
  intro E
  let q := actionMk U
  let A := (I.subgroupOf H).map q
  let B := ((L.subgroupOf H).map q).subgroupOf A
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    fun h => c.escaping.t_not_normalizes (h c.escaping.t_mem)
  obtain ⟨eB⟩ := c.small_local_quotient a
  obtain ⟨_,R,_,hlocal⟩ := a.small_local
  let S := R.mapSurjective (q.subgroupMap_surjective (I.subgroupOf H))
  have hr : primeRank 3 (B ⧸ pCore 2 B) ≤ 1 := by
    rw [primeRank_equiv 3 eB]
    exact Selection.ModuleChoice.component_quotient_odd_rank_le_one D hn 3
      Nat.prime_three (by decide)
  obtain ⟨e⟩ := binary_three_quotient_of_local (by omega) E S B hlocal hr
  exact ⟨eB.symm.trans e⟩


end CFSG.Quasithin.Chapter10.PointControl.Constrained
