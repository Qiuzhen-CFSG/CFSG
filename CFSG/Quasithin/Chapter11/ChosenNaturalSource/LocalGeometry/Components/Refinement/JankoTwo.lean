module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.JankoTwo
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.SecondSmallSporadic
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstFieldFour

/-!
# Both-normalizer exclusion of the Hall--Janko carrier

The literal full-Sylow embedding forces field four. At the first normalizer,
the faithful Cartan cubic is excluded by the actual center, cubic rank and
outer automorphism group. At the second, the full plane has binary dimension
at most six. A nontrivial action of its perfect containing component would
force 25 to divide GL(6,2), since its centerless quasisimple two-core quotient
is J₂. The quotient by an action kernel with full image modulo the two-core
is a two-group and is killed by perfectness. Thus no faithfulness on K or
irreducibility of full V₂ is assumed; C_V(L) remains in the plane.

The literal quotient, Cartan and natural-cover inputs belong to
qt-d-1222-natural-flag-cartan, with final discharge by
qt-d-1222-natural-local-geometry. The relative-components owner retains
the remaining carriers and the field-four triangle.
Source: Aschbacher--Smith 11.1.1--11.1.2 and G.7.1, printed pp.761--765,347,
combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding

private theorem jankoTwo_data {A : Type*} [Group A] [Finite A]
    (e : A ≃* Sporadic.LeechRelated.J2.Carrier) :
    center A = ⊥ ∧ 2 ≤ primeRank 3 A ∧ IsPGroup 2 (MulAut.Outer A) := by
  refine ⟨?_,?_,Sporadic.LeechRelated.J2.outer_isTwoGroup.of_equiv (MulAut.outerCongr e).symm⟩
  · apply _root_.eq_bot_iff.mpr
    intro a ha
    exact e.map_eq_one_iff.mp
      (Sporadic.LeechRelated.J2.ExceptionalParabolics.BlockGeometry.center_eq_bot.le
        ((centerCongr e) ⟨a,ha⟩).property)
  · rw [primeRank_congr 3 e]
    exact Sporadic.LeechRelated.J2.three_rank_ge_two

private theorem no_twentyFive_in_small_GL {d : ℕ} (hd : d ≤ 6) :
    ¬ 25 ∣ Nat.card (GL (Fin d) (ZMod 2)) := by
  interval_cases d <;> rw [Matrix.card_GL_field] <;>
    norm_num [Fin.prod_univ_succ]

private theorem small_action_trivial {A W : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] [IsQuasisimple (A ⧸ pCore 2 A)]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (hz : center (A ⧸ pCore 2 A) = ⊥) (h25 : 25 ∣ Nat.card (A ⧸ pCore 2 A))
    (ρ : Representation (ZMod 2) A W) (hd : Module.finrank (ZMod 2) W ≤ 6)
    (a : A) : ρ a = 1 := by
  let φ := ρ.asGroupHom
  let N := φ.ker
  let q := QuotientGroup.mk' (pCore 2 A)
  let : (N.map q).Normal := (inferInstance : N.Normal).map q (QuotientGroup.mk'_surjective _)
  have hfull : N.map q = ⊤ := by
    rcases IsQuasisimple.normal_le_center_or_eq_top (N.map q) with h | h
    · have hN : N ≤ pCore 2 A := by
        rw [hz] at h
        simpa only [q,MonoidHom.comap_bot,QuotientGroup.ker_mk'] using map_le_iff_le_comap.mp h
      have hdiv : 25 ∣ Nat.card φ.range := by
        have hi := h25.trans (index_dvd_of_le hN)
        simpa only [N,index_ker] using hi
      let R := φ.range
      let : Finite R := Finite.of_surjective _ φ.rangeRestrict_surjective
      let σ : Representation (ZMod 2) R W :=
        { toFun r := r.val.val
          map_one' := rfl
          map_mul' _ _ := rfl }
      have hf : Function.Injective σ := Units.val_injective.comp Subtype.val_injective
      exact (no_twentyFive_in_small_GL hd
        (hdiv.trans (Representation.card_dvd_card_GL_of_injective σ hf))).elim
    · exact h
  have hs : N ⊔ pCore 2 A = ⊤ := by
    have he := congrArg (comap q) hfull
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using he
  let : Group.IsNilpotent (A ⧸ N) :=
    (isPGroup_quotient_of_sup_eq_top N (pCore 2 A) pCore_isPGroup hs).isNilpotent
  have hN : N = ⊤ := top_unique (by simpa only [solvableResidual_eq_top] using
    solvableResidual_le_of_solvable_quotient N)
  have ha : a ∈ N := hN ▸ mem_top a
  exact congrArg Units.val ha

variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The first-normalizer J₂ row is excluded by the literal faithful Cartan
factor, with field four derived from the actual embedding. -/
theorem first_not_jankoTwo
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.J2.Carrier) := by
  intro hmodel
  have hn := flag_jankoTwo_parameters D S f 0 hm hK.1 hLK hmodel
  obtain ⟨hz,hr,ho⟩ := jankoTwo_data hmodel.some
  apply first_component_not_centerless_cubic D S f hm hfix hK hLK
    (inf_le_left.trans (f.cartan_normalizes hu hX 0)) _ hfaith hz hr ho
  exact hXcard.trans (by rw [hn]; decide)

/-- The full natural plane excludes J₂ at the second normalizer. -/
theorem second_not_jankoTwo
    (hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi 1 : Set G)) K)
    (hLK : f.Li 1 ≤ K)
    (π : f.Li 1 →* SL(2,S.field.Carrier)) (hπ : Function.Surjective π)
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hact : ∀ a : f.Li 1, ∀ v,
      p (flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v) =
        specialLinearNatural 2 (π a) (p v))
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G)) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.J2.Carrier) := by
  intro hmodel
  have hn := flag_jankoTwo_parameters D S f 1 hm hK hLK hmodel
  obtain ⟨hz,hr,_⟩ := jankoTwo_data hmodel.some
  let B := K.subgroupOf (normalizer (f.Vi 1 : Set G))
  let e : (B ⧸ pCore 2 B) ≃* (K ⧸ pCore 2 K) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hK.1) (pCore_map_iso 2 _)
  have hrB : 2 ≤ primeRank 3 B := by
    rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 B) pCore_isPGroup,
      primeRank_congr 3 e]
    exact hr
  let := ChapterA.Section03.cComponent_twoCore_quasisimple_of_three_rank
    (S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 1)) hK.2 hrB
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv e
  let : Group.IsPerfect B := hK.2.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hK.1).toMonoidHom) (subgroupOfEquivOfLe hK.1).surjective
  have h25 : 25 ∣ Nat.card (K ⧸ pCore 2 K) := by
    rw [Nat.card_congr hmodel.some.toEquiv,
      Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
    decide
  have hdim : Module.finrank (ZMod 2) (Additive (f.Vi 1)) ≤ 6 := by
    simpa only [hn] using second_cover_finrank_le D S f p hp hk
  let ρ := (flagAction f 1).comp (inclusion hK.1)
  obtain ⟨g,hg⟩ := Matrix.SL2.exists_mulVec_eq S.field.Carrier
    (![1,0]) (![0,1]) (by simp) (by simp)
  obtain ⟨a,rfl⟩ := hπ g
  obtain ⟨v,hv⟩ := hp (![1,0])
  have he : flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v = v :=
    LinearMap.congr_fun (small_action_trivial hz h25 ρ hdim ⟨a,hLK a.property⟩) v
  have ha := hact a v
  rw [he,hv] at ha
  have hg' : specialLinearNatural 2 (π a) (![1,0]) = (![0,1]) := hg
  rw [hg'] at ha
  have hz := congrFun ha 0
  simp at hz

/-- The actual first-normalizer refinement in the J₂ carrier row. -/
theorem first_refinement_of_jankoTwo
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hmodel : Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.J2.Carrier)) :
    RefinementAlternative T L (f.Li 0) (f.Li 1) K X 0 S.field.degree :=
  (first_not_jankoTwo D S f hu hm hfix hX hK hLK hXcard hfaith hmodel).elim

/-- The actual second-normalizer refinement in the J₂ carrier row. -/
theorem second_refinement_of_jankoTwo
    (hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2 ^ S.field.degree))
    {K X : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi 1 : Set G)) K)
    (hLK : f.Li 1 ≤ K)
    (π : f.Li 1 →* SL(2,S.field.Carrier)) (hπ : Function.Surjective π)
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hact : ∀ a : f.Li 1, ∀ v,
      p (flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v) =
        specialLinearNatural 2 (π a) (p v))
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G))
    (hmodel : Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.J2.Carrier)) :
    RefinementAlternative T L (f.Li 0) (f.Li 1) K X 1 S.field.degree :=
  (second_not_jankoTwo D S f hm hK hLK π hπ p hp hact hk hmodel).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
