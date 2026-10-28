module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.LocalSetup
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank.SmallFixed
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Theory.GroupTheory.ElementaryThompsonFrattini
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization

/-!
# The degree-four nonsingular Thompson argument

The actual nonsingular stabilizer is Aut(L₃(2)), so its elementary actors
have rank at most two. The natural and dual displacement bounds, including
the outer involutions, rule out an FF offender on the full doubled orbit.
B.2.7 applied to the literal point-centralizer action gives J(C_T(w)) ≤ Q.
Thompson heredity then identifies this subgroup with J(Q), and C(G,Q) ≤ M
controls its ambient normalizer. Thus C_T(w), originally Sylow in C_M(w),
is Sylow in C_G(w).

Only the finite module calculations are reused from the later low-rank
module; the proof uses no weak-closure or pure-fusion conclusion.
Source: Aschbacher--Smith, 12.1.1, printed p.788, using H.9.1(4) and B.2.7.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterH.NaturalDual
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular
variable {M E : Type*} [Group M] [Finite M] [AddCommGroup E] [Module (ZMod 2) E]

omit [Finite M] in
/-- Every elementary actor fixing a nonsingular point has rank at most two in degree four. -/
theorem four_point_actor_rank (S : SourceSetup 4 M E) (v : E)
    (hv : S.quadratic v = 1) (I : Subgroup M) [IsElementaryAbelian 2 I]
    (hI : I ≤ S.stabilizer v) : rank I ≤ 2 := by
  obtain ⟨e⟩ := (S.nonsingular_structure hv).2.2.1
  let A := I.subgroupOf (S.stabilizer v)
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hI
  let J := A.map e.toMonoidHom
  let : IsElementaryAbelian 2 J := IsElementaryAbelian.map _
  have hr : primeRank 2 (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))) ≤ 2 :=
    (Matrix.PSL3Even.automorphism_two_rank_eq_of_card_two (ZMod 2) (by simp)).le
  have hc : Nat.card J ≤ 4 := (primeRank_le_iff_elementary_card_le _).mp hr J inferInstance
  have he : Nat.card J = Nat.card I :=
    (Nat.card_congr (A.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm.trans
      (Nat.card_congr (subgroupOfEquivOfLe hI).toEquiv)
  rw [he] at hc
  exact (Nat.log_mono_right hc).trans (by decide : Nat.log 2 4 ≤ 2)

/-- The full doubled orbit has no FF offender in its nonsingular stabilizer in degree four. -/
theorem four_point_not_ff (S : SourceSetup 4 M E) (v : E)
    (hv : S.quadratic v = 1) :
    ¬ IsFFModule (S.representation.comp (S.stabilizer v).subtype) := by
  rintro ⟨A,hA⟩
  let := hA.1.2
  let I := A.map (S.stabilizer v).subtype
  let : IsElementaryAbelian 2 I := IsElementaryAbelian.map _
  have hne : I ≠ ⊥ := fun hz => hA.1.1
    ((A.map_eq_bot_iff_of_injective (S.stabilizer v).subtype_injective).mp hz)
  have hr := four_point_actor_rank S v hv I (map_subtype_le _)
  have he := rank_map_injective (S.stabilizer v).subtype (S.stabilizer v).subtype_injective A
  have hb : fixedCodim S.representation I ≤ rank I := by
    rw [he]
    have hh := hA.2
    change Module.finrank (ZMod 2) (E ⧸ fixedSpace (S.representation.comp
      (S.stabilizer v).subtype) A) ≤ rank A at hh
    rw [fixedSpace_comp_map S.representation (S.stabilizer v).subtype A] at hh
    exact hh
  obtain ⟨hi,hr1⟩ := four_small_fixedCodim S I (hb.trans hr)
  have hl := inner_fixedCodim_ge_two S I hi hne
  omega

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
open Stellmacher
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- B.2.7 for the literal point action forces the elementary Thompson subgroup to centralize the original doubled orbit. -/
theorem doubleNatural_four_adapted_thompson_centralizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      elementaryAbelianMaxJ (B.pointSylow w) ≤
        centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
  let := D.doubledOrbit_elementary h
  intro S w hw
  let W := componentOrbit V (T : Subgroup G)
  let M := B.localPointCentralizer w
  have hWP : W ≤ B.pointSylow w := le_inf (D.doubledOrbit_E322 h).le_sylow
    (B.orbit_le_pointCentralizer w)
  have hPM : B.pointSylow w ≤ M :=
    le_inf (inf_le_left.trans D.sylow_normalizes_component) inf_le_right
  have hWM : W ≤ M := hWP.trans hPM
  have hn : M ≤ normalizer (W : Set G) := by
    apply le_trans inf_le_left
    change normalizer (L : Set G) ≤ normalizer (componentOrbit V (T : Subgroup G) : Set G)
    rw [B.orbit_eq]
    exact le_normalizer_componentOrbit _ _
  let U := W.subgroupOf M
  let : U.Normal := normal_subgroupOf_of_le_normalizer hn
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hWM
  let q := S.localPointAction w
  have hq := S.localPointAction_surjective w
  have hMN : M ≤ normalizer (L : Set G) := inf_le_left
  have hk : q.ker = centralizer (U : Set M) := by
    ext x
    change q x = 1 ↔ _
    have he : q x = 1 ↔ B.actionProjection (inclusion hMN x) = 1 :=
      Subtype.ext_iff
    have he' : B.actionProjection (inclusion hMN x) = 1 ↔
        inclusion hMN x ∈ (normalizerAction T L V B.orbit_eq).ker :=
      QuotientGroup.eq_one_iff _
    rw [he, he', normalizerAction_ker]
    constructor
    · intro hx u hu
      exact Subtype.ext (hx u hu)
    · intro hx u hu
      exact congrArg M.subtype (hx ⟨u,hWM hu⟩ hu)
  obtain ⟨P,hP⟩ := hw.local_sylow
  have hUP : U ≤ (P : Subgroup M) := by
    intro u hu
    have hm := hP.symm ▸ hWP hu
    obtain ⟨a,ha,he⟩ := hm
    exact (Subtype.ext he : a = u) ▸ ha
  by_contra hJ
  have hJP : ¬ elementaryAbelianMaxJ (P : Subgroup M) ≤ q.ker := by
    intro hh
    have hm := map_mono hh (f := M.subtype)
    rw [← elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective,hP] at hm
    apply hJ
    intro x hx
    obtain ⟨a,ha,rfl⟩ := hm hx
    rw [hk] at ha
    intro u hu
    exact congrArg M.subtype (ha ⟨u,hWM hu⟩ hu)
  let ρ := Representation.NormalElementaryQuotient.representation U q hq hk
  have hff := Representation.NormalElementaryQuotient.isFFModule_of_thompson_not_le
    U q hq hk (P : Subgroup M) hUP hJP
  let e := subgroupOfEquivOfLe hWM
  let E : Additive U ≃ₗ[ZMod 2] Additive W :=
    LinearEquiv.ofBijective (e.toMonoidHom.toAdditive.toZModLinearMap 2) e.bijective
  apply Nonsingular.four_point_not_ff S.setup (Additive.ofMul w)
    (by rw [S.quadratic_eq]; exact hw.nonsingular)
  apply hff.map_equivariant ρ (S.setup.representation.comp
    (S.setup.stabilizer (Additive.ofMul w)).subtype)
    (MonoidHom.id _) Function.injective_id E
  intro a v
  obtain ⟨g,rfl⟩ := hq a
  rw [S.representation_eq]
  apply Additive.toMul.injective
  apply Subtype.ext
  change ((ρ (q g) v).toMul.val : G) = (g : G) * (v.toMul.val : G) * (g : G)⁻¹
  exact congrArg M.subtype
    (Representation.NormalElementaryQuotient.representation_apply U q hq hk g v)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Stellmacher Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The point Sylow and the original core have the same Thompson subgroup, whose full ambient normalizer lies in M. -/
theorem doubleNatural_four_adapted_thompson_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      elementaryAbelianMaxJ (B.pointSylow w) =
        elementaryAbelianMaxJ ((L ⊔ (T : Subgroup G)).pCoreIn 2) ∧
      normalizer (elementaryAbelianMaxJ (B.pointSylow w) : Set G) ≤ normalizer (L : Set G) := by
  let := D.doubledOrbit_elementary h
  intro S w hw
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hJQ : elementaryAbelianMaxJ (B.pointSylow w) ≤ Q := by
    change elementaryAbelianMaxJ (B.pointSylow w) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2
    rw [← D.doubledOrbit_sylow_centralizer h]
    exact le_inf ((sSup_le fun _ hA => hA.1).trans inf_le_left)
      (D.doubleNatural_four_adapted_thompson_centralizes h B S w hw)
  have hQP : Q ≤ B.pointSylow w := le_inf (by
    change (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G)
    rw [← D.doubledOrbit_sylow_centralizer h]
    exact inf_le_left) (D.doubleNatural_core_le_pointCentralizer h B w)
  have he := elementaryAbelianMaxJ_eq_of_intermediate (B.pointSylow w) Q hJQ hQP
  have hJne : elementaryAbelianMaxJ (B.pointSylow w) ≠ ⊥ := by
    rw [←he]
    exact elementaryAbelianMaxJ_ne_bot_of_finite_pGroup Q (isPGroup_pCoreIn 2 _)
      h.maximal_faithful.1.1.2.2
  exact ⟨he.symm, (normalizer_maxJ_le_characteristicNormalizerClosure
    (B.pointSylow w) Q hJQ hQP hJne).trans (D.doubleNatural_core_characteristicNormalizerClosure h)⟩

/-- In degree four the corrected relative Sylow is Sylow in the full ambient point centralizer. -/
theorem doubleNatural_four_adapted_ambientSylow
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) := by
  let := D.doubledOrbit_elementary h
  intro S w hw
  have hn := (normalizer_le_normalizer_elementaryAbelianMaxJ (B.pointSylow w)).trans
    (D.doubleNatural_four_adapted_thompson_core h B S w hw).2
  apply exists_sylow_eq_of_relative_normalizer_le hw.local_sylow inf_le_right
  exact le_inf (inf_le_right.trans hn) inf_le_left

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

