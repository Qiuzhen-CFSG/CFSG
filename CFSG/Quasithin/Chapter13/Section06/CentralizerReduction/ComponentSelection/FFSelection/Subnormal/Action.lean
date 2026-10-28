module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Algebra
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Geometry.Thompson
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.Actor
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.Maximum


/-!
# The genuine offender action for the subnormal obstruction

Restrict the faithful U_v representation to its offender subgroup. The
maximum elementary subgroups of the given Sylow give best offenders on
the normal elementary subgroup U_v, so the actual J(T_v) star image lies
in this actor. The full
commutator premise then places L_v* there too. Restriction preserves
faithfulness and vanishing two-core; taking the inverse image in the
specified SQTK group G_v supplies the B.5.3 cover.

The universal B.5.6 input returns all its original alternatives, including
the action identifications. Group commutator generators identify the linear
moved space with the literal ambient commutator, so rank two means order
four. The final helper applies this transport to the algebraic contradiction;
its rank and orbit bounds are still undischarged classification outputs.

The imported Geometry/Thompson module supplies the earlier faithful action.
Only its checked definitions and action theorems are used here; this module
does not assert that the geometric source reductions are complete.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.2.4,
B.5.3–6 and 13.6.10, printed pp.75–76, 104–105 and 928.
-/

@[expose] public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Maximum elementary subgroups of the actual Sylow give best offenders
on U_v, hence its literal Thompson star image lies in J(G*_v,U_v). -/
theorem thompson_star_le_offender (T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (internalUv z v)] (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v) :
    starImage z v (elementaryAbelianMaxJ (Tv T v)) ≤
      offenderSubgroup (uvRepresentation z v hz) := by
  have hU : internalUv z v ≤ (S : Subgroup (Gv v)) :=
    (IsElementaryAbelian.isPGroup 2 (internalUv z v)).le_sylow_of_normal S
  have he : (elementaryAbelianMaxJ (Tv T v)).subgroupOf (Gv v) =
      elementaryAbelianMaxJ (S : Subgroup (Gv v)) := by
    rw [← hS, elementaryAbelianMaxJ_map_injective (Gv v).subtype
      (Gv v).subtype_injective]
    exact comap_map_eq_self_of_injective (Gv v).subtype_injective _
  unfold starImage
  rw [he]
  exact thompson_image_le_internal_offenderSubgroup _ (internalUv z v) hU
    (starMk z v) (starMk_surjective z v) (starMk_ker_internal z v hz)

/-- The full commutator premise of 13.6.10 puts L*_v in the offender actor;
no equality between that actor and G*_v is imposed. -/
theorem Lv_star_le_offender (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (internalUv z v)] (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hfull : starImage z v (Lv L v) =
      ⁅starImage z v (Lv L v), starImage z v (elementaryAbelianMaxJ (Tv T v))⁆) :
    starImage z v (Lv L v) ≤ offenderSubgroup (uvRepresentation z v hz) := by
  calc
    _ = _ := hfull
    _ ≤ ⁅starImage z v (Lv L v), offenderSubgroup (uvRepresentation z v hz)⁆ :=
      commutator_mono le_rfl (thompson_star_le_offender T z v hz S hS)
    _ ≤ _ := commutator_le_right _ _

/-- All B.5.3 hypotheses hold after restricting the faithful U_v action to
its offender subgroup. The SQTK cover is the actual inverse image in G_v. -/
theorem uv_offender_hypothesis (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (internalUv z v)]
    {𝒦 : GroupClass.{u}} (hSQ : IsSQTK 𝒦 (Gv v))
    (hcore : pCore 2 (Gstar z v) = ⊥) :
    FFHypothesis 𝒦 (offenderRepresentation (uvRepresentation z v hz)) :=
  offender_hypothesis (uvRepresentation z v hz) (starMk z v) (starMk_surjective z v)
    hSQ (uvRepresentation_faithful z v hz) hcore

/-- Apply the full universal B.5.6 implication to this literal restricted
representation, preserving every group and module alternative. -/
theorem uv_offender_classification (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (internalUv z v)]
    {𝒦 : GroupClass.{u}} (classification : GeneralClassificationInput.{u,u} 𝒦)
    (hSQ : IsSQTK 𝒦 (Gv v)) (hcore : pCore 2 (Gstar z v) = ⊥) :
    SourceAlternative (offenderRepresentation (uvRepresentation z v hz)) :=
  classification _ _ _ (uv_offender_hypothesis z v hz hSQ hcore)

/-- The literal cubic subgroup retains its order and subnormality inside
the offender actor selected above. -/
theorem marked_cubic_in_offender {L V : Subgroup G} (s : A5Module.Marking L V)
    (T : Subgroup G)
    [IsElementaryAbelian 2 (internalUv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map
      (Gv (A5Module.markedV s)).subtype = Tv T (A5Module.markedV s))
    (hcore : pCore 2 (Gstar (A5Module.markedZ s) (A5Module.markedV s)) = ⊥)
    (hcard : Nat.card (Lv L (A5Module.markedV s) ⧸
      pCore 2 (Lv L (A5Module.markedV s))) = 3)
    (hfull : starImage (A5Module.markedZ s) (A5Module.markedV s) (Lv L (A5Module.markedV s)) =
      ⁅starImage (A5Module.markedZ s) (A5Module.markedV s) (Lv L (A5Module.markedV s)),
        starImage (A5Module.markedZ s) (A5Module.markedV s)
          (elementaryAbelianMaxJ (Tv T (A5Module.markedV s)))⁆)
    (hs : (starImage (A5Module.markedZ s) (A5Module.markedV s)
      (Lv L (A5Module.markedV s))).IsSubnormal) :
    let J := offenderSubgroup (uvRepresentation _ _ (A5Module.markedZ_mem_Gv s))
    let A := (starImage (A5Module.markedZ s) (A5Module.markedV s)
      (Lv L (A5Module.markedV s))).subgroupOf J
    A.IsSubnormal ∧ Nat.card A = 3 := by
  dsimp only
  have hle := Lv_star_le_offender L T _ _ (A5Module.markedZ_mem_Gv s) S hS hfull
  exact ⟨hs.subgroupOf, (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans
    (marked_star_card_three s hcore hcard hs)⟩

private theorem internal_moved_card {H D : Type*} [Group H] [Group D]
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (q : H →* D) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set H)) (A : Subgroup H) :
    Nat.card (subspaceCommutator
      (NormalElementaryQuotient.representation U q hq hk) ⊤ (A.map q)) =
      Nat.card ↥(⁅U, A⁆ : Subgroup H) := by
  let ρ := NormalElementaryQuotient.representation U q hq hk
  let C := subspaceCommutator ρ ⊤ (A.map q)
  let N := (⁅U, A⁆).subgroupOf U
  let W := NormalElementaryQuotient.subspace U N
  have hc : ⁅U, A⁆ ≤ C.toAddSubgroup.toSubgroup'.map U.subtype := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro a ha u hu
    let w : Additive U := Additive.ofMul ⟨u, hu⟩
    let d := ρ (q a) w - w
    refine ⟨d.toMul, ?_, ?_⟩
    · change d ∈ C
      exact Submodule.subset_span ⟨q a, mem_map_of_mem q ha, w, Submodule.mem_top, rfl⟩
    · change (((ρ (q a) w).toMul : U) : H) / u = _
      rw [NormalElementaryQuotient.representation_apply, div_eq_mul_inv]
      rfl
  have he : C = W := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨_, ⟨a, ha, rfl⟩, w, _, rfl⟩
      change (((ρ (q a) w).toMul : U) : H) / (w.toMul : H) ∈ ⁅U, A⁆
      rw [NormalElementaryQuotient.representation_apply, div_eq_mul_inv, commutator_comm]
      exact commutator_mem_commutator ha w.toMul.property
    · intro w hw
      obtain ⟨d, hd, he⟩ := hc hw
      have hdw : Additive.ofMul d = w := congrArg Additive.ofMul (Subtype.ext he)
      exact hdw ▸ hd
  rw [show subspaceCommutator (NormalElementaryQuotient.representation U q hq hk) ⊤
    (A.map q) = W from he]
  exact (Nat.card_congr (show W ≃ N from Equiv.refl _)).trans
    (Nat.card_congr (subgroupOfEquivOfLe (commutator_le_left U A)).toEquiv)

omit [Finite G] in
/-- The binary moved space has exactly the order of the literal ambient
commutator. Both quotient maps and the conjugation convention are retained. -/
theorem uv_moved_card (L : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (internalUv z v)] :
    Nat.card (moved (uvRepresentation z v hz) (starImage z v (Lv L v))) =
      Nat.card ↥(⁅Uv z v, Lv L v⁆ : Subgroup G) := by
  rw [show moved (uvRepresentation z v hz) (starImage z v (Lv L v)) =
    subspaceCommutator (NormalElementaryQuotient.representation (internalUv z v)
      (starMk z v) (starMk_surjective z v) (starMk_ker_internal z v hz)) ⊤
      (((Lv L v).subgroupOf (Gv v)).map (starMk z v)) from rfl,
    internal_moved_card]
  have hm : (⁅internalUv z v, (Lv L v).subgroupOf (Gv v)⁆).map (Gv v).subtype =
      ⁅Uv z v, Lv L v⁆ := by
    rw [map_commutator, map_subgroupOf_eq_of_le (Lv_le_Gv L v), internalUv,
      map_subgroupOf_eq_of_le (Uv_le_Gv z v hz)]
  rw [← hm]
  exact (card_map_of_injective (Gv v).subtype_injective).symm

/-- A rank-two B.5.6 conclusion gives order four for the original moved group. -/
theorem uv_moved_card_four (L : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (internalUv z v)]
    (hdim : Module.finrank (ZMod 2)
      (moved (uvRepresentation z v hz) (starImage z v (Lv L v))) = 2) :
    Nat.card ↥(⁅Uv z v, Lv L v⁆ : Subgroup G) = 4 := by
  rw [← uv_moved_card L z v hz, Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_zmod, hdim]
  rfl

/-- Consumer of the moved-space transport and the actual Sylow normality
argument. The rank and orbit bounds are still explicit classification outputs. -/
theorem contradiction_of_linear_classification_bounds
    (L V T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (internalUv z v)] (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hT : Tv T v ≤ normalizer (Lv L v : Set G))
    (hV : IsPGroup 2 V) (hL : Lv L v ≤ normalizer (V : Set G))
    (hsplit : Vv L z v = zpowers v ⊔ ⁅V, Lv L v⁆)
    (hsmall : Nat.card ↥(⁅V, Lv L v⁆ : Subgroup G) = 4)
    (hdim : Module.finrank (ZMod 2)
      (moved (uvRepresentation z v hz) (starImage z v (Lv L v))) = 2)
    (horbit : (normalizer (starImage z v (Lv L v) : Set (Gstar z v))).index ≤ 2)
    (hnormal : ¬ ((Vv L z v).subgroupOf (Gv v)).Normal) : False :=
  contradiction_of_classification_bounds L V T z v S hS hT hV hL hsplit hsmall
    (uv_moved_card_four L z v hz hdim).le horbit hnormal

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal

end
