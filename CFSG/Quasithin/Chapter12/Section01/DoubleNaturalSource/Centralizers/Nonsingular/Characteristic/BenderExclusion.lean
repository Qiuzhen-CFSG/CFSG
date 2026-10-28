module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.LocalMarking
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.SmallQuotients
public import Theory.SpecificGroups.SL2.PerfectImageCore
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.PerfectCore
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models

/-!
# Excluding the rank-one rows in the nonsingular centralizer

The original moving subgroup survives in K/Z(K) as a nontrivial normal
two-subgroup of the perfect local image. Thus that image has nontrivial
two-core, contrary to the proved perfect-image core theorems for binary
PSL₂ and PSU₃. The Suzuki order is prime to three, whereas the local
L_(n-1)(2) quotient has order divisible by three.

Both doubled degrees are covered, using the literal residual and quotient
maps from `LocalMarking`. `ModelReduction` applies this in the source
characteristic-two reduction; no ambient Sylow premise is added.
Source: Aschbacher--Smith, 12.1.1, printed p.788.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- No Bender model is the literal ordinary-component central quotient. -/
theorem doubleNatural_adapted_component_not_bender
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        ¬ ClassificationModels.IsBenderModel (K ⧸ center K) := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hK hm
  let C := K ⧸ center K
  let q := QuotientGroup.mk' (center K)
  let P := ((B.pointResidual w).subgroupOf K).map q
  let U := ((⁅componentOrbit V (T : Subgroup G),B.pointResidual w⁆).subgroupOf K).map q
  obtain ⟨hperf,⟨e₀⟩,hne,hele,_,hnorm⟩ := D.doubleNatural_adapted_component_local_marking h B S w hw K hK
  let : Group.IsPerfect P := hperf
  let : IsElementaryAbelian 2 U := hele
  have hUP : U ≤ P := map_mono (comap_mono (D.doubleNatural_moving_le_residual h B w))
  have hcore : U ≤ P.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 U) hUP hnorm
  have hnon : pCore 2 P ≠ ⊥ := by
    intro he
    have hb : P.pCoreIn 2 = ⊥ := by rw [pCoreIn,he,Subgroup.map_bot]
    exact hne (bot_unique (hcore.trans_eq hb))
  have hd : 3 ∣ Nat.card P := by
    apply dvd_trans _ (card_quotient_dvd_card (pCore 2 P))
    rcases B.degree with hn | hn
    · subst n
      rw [Nat.card_congr (e₀.trans Atlas.Comparisons.Exceptional.sl3TwoEquivPsl3Two.symm).toEquiv,
        Matrix.PSL3Two.card_SL]
      decide
    · subst n
      rw [Nat.card_congr (e₀.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8).toEquiv,
        nat_card_alternatingGroup,Nat.card_fin]
      decide
  cases hm with
  | linear f hf hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    let a := e.trans (Theory.PSL2.sl2QuotientEquiv F).symm
    let j := a.toMonoidHom.comp P.subtype
    have hj : Function.Injective j := a.injective.comp P.subtype_injective
    have hh := Matrix.SpecialLinearGroup.perfect_hom_twoCore_le_ker j
    exact hnon (bot_unique (hh.trans_eq ((MonoidHom.ker_eq_bot_iff j).mpr hj)))
  | unitary f hf hm =>
    have hh := ChapterF.Source.Unitary.perfect_hom_twoCore_le_ker (by omega) hm P.subtype
    exact hnon (bot_unique (hh.trans_eq ((MonoidHom.ker_eq_bot_iff P.subtype).mpr P.subtype_injective)))
  | suzuki m hm he =>
    obtain ⟨e⟩ := he
    have hh := hd.trans P.card_subgroup_dvd_card
    rw [Nat.card_congr e.toEquiv] at hh
    exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega) hh

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
