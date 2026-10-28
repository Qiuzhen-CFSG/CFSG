module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleExclusions
public import Theory.SpecificGroups.SL2.PerfectImageCore
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.PerfectCore
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder

/-!
# Rank-one exclusions for the nonsingular central quotient

The literal map L_v -> K_v/Z(K_v) cannot kill O₂(L_v), since that would
centralize its nontrivial moved subgroup. The binary linear and unitary
rank-one models kill the two-core of every perfect image. The Suzuki models
have order prime to three and kill the cubic residual L_v. These exclude
all three Bender rows without an additional Sylow-normalization hypothesis.

Source: Aschbacher--Smith, Lemma 12.6.12, printed pp.825--826.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The noncentral local two-core survives the literal central-quotient map. -/
theorem SourceHypothesis.nonsingular_local_core_not_centralQuotient_kernel
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hLK : Lv L (v : G) ≤ Kv (v : G)) :
    ¬ pCore 2 (Lv L (v : G)) ≤
      ((QuotientGroup.mk' (center (Kv (v : G)))).comp (inclusion hLK)).ker := by
  intro hk
  apply (H.nonsingular_local_core_moved D v hv).1
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rintro x ⟨a,ha,rfl⟩
  have hz : inclusion hLK a ∈ center (Kv (v : G)) :=
    (QuotientGroup.eq_one_iff _).mp (hk ha)
  intro b hb
  exact congrArg Subtype.val (mem_center_iff.mp hz ⟨b,hLK hb⟩)

/-- None of the actual rank-one models can be the central quotient of K_v. -/
theorem SourceHypothesis.nonsingular_not_bender_centralQuotient
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v) :
    ¬ ClassificationModels.IsBenderModel ((Kv (v : G)) ⧸ center (Kv (v : G))) := by
  let B := Lv L (v : G)
  let C := Kv (v : G)
  obtain ⟨eA⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
  let : Group.IsPerfect B := Lv_isPerfect_of_A6 L (v : G) eA
  have hBC : B ≤ C := Lv_le_Kv_of_A6 L (v : G) eA
  let j : B →* C ⧸ center C := (QuotientGroup.mk' (center C)).comp (inclusion hBC)
  have hk : ¬ pCore 2 B ≤ j.ker :=
    H.nonsingular_local_core_not_centralQuotient_kernel D v hv hBC
  intro hm
  cases hm with
  | linear f hf hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    let a := e.trans (Theory.PSL2.sl2QuotientEquiv F).symm
    have hh := Matrix.SpecialLinearGroup.perfect_hom_twoCore_le_ker
      (a.toMonoidHom.comp j)
    apply hk
    intro x hx
    exact a.injective (by simpa only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_one] using (hh hx))
  | unitary f hf hm =>
    exact hk (ChapterF.Source.Unitary.perfect_hom_twoCore_le_ker (by omega) hm j)
  | suzuki m hm he =>
    obtain ⟨e⟩ := he
    let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    let : IsSimpleGroup (B ⧸ pCore 2 B) := eA.isSimpleGroup
    have hp : IsPPerfect 2 B := isPPerfect_embedded_pResidual 2 (CLv L (v : G))
    have hd : 3 ∣ Nat.card (B ⧸ pCore 2 B) := by
      rw [Nat.card_congr eA.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
      decide
    have hr := primeToResidual_eq_top_of_simple_quotient 3 2 (pCore 2 B) pCore_isPGroup hp hd
    have hc : Nat.Coprime 3 (Nat.card (C ⧸ center C)) := by
      rw [Nat.card_congr e.toEquiv]
      exact Nat.prime_three.coprime_iff_not_dvd.mpr
        (BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega))
    have hh := primeToResidual_le_ker j hc
    rw [hr] at hh
    exact hk (le_top.trans hh)
end CFSG.Quasithin.Chapter12.Section06
