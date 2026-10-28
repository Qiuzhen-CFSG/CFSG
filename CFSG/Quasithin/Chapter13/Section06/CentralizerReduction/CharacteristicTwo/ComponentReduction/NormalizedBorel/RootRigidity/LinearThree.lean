module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.RootRigidity.Transport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.RootRigidity.LinearThreeAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ResidualAction
public import Theory.SpecificGroups.PSL3.NormalizedRootCentralizers.LinearBorel.Extensions

/-!
# The normalized linear-three root contradiction

The literal K/Z(K) model embeds in X* = N(K)/C(K) through the canonical
component image. Its full upper-unitriangular center is transported to the
source rootCenter, and the descended action agrees with conjugation under
this embedding. For a quasisimple K that action is faithful; no centerless
hypothesis on K is imposed, including for exceptional covers of PSL₃(4).

The marked source identity D = [D,T] and proved binary automorphism coverage
put the residual action in InnDiag(PSL₃). The trace-and-scaling calculation
then makes its centralizers uniform on nonidentity elements of rootCenter,
contradicting the marked a*/z* asymmetry. Only the parent-owned actual model
and Sylow alignment remain explicit. Borel placement is unnecessary for this
stronger coordinate calculation on the residual itself.

This route applies unchanged to A.3.18(iii): the PGL₃ alternative has even
binary degree, and the nonsplit linear-three alternative has positive degree
divisible by six. The imported mixed-extension application retains its actual
outer preimage. We neither assert uniformity for every field actor nor choose
a splitting of that extension.

Source: Aschbacher–Smith, A.3.16–18 and the proof of 13.6.6, printed p.927.
-/

public section

open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
open Subgroup Theory.GroupTheory A5Module
open Matrix.PSL3.LinearThree
variable {G : Type*} [Group G] {L V : Subgroup G}
variable {F : Type*} [Field F]

/-- The actual model embedding through K/Z(K) and the component image in X*. -/
noncomputable def linearThreeEmbedding {v : G} (K : Subgroup (Gv v))
    (e : K ⧸ center K ≃* PSL(3,F)) : PSL(3,F) →* XStar K :=
  (NormalizerAction.componentImage K).subtype.comp
    (e.symm.trans (NormalizerAction.componentCentralQuotientEquiv K)).toMonoidHom

theorem linearThreeEmbedding_injective {v : G} (K : Subgroup (Gv v))
    (e : K ⧸ center K ≃* PSL(3,F)) : Function.Injective (linearThreeEmbedding K e) :=
  Subtype.val_injective.comp (e.symm.trans (NormalizerAction.componentCentralQuotientEquiv K)).injective

@[simp] theorem linearThreeEmbedding_mk {v : G} (K : Subgroup (Gv v))
    (e : K ⧸ center K ≃* PSL(3,F)) (k : K) :
    linearThreeEmbedding K e (e (QuotientGroup.mk' (center K) k)) =
      NormalizerAction.componentMap K k := by
  change ((NormalizerAction.componentCentralQuotientEquiv K)
    (e.symm (e (QuotientGroup.mk' (center K) k))) : XStar K) = _
  rw [e.symm_apply_apply, NormalizerAction.componentCentralQuotientEquiv_mk]
  rfl

/-- A component-image marking gives exactly the same canonical embedding.
This equation connects the parent model-placement data to the central quotient. -/
@[simp] theorem linearThreeEmbedding_of_componentEquiv {v : G} (K : Subgroup (Gv v))
    (k : NormalizerAction.componentImage K ≃* PSL(3,F)) :
    linearThreeEmbedding K ((NormalizerAction.componentCentralQuotientEquiv K).trans k) =
      (NormalizerAction.componentImage K).subtype.comp k.symm.toMonoidHom := by
  apply MonoidHom.ext
  intro x
  change ((NormalizerAction.componentCentralQuotientEquiv K)
    ((NormalizerAction.componentCentralQuotientEquiv K).symm (k.symm x)) : XStar K) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- The descended model action remains faithful for every quasisimple cover,
including the exceptional covers of PSL₃(4). -/
theorem linearThreeAction_injective {v : G} (K : Subgroup (Gv v))
    (hK : IsComponent (Gv v) K) (e : K ⧸ center K ≃* PSL(3,F)) :
    Function.Injective ((MulAut.centralQuotientAction e).comp (NormalizerAction.action K)) := by
  let : IsQuasisimple K := hK.2
  exact MulAut.centralQuotientAction_comp_injective _ _ (NormalizerAction.action_injective K)

/-- Compatibility uses both literal quotient maps, even when K has center. -/
theorem linearThreeEmbedding_action {v : G} (K : Subgroup (Gv v))
    (e : K ⧸ center K ≃* PSL(3,F)) (b : XStar K) (x : PSL(3,F)) :
    linearThreeEmbedding K e
      (((MulAut.centralQuotientAction e).comp (NormalizerAction.action K)) b x) =
        b * linearThreeEmbedding K e x * b⁻¹ := by
  obtain ⟨n,rfl⟩ := QuotientGroup.mk'_surjective (NormalizerAction.C K) b
  obtain ⟨q,rfl⟩ := e.surjective x
  obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (center K) q
  change linearThreeEmbedding K e
    (MulAut.centralQuotientAction e (NormalizerAction.action K (NormalizerAction.quotient K n))
      (e (QuotientGroup.mk' (center K) k))) = _
  rw [MulAut.centralQuotientAction_apply, linearThreeEmbedding_mk,
    linearThreeEmbedding_mk, NormalizerAction.action_quotient]
  change NormalizerAction.quotient K _ = NormalizerAction.quotient K n *
    NormalizerAction.quotient K (inclusion K.le_normalizer k) * (NormalizerAction.quotient K n)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

/-- Model coordinates give the uniform calculation in the literal rootCenter
for any subgroup with inner-diagonal action. -/
theorem linearThree_root_centralizers [CharP F 2]
    (T : Subgroup G) {v : G} (K : Subgroup (Gv v))
    (e : K ⧸ center K ≃* PSL(3,F))
    (hU : (unipotent F).map (linearThreeEmbedding K e) =
      NormalizerAction.sylowImage K (localT T v) ⊓ NormalizerAction.componentImage K)
    (B : Subgroup (XStar K))
    (hB : B.map ((MulAut.centralQuotientAction e).comp (NormalizerAction.action K)) ≤
      Matrix.PSL3.OuterSolvable.innerDiagonal F)
    (r : XStar K) (hr : r ∈ rootCenter T K) (hne : r ≠ 1) :
    B ⊓ centralizer ({r} : Set (XStar K)) =
      B ⊓ centralizer (rootCenter T K : Set (XStar K)) := by
  have hR := rootCenter_eq_model_center T K (linearThreeEmbedding K e)
    (linearThreeEmbedding_injective K e) (unipotent F) hU
  rw [hR] at hr ⊢
  exact Matrix.PSL3.NormalizedRootCentralizers.uniform_mapped_center
    (linearThreeEmbedding K e) (linearThreeEmbedding_injective K e) _
    (linearThreeEmbedding_action K e) B hB r hr hne

/-- The source commutator identity removes the obstructing field action.
Standard coverage is discharged by the proved binary-field theorem. -/
theorem residual_linearThree_root_centralizers [Finite F]
    (s : Marking L V) (T : Subgroup G) (K : Subgroup (Gv (markedV s)))
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : K ⧸ center K ≃* PSL(3,F))
    (hU : (unipotent F).map (linearThreeEmbedding K e) =
      NormalizerAction.sylowImage K (localT T (markedV s)) ⊓ NormalizerAction.componentImage K)
    (hDN : residual s ≤ X K) (hTN : localT T (markedV s) ≤ X K)
    (hcomm : ⁅residual s, localT T (markedV s)⁆ = residual s)
    (r : XStar K) (hr : r ∈ rootCenter T K) (hne : r ≠ 1) :
    residualStar s K ⊓ centralizer ({r} : Set (XStar K)) =
      residualStar s K ⊓ centralizer (rootCenter T K : Set (XStar K)) := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  apply linearThree_root_centralizers T K e hU (residualStar s K) _ r hr hne
  exact residualStar_linearThree_innerDiagonal s T K e
    (Matrix.PSL3.OuterSolvable.standard_eq_top_of_two_power_card F (by omega) hF)
    hDN hTN hcomm

/-- The linear-three branch of the marked root contradiction, retaining the
source module/Sylow hypotheses and the genuine model of K/Z(K).
No uniformity, coverage or commutator identity is an extra premise. -/
theorem exclude_linearThree [Finite G] [Finite F] (s : Marking L V)
    (T : Subgroup G) (K : Subgroup (Gv (markedV s)))
    (ha : aLocal s ∈ X K) (hz : zLocal s ∈ X K) (hDN : residual s ≤ X K)
    (hac : aLocal s ∈ centralizer (residual s : Set (Gv (markedV s))))
    (han : aLocal s ∉ centralizer (K : Set (Gv (markedV s))))
    (hzn : zLocal s ∉ centralizer (K : Set (Gv (markedV s))))
    (hER : EStar s K ha hz ≤ rootCenter T K)
    (hk : IsPGroup 2 s.action.ker) (hTL : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (Gv (markedV s)))
    (hS : (S : Subgroup (Gv (markedV s))) = localT T (markedV s))
    (hTN : localT T (markedV s) ≤ X K)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : K ⧸ center K ≃* PSL(3,F))
    (hU : (unipotent F).map (linearThreeEmbedding K e) =
      NormalizerAction.sylowImage K (localT T (markedV s)) ⊓ NormalizerAction.componentImage K) :
    False := by
  apply exclude_of_root_centralizers s T K ha hz hDN hac han hzn hER
    (residualStar s K) le_rfl
  exact residual_linearThree_root_centralizers s T K hn hF e hU hDN hTN
    (residual_commutator s T hk hTL S hS)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
