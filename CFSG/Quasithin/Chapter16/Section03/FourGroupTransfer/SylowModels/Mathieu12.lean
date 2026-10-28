module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.SylowModels.ModelFacts
public import CFSG.Quasithin.Chapter16.Section03.Basic
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.SylowModels.Mathieu12.ComponentFusion
public import Theory.Mathieu.M12.SylowCenterSquares
public import Theory.Alternating.Aut

/-!
# The M₁₂ Sylow-center geometry in 16.3.4

For the supplied full M₁₂ model, conjugation by i induces an actual involutory
automorphism: [K,⟨i⟩] = K excludes the identity action. The given component L
embeds into its fixed subgroup and is nontrivial and perfect. The earlier exact
16.1.5(4) table then makes every involution of L a square in M₁₂, by
`Mathieu12.ComponentFusion`. The intrinsic square-fusion calculation constructs
a Sylow subgroup whose entire center is the prescribed order-two subgroup.
All maps are transported through the supplied K ≃ M₁₂, with no quotient.

The A₅ isomorphism gives |Aut(L)|₂ = 8, whereas |K|₂ = 64. No additional
global induction hypothesis is needed. The sole remaining source input is the
exact earlier automorphism-centralizer table, owned by `Mathieu.M12Table`;
the source assembly must instantiate it before claiming 16.3.4.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.1.5(4),
16.1.7(f), and the proof of 16.3.4, printed pp.1171–1172 and 1178 / PDF p.1195.
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
open ClassificationModels OtherPreliminaries.Mathieu
variable {G : Type*} [Group G] [Finite G] {L K : Subgroup G}

/-- The numerical inequality is independent of the centralizer table. -/
theorem mathieu12_sylow_order_gap
    (eK : K ≃* SporadicName.m12.Carrier) (eL : L ≃* alternatingGroup (Fin 5)) :
    SylowOrderGap L K := by
  have hK : Nat.card K = 95040 := (Nat.card_congr eK.toEquiv).trans m12_order
  have hA : Nat.card (MulAut L) = 120 := by
    calc
      Nat.card (MulAut L) = Nat.card (MulAut (alternatingGroup (Fin 5))) :=
        Nat.card_congr (MulAut.congr eL).toEquiv
      _ = Nat.card (Equiv.Perm (Fin 5)) := (Nat.card_congr
        (Equiv.ofBijective _ (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
          5 (by decide) (by decide)))).symm
      _ = 120 := by norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  intro A S
  have hAc : Nat.card A = 8 := A.card_eq_multiplicity.trans (by rw [hA]; decide +kernel)
  have hSc : Nat.card S = 64 := S.card_eq_multiplicity.trans (by rw [hK]; decide +kernel)
  omega

omit [Finite G] in
private theorem setup_action_order {T : Sylow 2 G} {z t i : G}
    (h : ExclusionSetup T z L K t i) (eK : K ≃* SporadicName.m12.Carrier)
    (hn : i ∈ normalizer (K : Set G)) :
    orderOf (K.normalizerMonoidHom ⟨i, hn⟩) = 2 := by
  apply orderOf_eq_prime
  · have hi : (⟨i, hn⟩ : normalizer (K : Set G)) ^ 2 = 1 := by
      apply Subtype.ext
      change i ^ 2 = 1
      simpa only [h.involution_i] using pow_orderOf_eq_one i
    rw [← map_pow, hi, map_one]
  · intro he
    have hc : i ∈ centralizer (K : Set G) := by
      have hk : (⟨i, hn⟩ : normalizer (K : Set G)) ∈ K.normalizerMonoidHom.ker := he
      rw [normalizerMonoidHom_ker] at hk
      exact hk
    have hb : K = ⊥ := h.commutator_eq.symm.trans (by
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr (zpowers_le.mpr hc))
    have hcard : Nat.card K = 95040 := (Nat.card_congr eK.toEquiv).trans m12_order
    simp [hb] at hcard

/-- Every order-two subgroup in the embedded L lifts to the whole center of
an actual Sylow subgroup of K. Only the earlier exact table remains an input. -/
theorem mathieu12_involution_center_lifting
    (table : ∀ r : MulAut M12, orderOf r = 2 → M12InvolutionAlternative r)
    {T : Sylow 2 G} {z t i : G} (h : ExclusionSetup T z L K t i)
    (eK : K ≃* SporadicName.m12.Carrier) : InvolutionCenterLifting L K := by
  let e : K ≃* M12 := eK
  let := h.localSetup.component.quasisimple
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  have hLK : L ≤ K := h.componentL.1.trans inf_le_left
  have hn : i ∈ normalizer (K : Set G) :=
    (le_normalizer_iff_commutator_le_left.mpr h.commutator_eq.le) (mem_zpowers i)
  let a := K.normalizerMonoidHom ⟨i, hn⟩
  let r : MulAut M12 := MulAut.congr e a
  have hr : orderOf r = 2 := (MulAut.congr e).orderOf_eq a |>.trans
    (setup_action_order h e hn)
  let j : L →* M12 := e.toMonoidHom.comp (inclusion hLK)
  let f : L →* r.fixedSubgroup := j.codRestrict r.fixedSubgroup (by
    intro l
    rw [MulAut.mem_fixedSubgroup]
    change e (a (e.symm (e (inclusion hLK l)))) = e (inclusion hLK l)
    rw [e.symm_apply_apply]
    apply congrArg e
    apply Subtype.ext
    change i * (l : G) * i⁻¹ = (l : G)
    rw [← h.centralizes l (mem_sup_left l.property), mul_inv_cancel_right])
  have hf : Function.Injective f := by
    intro x y hxy
    have he : e (inclusion hLK x) = e (inclusion hLK y) := congrArg Subtype.val hxy
    exact Subtype.ext (congrArg (fun k : K => (k : G)) (e.injective he))
  intro P V hV hcard
  have hVL : V ≤ L := by
    intro v hv
    obtain ⟨l, _, rfl⟩ := hV hv
    exact l.property
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := V) 2 (by rw [hcard])
  let x : L := ⟨v, hVL v.property⟩
  have hvG : orderOf (v : G) = 2 := (orderOf_coe v).trans hv
  have hx : orderOf x = 2 := (orderOf_coe x).symm.trans hvG
  have hgen : zpowers (v : G) = V := eq_of_le_of_card_ge (zpowers_le.mpr v.property)
    (by rw [Nat.card_zpowers, hvG, hcard])
  obtain ⟨y, hy⟩ := Mathieu12.fixed_perfect_involution_square table r hr f hf x hx
  have hfx : orderOf (f x : M12) = 2 := by
    change orderOf (e (inclusion hLK x)) = 2
    rw [e.orderOf_eq, ← orderOf_coe]
    exact hvG
  obtain ⟨S, hS⟩ := M12SylowCenters.exists_sylow_center_of_square (f x) hfx ⟨y, hy⟩
  let S' : Sylow 2 K := S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  refine ⟨S', ?_⟩
  rw [← map_subgroup_center_eq K.subtype K.subtype_injective]
  change ((center ((S : Subgroup M12).map e.symm.toMonoidHom)).map
    ((S : Subgroup M12).map e.symm.toMonoidHom).subtype).map K.subtype = V
  rw [← map_subgroup_center_eq e.symm.toMonoidHom e.symm.injective,
    hS, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  change zpowers (e.symm (e (inclusion hLK x)) : G) = V
  rw [e.symm_apply_apply]
  exact hgen

/-- The M₁₂ branch of the shared Sylow-model contract, conditional only on the
exact earlier 16.1.5(4) table. The parent source assembly supplies that table. -/
theorem mathieu12_geometry_of_involution_table
    (table : ∀ r : MulAut M12, orderOf r = 2 → M12InvolutionAlternative r)
    {T : Sylow 2 G} {z t i : G} (h : ExclusionSetup T z L K t i)
    (eK : K ≃* SporadicName.m12.Carrier) (eL : L ≃* alternatingGroup (Fin 5)) :
    InvolutionCenterLifting L K ∧ SylowOrderGap L K :=
  ⟨mathieu12_involution_center_lifting table h eK, mathieu12_sylow_order_gap eK eL⟩
end CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
