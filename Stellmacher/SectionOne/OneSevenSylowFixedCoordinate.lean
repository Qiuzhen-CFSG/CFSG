module
public import Stellmacher.SectionOne.OneSevenFactorAction
public import Stellmacher.SectionOne.SL2ProductNormalizerRigidity
public import Theory.GroupAction.NormalizingActor
public import Theory.GroupAction.NormalizingFixedPoints
public import Theory.GroupTheory.SylowNormalClosure
public import Theory.GroupAction.CommutatorSemidirect
public import Mathlib.Tactic.FinCases
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaIndependence

/-!
# The Sylow-fixed coordinate of a normal one-seven factor

A normal one-seven factor has a four-element action support. Its fixed
subgroup under the supplied Sylow two-subgroup has order two; the Sylow
fixed space has index two over its intersection with the factor's fixed
space. The derived order-three subgroup acting on that Sylow fixed space
generates the full support. All actions are restrictions of the given action.

Orbit parity gives at least two fixed support elements. If the whole support
were fixed, the action kernel would contain the Sylow subgroup and therefore
every involution of the factor. Involution generation would force the factor
to fix its support, contrary to the coprime fixed/support decomposition.
That same invariant decomposition gives the index formula. Finally the
orbit of a nonidentity fixed-line vector under the derived group gives two
distinct nonidentity commutators, which generate the four-element support.

This supplies the natural fixed-line and fixed-index calculation for the
actual omega modules in Stellmacher (6.3), journal p31, from the one-seven
factor data of (1.7)/(2.2); source refs/latex/stellmacher-n-group.tex.
-/

open scoped IsMulCommutative
namespace Stellmacher.SectionOne
universe u

private theorem support_sylow_fixed_card
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (T : Sylow 2 G) (D : Subgroup G) [D.Normal]
    (hD : IsOneSevenFactor (V := V) D)
    (hdisj : Disjoint (FixedPoints.subgroup ((commutator D).map D.subtype) V)
      (commutatorAction D V)) :
    Nat.card (↥(commutatorAction D V ⊓ FixedPoints.subgroup T V)) = 2 := by
  let M := commutatorAction D V
  let _ : IsInvariant (⊤ : Subgroup G) V M :=
    commutatorAction_isInvariant_of_normalizing_actor ⊤ D (by rw [Subgroup.normalizer_eq_top])
  let _ : IsInvariant G V M := ⟨fun g v =>
    IsInvariant.invariant (A := (⊤ : Subgroup G)) (H := M) ⟨g, Subgroup.mem_top g⟩ v⟩
  let _ : IsInvariant T V M := ⟨fun t v =>
    IsInvariant.invariant (A := G) (H := M) (t : G) v⟩
  have hMcard : Nat.card M = 4 := hD.2.2.1
  have hmap : Nat.card (↥(M ⊓ FixedPoints.subgroup T V)) =
      Nat.card (FixedPoints.subgroup T M) := by
    rw [← fixedPoints_subgroup_map_subtype_eq_inf M,
      Subgroup.card_map_of_injective M.subtype_injective]
  have hge : 2 ≤ Nat.card (FixedPoints.subgroup T M) := by
    have hp := T.isPGroup'.card_modEq_card_fixedPoints M
    change Nat.card M % 2 = Nat.card (FixedPoints.subgroup T M) % 2 at hp
    rw [hMcard] at hp
    have hpos : 0 < Nat.card (FixedPoints.subgroup T M) := Nat.card_pos
    omega
  have hnot : ¬ M ≤ FixedPoints.subgroup T V := by
    intro hfix
    let f := MulDistribMulAction.toMulAut G M
    have hTk : (T : Subgroup G) ≤ f.ker := by
      intro t ht
      rw [MonoidHom.mem_ker]
      ext v
      exact (hfix v.property) (⟨t, ht⟩ : T)
    have hNk : Subgroup.normalClosure (T : Set G) ≤ f.ker :=
      Subgroup.normalClosure_le_normal hTk
    have hDk : D ≤ f.ker := by
      intro d hd
      obtain ⟨a, b, ha, hb, hab⟩ := sl2_involution_products hD.1 (⟨d, hd⟩ : D)
      have hk (x : D) (hx : x ^ 2 = 1) : (x : G) ∈ f.ker := by
        have hxG : (x : G) ^ 2 = 1 := congrArg Subtype.val hx
        have hp := (IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) hxG).isPGroup 2 _
        exact hNk (hp.le_normalClosure_sylow T (Subgroup.mem_zpowers _))
      have heq : d = (a : G) * b := congrArg Subtype.val hab
      rw [heq]
      exact f.ker.mul_mem (hk a ha) (hk b hb)
    have hMbot : M = ⊥ := by
      apply le_bot_iff.mp
      intro v hv
      apply hdisj.le_bot
      refine ⟨?_, hv⟩
      intro a
      have hak := MonoidHom.mem_ker.mp (hDk ((Subgroup.map_subtype_le _) a.property))
      have he := DFunLike.congr_fun hak (⟨v, hv⟩ : M)
      exact congrArg Subtype.val he
    have hc := Subgroup.card_eq_one.mpr hMbot
    omega
  have hlt : Nat.card (↥(M ⊓ FixedPoints.subgroup T V)) < 4 := by
    have hle := Subgroup.card_le_of_le (inf_le_left : M ⊓ FixedPoints.subgroup T V ≤ M)
    rw [hMcard] at hle
    by_contra hn
    have heq := Subgroup.eq_of_le_of_card_ge
      (inf_le_left : M ⊓ FixedPoints.subgroup T V ≤ M) (by rw [hMcard]; omega)
    exact hnot (heq ▸ inf_le_right)
  have hdvd : Nat.card (↥(M ⊓ FixedPoints.subgroup T V)) ∣ 4 := by
    rw [← hMcard]
    exact Subgroup.card_dvd_of_le inf_le_left
  rw [hmap] at hlt hdvd ⊢
  interval_cases hc : Nat.card (FixedPoints.subgroup T M) <;> omega


private theorem three_action_commutator_eq_support
    {F V : Type u} [Group F] [Group V] [Finite F] [Finite V]
    [MulDistribMulAction F V] (M A : Subgroup V)
    (hF : Nat.card F = 3) (hM : Nat.card M = 4)
    (hcomm : commutatorAction F V ≤ M)
    (hdisj : Disjoint (FixedPoints.subgroup F V) M)
    (a : V) (haM : a ∈ M) (haA : a ∈ A) (hane : a ≠ 1) :
    commutatorSubgroup F V A = M := by
  classical
  have hnfix : ¬ a ∈ FixedPoints.subgroup F V := by
    intro ha
    exact hane (hdisj.le_bot ⟨ha, haM⟩)
  obtain ⟨f, hf⟩ : ∃ f : F, f • a ≠ a := by
    exact not_forall.mp hnfix
  have hf3 : f ^ 3 = 1 := by rw [← hF]; exact pow_card_eq_one' (x := f)
  have hf2 : f ^ 2 • a ≠ a := by
    intro hh
    apply hf
    calc
      f • a = f • (f ^ 2 • a) := by rw [hh]
      _ = f ^ 3 • a := by rw [← mul_smul]; congr 1; group
      _ = a := by rw [hf3, one_smul]
  have hdiff : f ^ 2 • a ≠ f • a := by
    intro hh
    apply hf
    have he := congrArg (fun v : V => f⁻¹ • v) hh
    simpa only [← mul_smul, pow_two, inv_mul_cancel_left, inv_mul_cancel, one_smul] using he
  let C := commutatorSubgroup F V A
  let b := a⁻¹ * (f • a)
  let c := a⁻¹ * (f ^ 2 • a)
  have hb : b ∈ C := Subgroup.subset_closure ⟨f, a, haA, rfl⟩
  have hc : c ∈ C := Subgroup.subset_closure ⟨f ^ 2, a, haA, rfl⟩
  have hbne : b ≠ 1 := by
    intro hh
    exact hf (inv_mul_eq_one.mp hh).symm
  have hcne : c ≠ 1 := by
    intro hh
    exact hf2 (inv_mul_eq_one.mp hh).symm
  have hbc : b ≠ c := by
    intro hh
    exact hdiff (mul_left_cancel hh).symm
  let e : Fin 3 → C := ![1, ⟨b, hb⟩, ⟨c, hc⟩]
  have hinj : Function.Injective e := by
    intro i j hij
    have he := congrArg Subtype.val hij
    clear hij
    fin_cases i <;> fin_cases j <;> simp_all [e]
  have hge : 3 ≤ Nat.card C := by
    simpa using Nat.card_le_card_of_injective e hinj
  have hCM : C ≤ M := (commutatorSubgroup_mono (A := F) le_top).trans hcomm
  have hdvd : Nat.card C ∣ 4 := by
    rw [← hM]
    exact Subgroup.card_dvd_of_le hCM
  have hle : Nat.card C ≤ 4 := Nat.le_of_dvd (by decide) hdvd
  have hcard : Nat.card C = 4 := by
    interval_cases h : Nat.card C <;> norm_num at *
  exact Subgroup.eq_of_le_of_card_ge hCM (by rw [hcard, hM])


public theorem oneSevenFactor_sylow_fixed_coordinate
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (T : Sylow 2 G) (D : Subgroup G) [D.Normal]
    (hD : IsOneSevenFactor (V := V) D) :
    let A := FixedPoints.subgroup T V
    let M := commutatorAction D V
    Nat.card (↥(M ⊓ A)) = 2 ∧
      (A ⊓ FixedPoints.subgroup D V).relIndex A = 2 ∧
      commutatorSubgroup ((commutator D).map D.subtype) V A = M := by
  let A := FixedPoints.subgroup T V
  let M := commutatorAction D V
  let F := (commutator D).map D.subtype
  let C := FixedPoints.subgroup D V
  have hCF : C = FixedPoints.subgroup F V := by
    apply le_antisymm
    · intro v hv f
      exact hv (⟨f, (Subgroup.map_subtype_le _) f.property⟩ : D)
    · intro v hv d
      exact oneSevenFactor_fixes_derived_fixedPoints D hD d d.property v hv
  have hcop : Nat.Coprime (Nat.card F) (Nat.card V) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [show Nat.card F = 3 from hD.2.1.2.1, hn]
    exact (show Nat.Coprime 3 2 by decide).pow_right n
  have hcompl : IsCompl C M := by
    rw [hCF]
    dsimp only [M]
    rw [oneSevenFactor_full_commutator_eq_derived D hD]
    exact isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := F)
      (Group.isSolvable_of_comm fun x y => (IsMulCommutative.is_comm (M := V)).comm x y)
      hcop (inferInstance : IsMulCommutative V)
  have hdisj : Disjoint (FixedPoints.subgroup F V) M := hCF ▸ hcompl.disjoint
  have hline : Nat.card (↥(M ⊓ A)) = 2 := support_sylow_fixed_card T D hD hdisj
  refine ⟨hline, ?_, ?_⟩
  · let _ : IsInvariant T V C :=
      fixedPoints_isInvariant_of_normalizing_actor T D (by rw [Subgroup.normalizer_eq_top]; exact le_top)
    let _ : IsInvariant T V M :=
      commutatorAction_isInvariant_of_normalizing_actor T D (by rw [Subgroup.normalizer_eq_top]; exact le_top)
    have hprod := RankOneThreeGroupAssembly.natCard_inf_fixedPoints_sup_eq_mul
      (A := T) C M hcompl.disjoint
    rw [hcompl.sup_eq_top, top_inf_eq] at hprod
    change Nat.card A = Nat.card (↥(C ⊓ A)) * Nat.card (↥(M ⊓ A)) at hprod
    rw [hline, inf_comm C A] at hprod
    have hidx := (A ⊓ C).subgroupOf A |>.index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : A ⊓ C ≤ A)).toEquiv] at hidx
    change (A ⊓ C).relIndex A * Nat.card (↥(A ⊓ C)) = Nat.card A at hidx
    have hpos : 0 < Nat.card (↥(A ⊓ C)) := Nat.card_pos
    change (A ⊓ C).relIndex A = 2
    nlinarith
  · have hne : M ⊓ A ≠ ⊥ := by
      intro hh
      have hc := Subgroup.card_eq_one.mpr hh
      omega
    obtain ⟨a, hane⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact three_action_commutator_eq_support M A hD.2.1.2.1 hD.2.2.1
      (oneSevenFactor_full_commutator_eq_derived D hD).symm.le hdisj (a : V) a.property.1 a.property.2 (fun hh => hane (Subtype.ext hh))

end Stellmacher.SectionOne
