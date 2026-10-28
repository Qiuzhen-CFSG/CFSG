module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank.PurePlane

/-!
# The low-rank first-stage offender contradiction

The pure plane in the corank-two core normalizes the actual conjugate and
acts faithfully on it. Lifting the rank-two inner actor inside the original
offender gives a subspace of the conjugate of corank at most two, centralized
by that plane. The small-fixed-codimension bound permits image rank at most
one, contradicting the faithful plane. This closes the degree-four rank-three
branch; degree five was already excluded by the inner-rank bound.
Source: Aschbacher--Smith, 12.1.8, printed pp.792--793 (PDF809--810).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender BinaryNaturalDual
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterH.NaturalDual
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (B : DoubledBranch T L V 4)
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

theorem four_first_low_rank_false (M : B.MarkedAutomizerModel)
    (hp : B.PureIntersectionCentralizes) {g : G}
    (C : ConjugateConfiguration (componentOrbit V (T : Subgroup G)) g 1 4)
    (hr : rank (inducedAutomizer (componentOrbit V (T : Subgroup G))
      (offenderNormalizer (componentOrbit V (T : Subgroup G)) g)) = 3) : False := by
  let W := componentOrbit V (T : Subgroup G)
  let Wg := W.map (MulAut.conj g).toMonoidHom
  let A := offenderNormalizer W g
  let I := inducedAutomizer W A
  let J := I ⊓ componentLayer (Automizer W)
  let : IsElementaryAbelian 2 Wg := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ Wg from inf_le_left)
  let := offender_inducedAutomizer_elementary W g
  have hprof := first_low_rank_profile B M hp C hr
  have hj : rank J = 2 := hprof.2.1
  have hout : ¬ I ≤ componentLayer (Automizer W) := hprof.2.2
  obtain ⟨P,hPn,hPc,hPf,hPd,hPz⟩ := four_low_pure_plane M.setup I hr hj hout
    (first_core_restrictions B M hp C).1
  let D : Subgroup G := P.toAddSubgroup.toSubgroup'.map W.subtype
  have hDW : D ≤ W := Subgroup.map_subtype_le _
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le hDW
  have hmem (v : Additive W) : (v.toMul : G) ∈ D ↔ v ∈ P := by
    constructor
    · rintro ⟨u,hu,he⟩
      have hu' : u = v.toMul := Subtype.ext he
      rw [hu'] at hu
      exact hu
    · intro hv
      exact ⟨v.toMul,hv,rfl⟩
  have hDN : D ≤ normalizer (Wg : Set G) := by
    intro d hd
    let v : Additive W := Additive.ofMul ⟨d,hDW hd⟩
    have hv := hPc ((hmem v).mp hd)
    rw [M.representation_eq] at hv
    exact (C.core_le 2 (by decide) ((ZeroClosure.mem_core_iff I 2 v).mpr hv)).2
  have hfaith : D ⊓ centralizer (Wg : Set G) = ⊥ := by
    apply bot_unique
    intro d hd
    let v : Additive W := Additive.ofMul ⟨d,hDW hd.1⟩
    have hvP := (hmem v).mp hd.1
    have hvF : v ∈ M.setup.fixed I := by
      change v ∈ fixedSpace M.setup.representation I
      rw [M.representation_eq]
      apply (mem_fixedSpace_inducedAutomizer W A inf_le_right v).mpr
      exact centralizer_le (show (A : Set G) ⊆ Wg from inf_le_left) hd.2
    have hv0 : v = 0 := by
      have hv : v ∈ P ⊓ M.setup.fixed I := ⟨hvP,hvF⟩
      rwa [hPz] at hv
    change d = 1
    exact congrArg (fun u : Additive W => (u.toMul : G)) hv0
  have hDr : 2 ≤ rank D := by
    let e : P ≃ D := {
      toFun := fun v => ⟨v.val.toMul,(hmem v.val).mpr v.property⟩
      invFun := fun d => ⟨Additive.ofMul ⟨d.val,hDW d.property⟩,(hmem _).mp d.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    rw [rank,← Nat.card_congr e,Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod,Nat.log_pow (by decide)]
    exact hPd
  obtain ⟨K,hKA,hKI,hKcor⟩ := core_lift_image_subgroup
    (show A ≤ normalizer (W : Set G) from inf_le_right) J inf_le_left
  have hKN : K ≤ normalizer (W : Set G) := hKA.trans inf_le_right
  have hKWg : K ≤ Wg := hKA.trans inf_le_left
  have hDCK : D ≤ centralizer (K : Set G) := by
    intro d hd
    let v : Additive W := Additive.ofMul ⟨d,hDW hd⟩
    apply (mem_fixedSpace_inducedAutomizer W K hKN v).mp
    rw [hKI,← M.representation_eq]
    exact hPf ((hmem v).mp hd)
  have hKCD : K ≤ Wg ⊓ centralizer (D : Set G) :=
    le_inf hKWg (le_centralizer_iff.mp hDCK)
  have hcor1 : subgroupCorank A K ≤ 1 := by
    have hh := rank_add_corank (show J ≤ I from inf_le_left)
    change rank I = 3 at hr
    change subgroupCorank A K = subgroupCorank I J at hKcor
    omega
  have hcor2 : subgroupCorank Wg K ≤ 2 := by
    have hh := offender_corank_add hKA (show A ≤ Wg from inf_le_left)
    have hc : subgroupCorank Wg A = 1 := C.corank
    omega
  have hc : subgroupCorank Wg (Wg ⊓ centralizer (D : Set G)) ≤ 2 := by
    have hh := offender_corank_add hKCD
      (show Wg ⊓ centralizer (D : Set G) ≤ Wg from inf_le_left)
    omega
  have hb := reverse_small_fixedCodim M.setup M.representation_eq g D hDN hc
  rw [rank_inducedAutomizer Wg D hDN,hfaith,subgroupCorank,Subgroup.relIndex_bot_left] at hb
  change rank D ≤ 1 at hb
  exact (by omega : False)

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank
