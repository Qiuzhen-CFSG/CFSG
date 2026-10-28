module
public import Theory.GroupTheory.MinusExtraspecialA5Fusion.Calculation
public import Theory.SpecificGroups.Alternating.SmallInvolutionCentralizers
public import Theory.SpecificGroups.MinusExtraspecial.CentralStructure
public import Theory.SpecificGroups.MinusExtraspecial.Factors
public import Theory.GroupTheory.QuaternionDihedralInvolutionCosets
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
import all Theory.SpecificGroups.MinusExtraspecial.ModelFixedFour

/-!
# Vanishing of involution cocycles in the minus extraspecial model

The five representatives 8, 16, 25, 28 and 29 in the established bit
coordinates give an actual equivalence with the intrinsic nonidentity
central involution cosets. Transporting their action gives a homomorphism
into S₅ whose kernel is precisely the inner automorphisms. A nonidentity
even involution moves four points, so the finite cocycle calculation applies.

The `import all` deliberately reuses the private coordinate conversion proofs
from `ModelFixedFour`, as an internal computational proof dependency. None of
those private coordinates occurs in the public group-theoretic interface.

Source: Aschbacher, *Sporadic Groups* (1994), 46.11, printed p.255.
-/

open Subgroup
namespace MinusExtraspecial.FixedFourCalculation.Outside

def rep : Fin 5 → B := ![8,16,25,28,29]

theorem rep_sq (i : Fin 5) : decode (rep i) ^ 2 = 1 := by revert i; decide +kernel

theorem rep_noncentral (i : Fin 5) : decode (rep i) ∉ center Model := by
  rw [MinusExtraspecial.mem_center_iff]
  revert i
  decide +kernel

def point (i : Fin 5) : CentralInvolutionCosets Model :=
  centralInvolutionCoset (decode (rep i)) (rep_sq i) (rep_noncentral i)

theorem coset_eq (x : B) (i : Fin 5) :
    QuotientGroup.mk' (center Model) (decode x) = (point i).val ↔ x &&& 29 = rep i := by
  change QuotientGroup.mk' (center Model) (decode x) =
    QuotientGroup.mk' (center Model) (decode (rep i)) ↔ _
  change (QuotientGroup.mk (decode x) : Model ⧸ center Model) =
    QuotientGroup.mk (decode (rep i)) ↔ _
  rw [QuotientGroup.eq, MinusExtraspecial.mem_center_iff]
  revert x i
  decide +kernel

theorem point_injective : Function.Injective point := by
  intro i j h
  have he := (coset_eq (rep i) j).mp (congrArg Subtype.val h)
  exact (show ∀ i j : Fin 5, rep i &&& 29 = rep j → i = j by decide +kernel) i j he

theorem point_surjective : Function.Surjective point := by
  intro v
  obtain ⟨x, hx, he⟩ := v.property.2
  have hn : x ∉ center Model := by
    intro hn
    exact v.property.1 (he.symm.trans ((QuotientGroup.eq_one_iff x).mpr hn))
  have hc : ∀ x : Model, x ^ 2 = 1 → (x ≠ 1 ∧ x ≠ quaternion z) →
      ∃ i : Fin 5, encode x &&& 29 = rep i := by decide +kernel
  obtain ⟨i, hi⟩ := hc x hx (by simpa only [MinusExtraspecial.mem_center_iff, not_or] using hn)
  refine ⟨i, Subtype.ext ?_⟩
  have hh := (coset_eq (encode x) i).mpr hi
  rw [decode_encode] at hh
  exact hh.symm.trans he

noncomputable def pointEquiv : Fin 5 ≃ CentralInvolutionCosets Model :=
  Equiv.ofBijective point ⟨point_injective, point_surjective⟩

public noncomputable def fivePointAction : MulAut Model →* Equiv.Perm (Fin 5) :=
  pointEquiv.symm.permCongrHom.toMonoidHom.comp centralInvolutionCosetAction

theorem action_eq_iff (a : MulAut Model) (i j : Fin 5) :
    fivePointAction a i = j ↔ encode (a (decode (rep i))) &&& 29 = rep j := by
  change pointEquiv.symm (centralInvolutionCosetAction a (pointEquiv i)) = j ↔ _
  rw [Equiv.symm_apply_eq]
  change centralInvolutionCosetAction a (point i) = point j ↔ _
  have he : centralInvolutionCosetAction a (point i) = point j ↔
      (centralInvolutionCosetAction a (point i)).val = (point j).val :=
    ⟨congrArg Subtype.val, Subtype.ext⟩
  rw [he, centralInvolutionCosetAction_val]
  change quotientAut (center Model) a (QuotientGroup.mk' (center Model) (decode (rep i))) = _ ↔ _
  rw [quotientAut_apply_mk, ← decode_encode (a (decode (rep i))), coset_eq, decode_encode]

public theorem action_kernel : fivePointAction.ker =
    (MulAut.conj : Model →* MulAut Model).range := by
  obtain ⟨B, C, hB, hC, hcomm, hgen⟩ := factors_of_equiv (MulEquiv.refl Model)
  have hk := quaternion_dihedral_central_involution_coset_kernel B C hB hC hcomm hgen
  rw [← IsExtraspecial.quotientAut_center_ker_eq_range_conj (p := 2), ← hk]
  ext a
  change pointEquiv.symm.permCongrHom (centralInvolutionCosetAction a) = 1 ↔
    centralInvolutionCosetAction a = 1
  exact pointEquiv.symm.permCongrHom.map_eq_one_iff

theorem moved_eq (a : MulAut Model) :
    moved (encode (a (generators 0))) (encode (a (generators 1)))
      (encode (a (generators 2))) (encode (a (generators 3))) =
        (fivePointAction a).support.card := by
  let idx : List (Fin 5) := [0,1,2,3,4]
  have hall : points = idx.map rep := by decide +kernel
  have hw (x : B) : word (encode (a (generators 0))) (encode (a (generators 1)))
      (encode (a (generators 2))) (encode (a (generators 3))) x =
        encode (a (decode x)) := by
    rw [← decode_word a x, encode_decode]
  have hp : (fun i : Fin 5 =>
      (word (encode (a (generators 0))) (encode (a (generators 1)))
        (encode (a (generators 2))) (encode (a (generators 3))) (rep i) &&& 29) != rep i) =
      (fun i : Fin 5 => decide (fivePointAction a i ≠ i)) := by
    funext i
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne, decide_eq_true_eq, hw]
    exact (not_congr (action_eq_iff a i i)).symm
  have he : (fivePointAction a).support = idx.toFinset.filter
      (fun i => fivePointAction a i ≠ i) := by
    have hi : idx.toFinset = Finset.univ := by decide +kernel
    rw [hi]
    ext i
    simp only [Equiv.Perm.mem_support, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [moved, hall, List.countP_map]
  dsimp only [Function.comp_def]
  rw [hp, he,
    List.Nodup.card_eq_countP (show idx.Nodup by decide +kernel)]

/-- Every twisted cocycle for an involutive automorphism inducing a nonidentity
 even permutation on the five singular points is a coboundary. -/
public theorem cocycle_eq_coboundary (a : MulAut Model) (ha : a ^ 2 = 1)
    (heven : Equiv.Perm.sign (fivePointAction a) = 1)
    (hne : fivePointAction a ≠ 1) (d : Model) (hd : d * a d = 1) :
    ∃ q : Model, d = q * (a q)⁻¹ := by
  let ap : alternatingGroup (Fin 5) := ⟨fivePointAction a, heven⟩
  have hap : orderOf ap = 2 := orderOf_eq_prime
    (Subtype.ext (by change fivePointAction a ^ 2 = 1; rw [← map_pow, ha, map_one]))
    (fun hh => hne (congrArg Subtype.val hh))
  have hs : (fivePointAction a).support.card = 4 := by
    rw [← Equiv.Perm.sum_cycleType,
      alternatingGroup.involution_cycleType_of_degree_le_six (by decide) ap hap]
    rfl
  have hr := relations_aut a
  simp only [relations, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, and_assoc] at hr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hr
  have hi : invol (encode (a (generators 0))) (encode (a (generators 1)))
      (encode (a (generators 2))) (encode (a (generators 3))) := by
    apply List.all_eq_true.mpr
    intro g _
    apply beq_iff_eq.mpr
    apply equiv.injective
    change decode (word _ _ _ _ (word _ _ _ _ g)) = decode g
    rw [decode_word, decode_word]
    have hh := congrArg (fun b : MulAut Model => b (decode g)) ha
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using hh
  have hm := (moved_eq a).trans hs
  have hd' : mul (encode d)
      (word (encode (a (generators 0))) (encode (a (generators 1)))
        (encode (a (generators 2))) (encode (a (generators 3))) (encode d)) = 0 := by
    apply equiv.injective
    change decode (mul _ _) = decode 0
    rw [decode_mul, decode_word, decode_encode, decode_zero]
    exact hd
  obtain ⟨q, hq⟩ := calculation_all (encode (a (generators 0))) h1 _ h2 h3 _ h4 h5 h6
    _ h7 h8 h9 h10 hi hm (encode d) hd'
  refine ⟨decode q, ?_⟩
  have hh := congrArg decode hq
  simpa only [decode_encode, decode_mul, decode_inv, decode_word] using hh
end MinusExtraspecial.FixedFourCalculation.Outside
