module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.SylowModels.ModelFacts
public import CFSG.Quasithin.Chapter16.Section03.Basic
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismOrder
public import Theory.SpecificGroups.SU3.BinarySylowOrder
public import Theory.SpecificGroups.SU3.ProjectiveGraphFixed
public import Theory.SpecificGroups.SU3.GraphFixedSylowCenters
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# The unitary calculation in 16.3.4: order and embedding reductions

For q = 2ⁿ the full automorphism group of PSL₂(q) has two-part at most qn,
whereas the explicit root group in PSU₃(q) has order q³. This proves the strict
Sylow-order gap. If the earlier graph-involution clause identifies the actual
ambient conjugation on K with entrywise conjugation on its full projective
unitary model, the image of L is the entire fixed group: containment follows
from the component hypothesis and equality follows from the PSL₂ orders.

The embedding transport carries intrinsic whole-center equalities back into G.
The intrinsic root-group calculation proves that every Sylow subgroup of the
graph-fixed group is the whole center of a Sylow subgroup of the projective
unitary group.

Source: Aschbacher–Smith, 16.1.3–4 and 16.1.7(c), printed pp.1171–1172,
and the proof of 16.3.4, printed p.1178 / PDF p.1195.
-/

namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
open Subgroup BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm
variable {G : Type*} [Group G] [Finite G] {L K : Subgroup G}

/-- The concrete graph-action clause of the earlier 16.1.4/16.1.7 tables.
The field has order q² and its stored conjugation is the q-th power map.
The final equation ties the model action to the actual ambient involution.
This is an input specification, not an automorphism-classification theorem. -/
@[expose] public def UnitaryGraphAction (K : Subgroup G) (i : G) (n : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (J : HermitianForm 3 F)
      (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
      (e : K ≃* ProjectiveSpecialUnitaryMatrixGroup J),
    Nat.card F = (2 ^ n) ^ 2 ∧ (∀ x, J.conj x = x ^ (2 ^ n)) ∧
      ∀ x : K, ((e.symm (projectiveGraphAut J hJ (e x)) : K) : G) = i * x * i⁻¹

/-- The strict comparison in 16.3.4 for the two full classical-group models. -/
public theorem unitary_sylowOrderGap {n : ℕ} (hn : 2 ≤ n)
    (hK : ClassicalGroup.IsPSU K 3 (2 ^ n))
    (hL : ClassicalGroup.IsPSL L 2 (2 ^ n)) : SylowOrderGap L K := by
  rcases hL with ⟨F, hF, hfinF, hcardF, ⟨eL⟩⟩
  rcases hK with ⟨E, hE, hfinE, J, hcardE, hconj, ⟨eK⟩⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hcardF)
  intro A S
  let A' := A.mapSurjective (f := (MulAut.congr eL).toMonoidHom) (MulAut.congr eL).surjective
  have hA : Nat.card A ≤ 2 ^ n * n := by
    have he : Nat.card A = Nat.card A' :=
      Nat.card_congr ((MulAut.congr eL).subgroupMap (A : Subgroup _)).toEquiv
    rw [he]
    exact Theory.PSL2.BinaryAutomorphismOrder.sylow_aut_card_le (by omega) hcardF A'
  have hS : (2 ^ n) ^ 3 ≤ Nat.card S := by
    apply Nat.le_of_dvd Nat.card_pos
    rw [← pow_mul]
    apply S.pow_dvd_card_of_pow_dvd_card
    rw [Nat.card_congr eK.toEquiv, pow_mul]
    exact BinarySylowOrder.cube_dvd_card_projective J (by omega) hcardE hconj
  apply lt_of_le_of_lt hA
  apply lt_of_lt_of_le _ hS
  have hq : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
  calc
    2 ^ n * n < 2 ^ n * 2 ^ n := Nat.mul_lt_mul_of_pos_left n.lt_two_pow_self (by positivity)
    _ ≤ (2 ^ n) ^ 3 := by nlinarith

private theorem psl_card {X : Type*} [Group X] {n : ℕ}
    (h : ClassicalGroup.IsPSL X 2 (2 ^ n)) :
    Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  rcases h with ⟨F, hF, hfin, hc, ⟨e⟩⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hc)
  rw [Nat.card_congr e.toEquiv,
    ← Nat.card_congr (BenderSuzuki.ZD.Linear.sl2QuotientEquiv F).toEquiv,
    BenderSuzuki.External.huppert614_card_specialLinearGroup, hc]

omit [Finite G] in
/-- The actual graph action identifies the embedded L with the entire fixed group.
The action formula is the earlier 16.1.4/16.1.7 graph clause; the subgroup
equality is proved here from containment and the two full group orders. -/
public theorem unitary_graph_image_eq_fixed {T : Sylow 2 G} {z t i : G}
    (h : ExclusionSetup T z L K t i) {n : ℕ}
    (hL : ClassicalGroup.IsPSL L 2 (2 ^ n))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (J : HermitianForm 3 F)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hfixed : Nat.card {x : F // J.conj x = x} = 2 ^ n)
    (e : K ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hgraph : ∀ x : K,
      ((e.symm (projectiveGraphAut J hJ (e x)) : K) : G) = i * x * i⁻¹) :
    (L.subgroupOf K).map e.toMonoidHom = (projectiveGraphAut J hJ).fixedSubgroup := by
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hLK : L ≤ K := h.componentL.1.trans inf_le_left
  have hle : (L.subgroupOf K).map e.toMonoidHom ≤ (projectiveGraphAut J hJ).fixedSubgroup := by
    rintro _ ⟨x, hx, rfl⟩
    rw [MulAut.mem_fixedSubgroup]
    apply e.symm.injective
    apply Subtype.ext
    change ((e.symm (projectiveGraphAut J hJ (e x)) : K) : G) = (e.symm (e x) : G)
    rw [hgraph, e.symm_apply_apply]
    have hxi := mem_centralizer_singleton_iff.mp (h.componentL.1 hx).2
    change (x : G) * i = i * (x : G) at hxi
    rw [← hxi, mul_inv_cancel_right]
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [Subgroup.card_map_of_injective e.injective,
    Nat.card_congr (subgroupOfEquivOfLe hLK).toEquiv, psl_card hL]
  rw [Nat.card_congr (projectiveGraphFixedEquiv J hJ).toEquiv,
    ← Nat.card_congr (BenderSuzuki.ZD.Linear.sl2QuotientEquiv (FixedBy.subfield F J.conj)).toEquiv,
    BenderSuzuki.External.huppert614_card_specialLinearGroup]
  change Nat.card {x : F // J.conj x = x} *
    (Nat.card {x : F // J.conj x = x} ^ 2 - 1) ≤ _
  rw [hfixed]

/-- Transport an intrinsic Sylow-center calculation through an actual embedding.
This is conditional: the concrete calculation `hcenters` remains to be proved. -/
public theorem fullSylowCenterLifting_of_model {B : Type*} [Group B] {W : Subgroup B}
    (hLK : L ≤ K) (e : K ≃* B) (hW : (L.subgroupOf K).map e.toMonoidHom = W)
    (hcenters : ∀ P : Sylow 2 W, ∃ S : Sylow 2 B,
      (center S).map (S : Subgroup B).subtype = (P : Subgroup W).map W.subtype) :
    FullSylowCenterLifting L K := by
  let : Finite B := Finite.of_equiv K e.toEquiv
  let eL : L ≃* W := (subgroupOfEquivOfLe hLK).symm.trans
    ((e.subgroupMap (L.subgroupOf K)).trans (MulEquiv.subgroupCongr hW))
  let f : B →* G := K.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := K.subtype_injective.comp e.symm.injective
  intro P
  let P' := P.mapSurjective (f := eL.toMonoidHom) eL.surjective
  obtain ⟨S, hS⟩ := hcenters P'
  refine ⟨S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective, ?_⟩
  change (center (((S : Subgroup B).map e.symm.toMonoidHom).map K.subtype)).map
      (((S : Subgroup B).map e.symm.toMonoidHom).map K.subtype).subtype = _
  rw [Subgroup.map_map, ← Subgroup.map_embeddedCenter _ f hf, hS]
  change (((P : Subgroup L).map eL.toMonoidHom).map W.subtype).map f = _
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  change ((e.symm (e (⟨x, hLK x.property⟩ : K)) : K) : G) = x
  rw [e.symm_apply_apply]

/-- Unitary assembly from the earlier graph-action clause and the intrinsic
whole-center calculation for the projective unitary model. -/
public theorem unitary_calculation_of_graph_centers
    {T : Sylow 2 G} {z t i : G} {n : ℕ}
    (h : ExclusionSetup T z L K t i) (hn : 2 ≤ n)
    (hK : ClassicalGroup.IsPSU K 3 (2 ^ n))
    (hL : ClassicalGroup.IsPSL L 2 (2 ^ n))
    (graph_1617 : UnitaryGraphAction K i n) :
    FullSylowCenterLifting L K ∧ SylowOrderGap L K := by
  refine ⟨?_, unitary_sylowOrderGap hn hK hL⟩
  rcases graph_1617 with ⟨F, hF, hfin, J, hJ, e, hcard, hconj, hgraph⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa only [Nat.card_eq_fintype_card, pow_mul] using hcard)
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  exact fullSylowCenterLifting_of_model (h.componentL.1.trans inf_le_left) e
    (unitary_graph_image_eq_fixed h hL J hJ hfixed e hgraph)
    (by
      intro P
      exact BenderSuzuki.MatrixGroups.HermitianForm.GraphFixedSylowCenters.exists_sylow_center_eq
        J hJ hn hcard hfixed P)

end CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
