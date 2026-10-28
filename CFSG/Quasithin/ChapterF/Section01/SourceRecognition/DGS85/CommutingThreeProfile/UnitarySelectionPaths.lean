module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.UnitarySelectionLayer
public import Theory.SpecificGroups.SU3.EvenTwoRank
public import Theory.Quasithin.CoprimeRank
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearIntersectionTransitivity

/-!
# Remote-core indices in the unitary selection branch

An elementary subgroup of a genuine SL₂(q), SU₃(q), or PSU₃(q) quotient
has order at most q. In the special unitary case, the scalar kernel is
of odd order, so passage to the projective carrier preserves two-rank.
Transport an actual edge to the base edge, keeping the original quotient
and core maps, to bound the index lost by an elementary subgroup at one
further vertex. Iterating along a walk bounds that index by q to its length.

Apply this to V_y, which lies in every neighboring core. The length-four
and length-two tails on printed p.182 give the required q⁴ and q² bounds.
Only the original linear/unitary markings, common-Sylow placements and
b > 2 are used. No remote index or path-fixer conclusion is assumed.
UnitarySelectionCentralizer combines these bounds with the constructed
q⁷ span to select the nonidentity element used in (12.5).

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.5), printed p.182, using the earlier (12.1) common-Sylow data.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem unitary_elementary_card_le {A : Type*} [Group A] [Finite A]
    {n : ℕ} (hn : 0 < n)
    (hu : ClassicalGroup.IsPSU A 3 (2^n) ∨ IsSU A 3 (2^n))
    (E : Subgroup A) [IsElementaryAbelian 2 E] : Nat.card E ≤ 2^n := by
  have hr : primeRank 2 A ≤ n := by
    rcases hu with hu | hu
    · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
      let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
        Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
      rw [primeRank_equiv 2 e]
      exact (HermitianForm.EvenTwoRank.two_rank J hn hK hconj).le
    · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
      let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
        Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
      have hk : IsPGroup 3 J.specialToProjective.ker :=
        fun x => ⟨1,by simpa only [pow_one] using J.specialToProjective_ker_cube x⟩
      obtain ⟨r,hr⟩ := hk.exists_card_eq
      have hp : Nat.Coprime 2 (Nat.card J.specialToProjective.ker) := by
        rw [hr]
        exact (by decide : Nat.Coprime 2 3).pow_right r
      rw [primeRank_equiv 2 e,
        primeRank_eq_of_surjective_of_coprime 2 J.specialToProjective J.specialToProjective_surjective hp]
      exact (HermitianForm.EvenTwoRank.two_rank J hn hK hconj).le
  exact (primeRank_le_iff_elementary_card_le A).mp hr E inferInstance

private theorem linear_elementary_card_le {k A : Type*} [Field k] [Finite k] [CharP k 2]
    [Group A] [Finite A] (e : A ≃* SL(2,k))
    (E : Subgroup A) [IsElementaryAbelian 2 E] : Nat.card E ≤ Nat.card k := by
  let D := E.map e.toMonoidHom
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map e.toMonoidHom
  obtain ⟨T,hT⟩ := (IsElementaryAbelian.isPGroup (p := 2) (G := D)).exists_le_sylow
  calc Nat.card E = Nat.card D := (card_map_of_injective e.injective).symm
       _ ≤ Nat.card T := Nat.card_le_card_of_injective (inclusion hT) (inclusion_injective _)
       _ = Nat.card k := (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 T).toEquiv).symm

private theorem elementary_neighbor_index
    (h : HypothesisF11 L S) {q : ℕ}
    (hplace : ∀ j, Q (reducedFamily L S) (base (reducedFamily L S) (!j)) ≤ star L S j)
    (hmodel : ∀ j : Bool, ∀ E : Subgroup
      (L (if j then 1 else 0) ⧸ pCore 2 (L (if j then 1 else 0))),
      IsElementaryAbelian 2 E → Nat.card E ≤ q)
    {v w : Vertex (reducedFamily L S)} (hvw : (graph (reducedFamily L S)).Adj v w)
    (E : Subgroup (G₀ L S)) [IsElementaryAbelian 2 E]
    (hE : E ≤ Q (reducedFamily L S) v) :
    (Q (reducedFamily L S) w).relIndex E ≤ q := by
  let F := reducedFamily L S
  let j := w.type
  have hvtype : v.type = !j := Bool.eq_not_iff.mpr hvw.1
  obtain ⟨g,hgv,hgw⟩ := incident_common_translate F hvw.2
  rw [hvtype] at hgv
  let c := (MulAut.conj g⁻¹).toMonoidHom
  let D := E.map c
  let A := star L S j
  let f := (originalQuotient h j).symm.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hv : g⁻¹ • v = base F (!j) := by rw [←hgv,inv_smul_smul]
  have hw : g⁻¹ • w = base F j := by rw [←hgw,inv_smul_smul]
  have hDQ : D ≤ Q F (base F (!j)) := by
    have hh := map_mono (f := c) hE
    change D ≤ (Q F v).map (MulAut.conj g⁻¹).toMonoidHom at hh
    rwa [←Q_translate F,hv] at hh
  have hDA : D ≤ A := hDQ.trans (hplace j)
  have hk : f.ker = (Q F (base F j)).subgroupOf A := by
    rw [MonoidHom.ker_comp_of_injective _ _ (originalQuotient h j).symm.injective,
      QuotientGroup.ker_mk',←star_core h j]
    exact (comap_map_eq_self_of_injective A.subtype_injective _).symm
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map c
  let : IsElementaryAbelian 2 (D.subgroupOf A) := IsElementaryAbelian.subgroupOf hDA
  let : IsElementaryAbelian 2 ((D.subgroupOf A).map f) := IsElementaryAbelian.map f
  have hi : (Q F w).relIndex E = Nat.card ((D.subgroupOf A).map f) := by
    rw [←relIndex_map_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (Q F w) E (MulAut.conj g⁻¹).injective,
      ←Q_translate F,hw]
    change (Q F (base F j)).relIndex D = _
    rw [←relIndex_subgroupOf hDA,←hk,relIndex_ker]
  rw [hi]
  exact hmodel j _ inferInstance

private theorem elementary_path_index
    (h : HypothesisF11 L S) {q : ℕ}
    (hplace : ∀ j, Q (reducedFamily L S) (base (reducedFamily L S) (!j)) ≤ star L S j)
    (hmodel : ∀ j : Bool, ∀ E : Subgroup
      (L (if j then 1 else 0) ⧸ pCore 2 (L (if j then 1 else 0))),
      IsElementaryAbelian 2 E → Nat.card E ≤ q)
    {v w : Vertex (reducedFamily L S)} (p : (graph (reducedFamily L S)).Walk v w)
    (E : Subgroup (G₀ L S)) [IsElementaryAbelian 2 E]
    (hE : E ≤ Q (reducedFamily L S) v) :
    (Q (reducedFamily L S) w).relIndex E ≤ q^p.length := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  induction p generalizing E with
  | nil => simp only [SimpleGraph.Walk.length_nil,pow_zero,relIndex_eq_one.mpr hE,le_refl]
  | @cons v u w hvu p ih =>
    let D := E ⊓ Q F u
    let : Finite E := Finite.of_injective (inclusion (hE.trans (Q_le_stabilizer F v)))
      (inclusion_injective _)
    let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_injective
      (inclusion (show D ≤ E from inf_le_left)) (inclusion_injective _)
    have hi := ih D (show D ≤ Q F u from inf_le_right)
    have hj := elementary_neighbor_index h hplace hmodel hvu E hE
    have hh := relIndex_inf_mul_relIndex (Q F w) (Q F u) E
    rw [inf_comm (Q F u) E] at hh
    calc
      (Q F w).relIndex E ≤ (Q F w ⊓ Q F u).relIndex E :=
        relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite
      _ = (Q F w).relIndex D * (Q F u).relIndex E := hh.symm
      _ ≤ q^p.length*q := Nat.mul_le_mul hi hj
      _ = q^(SimpleGraph.Walk.cons hvu p).length := by rw [SimpleGraph.Walk.length_cons,pow_succ]

/-- Along any actual walk from a neighbor of y, the elementary center span
loses at most one field factor per further edge. Both original quotient markings
and their common-Sylow placements supply the bound. -/
theorem source_unitary_span_path_index
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {n : ℕ} (hn : 0 < n) (hfield : Nat.card k = 2^n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (hu : ClassicalGroup.IsPSU (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) 3 (2^n) ∨
      IsSU (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) 3 (2^n))
    (T : Sylow 2 (star L S i)) (R : Sylow 2 (star L S (!i)))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    {u z : Vertex (reducedFamily L S)}
    (hyu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) u)
    (p : (graph (reducedFamily L S)).Walk u z) :
    (Q (reducedFamily L S) z).relIndex (V (reducedFamily L S) (base (reducedFamily L S) i) 1) ≤ (2^n)^p.length := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : ∀ j, Finite (L j) := h.finite_local
  let := V_elementary F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb (base F i)
  have hp : ∀ j, Q F (base F (!j)) ≤ star L S j := by
    intro j
    by_cases hj : j=i
    · subst j; exact (le_sup_left.trans hT.ge).trans (map_subtype_le _)
    · have hj : j = !i := Bool.eq_not_iff.mpr hj
      subst j
      simpa only [Bool.not_not] using (le_sup_left.trans hR.ge).trans (map_subtype_le _)
  have hm : ∀ j : Bool, ∀ E : Subgroup
      (L (if j then 1 else 0) ⧸ pCore 2 (L (if j then 1 else 0))),
      IsElementaryAbelian 2 E → Nat.card E ≤ 2^n := by
    intro j E hE
    let := hE
    by_cases hj : j=i
    · subst j; exact unitary_elementary_card_le hn hu E
    · have hj : j = !i := Bool.eq_not_iff.mpr hj
      subst j
      exact (linear_elementary_card_le eLin E).trans_eq hfield
  exact elementary_path_index h hp hm p _
    (V_le_neighbor_Q F (reduced_triple h).generate
      (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb hyu)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
