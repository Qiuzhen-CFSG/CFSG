module
public import Theory.SpecificGroups.SU3.BorelElementary
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiIndices
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiIndices

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSpanFixedIndex
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSpanFixedIndex

/-!
# The full unitary omega image of the original neighbor span

In the contrary unitary case of DGS (12.5), a critical center makes V_x
escape the opposite core. The original full edge complement can be chosen
to fix x. Its restriction, together with the quotient Sylow, normalizes the
literal elementary image of V_x. Unitary Borel invariance therefore makes
that image the entire Sylow omega, of order q. The canonical quotient
kernel gives the exact first index of (12.3)(a). An actual linear neighbor
exchange reverses this index without assuming a second critical pair.

Both SU₃ and PSU₃ markings and the inclusion in the original completion
are retained. UnitaryCentralizerOmega applies the reversed index to the
same selected involution; the ensuing centralizer transitivity and final
unitary exclusion remain separate mathematical steps in this family.
The implementation imports reuse proved local complement and neighbor
exchange lemmas without changing their public boundaries.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(5.9)(b), (12.3)(a) and (12.5), printed pp.110,179,182.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem unitary_sylow_omega {A : Type*} [Group A] [Finite A]
    {n : ℕ} (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU A 3 (2^n) ∨ IsSU A 3 (2^n)) (T : Sylow 2 A) :
    omegaOneAmbient (T : Subgroup A) = (center T).map (T : Subgroup A).subtype ∧
    IsElementaryAbelian 2 (omegaOneAmbient (T : Subgroup A)) ∧
    Nat.card (omegaOneAmbient (T : Subgroup A)) = 2^n := by
  rcases hu with hu | hu
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hK hconj
    obtain ⟨C,hC⟩ := exists_standard_basis J (2^n) hK hf
    exact HermitianForm.SylowOmega.omega_of_projective_equiv (standardForm J) hn hK hf rfl
      (e.trans (projectiveEquiv J C hC)) T
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hK hconj
    obtain ⟨C,hC⟩ := exists_standard_basis J (2^n) hK hf
    exact HermitianForm.SylowOmega.omega_of_special_equiv (standardForm J) hn hK hf rfl
      (e.trans (specialEquiv J C hC)) T

private theorem unitary_borel_elementary {A : Type*} [Group A] [Finite A]
    {n : ℕ} (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU A 3 (2^n) ∨ IsSU A 3 (2^n))
    (T : Sylow 2 A) (D : Subgroup A) [IsElementaryAbelian 2 D]
    (hDT : D ≤ T) (hne : D ≠ ⊥)
    (hnorm : normalizer (T : Set A) ≤ normalizer (D : Set A)) :
    D = omegaOneAmbient (T : Subgroup A) ∧ Nat.card D = 2^n := by
  rcases hu with hu | hu
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    exact HermitianForm.BorelElementary.of_projective_equiv J hn hK hconj e T D hDT hne hnorm
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    exact HermitianForm.BorelElementary.of_special_equiv J hn hK hconj e T D hDT hne hnorm

/-- The first index of (12.3)(a) in the nonbinary unitary alternative,
with the actual original quotient image identified as the full Sylow omega. -/
theorem source_unitary_first_index
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (hb : 2 < b (reducedFamily L S))
    {a x m : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x m)
    (hym : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) m)
    {n : ℕ} (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) 3 (2^n) ∨
      IsSU (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) 3 (2^n))
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) m ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    let : ∀ j, Finite (L j) := h.finite_local
  let F := reducedFamily L S
    let Vx := V F x 1
    let W := Vx ⊓ Q F (base F i)
    W.relIndex Vx = 2^n ∧
      (W.map (G₀ L S).subtype).relIndex (Vx.map (G₀ L S).subtype) = 2^n ∧
      ∃ T : Sylow 2 (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))),
        (Vx.subgroupOf (star L S i)).map
          ((originalQuotient h i).symm.toMonoidHom.comp
            (QuotientGroup.mk' (pCore 2 (star L S i)))) = omegaOneAmbient (T : Subgroup _) := by
  let : ∀ j, Finite (L j) := h.finite_local
  let F := reducedFamily L S
  let A := star L S i
  let E := stabilizer F m ⊓ stabilizer F (base F i)
  let Vx := V F x 1
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hSyl := reduced_kernel_sylow h
  have hescape : ¬ Vx ≤ Q F (base F i) := by
    intro he
    have hseed : Z F a ≤ Vx :=
      le_iSup_of_le _ (le_iSup_of_le ((mem_ball_one F _ _).mpr (Or.inl hxa)) le_rfl)
    exact hc.2 (hseed.trans (he.trans (source_Z_Q_U (reduced_triple h) (base F i)).2))
  have hyx : base F i ≠ x := by
    intro he
    apply hescape
    change V F x 1 ≤ Q F (base F i)
    rw [← he]
    exact V_le_Q F (reduced_triple h).generate hZ hSyl hb _
  have hVm : Vx ≤ Q F m := V_le_neighbor_Q F (reduced_triple h).generate hZ hSyl hb hxm
  have hVA : Vx ≤ A :=
    (hVm.trans (le_sup_left.trans hR.ge)).trans (map_subtype_le _)
  let : IsElementaryAbelian 2 Vx := V_elementary F (reduced_triple h).generate hZ hSyl hb x
  let : IsElementaryAbelian 2 (Vx.subgroupOf A) := IsElementaryAbelian.subgroupOf hVA
  let q := (originalQuotient h i).symm.toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 A))
  let D := (Vx.subgroupOf A).map q
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map q
  obtain ⟨K, hK, hodd, hKx⟩ := source_middle_edge_complement h i eLin hxm hym hyx
  obtain ⟨T, hTN, hsup⟩ := source_quotient_edge_complement_supplement h i hym (MulEquiv.refl _) K hK hodd
  change (normalizer (T : Set (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))))).comap q =
    (stabilizer F m).subgroupOf A at hTN
  change (T : Subgroup (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0)))) ⊔
    ((K.map E.subtype).subgroupOf A).map q = normalizer (T : Set _) at hsup
  let C := (K.map E.subtype).subgroupOf A
  have hDN : D ≤ normalizer (T : Set (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0)))) := by
    apply map_le_iff_le_comap.mpr
    rw [hTN]
    intro v hv
    exact Q_le_stabilizer F m (hVm hv)
  have hDT : D ≤ T := by
    rw [← inf_eq_left.mpr hDN, (IsElementaryAbelian.isPGroup 2 D).inf_normalizer_sylow T]
    exact inf_le_right
  have hk : q.ker = (Q F (base F i)).subgroupOf A := by
    have hq : q.ker = pCore 2 A := by
      ext v
      change (originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) v) = 1 ↔ v ∈ pCore 2 A
      rw [map_eq_one_iff _ (originalQuotient h i).symm.injective]
      exact QuotientGroup.eq_one_iff v
    rw [hq, ← star_core h i]
    exact (comap_map_eq_self_of_injective A.subtype_injective (pCore 2 A)).symm
  have hne : D ≠ ⊥ := by
    intro he
    have hh := (map_eq_bot_iff (Vx.subgroupOf A)).mp he
    rw [hk] at hh
    exact hescape (fun v hv => hh (show (⟨v, hVA hv⟩ : A) ∈ Vx.subgroupOf A from hv))
  have hDZ : D ≤ (center T).map (T : Subgroup (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0)))).subtype := by
    rw [← (unitary_sylow_omega hn hu T).1, ← omegaOneAmbient_eq_self D]
    exact omegaOneAmbient_mono hDT
  have hnorm : normalizer (T : Set (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0)))) ≤ normalizer (D : Set _) := by
    rw [← hsup]
    apply sup_le
    · apply (le_centralizer_iff.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
      intro d hd t ht
      obtain ⟨d', hd', he⟩ := hDZ hd
      rw [← he]
      exact congrArg Subtype.val ((mem_center_iff.mp hd') ⟨t, ht⟩)
    · have hCV : C ≤ normalizer (Vx.subgroupOf A : Set A) := by
        intro c hc
        exact le_normalizer_comap A.subtype
          (stabilizer_normalizes_V F x 1 (hKx hc))
      exact (map_mono hCV).trans ((Vx.subgroupOf A).le_normalizer_map q)
  have him : D = omegaOneAmbient (T : Subgroup _) :=
    (unitary_borel_elementary hn hu T D hDT hne hnorm).1
  have hi : (Vx ⊓ Q F (base F i)).relIndex Vx = 2^n := by
    rw [inf_relIndex_left, ← relIndex_subgroupOf hVA, ← hk, relIndex_ker]
    change Nat.card D = _
    rw [him]
    exact (unitary_sylow_omega hn hu T).2.2
  refine ⟨hi, ?_, T, him⟩
  rw [relIndex_map_map_of_injective _ _ (G₀ L S).subtype_injective]
  exact hi


/-- Reverse the first source index by the literal linear neighbor exchange. -/
theorem source_unitary_reverse_first_index
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (hb : 2 < b (reducedFamily L S))
    {a x m : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x m)
    (hym : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) m)
    {n : ℕ} (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) 3 (2^n) ∨
      IsSU (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) 3 (2^n))
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) m ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    let F := reducedFamily L S
    (Q F x).relIndex (V F (base F i) 1) = 2^n ∧
      ((Q F x).map (G₀ L S).subtype).relIndex
        ((V F (base F i) 1).map (G₀ L S).subtype) = 2^n := by
  let F := reducedFamily L S
  let y := base F i
  let z := base F (!i)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hi : (Q F y).relIndex (V F x 1) = 2^n := by
    simpa only [inf_relIndex_left] using
      (source_unitary_first_index h i hb hc hxa hxm hym hn hu eLin R hR).1
  have hne : x ≠ y := by
    intro he
    have hZx : Z F a ≤ V F x 1 := Z_neighbor_le_V F hxa
    have hV := V_le_Q F (reduced_triple h).generate
      (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb x
    rw [he] at hV hZx
    exact hc.2 (hZx.trans (hV.trans (source_Z_Q_U (reduced_triple h) y).2))
  have hyz : (graph F).Adj y z :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨g,hg,hgm⟩ := star_locally_transitive h i hym hyz
  have hgy : g • y = y := star_le_stabilizer i hg
  have hzx : (graph F).Adj z (g • x) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hxm.symm
    change (graph F).Adj (g • m) (g • x) at hh
    rwa [hgm] at hh
  have hne' : g • x ≠ y := fun he => hne ((MulAction.injective g) (he.trans hgy.symm))
  obtain ⟨u,_,hux,huy⟩ := linear_neighbor_swap h (!i) eLin hzx hyz.symm hne'
  let t := g⁻¹ * u * g
  have htx : t • x = y := by
    dsimp only [t]
    rw [mul_smul,mul_smul,hux,inv_smul_eq_iff]
    exact hgy.symm
  have hty : t • y = x := by
    dsimp only [t]
    rw [mul_smul,mul_smul,hgy,huy,inv_smul_smul]
  have he := relIndex_map_map_of_injective (Q F y) (V F x 1)
    (f := (MulAut.conj t).toMonoidHom) (MulAut.conj t).injective
  rw [←Q_translate F,←V_translate F,htx,hty] at he
  have hj := he.trans hi
  exact ⟨hj,(relIndex_map_map_of_injective _ _ (G₀ L S).subtype_injective).trans hj⟩


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
