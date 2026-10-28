module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SecondKernelLayer
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Valence

/-!
# Full kernels in the binary linear--Suzuki branch

The Sylow two-subgroups of Sz(2) have order four and normalizers of index
five, so they are self-normalizing. Lifting this through the actual
quotient by O₂ identifies the original Suzuki Borel with its Sylow.
Together with the original SL₂(2) marking this proves B = S, including
the full Borel used in the reduction. Every edge stabilizer is therefore
a two-group. The source kernel-Sylow theorem now identifies each full
radius-one kernel with Q, and puts each full radius-two kernel in Q.

The last theorem applies this containment to the previously constructed
span action: its centralizer is the whole second kernel, with no residual
odd part. Thus the denominator in the literal second-kernel representation
is the full source denominator in this binary branch. The two model
markings are explicit earlier selection inputs; this does not prove
Suzuki selection or either TYPE₂F₄(2) alternative.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(6.2)(d), (12.5)--(12.6), printed pp.119,182--183.
-/

public noncomputable section

open Subgroup
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Reduction Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem suzuki_zero_sylow_self_normalizing
    {A : Type*} [Group A] [Finite A]
    (e : (A ⧸ pCore 2 A) ≃* SuzukiMatrixGroup 0) (P : Sylow 2 A) :
    normalizer (P : Set A) = (P : Subgroup A) := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 A := by
    ext x
    change e (QuotientGroup.mk' _ x) = 1 ↔ x ∈ pCore 2 A
    rw [map_eq_one_iff _ e.injective]
    exact QuotientGroup.eq_one_iff x
  let R := P.mapSurjective hf
  have hR : Nat.card R = 4 := by
    rw [R.card_eq_multiplicity, suzukiZero_card]
    decide +kernel
  have hi : (normalizer (R : Set (SuzukiMatrixGroup 0))).index = 5 := by
    simpa using suzuki_sylow_normalizer_index 0 R
  have hc : Nat.card (normalizer (R : Set (SuzukiMatrixGroup 0))) = 4 := by
    have hh := (normalizer (R : Set (SuzukiMatrixGroup 0))).index_mul_card
    rw [hi, suzukiZero_card] at hh
    omega
  have he : normalizer (R : Set (SuzukiMatrixGroup 0)) = (R : Subgroup _) :=
    (eq_of_le_of_card_ge le_normalizer (by
      change Nat.card (normalizer (R : Set (SuzukiMatrixGroup 0))) ≤ Nat.card R
      rw [hc,hR])).symm
  have hRP : (R : Subgroup (SuzukiMatrixGroup 0)).comap f = (P : Subgroup A) := by
    apply comap_map_eq_self
    rw [hk]
    exact pCore_isPGroup.le_sylow_of_normal P
  have hh := congrArg (Subgroup.comap f) he
  change (normalizer ((R : Subgroup (SuzukiMatrixGroup 0)) : Set _)).comap f =
    (R : Subgroup (SuzukiMatrixGroup 0)).comap f at hh
  rwa [comap_normalizer_eq_of_surjective _ hf,hRP] at hh

/-- The actual original Sz(2) Borel is its local Sylow subgroup. -/
theorem suzuki_zero_local_borel (h : HypothesisF11 L S) (i : Fin 2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup 0) :
    borel (L i) S = S ⊓ L i := by
  let := h.finite_local i
  obtain ⟨P,hP⟩ := h.sylow i
  have hP' : (P : Subgroup (L i)) = (S ⊓ L i).subgroupOf (L i) := by
    apply map_injective (L i).subtype_injective
    rw [hP,map_subgroupOf_eq_of_le inf_le_right]
  have hn := suzuki_zero_sylow_self_normalizing e P
  change normalizer ((P : Subgroup (L i)) : Set (L i)) = (P : Subgroup (L i)) at hn
  rw [hP', ←subgroupOf_normalizer_eq (show S ⊓ L i ≤ L i from inf_le_right)] at hn
  apply le_antisymm
  · rintro x ⟨hx,hxn⟩
    change (⟨x,hx⟩ : L i) ∈ (S ⊓ L i).subgroupOf (L i)
    exact hn ▸ (show (⟨x,hx⟩ : L i) ∈
      (normalizer ((S ⊓ L i : Subgroup G) : Set G)).subgroupOf (L i) from hxn)
  · exact le_inf inf_le_right (S ⊓ L i).le_normalizer

/-- The two binary markings identify the full original Borel with S. -/
theorem binary_suzuki_commonBorel (h : HypothesisF11 L S) (i : Bool)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup 0)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃*
      SL(2,ZMod 2)) : commonBorel L S = S := by
  have hzero : borel (L 0) S = S ⊓ L 0 := by
    cases i
    · exact suzuki_zero_local_borel h 0 eSuz
    · exact binary_local_borel h 0 eLin
  have hone : borel (L 1) S = S ⊓ L 1 := by
    cases i
    · exact binary_local_borel h 1 eLin
    · exact suzuki_zero_local_borel h 1 eSuz
  change borel (L 0) S ⊔ borel (L 1) S ⊔ S = S
  rw [hzero,hone]
  exact sup_eq_right.mpr (sup_le inf_le_left inf_le_left)

/-- The full reduced Borel is also the original common Sylow. -/
theorem binary_suzuki_reduced_borel (h : HypothesisF11 L S) (i : Bool)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup 0)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃*
      SL(2,ZMod 2)) : B₀ L S = S := by
  have hc : (commonBorel L S).pCoreIn 2 = S := by
    rw [binary_suzuki_commonBorel h i eSuz eLin,pCoreIn_eq_self_of_isPGroup 2 S h.S_isP]
  exact le_antisymm ((B₀_le h).trans_eq (binary_suzuki_commonBorel h i eSuz eLin))
    (hc.ge.trans (show (commonBorel L S).pCoreIn 2 ≤ B₀ L S from le_sup_right))

/-- Every full first kernel in the binary linear--Suzuki graph equals its two-core. -/
theorem source_binary_suzuki_kernel_eq_core (h : HypothesisF11 L S) (i : Bool)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup 0)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃*
      SL(2,ZMod 2))
    {v w : Vertex (reducedFamily L S)} (he : (graph (reducedFamily L S)).Adj v w) :
    U (reducedFamily L S) v = Q (reducedFamily L S) v := by
  let F := reducedFamily L S
  have hbase : IsPGroup 2 (F false ⊓ F true : Subgroup (G₀ L S)) := by
    change IsPGroup 2 (((P₀ L S 0).subgroupOf (G₀ L S)) ⊓
      ((P₀ L S 1).subgroupOf (G₀ L S)) : Subgroup (G₀ L S))
    rw [(reduced_triple h).intersection,binary_suzuki_reduced_borel h i eSuz eLin]
    exact h.S_isP.comap_subtype
  obtain ⟨g,hg⟩ := edgeStabilizer_map_base F he
  have hedge : IsPGroup 2 (stabilizer F v ⊓ stabilizer F w : Subgroup (G₀ L S)) := by
    rw [hg]
    exact hbase.map _
  have hU : IsPGroup 2 (U F v) := hedge.to_le (ballKernel_one_le_edge F he)
  obtain ⟨T,hT⟩ := reduced_kernel_sylow h v
  have ht : (T : Subgroup (U F v)) = ⊤ := (T.is_maximal' (hU.to_subgroup ⊤) le_top).symm
  rw [ht, ←MonoidHom.range_eq_map,range_subtype] at hT
  exact hT

/-- The whole second kernel, including possible odd elements a priori, lies in Q. -/
theorem source_binary_suzuki_second_kernel_le_core (h : HypothesisF11 L S) (i : Bool)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup 0)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃*
      SL(2,ZMod 2))
    {v w : Vertex (reducedFamily L S)} (he : (graph (reducedFamily L S)).Adj v w) :
    ballKernel (reducedFamily L S) v 2 ≤ Q (reducedFamily L S) v := by
  rw [←source_binary_suzuki_kernel_eq_core h i eSuz eLin he]
  exact ballKernel_antitone (reducedFamily L S) v (by decide : 1 ≤ 2)


/-- The actual span centralizer is the full second kernel in the binary branch. -/
theorem source_binary_suzuki_second_kernel_centralizer (h : HypothesisF11 L S) (i : Bool)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup 0)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃*
      SL(2,ZMod 2))
    (T : Sylow 2 (ReducedLayer.star L S (!i)))
    (hT : (T : Subgroup (ReducedLayer.star L S (!i))).map (ReducedLayer.star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hnat : Noncommuting.HasNaturalCenter (ReducedLayer.star L S (!i))
      (Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
      (Q (reducedFamily L S) (base (reducedFamily L S) (!i)))) :
    let F := reducedFamily L S
    let v := base F i
    Q F v ⊓ centralizer (V F v 1 : Set (G₀ L S)) = ballKernel F v 2 := by
  let F := reducedFamily L S
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hplace : Q F (base F i) ≤ ReducedLayer.star L S (!i) :=
    (le_sup_left.trans hT.ge).trans (map_subtype_le _)
  exact (source_core_span_centralizer_eq_second_kernel h i hplace hnat).trans
    (inf_eq_right.mpr (source_binary_suzuki_second_kernel_le_core h i eSuz eLin hadj))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
