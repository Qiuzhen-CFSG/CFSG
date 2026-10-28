module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianExchangedBorel
public import Theory.SpecificGroups.SL2.RootNormalizedNine.SylowCore
public import Theory.ElementaryAbelian.PrimePlane

/-!
# The actual exchanged Sylow intersection in the edge two-core

The marked L₁/O₂(L₁) is E₉, including after taking its image in H/O₂(H).
In the exchanged PSL₂ pair, the product Sylow normalizes that image.
The rank-one root calculation identifies the image's intrinsic two-core
with the full product Sylow. It follows that the literal T ∩ K₀ lies in
O₂(L₁T): the full O₂(H) kernel is itself contained in this edge core.

The final application uses the original reduced actor J=K₀L₁T, with
relative component status and both original model quotients retained.
This supplies the Sylow containment used before the outer-action and torus
arguments of 12.6.31. It does not yet force field order four or prove the
universal NaturalReduction.
Source: Aschbacher--Smith 12.6.31, printed p.836.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter13.Section08.Components Chapter13.Section08.Components.Swapped
open Chapter13.Section08.Components.Swapped.LinearTwo
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
    (T : Subgroup G) = H)


include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The image of the intrinsic O₂(L₁) is the full product Sylow on the
actual exchanged component orbit. The ambient O₂(H) is not O₂(L₁). -/
theorem SourceHypothesis.original_abelian_exchanged_star_core
    (hn : ¬ (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n)) :
    (actorImage H (D.fullSetup hZ T z).L₁).pCoreIn 2 =
      actorImage H ((T : Subgroup G) ⊓ conjugateSpanBy K (T : Subgroup G)) := by
  let E := D.fullSetup hZ T z
  let O := conjugateSpanBy K (T : Subgroup G)
  obtain ⟨t,ht,hTH,htn,hOH,e,P,he,hP,hstar,hsol,hLB,hBM,hnB,heven,hBrank,hOT,hBeq,hMeq⟩ :=
    S.original_abelian_exchanged_borel D hZ z hz hTV hTz hbound hTI hns
      hH hKH hK hgen hn hn2 hm
  have hLO : E.L₁ ≤ O := hLB.trans (borelLift_le H O hOH _)
  have hLH : E.L₁ ≤ H := hLO.trans hOH
  let A := actorImage H O
  let Cstar := actorImage H E.L₁
  have hCA : Cstar ≤ A := map_mono (comap_mono hLO)
  let C := Cstar.subgroupOf A
  have hTL : (T : Subgroup G) ≤ normalizer (E.L₁ : Set G) :=
    (le_inf hTH hTV).trans
      (S.original_module_normalizer_normalizes_residual D hZ z hTV hH)
  have hnCstar : actorImage H T ≤ normalizer (Cstar : Set (H ⧸ pCore 2 H)) :=
    Chapter13.Section08.Components.Suzuki.BorelSource.starImage_normalizes H E.L₁ T hTL
  have hnC : (P : Subgroup A) ≤ normalizer (C : Set A) := by
    intro x hx
    have hxT : (x : H ⧸ pCore 2 H) ∈ actorImage H T :=
      (map_mono (comap_mono inf_le_left)) (hP ▸ mem_map_of_mem A.subtype hx)
    exact mem_normalizer_iff.mpr (fun y => mem_normalizer_iff.mp (hnCstar hxT) y.val)
  let q := QuotientGroup.mk' (pCore 2 H)
  let c := subgroupOfEquivOfLe hLH
  let d := subgroupOfEquivOfLe hCA
  let f : E.L₁ →* C := d.symm.toMonoidHom.comp
    ((q.subgroupMap (E.L₁.subgroupOf H)).comp c.symm.toMonoidHom)
  have hf : Function.Surjective f := d.symm.surjective.comp
    ((q.subgroupMap_surjective _).comp c.symm.surjective)
  have hkdef : f.ker = (pCore 2 H).comap (inclusion hLH) := by
    ext x
    change f x = 1 ↔ inclusion hLH x ∈ pCore 2 H
    rw [←QuotientGroup.eq_one_iff]
    change f x = 1 ↔ ((f x : A) : H ⧸ pCore 2 H) = 1
    exact ⟨fun h => congrArg (fun y : C => ((y : A) : H ⧸ pCore 2 H)) h,
      fun h => Subtype.ext (Subtype.ext h)⟩
  have hk : IsPGroup 2 f.ker := by
    rw [hkdef]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hLH)
  obtain ⟨_,_,_,e9,_,_⟩ := S.original_point_residual_quotient D hZ z hz hTz
  obtain ⟨a9⟩ := IsElementaryAbelian.nonempty_mulEquiv_plane_of_card
    (p := 3) (G := BinaryPermutation.TerminalOrthogonal.FourBlockResidual.E9)
    (by simpa using BinaryPermutation.TerminalOrthogonal.FourBlockResidual.E9_card)
  let eC : (C ⧸ pCore 2 C) ≃* Multiplicative (ZMod 3 × ZMod 3) :=
    (f.quotientPCoreEquivOfSurjective hf hk).symm.trans
      (e9.trans (a9.trans (MulEquiv.prodMultiplicative (ZMod 3) (ZMod 3)).symm))
  have hmstar := hm.of_mulEquiv (componentStarEquiv H K hKH hK).symm
  obtain ⟨F,hF,hfin,hcard,⟨a⟩⟩ := hmstar
  let := hF
  let := hfin
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let a' := a.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm
  let eA := e.trans (MulEquiv.prodCongr a' a')
  have hfour : 2 < Nat.card F := by
    rw [hcard]
    have := Nat.pow_le_pow_right (n := 2) (by decide : 1 ≤ 2) hn2
    omega
  have hc := Matrix.SpecialLinearGroup.RootNormalizedNine.sylow_eq_core_of_equiv
    eA P C hfour hnC eC
  have hh := congrArg (map A.subtype) hc
  rw [map_pCoreIn_of_injective 2 C A.subtype A.subtype_injective,
    map_subgroupOf_eq_of_le hCA] at hh
  exact hh.trans hP

private theorem actorImage_core {H Y : Subgroup G} (hYH : Y ≤ H) :
    actorImage H (Y.pCoreIn 2) = (actorImage H Y).pCoreIn 2 := by
  have he : ((Y.subgroupOf H).pCoreIn 2).map H.subtype = Y.pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le hYH]
  have hi : (Y.pCoreIn 2).subgroupOf H = (Y.subgroupOf H).pCoreIn 2 := by
    rw [←he]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  change ((Y.pCoreIn 2).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) = _
  rw [hi,map_pCoreIn_of_ker_isPGroup (QuotientGroup.mk' (pCore 2 H))
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)]
  rfl

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The original intersection T ∩ K₀ is contained in O₂(L₁T), including
the full kernel of H → H/O₂(H). This is the source's outer-action input. -/
theorem SourceHypothesis.original_abelian_exchanged_sylow_le_edge_core
    (hn : ¬ (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n)) :
    (T : Subgroup G) ⊓ conjugateSpanBy K (T : Subgroup G) ≤
      (D.fullSetup hZ T z).R₁ := by
  let E := D.fullSetup hZ T z
  let J := E.L₁ ⊔ (T : Subgroup G)
  have hJH : J ≤ H := sup_le (fun x hx => hH.1.2 (Or.inl hx))
    (fun x hx => hH.1.2 (Or.inr hx))
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hJH
  have hTL : (T : Subgroup G) ≤ normalizer (E.L₁ : Set G) :=
    (le_inf hTH hTV).trans
      (S.original_module_normalizer_normalizes_residual D hZ z hTV hH)
  have hnL : J ≤ normalizer (E.L₁ : Set G) := sup_le E.L₁.le_normalizer hTL
  have hmcore : (actorImage H E.L₁).pCoreIn 2 ≤ (actorImage H J).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes (map_mono (comap_mono le_sup_left))
      (Chapter13.Section08.Components.Suzuki.BorelSource.starImage_normalizes H E.L₁ J hnL)
  have hs := S.original_abelian_exchanged_star_core D hZ z hz hTV hTz hbound hTI hns
    hH hKH hK hgen hn hn2 hm
  have himage : actorImage H ((T : Subgroup G) ⊓ conjugateSpanBy K (T : Subgroup G)) ≤
      actorImage H E.R₁ := by
    rw [←hs]
    change _ ≤ actorImage H (J.pCoreIn 2)
    rw [actorImage_core hJH]
    exact hmcore
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow H (T.subtype hTH)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] using hh
  have hQR : H.pCoreIn 2 ≤ E.R₁ :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H) (hQT.trans le_sup_right)
      (hJH.trans (H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))
  intro x hx
  let xH : H := ⟨x,hTH hx.1⟩
  have hmX : QuotientGroup.mk' (pCore 2 H) xH ∈ actorImage H E.R₁ :=
    himage (mem_map_of_mem _ hx)
  obtain ⟨y,hy,he⟩ := hmX
  have hxy : xH * y⁻¹ ∈ pCore 2 H := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 H) (xH * y⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hmem := E.R₁.mul_mem (hQR (mem_map_of_mem H.subtype hxy)) hy
  change (x * y.val⁻¹) * y.val ∈ E.R₁ at hmem
  simpa only [inv_mul_cancel_right] using hmem

include hz hTV hTz hbound hTI hns hH in
/-- The original reduced actor retains the full even-field and Borel
conclusions, and its actual Sylow intersection lies in the original edge core. -/
theorem SourceHypothesis.original_abelian_reduced_even_Lie_models_core :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧ ¬ K ≤ M L ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧
      (D.fullSetup hZ T z).L₁ ≤ normalizer (K : Set G) ∧
      let K₀ := conjugateSpanBy K (T : Subgroup G)
      let J := K₀ ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)
      (K₀.subgroupOf H).Normal ∧ J ≤ H ∧ J ∈ (D.fullSetup hZ T z).Hz ∧
      (K.subgroupOf J).IsCComponent ∧
      (((K.subgroupOf J).Normal ∧
          AbelianLieHigherFieldModel (K ⧸ pCore 2 K) ∧
          AbelianLieHigherFieldModel (actorImage J K)) ∨
        (¬ (K.subgroupOf J).Normal ∧ (normalizer (K.subgroupOf J : Set J)).index = 2 ∧
          ∃ n : ℕ, 2 ≤ n ∧ Even n ∧
            ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n) ∧
            ClassicalGroup.IsPSL (actorImage J K) 2 (2 ^ n) ∧
            (primeToResidual 3 J).map J.subtype = K₀ ∧
            (D.fullSetup hZ T z).L₁ ≤ K₀ ⊓ M L ∧
            K₀ ⊔ (T : Subgroup G) = J ∧
            J ⊓ M L = (K₀ ⊓ M L) ⊔ (T : Subgroup G) ∧
            Group.IsSolvable (K₀ ⊓ M L : Subgroup G) ∧
            primeRank 3 (K₀ ⊓ M L : Subgroup G) = 2 ∧
            (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G) ≤
              normalizer ((K₀ ⊓ M L : Subgroup G) : Set G) ∧
            (T : Subgroup G) ⊓ K₀ ≤ (D.fullSetup hZ T z).R₁)) := by
  obtain ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ,halt⟩ :=
    S.original_abelian_reduced_even_Lie_models D hZ z hz hTV hTz hbound hTI hns hH
  have hKle := (le_conjugateSpanBy K (T : Subgroup G)).trans
    (le_sup_left.trans (le_sup_left :
      conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ≤
        conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)))
  refine ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ,?_⟩
  rcases halt with hnormal | ⟨hn,hi,n,hn2,heven,hm,hmstar,hr,hLB,hOT,hMeq,hsol,hrank,hnB⟩
  · exact Or.inl hnormal
  · exact Or.inr ⟨hn,hi,n,hn2,heven,hm,hmstar,hr,hLB,hOT,hMeq,hsol,hrank,hnB,
      S.original_abelian_exchanged_sylow_le_edge_core D hZ z hz hTV hTz hbound hTI hns
        hJ hKle hKJ rfl hn hn2 hm⟩

end CFSG.Quasithin.Chapter12.Section06
