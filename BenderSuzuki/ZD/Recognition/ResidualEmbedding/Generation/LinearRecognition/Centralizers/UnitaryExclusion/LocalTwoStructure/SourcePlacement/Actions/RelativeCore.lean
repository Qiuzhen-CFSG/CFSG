module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.SourcePlacement.Foundations
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryGeometry.ModelTransport

public import Theory.GroupTheory.SylowCommutatorCore

/-!
# Relative commutator cores and the actual local two-point torus

The SU₃/PSU₃ Borel geometry makes D ∩ Lᵤ cyclic, so it centralizes B and
normalizes the literal U=N_V(A⟨u⟩). Relative normality of Lᵤ in C_G(u)
places [B,C_G(A⟨u⟩)] inside C_(Lᵤ)(A) ≤ M ∩ Lᵤ. That last centralizer
normalizes T, and the Sylow property proves the unconditional bound T₁ ≤ T.
The converse bound is proved from the two explicit model calculations
T ≤ C_G(A) and [B,T]=T; their existence is not asserted here.

Source: GLS, Volume 4, Chapter 2, proof of Lemma 13.4, lines 2397–2420;
Chapter 4, Lemmas 3.2(c) and 3.5(c). All maps retain the original ambient
subgroups and the special/projective cover choice.
-/

noncomputable section
namespace BenderSuzuki.ZD.UnitaryExclusion.SourcePlacement
open Subgroup Theory.GroupTheory PFchapter1section1 PFAppendixIII RankOneModelGeometry
universe v
variable {G : Type v} [Group G] [Finite G]
variable {Z : Set G} {M : Subgroup G} {z t u : G} {n : ℕ}

omit [Finite G] in
private theorem mem_right_conjugate (B : Subgroup G) (t x : G) :
    x ∈ rightConjugate B t ↔ t * x * t⁻¹ ∈ B := by
  rw [rightConjugate, Subgroup.conjBy, mem_map_equiv]
  simp [MulAut.conj_apply]

omit [Finite G] in
/-- The local two-point subgroup has the literal ambient pair stabilizer as image. -/
public theorem localPair_eq_map (htH : t ∈ centralizerClosure Z u) :
    residualPairStabilizer M t ⊓ centralizerClosure Z u =
      (twoPoint (M.comap (centralizerClosure Z u).subtype)
        (⟨t, htH⟩ : centralizerClosure Z u)).map (centralizerClosure Z u).subtype := by
  symm
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨hy.1, ?_⟩, y.property⟩
    exact (mem_right_conjugate M t _).mpr
      ((mem_right_conjugate (M.comap (centralizerClosure Z u).subtype)
        (⟨t, htH⟩ : centralizerClosure Z u) y).mp hy.2)
  · rintro ⟨⟨hxM, hxtM⟩, hxH⟩
    refine ⟨⟨x, hxH⟩, ⟨hxM, ?_⟩, rfl⟩
    exact (mem_right_conjugate (M.comap (centralizerClosure Z u).subtype)
      (⟨t, htH⟩ : centralizerClosure Z u) ⟨x, hxH⟩).mpr
        ((mem_right_conjugate M t x).mp hxtM)

private theorem cover_twoPoint_cyclic {H : Type*} [Group H] [Finite H]
    (hn : 2 ≤ n) (hc : IsUnitaryCentralizerCoverAt n H)
    (N : Subgroup H) (hN : IsBorelSubgroup N)
    (s : H) (hs : PFAppendixIII.IsInvolution s) (hsN : s ∉ N) : IsCyclic (twoPoint N s) := by
  obtain ⟨_, P, rfl⟩ := hN
  obtain ⟨E, _, _, J, hJ, hcard, hfixed, he | he⟩ := hc
  · obtain ⟨e⟩ := he
    exact (unitary_projective_tori_of_equiv J hn hJ hcard hfixed e P s hs hsN).1
  · obtain ⟨e⟩ := he
    exact (unitary_special_tori_of_equiv J hn hJ hcard hfixed e P s hs hsN).1

/-- The actual D ∩ Lᵤ is cyclic in both unitary covers. -/
public theorem localPair_cyclic
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (ht : t ∈ Z) (htM : t ∉ M) (hn : 2 ≤ n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u) :
    IsCyclic (residualPairStabilizer M t ⊓ centralizerClosure Z u : Subgroup G) := by
  have htH : t ∈ centralizerClosure Z u := (hunitary u huD hu).1.le
    ((show zpowers t ≤ residualGenerated M z t from le_sup_right.trans le_sup_left)
      (mem_zpowers t))
  have hN := pair_involution_unitary_borel h r htM huD hu hn (hunitary u huD hu).2
  have hc := cover_twoPoint_cyclic hn (hunitary u huD hu).2
    (M.comap (centralizerClosure Z u).subtype) hN ⟨t, htH⟩
    (IsInvolution.subtype (h.involutions t ht) htH) htM
  let P := twoPoint (M.comap (centralizerClosure Z u).subtype)
    (⟨t, htH⟩ : centralizerClosure Z u)
  let e := (P.equivMapOfInjective (centralizerClosure Z u).subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr (localPair_eq_map (M := M) htH).symm)
  exact e.isCyclic.mp hc

/-- Cyclicity of the whole local pair forces it to centralize the specified B. -/
public theorem localPair_centralizes_torus
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (ht : t ∈ Z) (htM : t ∉ M) (hn : 2 ≤ n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (d : SecondCentralizerData Z M z t u n) :
    residualPairStabilizer M t ⊓ centralizerClosure Z u ≤ centralizer (d.torus : Set G) := by
  let D := residualPairStabilizer M t ⊓ centralizerClosure Z u
  let : IsCyclic D := localPair_cyclic h r ht htM hn hunitary huD hu
  let : CommGroup D := IsCyclic.commGroup
  intro x hx b hb
  exact congrArg Subtype.val (mul_comm (⟨b, d.torus_le_pair hb, d.torus_le_local hb⟩ : D) ⟨x, hx⟩)

omit [Finite G] in
private theorem centralizer_normalizes_distinguishedCentralizer
    (h : IsProductDisconnected Z M) (B : Subgroup G) :
    centralizer (B : Set G) ≤ normalizer (distinguishedCentralizer Z B : Set G) := by
  apply le_normalizer_closure_iff.mpr
  intro g hg x hx
  exact subset_closure ⟨h.invariant g x hx.1,
    (centralizer (B : Set G)).mul_mem
      ((centralizer (B : Set G)).mul_mem hg hx.2)
      ((centralizer (B : Set G)).inv_mem hg)⟩

/-- Every element of D ∩ Lᵤ preserves the corrected subgroup U=N_V(A⟨u⟩). -/
public theorem localPair_normalizes_sourceLocalU
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M) (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hn : 2 ≤ n) (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (d : SecondCentralizerData Z M z t u n) :
    residualPairStabilizer M t ⊓ centralizerClosure Z u ≤
      normalizer (sourceLocalU Z M d.torus u : Set G) := by
  have hMA := (distinguishedClosure_data h r ha hz hzM ht htM hL heven).2.1
  let D := residualPairStabilizer M t ⊓ centralizerClosure Z u
  have hDM : D ≤ M := inf_le_left.trans inf_le_left
  have hDF : D ≤ normalizer (distinguishedCentralizer Z d.torus : Set G) :=
    (localPair_centralizes_torus h.disconnected r ht htM hn hunitary huD hu d).trans
      (centralizer_normalizes_distinguishedCentralizer h.disconnected _)
  have hDV : D ≤ normalizer (localV Z M d.torus : Set G) :=
    ((le_inf (hDM.trans M.le_normalizer) hDF).trans inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hDu : D ≤ normalizer (zpowers u : Set G) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    have he := mem_centralizer_singleton_iff.mp (centralizerClosure_le Z u hx.2)
    change zpowers (x * u * x⁻¹) = zpowers u
    rw [mul_inv_eq_iff_eq_mul.mpr he]
  have hDJ : D ≤ normalizer
      (closure (Z ∩ (M : Set G)) ⊔ zpowers u : Subgroup G) :=
    (le_inf (hDM.trans hMA) hDu).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hDN : D ≤ normalizer ((normalizer
      ((closure (Z ∩ (M : Set G)) ⊔ zpowers u : Subgroup G) : Set G)) : Set G) := by
    intro x hx
    exact (normalizer ((closure (Z ∩ (M : Set G)) ⊔ zpowers u : Subgroup G) : Set G)).le_normalizer (hDJ hx)
  exact (le_inf hDV hDN).trans inf_normalizer_le_normalizer_inf

omit [Finite G] in
/-- A distinguished element in A puts C_G(A), and thus C_(Lᵤ)(A), inside M. -/
public theorem distinguishedClosure_centralizer_le
    (h : IsProductDisconnected Z M) (hz : z ∈ Z) (hzM : z ∈ M) :
    centralizer (closure (Z ∩ (M : Set G)) : Set G) ≤ M :=
  (centralizer_le (Set.singleton_subset_iff.mpr (show z ∈ closure (Z ∩ (M : Set G)) from subset_closure ⟨hz, hzM⟩))).trans
    (h.centralizer_le hz hzM)

omit [Finite G] in
/-- The commutator defining T₁ lies in the relative centralizer C_(Lᵤ)(A). -/
public theorem source_commutator_le_relativeCentralizer
    (h : IsProductDisconnected Z M)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (d : SecondCentralizerData Z M z t u n) :
    ⁅d.torus, centralizer ((closure (Z ∩ (M : Set G)) ⊔ zpowers u : Subgroup G) : Set G)⁆ ≤
      centralizerClosure Z u ⊓ centralizer (closure (Z ∩ (M : Set G)) : Set G) := by
  let C := centralizer ((closure (Z ∩ (M : Set G)) ⊔ zpowers u : Subgroup G) : Set G)
  have hCu : C ≤ centralizer ({u} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.mpr ((show zpowers u ≤ closure (Z ∩ (M : Set G)) ⊔ zpowers u from le_sup_right) (mem_zpowers u)))
  have hCH : C ≤ normalizer (centralizerClosure Z u : Set G) := hCu.trans
    ((normal_subgroupOf_iff_le_normalizer (centralizerClosure_le Z u)).mp
      (centralizerClosure_normal_in_centralizer h u))
  refine le_inf ?_ ?_
  · exact (commutator_mono d.torus_le_local le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hCH)
  · exact (Subgroup.commutator_le_sup _ _).trans (sup_le
      (d.torus_centralizes.trans (centralizer_le hAL))
      (centralizer_le (show closure (Z ∩ (M : Set G)) ≤
        closure (Z ∩ (M : Set G)) ⊔ zpowers u from le_sup_left)))

omit [Finite G] in
/-- Normality of T is only needed inside the indicated relative centralizer. -/
public theorem relativeCentralizer_normalizes_localT
    (h : IsProductDisconnected Z M) (hz : z ∈ Z) (hzM : z ∈ M) :
    centralizerClosure Z u ⊓ centralizer (closure (Z ∩ (M : Set G)) : Set G) ≤
      normalizer (localT Z M u : Set G) := by
  have hCM : centralizerClosure Z u ⊓ centralizer (closure (Z ∩ (M : Set G)) : Set G) ≤
      M ⊓ centralizerClosure Z u :=
    le_inf (inf_le_right.trans (distinguishedClosure_centralizer_le h hz hzM)) inf_le_left
  exact (hCM.trans (M ⊓ centralizerClosure Z u).le_normalizer).trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))



/-- The upper containment T₁ ≤ T needs no unproved torus-action assertion. -/
public theorem commutatorCore_le_localT
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (hz : z ∈ Z) (hzM : z ∈ M) (htM : t ∉ M)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hn : 2 ≤ n) (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (d : SecondCentralizerData Z M z t u n) :
    commutatorCore Z M d.torus u ≤ localT Z M u := by
  obtain ⟨P, hP⟩ := sylow_T h r htM huD hu hn hunitary
  have hK := source_commutator_le_relativeCentralizer h hAL d
  exact le_sylow_image_of_normalizes _ P hP (isPGroup_pCoreIn 2 _)
    ((pCoreIn_le 2 _).trans (hK.trans inf_le_left))
    ((pCoreIn_le 2 _).trans (hK.trans (relativeCentralizer_normalizes_localT h hz hzM)))

/-- The lower containment in the source follows from T=[B,T] and centralization
of A. All relative-normality and ambient-containment premises are discharged. -/
public theorem commutatorCore_eq_of_torus_generation
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (hz : z ∈ Z) (hzM : z ∈ M) (htM : t ∉ M)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hn : 2 ≤ n) (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (d : SecondCentralizerData Z M z t u n)
    (hTA : localT Z M u ≤ centralizer (closure (Z ∩ (M : Set G)) : Set G))
    (hBT : ⁅d.torus, localT Z M u⁆ = localT Z M u) :
    commutatorCore Z M d.torus u = localT Z M u := by
  obtain ⟨P, hP⟩ := sylow_T h r htM huD hu hn hunitary
  have hK := source_commutator_le_relativeCentralizer h hAL d
  apply commutator_pCoreIn_eq_sylow_image _ P _ _ _ hP (hK.trans inf_le_left)
    (hK.trans (relativeCentralizer_normalizes_localT h hz hzM)) _ hBT
  apply le_centralizer_iff.mpr
  refine sup_le (le_centralizer_iff.mp hTA) (zpowers_le.mpr ?_)
  intro x hx
  exact mem_centralizer_singleton_iff.mp
    (centralizerClosure_le Z u (localTwoCore_le M (centralizerClosure Z u) hx).2)

omit [Finite G] in
/-- The distinguished involution z already makes T nontrivial. -/
public theorem localT_ne_bot
    (h : IsProductDisconnected Z M) (hz : z ∈ Z) (hzM : z ∈ M)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hMA : M ≤ normalizer (closure (Z ∩ (M : Set G)) : Set G))
    (hA : IsPGroup 2 (closure (Z ∩ (M : Set G))))
    (d : SecondCentralizerData Z M z t u n) : localT Z M u ≠ ⊥ := by
  have hAM : closure (Z ∩ (M : Set G)) ≤ M := (closure_le _).mpr fun _ hx => hx.2
  have hLH : residualGenerated M z t ≤ centralizerClosure Z u :=
    d.intersection ▸ inf_le_right
  have hAT : closure (Z ∩ (M : Set G)) ≤ localT Z M u :=
    le_pCoreIn_of_normalizes hA (le_inf hAM (hAL.trans hLH)) (inf_le_left.trans hMA)
  intro he
  have hzT := hAT (subset_closure ⟨hz, hzM⟩)
  rw [he, mem_bot] at hzT
  exact (h.involutions z hz).ne_one hzT

end BenderSuzuki.ZD.UnitaryExclusion.SourcePlacement
