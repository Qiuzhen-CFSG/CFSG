module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.QuadraticBound
public import Theory.GroupTheory.PResidual.NormalizerImage
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry

/-!
# The original point-centralizer escape and its natural action

For D = C_{G₁}(K₁/O₂(K₁)), the point-component core lies in the original
Sylow subgroup and normalizes L₁. Two-perfectness therefore lifts quotient
centralization to normalization of L₁, and [D,L₁] lies in O₂(L₁).
If D escapes N_G(L), minimal selection constructs the actual H₁ in HStar
with O²(H₁) ≤ D and J = L₁H₁ in Hz. The genuine nonzero F.9 actor shows
that J cannot normalize L₁T. Consequently T is not normal in H₁, proving
that H₁ is a minimal parabolic without an extra Sylow-normalizer premise.

The original map into G₁/V₁ transports the homogeneous decomposition to
the literal F.9 module U_J/V₁. It retains the full natural L₁ actor, its
exact O₂(L₁) kernel, and the actual inclusion and quotient action. The
edge core and O²(H₁) centralize that natural image in J/O₂(J). The final
application constructs the same quadratic actor inside both R₁ and H₁,
with positive multiplicity and its original fixed-codimension bound.
The chief-factor multiplicity inequality and the resulting point-centralizer
bound remain to be proved; this construction does not assert 12.9.5(1).

Source: Aschbacher--Smith, proof of 12.9.5, Case I, printed pp.860--861;
12.8.5(1), p.850; F.9.16(3--4), pp.323--324 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
open Chapter15.Section03.AbelianAmalgam
universe u
variable {G : Type u} [Group G] [Finite G]
  {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The point-component core lies in the original Sylow, hence normalizes L₁. -/
theorem point_component_core_normalizes_residual
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (C : ComponentGeometry F L) :
    C.K1.pCoreIn 2 ≤ normalizer (F.Li L 1 : Set G) := by
  have hn : F.H ≤ normalizer (C.K1.pCoreIn 2 : Set G) :=
    ((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal).trans
      (normalizer_le_normalizer_characteristic_image C.K1 (pCore 2 C.K1))
  have hcH : C.K1.pCoreIn 2 ≤ F.H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 C.K1)
      ((pCoreIn_le 2 C.K1).trans C.point_le) hn
  have hcT : C.K1.pCoreIn 2 ≤ (T : Subgroup G) := by
    apply hcH.trans
    have ht := pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))
    change F.H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf F.H).map F.H.subtype at ht
    exact ht.trans_eq (map_subgroupOf_eq_of_le (F.invariant 1))
  exact hcT.trans (Components.sylow_normalizes_Li h earlier F 1)

omit [Finite G] in
/-- The literal quotient-action kernel has commutators in the literal core. -/
theorem point_quotient_centralizer_commutator
    (F : InvariantFlag T V n) (C : ComponentGeometry F L) :
    ⁅pointQuotientCentralizer C,C.K1⁆ ≤ C.K1.pCoreIn 2 := by
  apply commutator_le.mpr
  intro d hd k hk
  obtain ⟨d,hd,rfl⟩ := hd
  have he := congrArg (fun a : MulAut (C.K1 ⧸ pCore 2 C.K1) =>
    a (QuotientGroup.mk' (pCore 2 C.K1) ⟨k,hk⟩)) hd
  change quotientAut (pCore 2 C.K1) _ (QuotientGroup.mk' (pCore 2 C.K1) ⟨k,hk⟩) =
    QuotientGroup.mk' (pCore 2 C.K1) ⟨k,hk⟩ at he
  rw [quotientAut_apply_mk] at he
  have hh := QuotientGroup.eq_iff_div_mem.mp he
  refine ⟨_,hh,?_⟩
  change ((d : G) * k * (d : G)⁻¹) / k = ⁅(d : G),k⁆
  exact div_eq_mul_inv _ _

private theorem normalizes_twoPerfect_of_commutator
    {X : Type*} [Group X] (A Q B : Subgroup X) [Q.Normal]
    (hA : IsPPerfect 2 A) (hQ : IsPGroup 2 Q)
    (hQA : Q ≤ normalizer (A : Set X)) (hAB : ⁅A,B⁆ ≤ Q) :
    B ≤ normalizer (A : Set X) := by
  let q := QuotientGroup.mk' Q
  have hc : ⁅A.map q,B.map q⁆ = ⊥ := by
    rw [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
    exact hAB
  have hn : B.map q ≤ normalizer (A.map q : Set (X ⧸ Q)) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hh := map_le_iff_le_comap.mp hn
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact hQ
  have hkA : q.ker ≤ normalizer (A : Set X) := by rw [QuotientGroup.ker_mk']; exact hQA
  rwa [comap_normalizer_map_of_pPerfect q A hA hk hkA] at hh

/-- Centralization on K₁/O₂(K₁) already normalizes the original L₁.
The essential core-normalization premise is supplied by the original Sylow. -/
theorem point_quotient_centralizer_normalizes_residual
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (C : ComponentGeometry F L) :
    pointQuotientCentralizer C ≤ normalizer (F.Li L 1 : Set G) := by
  let A := (F.Li L 1).subgroupOf F.H
  let Q := (C.K1.pCoreIn 2).subgroupOf F.H
  let D := (pointQuotientCentralizer C).subgroupOf F.H
  have hAH : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  have hQH : C.K1.pCoreIn 2 ≤ F.H := (pCoreIn_le 2 C.K1).trans C.point_le
  have hDH : pointQuotientCentralizer C ≤ F.H := map_subtype_le _
  have hnQ : F.H ≤ normalizer (C.K1.pCoreIn 2 : Set G) :=
    ((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal).trans
      (normalizer_le_normalizer_characteristic_image C.K1 (pCore 2 C.K1))
  let : Q.Normal := normal_subgroupOf_of_le_normalizer hnQ
  have hQA : Q ≤ normalizer (A : Set F.H) := by
    intro q hq a
    exact point_component_core_normalizes_residual h earlier F C hq (a : G)
  have hA : IsPPerfect 2 A := (Components.Li_twoPerfect F 1).of_surjective
    (subgroupOfEquivOfLe hAH).symm.toMonoidHom (subgroupOfEquivOfLe hAH).symm.surjective
  have hcomm : ⁅A,D⁆ ≤ Q := by
    apply map_le_map_iff_of_injective F.H.subtype_injective |>.mp
    rw [map_commutator,map_subgroupOf_eq_of_le hAH,map_subgroupOf_eq_of_le hDH,
      map_subgroupOf_eq_of_le hQH,commutator_comm]
    exact (commutator_mono le_rfl C.contains).trans (point_quotient_centralizer_commutator F C)
  have hn := normalizes_twoPerfect_of_commutator A Q D hA
    (isPGroup_pCoreIn 2 C.K1).comap_subtype hQA hcomm
  intro d hd
  have hdn := hn (show (⟨d,hDH hd⟩ : F.H) ∈ D from hd)
  rw [←map_subgroupOf_eq_of_le hAH]
  exact A.le_normalizer_map F.H.subtype (mem_map_of_mem F.H.subtype hdn)

/-- The same kernel centralizes L₁ modulo its own two-core, not just that of K₁. -/
theorem point_quotient_centralizer_residual_commutator
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (C : ComponentGeometry F L) :
    ⁅pointQuotientCentralizer C,F.Li L 1⁆ ≤ (F.Li L 1).pCoreIn 2 := by
  have hn := point_quotient_centralizer_normalizes_residual h earlier F C
  have hcap : F.Li L 1 ⊓ C.K1.pCoreIn 2 ≤ (F.Li L 1).pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 C.K1).to_le inf_le_right) inf_le_left
      ((le_inf (F.Li L 1).le_normalizer
        (C.contains.trans (C.K1.le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image C.K1 (pCore 2 C.K1))))).trans
            inf_normalizer_le_normalizer_inf)
  exact (le_inf (le_normalizer_iff_commutator_le_right.mp hn)
    ((commutator_mono le_rfl C.contains).trans (point_quotient_centralizer_commutator F C))).trans hcap

omit [Finite G] in
/-- The original quotient-action centralizer is normal in the point normalizer. -/
theorem point_quotient_centralizer_normal
    (F : InvariantFlag T V n) (C : ComponentGeometry F L) :
    F.H ≤ normalizer (pointQuotientCentralizer C : Set G) := by
  change F.H ≤ normalizer ((pointQuotientAction C).ker.map F.H.subtype : Set G)
  simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
    (pointQuotientAction C).ker.le_normalizer_map F.H.subtype

private theorem point_interval_mem_HOver
    (h : HigherRankHypothesis K T L V n) (F : InvariantFlag T V n)
    {J : Subgroup G} (hTJ : (T : Subgroup G) ≤ J) (hJH : J ≤ F.H) :
    J ∈ Chapter1.HOver G (T : Set G) := by
  have hcard : Nat.card (F.Vi 1) = 2 := by
    simpa using F.card 1 (by have := h.rank; omega)
  have hp : IsPGroup 2 (F.Vi 1) := IsPGroup.of_card (n := 1) (by simpa using hcard)
  have hcore := le_pCoreIn_of_normalizes hp
    (((F.le_seed 1).trans h.chosen.le_sylow).trans hTJ) hJH
  refine ⟨?_,hTJ⟩
  intro he
  have hb : F.Vi 1 = ⊥ := bot_unique (he ▸ hcore)
  rw [hb,card_bot] at hcard
  contradiction

/-- Failure of source 12.9.5(1) supplies its actual Case I overgroup.
Its two-residual lies in the original quotient centralizer; adjoining L₁
gives a member of Hz in which that same L₁ is normal. -/
theorem point_centralizer_escape
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (C : ComponentGeometry F L)
    (hout : ¬ pointQuotientCentralizer C ≤ normalizer (L : Set G)) :
    ∃ H₁ : Subgroup G,
      H₁ ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      H₁ ≤ pointQuotientCentralizer C ⊔ (T : Subgroup G) ∧
      (pResidual 2 H₁).map H₁.subtype ≤ pointQuotientCentralizer C ∧
      (F.Li L 1 ⊔ H₁) ∈ F.Hz L (normalizer (L : Set G)) ∧
      ((F.Li L 1).subgroupOf (F.Li L 1 ⊔ H₁)).Normal ∧
      ⁅(pResidual 2 H₁).map H₁.subtype,F.Li L 1⁆ ≤ (F.Li L 1).pCoreIn 2 := by
  let D := pointQuotientCentralizer C
  let J := D ⊔ (T : Subgroup G)
  let M := normalizer (L : Set G)
  have hDH : D ≤ F.H := map_subtype_le _
  have hJH : J ≤ F.H := sup_le hDH (F.invariant 1)
  have hJM : ¬ J ≤ M := fun he => hout (le_sup_left.trans he)
  let P := fun H : Subgroup G => H ∈ Chapter1.HOver G (T : Set G) ∧ ¬ H ≤ M
  obtain ⟨H₁,hHJ,hH,hmin⟩ := exists_minimal_le_of_wellFoundedLT P J
    (show P J from ⟨point_interval_mem_HOver h F le_sup_right hJH,hJM⟩)
  have hstar : H₁ ∈ Chapter3.HStar (T : Subgroup G) M := ⟨hH,hmin⟩
  have hDn : J ≤ normalizer (D : Set G) :=
    hJH.trans (point_quotient_centralizer_normal F C)
  let : (D.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hDn
  have hquot : IsPGroup 2 (J ⧸ D.subgroupOf J) :=
    isPGroup_quotient_of_sup_eq_top (D.subgroupOf J)
      ((T : Subgroup G).subgroupOf J) T.isPGroup'.comap_subtype
      (codisjoint_subgroupOf_sup D (T : Subgroup G)).eq_top
  have hrJ : pResidual 2 J ≤ D.subgroupOf J := sInf_le ⟨inferInstance,hquot⟩
  have hr : (pResidual 2 H₁).map H₁.subtype ≤ D := by
    have hh := (map_pResidual_le 2 (inclusion hHJ)).trans hrJ
    have hh' := map_mono (f := J.subtype) hh
    rw [map_map,map_subgroupOf_eq_of_le (show D ≤ J from le_sup_left)] at hh'
    exact hh'
  have hn₁ : H₁ ≤ normalizer (F.Li L 1 : Set G) := hHJ.trans
    (sup_le (point_quotient_centralizer_normalizes_residual h earlier F C)
      (Components.sylow_normalizes_Li h earlier F 1))
  have hNH : F.Li L 1 ⊔ H₁ ≤ F.H :=
    sup_le ((F.Li_le L 1).trans inf_le_right) (hHJ.trans hJH)
  have hTN : (T : Subgroup G) ≤ F.Li L 1 ⊔ H₁ := (show (T : Subgroup G) ≤ H₁ from hstar.1.1.2).trans le_sup_right
  refine ⟨H₁,hstar,hHJ,hr,?_,normal_subgroupOf_of_le_normalizer
    (sup_le (F.Li L 1).le_normalizer hn₁),?_⟩
  · refine ⟨⟨(point_interval_mem_HOver h F hTN hNH).1,?_⟩,hNH,?_⟩
    · intro x hx
      rcases hx with hx | hx
      · exact mem_sup_left hx
      · exact hTN hx
    · exact fun he => hstar.1.2 (le_sup_right.trans he)
  · exact (commutator_mono hr le_rfl).trans
      (point_quotient_centralizer_residual_commutator h earlier F C)

/-- The original F.9 actor prevents a point overgroup from normalizing
its overlap L₁T: otherwise the actor would vanish modulo O₂(J). -/
theorem abelian_local_not_normalizes_edge
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G))) :
    ¬ J ≤ normalizer ((F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G) : Set G) := by
  intro hn
  obtain ⟨hU,a,_,B,hBR,hA,_,_⟩ := abelian_local_quadratic_actor h earlier F hab J hJ
  let := hU
  have hEJ : F.Li L 1 ⊔ (T : Subgroup G) ≤ J := sup_le
    (F.Li_one_le_of_mem_Hz hJ) (F.sylow_le_of_mem_Hz hJ)
  have hRJ : F.Ri L 1 ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 _) ((pCoreIn_le 2 _).trans hEJ)
    (hn.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  apply hA.1
  apply (Subgroup.map_eq_bot_iff B).mpr
  rw [QuotientGroup.ker_mk']
  intro b hb
  obtain ⟨x,hx,he⟩ := hRJ (hBR hb)
  have he' : x = b := Subtype.ext he
  exact he' ▸ hx

/-- Case I yields a genuine minimal parabolic of the original Sylow.
Normality of that Sylow would preserve L₁T, contradicting the actual
nonzero F.9 actor, so no extra Sylow-normalizer premise is needed. -/
theorem point_centralizer_escape_minimal
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (hout : ¬ pointQuotientCentralizer C ≤ normalizer (L : Set G)) :
    ∃ H₁ : Subgroup G,
      H₁ ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ChapterB.IsMinimalParabolicOver T H₁ ∧
      H₁ ≤ pointQuotientCentralizer C ⊔ (T : Subgroup G) ∧
      (pResidual 2 H₁).map H₁.subtype ≤ pointQuotientCentralizer C ∧
      (F.Li L 1 ⊔ H₁) ∈ F.Hz L (normalizer (L : Set G)) ∧
      ((F.Li L 1).subgroupOf (F.Li L 1 ⊔ H₁)).Normal ∧
      ⁅(pResidual 2 H₁).map H₁.subtype,F.Li L 1⁆ ≤ (F.Li L 1).pCoreIn 2 := by
  obtain ⟨H₁,hstar,hHJ,hr,hJ,hn,hcomm⟩ := point_centralizer_escape h earlier F C hout
  refine ⟨H₁,hstar,?_,hHJ,hr,hJ,hn,hcomm⟩
  apply Chapter3.HStar.minimalParabolic T (h.sylow_normalizes earlier.structural) hstar
  right
  intro hnorm
  have hTN : H₁ ≤ normalizer (T : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show (T : Subgroup G) ≤ H₁ from hstar.1.1.2)).mp hnorm
  have hLN : H₁ ≤ normalizer (F.Li L 1 : Set G) :=
    le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer (show F.Li L 1 ≤ F.Li L 1 ⊔ H₁
      from le_sup_left)).mp hn)
  apply abelian_local_not_normalizes_edge h earlier F hab _ hJ
  exact sup_le (le_sup_left.trans (F.Li L 1 ⊔ (T : Subgroup G)).le_normalizer)
    ((le_inf hLN hTN).trans (normalizer_inf_normalizer_le_normalizer_sup _ _))

/-- Homogeneous natural coordinates on the exact U_J/V₁ of the F.9 action.
The quotient equivalence is induced by the original map into G₁/V₁, and
the action equation retains the original L₁ inclusion and J/O₂(J) map. -/
theorem normal_local_quotient_natural_coordinates
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    [((F.Li L 1).subgroupOf J).Normal] [IsElementaryAbelian 2 (F.UH J)]
    (a : LocalQuotientAction J (F.UH J) (F.Vi 1)) :
    ∃ α : F.Li L 1 →* BinaryLinear.OuterCyclic.LinearGroup (n - 1),
      Function.Surjective α ∧ α.ker = pCore 2 (F.Li L 1) ∧
      ∃ r : ℕ, ∃ e : Additive (F.UH J ⧸ (F.Vi 1).subgroupOf (F.UH J)) ≃ₗ[ZMod 2]
          (Fin r → Fin (n - 1) → ZMod 2),
        ∀ (k : F.Li L 1) u i,
          e (a.representation (QuotientGroup.mk' (pCore 2 J)
            (inclusion (F.Li_one_le_of_mem_Hz hJ) k)) u) i = α k (e u i) := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  let := F.localKernel_tilde_UH_elementary h.source.simpleQTKE L _ J
    (by have := h.rank; omega) h.chosen.le_sylow h.chosen.normalizes
    (h.sylow_normalizes earlier.structural) h.residual (fun _ => ⟨h.naturalMarking⟩) hJ
  have hUH : F.UH J ≤ F.H := a.le_local.trans hJ.2.1
  let q := F.tildeMap (F.UH J) hUH
  have hk : q.ker = (F.Vi 1).subgroupOf (F.UH J) := by
    ext u
    change q u = 1 ↔ _
    rw [Subtype.ext_iff]
    change F.tildeProjection ⟨u,hUH u.property⟩ = 1 ↔ _
    exact QuotientGroup.eq_one_iff _
  let e₀ : (F.UH J ⧸ (F.Vi 1).subgroupOf (F.UH J)) ≃* F.tilde (F.UH J) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q (F.tildeMap_surjective _ hUH))
  let e₁ : Additive (F.UH J ⧸ (F.Vi 1).subgroupOf (F.UH J)) ≃ₗ[ZMod 2]
      Additive (F.tilde (F.UH J)) :=
    LinearEquiv.ofBijective (e₀.toMonoidHom.toAdditive.toZModLinearMap 2) e₀.bijective
  have hem (u : F.UH J) : e₁ (Additive.ofMul (QuotientGroup.mk' _ u)) =
      Additive.ofMul (q u) := rfl
  have hea (j : J) (u : Additive (F.UH J ⧸ (F.Vi 1).subgroupOf (F.UH J))) :
      e₁ (a.representation (QuotientGroup.mk' (pCore 2 J) j) u) =
        Additive.ofMul (F.localTildeAction J hJ.2.1 j (e₁ u).toMul) := by
    obtain ⟨v,hv⟩ := QuotientGroup.mk'_surjective ((F.Vi 1).subgroupOf (F.UH J)) u.toMul
    have hv' : Additive.ofMul (QuotientGroup.mk' _ v) = u := congrArg Additive.ofMul hv
    rw [←hv',a.conjugation,hem,hem]
    exact congrArg Additive.ofMul (F.tildeAction_apply_map J (F.UH J) hJ.2.1
      hUH a.normalizes j v).symm
  obtain ⟨D,r,e,_,he,_⟩ := F.homogeneous_natural_decomposition_of_ambient
    h.rank.1 h.rank.2 L h.chosen.normalizes h.naturalMarking hJ
  let eU := (e₁.trans e).trans (LinearEquiv.piCongrRight (fun _ => D.coordinates))
  refine ⟨D.naturalActor,D.naturalActor_surjective (by rcases hn with rfl | rfl <;> decide),?_,r,eU,?_⟩
  · rw [NaturalSeedMarking.naturalActor,MonoidHom.ker_comp_of_injective _ _ Subtype.val_injective,
      MonoidHom.ker_comp_of_injective _ _ D.quotientEquiv.injective,QuotientGroup.ker_mk']
  intro k u i
  change D.coordinates (e (e₁ (a.representation _ u)) i) = _
  rw [hea,he]
  exact D.equivariant k (e (e₁ u) i)

omit [Finite G] in
private theorem normal_local_commuting_images
    (F : InvariantFlag T V n) {J X : Subgroup G}
    (hLJ : F.Li L 1 ≤ J) [((F.Li L 1).subgroupOf J).Normal]
    (hXJ : X ≤ J) (hc : ⁅X,F.Li L 1⁆ ≤ (F.Li L 1).pCoreIn 2) :
    (X.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) ≤
      centralizer (((F.Li L 1).subgroupOf J).map
        (QuotientGroup.mk' (pCore 2 J)) : Set (J ⧸ pCore 2 J)) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
  apply map_le_map_iff_of_injective J.subtype_injective |>.mp
  rw [map_commutator,map_subgroupOf_eq_of_le hXJ,map_subgroupOf_eq_of_le hLJ]
  exact hc.trans (pCoreIn_mono_of_normalizes hLJ
    ((normal_subgroupOf_iff_le_normalizer hLJ).mp inferInstance))

/-- The edge core acts on multiplicities: its literal image in J/O₂(J)
centralizes the natural L₁ image whenever L₁ is normal in J. -/
theorem normal_local_edge_core_commuting_images
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) {J : Subgroup G}
    (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    [((F.Li L 1).subgroupOf J).Normal] :
    ((F.Ri L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) ≤
      centralizer (((F.Li L 1).subgroupOf J).map
        (QuotientGroup.mk' (pCore 2 J)) : Set (J ⧸ pCore 2 J)) := by
  let E := F.Li L 1 ⊔ (T : Subgroup G)
  have hEN : E ≤ normalizer (F.Li L 1 : Set G) :=
    sup_le (F.Li L 1).le_normalizer (Components.sylow_normalizes_Li h earlier F 1)
  have hER : E ≤ normalizer (F.Ri L 1 : Set G) :=
    E.le_normalizer.trans (normalizer_le_normalizer_characteristic_image E (pCore 2 E))
  have hRL : ⁅F.Ri L 1,F.Li L 1⁆ ≤ F.Li L 1 :=
    le_normalizer_iff_commutator_le_right.mp ((pCoreIn_le 2 E).trans hEN)
  have hRR : ⁅F.Ri L 1,F.Li L 1⁆ ≤ F.Ri L 1 :=
    le_normalizer_iff_commutator_le_left.mp ((show F.Li L 1 ≤ E from le_sup_left).trans hER)
  apply normal_local_commuting_images F (F.Li_one_le_of_mem_Hz hJ)
    ((pCoreIn_le 2 E).trans (sup_le (F.Li_one_le_of_mem_Hz hJ) (F.sylow_le_of_mem_Hz hJ)))
  exact (le_inf hRL hRR).trans (inf_pCoreIn_le_of_le 2 (show F.Li L 1 ≤ E from le_sup_left))

/-- The same escaping minimal parabolic, original quadratic actor, and natural
coordinates needed in Case I of 12.9.5. Both its residual and the actual
quadratic actor centralize the natural image in the literal J/O₂(J).
The chief-factor multiplicity inequality is the remaining source step. -/
theorem point_centralizer_escape_quadratic_coordinates
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (hout : ¬ pointQuotientCentralizer C ≤ normalizer (L : Set G)) :
    ∃ H₁ : Subgroup G,
      H₁ ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ChapterB.IsMinimalParabolicOver T H₁ ∧
      (pResidual 2 H₁).map H₁.subtype ≤ pointQuotientCentralizer C ∧
      let J := F.Li L 1 ⊔ H₁
      ∃ hJ : J ∈ F.Hz L (normalizer (L : Set G)),
        ((F.Li L 1).subgroupOf J).Normal ∧
        ∃ hU : IsElementaryAbelian 2 (F.UH J),
          let := hU
          ∃ a : LocalQuotientAction J (F.UH J) (F.Vi 1),
            quadraticRatio a.representation ≤ 2 ∧
            let q := QuotientGroup.mk' (pCore 2 J)
            ∃ B : Subgroup J,
              B ≤ (F.Ri L 1).subgroupOf J ∧ B ≤ H₁.subgroupOf J ∧
              IsElementaryTwo (B.map q) ∧ IsQuadratic a.representation (B.map q) ∧
              fixedCodim a.representation (B.map q) ≤ 2 * rank (B.map q) ∧
              B.map q ≤ centralizer (((F.Li L 1).subgroupOf J).map q : Set (J ⧸ pCore 2 J)) ∧
              (((pResidual 2 H₁).map H₁.subtype).subgroupOf J).map q ≤
                centralizer (((F.Li L 1).subgroupOf J).map q : Set (J ⧸ pCore 2 J)) ∧
              ∃ α : F.Li L 1 →* BinaryLinear.OuterCyclic.LinearGroup (n - 1),
                Function.Surjective α ∧ α.ker = pCore 2 (F.Li L 1) ∧
                ∃ r : ℕ, 0 < r ∧ ∃ e : Additive (F.UH J ⧸ (F.Vi 1).subgroupOf (F.UH J)) ≃ₗ[ZMod 2]
                    (Fin r → Fin (n - 1) → ZMod 2),
                  ∀ (k : F.Li L 1) u i,
                    e (a.representation (q (inclusion (F.Li_one_le_of_mem_Hz hJ) k)) u) i =
                      α k (e u i) := by
  obtain ⟨H₁,hstar,hmin,_,hr,hJ,hN,hcomm⟩ :=
    point_centralizer_escape_minimal h earlier F hab C hout
  let J := F.Li L 1 ⊔ H₁
  let := hN
  obtain ⟨hU,a,ha,B,hBR,hB,hquad,hbound⟩ := abelian_local_quadratic_actor h earlier F hab J hJ
  let := hU
  have hRT : F.Ri L 1 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow (F.Li L 1 ⊔ (T : Subgroup G)) (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  refine ⟨H₁,hstar,hmin,hr,hJ,hN,hU,a,ha,B,hBR,?_,hB,hquad,hbound,?_,?_,?_⟩
  · intro b hb
    exact (show (T : Subgroup G) ≤ H₁ from hstar.1.1.2) (hRT (hBR hb))
  · exact (map_mono hBR).trans (normal_local_edge_core_commuting_images h earlier F hJ)
  · exact normal_local_commuting_images F (F.Li_one_le_of_mem_Hz hJ)
      ((map_subtype_le _).trans le_sup_right) hcomm
  · obtain ⟨α,hα,hker,r,e,he⟩ := normal_local_quotient_natural_coordinates h hn earlier F J hJ a
    refine ⟨α,hα,hker,r,?_,e,he⟩
    by_contra! hr
    have hr0 : r = 0 := Nat.eq_zero_of_le_zero hr
    have hzero (u : Additive (F.UH J ⧸ (F.Vi 1).subgroupOf (F.UH J))) : u = 0 := by
      apply e.injective
      ext i
      exact Fin.elim0 (hr0 ▸ i)
    have hone (g : J ⧸ pCore 2 J) : g = 1 := by
      apply a.faithful
      ext u
      exact (hzero _).trans (hzero _).symm
    exact hB.1 (bot_unique (fun g _ => hone g))

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
