module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFixedSpacesLines
public import Theory.Representation.CentralCoverOriginalAction.Quadratic
public import Theory.Representation.SL2NaturalOffenders.Semilinear
public import Theory.GroupTheory.ReducedNormal.CentralSeedClosure
public import Theory.GroupTheory.PCoreCentralQuotient
public import Theory.GroupTheory.PCoreSurjective
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalEscapeDefs

/-!
# The two-core and reduced quotient of the escaping conjugate closure

The pointwise fixer of the natural Sylow line acts linearly over its defining
field: semilinearity and one nonzero fixed field line eliminate the field
coefficient. Its one-dimensional quotient action has two-power order, hence is
trivial. This proves [V_L,C_T(Z_S)] = Z_S on the original ambient subgroups.

Inside I = C_G(Z_S), the quotient by the central Z_S has characteristic two.
The image of V_L is a central elementary Sylow seed, so B.2.14 makes its normal
closure reduced and central in the quotient two-core. Lifting through the
literal quotient gives U ≤ O₂(I), [U,O₂(I)] ≤ Z_S, U ≤ T and elementarity of
U/Z_S. These conclusions require the initial natural action, but no escape
geometry, size bound or PSL₂ component is assumed.

Source: Aschbacher–Smith, 6.1.17(1–2) for H = IT and 6.1.20(1), printed
pp.672–675, using B.2.14. The initial-action proof and the remaining escaping
geometry stay with qt-d-1222-rankone-recognition-natural.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open ConjugateFixedSpaces

private theorem displacement_mem_line
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (W : Submodule F (Fin 2 → F)) (hd : Module.finrank F W = 1)
    (d : Module.End F (Fin 2 → F)) (hfix : ∀ w ∈ W, d w = w)
    {k : ℕ} (hp : d ^ (2 ^ k) = 1) (v : Fin 2 → F) : d v - v ∈ W := by
  have hn : W ≤ W.comap d := fun w hw => by simpa only [Submodule.mem_comap, hfix w hw] using hw
  let a := W.mapQ W d hn
  have ha : a ^ (2 ^ k) = 1 := by
    change (W.mapQ W d hn) ^ (2 ^ k) = 1
    rw [← Submodule.mapQ_pow]
    simp [hp, Module.End.one_eq_id]
  have hdim : Module.finrank F ((Fin 2 → F) ⧸ W) = 1 := by
    have hh := W.finrank_quotient_add_finrank
    simp only [Module.finrank_pi, Fintype.card_fin, hd] at hh
    omega
  obtain ⟨c, hc, _⟩ := a.existsUnique_eq_smul_id_of_finrank_eq_one hdim
  have hc1 : c ^ (2 ^ k) = 1 := by
    obtain ⟨w, hw⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (show 0 < Module.finrank F ((Fin 2 → F) ⧸ W) by omega)
    apply smul_left_injective F hw
    have hh := LinearMap.congr_fun ha w
    rw [hc, smul_pow] at hh
    simpa using hh
  have hcOne : c = 1 := by
    simpa using (ExpChar.pow_prime_pow_mul_eq_one_iff 2 k 1 c).mp (by simpa using hc1)
  have he : a = 1 := by simpa [hcOne, Module.End.one_eq_id] using hc
  apply (Submodule.Quotient.mk_eq_zero W).mp
  have hh := LinearMap.congr_fun he (W.mkQ v)
  change W.mkQ (d v) = W.mkQ v at hh
  change W.mkQ (d v - v) = 0
  rw [map_sub, hh, sub_self]

universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass.{u}} {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- The central-line fixer in the original Sylow has exactly the same commutator
line as T ∩ L. -/
theorem natural_central_line_sylow_commutator
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n) :
    ⁅layer L V, (T : Subgroup G) ⊓ centralizer (ZS (T : Subgroup G) L V : Set G)⁆ =
      ZS (T : Subgroup G) L V := by
  have hgeo := hnatural.sylow_intersection_geometry T h.sylow_normalizes_L
  apply le_antisymm
  · rw [commutator_comm]
    apply commutator_le.mpr
    intro s hs v hv
    obtain ⟨F, _, _, _, hF, e, f, hf⟩ := hnatural
    let : Algebra (ZMod 2) F := ZMod.algebra _ 2
    let W := sylowSpace (T : Subgroup G) e
    have hW : W.toAddSubgroup = coordinateSpace f (ZS (T : Subgroup G) L V) :=
      AddSubgroup.ext (mem_sylowSpace_iff (T : Subgroup G) e f hf)
    have hc : Nat.card W = Nat.card F := by
      change Nat.card W.toAddSubgroup = Nat.card F
      rw [hW, coordinateSpace_card f (show ZS (T : Subgroup G) L V ≤ layer L V from inf_le_left), hF]
      exact hgeo.1
    have hd : Module.finrank F W = 1 := by
      apply Nat.pow_right_injective (Finite.one_lt_card (α := F))
      change Nat.card F ^ Module.finrank F W = Nat.card F ^ 1
      rw [← Module.natCard_eq_pow_finrank, hc, pow_one]
    let sB : normalizer (layer L V : Set G) := ⟨s, h.sylow_normalizes_layer hs.1⟩
    let sL : normalizer (L : Set G) := ⟨s, h.sylow_normalizes_L hs.1⟩
    let a := vectorActor f sB
    have hfix : ∀ w ∈ W, a w = w := by
      intro w hw
      have hz : (f.symm (Multiplicative.ofAdd w) : G) ∈ ZS (T : Subgroup G) L V := by
        exact (show w ∈ coordinateSpace f (ZS (T : Subgroup G) L V) from hW ▸ hw)
      apply (vectorActor_fixed_iff f sB w).mpr
      exact mem_centralizer_singleton_iff.mpr (hs.2 _ hz)
    obtain ⟨σ, hσ⟩ := Representation.OneCohomology.CentralCoverOriginalAction.normalizer_semilinear
      (Representation.specialLinearNatural 2 (k := F))
      (fun k hk => Representation.SL2NaturalOffenders.centralizer_scalar k hk)
      (quotientActor e sL) a (vectorActor_intertwines e f hf sL sB.property)
    obtain ⟨w, hw, hw0⟩ := W.ne_bot_iff.mp (Submodule.isAtom_iff_finrank_eq_one.mpr hd).ne_bot
    have hsigma (c : F) : σ c = c := by
      apply smul_left_injective F hw0
      change σ c • w = c • w
      calc
        σ c • w = σ c • a w := by rw [hfix w hw]
        _ = a (c • w) := (hσ c w).symm
        _ = c • w := hfix _ (W.smul_mem c hw)
    let d : Module.End F (Fin 2 → F) := {
      toFun := a
      map_add' := a.map_add
      map_smul' := fun c w => by simpa only [RingHom.id_apply, hsigma] using hσ c w }
    obtain ⟨k, hk⟩ := isPGroup_iff_pow_pow_eq_one.mp T.isPGroup' ⟨s,hs.1⟩
    have hsPow : s ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have hp : d ^ (2 ^ k) = 1 := by
      have hpow (j : ℕ) (w : Fin 2 → F) :
          (f.symm (Multiplicative.ofAdd ((d ^ j) w)) : G) =
            s ^ j * (f.symm (Multiplicative.ofAdd w) : G) * (s ^ j)⁻¹ := by
        induction j with
        | zero => simp
        | succ j ih =>
          rw [pow_succ', Module.End.mul_apply]
          change (f.symm (Multiplicative.ofAdd (a ((d ^ j) w))) : G) = _
          rw [vectorActor_coe, ih]
          change s * (s ^ j * _ * (s ^ j)⁻¹) * s⁻¹ = _
          simp only [pow_succ']
          group
      apply LinearMap.ext
      intro w
      apply Multiplicative.ofAdd.injective
      apply f.symm.injective
      apply Subtype.ext
      simpa only [hsPow, one_mul, inv_one, mul_one, Module.End.one_apply] using hpow (2 ^ k) w
    have hdisp := displacement_mem_line W hd d hfix hp (f ⟨v,hv⟩).toAdd
    have hz : (f.symm (Multiplicative.ofAdd (a (f ⟨v,hv⟩).toAdd - (f ⟨v,hv⟩).toAdd)) : G) ∈
        ZS (T : Subgroup G) L V := by
      exact (show a (f ⟨v,hv⟩).toAdd - (f ⟨v,hv⟩).toAdd ∈ coordinateSpace f
        (ZS (T : Subgroup G) L V) from hW ▸ hdisp)
    rw [ofAdd_sub, map_div, Subgroup.coe_div, vectorActor_coe,
      ofAdd_toAdd, f.symm_apply_apply] at hz
    simpa only [sB, div_eq_mul_inv, commutatorElement_def] using hz
  · change layer L V ⊓ centralizer ((T : Subgroup G) ⊓ L : Set G) ≤ _
    rw [← hgeo.2]
    apply commutator_mono le_rfl
    exact le_inf inf_le_left (le_centralizer_iff.mp inf_le_right)

private theorem central_quotient_seed_closure
    {H : Type*} [Group H] [Finite H] (P : Sylow 2 H)
    (B Z : Subgroup H) [IsElementaryAbelian 2 B] [Z.Normal]
    (hZ : Z ≤ center H) (hchar : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hBP : B ≤ P) (hcomm : ⁅B, (P : Subgroup H)⁆ ≤ Z) :
    IsPReduced 2 ((normalClosure (B : Set H)).map (QuotientGroup.mk' Z)) ∧
      normalClosure (B : Set H) ≤ pCore 2 H ∧
      ⁅normalClosure (B : Set H), pCore 2 H⁆ ≤ Z := by
  let q := QuotientGroup.mk' Z
  have hq := QuotientGroup.mk'_surjective Z
  have hqchar : centralizer (pCore 2 (H ⧸ Z) : Set (H ⧸ Z)) ≤ pCore 2 (H ⧸ Z) :=
    q.centralizer_pCore_le_of_surjective_centralKernel hq
      (by rwa [QuotientGroup.ker_mk']) hchar
  let Pq := P.mapSurjective hq
  have hBc : B.map q ≤ centralizer (Pq : Set (H ⧸ Z)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    change ⁅B.map q, (P : Subgroup H).map q⁆ = ⊥
    rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hcomm
  let : IsElementaryAbelian 2 (B.map q) := IsElementaryAbelian.map q
  have hr := centralSeed_normalClosure_reduced Pq (B.map q) (map_mono hBP) hBc hqchar
  have he : (normalClosure (B : Set H)).map q = normalClosure (B.map q : Set (H ⧸ Z)) :=
    map_normalClosure (B : Set H) q hq
  rw [← he] at hr
  have hZQ : Z ≤ pCore 2 H := (hZ.trans (center_le_centralizer _)).trans hchar
  have hpre : (pCore 2 (H ⧸ Z)).comap q = pCore 2 H :=
    q.comap_pCore_of_ker_isPGroup hq (by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup.to_le hZQ)
  refine ⟨hr, ?_, ?_⟩
  · rw [← hpre]
    exact map_le_iff_le_comap.mp hr.le_pCore
  · have hmap : (pCore 2 H).map q ≤ pCore 2 (H ⧸ Z) := by
      rw [← hpre, map_comap_eq_self_of_surjective hq]
    have hzero : ⁅(normalClosure (B : Set H)).map q, (pCore 2 H).map q⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr
        (hr.le_centralizer_pCore.trans (centralizer_le hmap))
    rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hzero
    exact hzero

omit [Finite G] in
/-- The denominator is normal relative to its actual centralizer. -/
theorem natural_escape_central_line_normal :
    ((ZS (T : Subgroup G) L V).subgroupOf (Escape.I (T : Subgroup G) L V)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  exact Subgroup.centralizer_le_normalizer _

/-- Source 6.1.17(2) and 6.1.20(1) on the literal image of U in I/Z_S.
The two-core and centrality conclusions are lifted back to G. -/
theorem natural_escape_reduced_core
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n) :
    letI := natural_escape_central_line_normal (T := T) (L := L) (V := V)
    IsPReduced 2 (((Escape.U (T : Subgroup G) L V).subgroupOf (Escape.I (T : Subgroup G) L V)).map
      (QuotientGroup.mk' ((ZS (T : Subgroup G) L V).subgroupOf (Escape.I (T : Subgroup G) L V)))) ∧
    Escape.U (T : Subgroup G) L V ≤ (Escape.I (T : Subgroup G) L V).pCoreIn 2 ∧
      ⁅Escape.U (T : Subgroup G) L V, (Escape.I (T : Subgroup G) L V).pCoreIn 2⁆ ≤
        ZS (T : Subgroup G) L V := by
  let I := Escape.I (T : Subgroup G) L V
  let Z := ZS (T : Subgroup G) L V
  let B := layer L V
  have hBI : B ≤ I := h.layer_centralizes_ZS
  have hZI : Z ≤ I := inf_le_left.trans hBI
  have hTI : (T : Subgroup G) ≤ normalizer (I : Set G) :=
    h.sylow_normalizes_ZS.trans (normalizer_le_normalizer_centralizer Z)
  obtain ⟨P, hP⟩ := NormalSylowQuotientAction.intersection_sylow T I hTI
  let : (Z.subgroupOf I).Normal := natural_escape_central_line_normal
  let : IsElementaryAbelian 2 B := h.layer_elementary
  let : IsElementaryAbelian 2 (B.subgroupOf I) := IsElementaryAbelian.subgroupOf hBI
  have hZc : Z.subgroupOf I ≤ center I := by
    intro z hz
    exact mem_center_iff.mpr fun i => Subtype.ext (i.property z hz).symm
  have hBP : B.subgroupOf I ≤ P := by
    rw [hP]
    intro b hb
    exact h.layer_le_T hb
  have hc : ⁅B.subgroupOf I, (P : Subgroup I)⁆ ≤ Z.subgroupOf I := by
    apply commutator_le.mpr
    intro b hb p hp
    have hpT : (p : G) ∈ (T : Subgroup G) := by
      exact (show p ∈ (T : Subgroup G).subgroupOf I from hP ▸ hp)
    exact (natural_central_line_sylow_commutator h hnatural).le
      (commutator_mem_commutator hb ⟨hpT,p.property⟩)
  obtain ⟨hred, hcore, hcentral⟩ := central_quotient_seed_closure P (B.subgroupOf I)
    (Z.subgroupOf I) hZc (Chapter1.mem_He_iff.mp h.ZS_centralizer_mem_He) hBP hc
  have he : (normalClosure (B.subgroupOf I : Set I)).map I.subtype =
      Escape.U (T : Subgroup G) L V := by
    apply le_antisymm
    · apply map_le_iff_le_comap.mpr
      let : ((Escape.U (T : Subgroup G) L V).subgroupOf I).Normal :=
        normal_subgroupOf_of_le_normalizer
          (le_normalizer_iSup_conjugates B I)
      change normalClosure (B.subgroupOf I : Set I) ≤ (Escape.U (T : Subgroup G) L V).subgroupOf I
      exact normalClosure_le_normal (fun b hb => Escape.layer_le_U _ _ _ hb)
    · apply iSup_le
      intro i
      rintro x ⟨b,hb,rfl⟩
      refine ⟨i * ⟨b,hBI hb⟩ * i⁻¹, ?_, rfl⟩
      exact (inferInstance : (normalClosure (B.subgroupOf I : Set I)).Normal).conj_mem
        _ (le_normalClosure hb) i
  have hsub : normalClosure (B.subgroupOf I : Set I) =
      (Escape.U (T : Subgroup G) L V).subgroupOf I := by
    rw [← he]
    exact (comap_map_eq_self_of_injective I.subtype_injective _).symm
  refine ⟨?_, ?_, ?_⟩
  · rwa [hsub] at hred
  · rw [← he]
    exact map_mono hcore
  · have hh := map_mono (f := I.subtype) hcentral
    rw [map_commutator, he, map_subgroupOf_eq_of_le hZI] at hh
    exact hh

/-- The original conjugate closure lies in the two-core of I and centralizes
that core modulo Z_S. -/
theorem natural_escape_core
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n) :
    Escape.U (T : Subgroup G) L V ≤ (Escape.I (T : Subgroup G) L V).pCoreIn 2 ∧
      ⁅Escape.U (T : Subgroup G) L V, (Escape.I (T : Subgroup G) L V).pCoreIn 2⁆ ≤
        ZS (T : Subgroup G) L V :=
  (natural_escape_reduced_core h hnatural).2

/-- The generated U lies in the original ambient Sylow T. -/
theorem natural_escape_U_le_sylow
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n) : Escape.U (T : Subgroup G) L V ≤ T := by
  have hTI : (T : Subgroup G) ≤ normalizer (Escape.I (T : Subgroup G) L V : Set G) :=
    h.sylow_normalizes_ZS.trans (normalizer_le_normalizer_centralizer _)
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T (Escape.I (T : Subgroup G) L V) hTI
  apply (natural_escape_core h hnatural).1.trans
  have hh := pCoreIn_le_sylow (Escape.I (T : Subgroup G) L V) P
  rw [hP, subgroupOf_map_subtype] at hh
  exact hh.trans inf_le_left

/-- All commutators in the original U lie in the original Z_S. -/
theorem natural_escape_commutator
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n) :
    ⁅Escape.U (T : Subgroup G) L V, Escape.U (T : Subgroup G) L V⁆ ≤ ZS (T : Subgroup G) L V :=
  (commutator_mono le_rfl (natural_escape_core h hnatural).1).trans
    (natural_escape_core h hnatural).2

/-- The literal U/Z_S carrying NaturalEscape.action is elementary abelian. -/
theorem natural_escape_quotient_elementary
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n) :
    letI := h.ZS_normal_in_escape_U
    IsElementaryAbelian 2 (NaturalEscape.Quotient (T : Subgroup G) L V) := by
  let := h.ZS_normal_in_escape_U
  exact NaturalEscape.quotient_elementary_of_commutator _ _ _ h.layer_elementary
    (natural_escape_commutator h hnatural)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
