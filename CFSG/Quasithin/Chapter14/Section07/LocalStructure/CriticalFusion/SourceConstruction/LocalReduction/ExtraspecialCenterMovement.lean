module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSixteenExclusion
public import Theory.GroupTheory.PResidual.PrimeToAction
/-!
# The original residual-core center and its moved chief factor

Put P = O₂(K) and Z = Z(P), both embedded in the original group. The
commutator pairing gives U ∩ Z = V₁. In the central alternative of
14.7.20, [Z,K] lies in V₁; two-perfect commutator idempotence therefore
proves Z ≤ Z(K).

In the faithful alternative, K acts on the abelian Z through its odd
quotient. Coprime splitting separates [Z,K] from the fixed subgroup.
The lower central flank meets Z only in that fixed subgroup, so the
literal inclusion of [Z,K] into the chief numerator has trivial kernel.
If Z is not central in K, chiefness makes this inclusion surjective onto
the original order-64 interval. The resulting equivariant isomorphism
proves [Z,K] is elementary of order 64 and has exact H-action kernel O₂(H).
No moved-center witness or later Data is assumed in the original application.

This supplies the center reduction in Aschbacher–Smith 14.7.21(2), printed
p.1050, refs/quasithin.pdf. Excluding this moved center by Thompson–Baumann
control, the maximal-normalizer clause, and the remaining local reductions
through 14.7.52 are not asserted here. Genuine earlier structural and
faithful-classification inputs retain their existing source producers.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

omit [Finite G] in
private theorem centerControl_normalized :
    F.H ≤ normalizer ((center ((K F).pCoreIn 2)).map ((K F).pCoreIn 2).subtype : Set G) :=
  (le_normalizer_embedded_pResidual 2 F.H).trans
    ((normalizer_le_normalizer_characteristic_image (K F) (pCore 2 (K F))).trans
      (normalizer_le_normalizer_characteristic_image ((K F).pCoreIn 2)
        (center ((K F).pCoreIn 2))))

/-- The literal core center meets U precisely in the original point. -/
theorem extraspecial_core_center_inf_span
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    F.U ⊓ (center ((K F).pCoreIn 2)).map ((K F).pCoreIn 2).subtype = F.Vi 1 := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hUP : F.U ≤ (K F).pCoreIn 2 := span_le_residual_core h hab
  rw [map_center_subtype_eq_inf_centralizer,←inf_assoc,inf_eq_left.mpr hUP]
  exact extraspecial_residual_core_centralizer h hab structural previous hex hcard hexp

/-- The central branch of 14.7.20 implies the center clause of 14.7.21. -/
theorem extraspecial_core_center_central_of_centralizer_central
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (hc : ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U) :
    (center ((K F).pCoreIn 2)).map ((K F).pCoreIn 2).subtype ≤
      (center (K F)).map (K F).subtype := by
  let P := (K F).pCoreIn 2
  let Z := (center P).map P.subtype
  have hZP : Z ≤ P := map_subtype_le _
  have hZK : Z ≤ K F := hZP.trans (pCoreIn_le 2 _)
  have hnorm : K F ≤ normalizer (Z : Set G) :=
    (map_subtype_le _).trans centerControl_normalized
  have hZC : Z ≤ centralizer (F.U : Set G) := by
    have hz : Z ≤ centralizer (P : Set G) := by
      rw [show Z = P ⊓ centralizer (P : Set G) from map_center_subtype_eq_inf_centralizer P]
      exact inf_le_right
    exact hz.trans (centralizer_le (span_le_residual_core h hab))
  have hmove : ⁅Z,K F⁆ ≤ F.Vi 1 := by
    rw [←extraspecial_core_center_inf_span h hab structural previous he]
    exact le_inf ((commutator_mono hZC le_rfl).trans hc)
      (le_normalizer_iff_commutator_le_left.mp hnorm)
  have hpoint : F.Vi 1 ≤ centralizer (K F : Set G) :=
    (le_centralizer_iff.mp (normalizer_le_centralizer_of_card_two _
      (by simpa using F.card 1 (by decide)))).trans (centralizer_le (map_subtype_le _))
  have hid := commutator_isPPerfect_idempotent (K F) Z
    (isPPerfect_embedded_pResidual 2 F.H) ((isPGroup_pCoreIn 2 _).to_le hZP) hnorm
  have hz : ⁅Z,K F⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [←hid]
    exact (commutator_mono hmove le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.mpr hpoint).le
  rw [map_center_subtype_eq_inf_centralizer (K F)]
  exact le_inf hZK (commutator_eq_bot_iff_le_centralizer.mp hz)
private theorem centerControl_splitting
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let P := (K F).pCoreIn 2
    let Z := (center P).map P.subtype
    ⁅Z,K F⁆ ⊔ (Z ⊓ centralizer (K F : Set G)) = Z ∧
      ⁅Z,K F⁆ ⊓ (Z ⊓ centralizer (K F : Set G)) = ⊥ := by
  let P := (K F).pCoreIn 2
  let Z := (center P).map P.subtype
  let : IsMulCommutative Z := map_isMulCommutative _ _
  have hn : K F ≤ normalizer (Z : Set G) :=
    (map_subtype_le _).trans centerControl_normalized
  let f := Z.normalizerMonoidHom.comp (inclusion hn)
  have hk : pCore 2 (K F) ≤ f.ker := by
    intro p hp
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    change (p : G) * (z : G) * (p : G)⁻¹ = (z : G)
    have hz : (z : G) ∈ P ⊓ centralizer (P : Set G) := by
      simpa only [Z,map_center_subtype_eq_inf_centralizer] using z.property
    rw [hz.2 p (mem_map_of_mem (K F).subtype hp),mul_inv_cancel_right]
  have hc : Nat.card f.range ∣ 27 := by
    obtain ⟨e⟩ := he
    have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
      (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
    rw [←index_ker]
    simpa only [index_eq_card,hcard] using index_dvd_of_le hk
  have hf : IsPGroup 3 f.range := isPGroup_iff_card_dvd_pow.mpr ⟨3,hc⟩
  have hz : IsPGroup 2 Z := (isPGroup_pCoreIn 2 (K F)).to_le (map_subtype_le _)
  exact commutator_centralizer_decomposition_of_coprime_image Z (K F) hn
    (IsPGroup.coprime_card_of_ne 3 2 (by decide) f.range Z hf hz)

open NoncentralChiefRefinement in
/-- Both central flanks disappear on the moved core center. This retains
its literal inclusion in the faithful chief numerator and trivial lower kernel. -/
theorem extraspecial_moved_core_center_interval
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (N B : NormalNode F.H)
    (hupper : ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype)
    (hlower : ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U) :
    let Z := (center ((K F).pCoreIn 2)).map ((K F).pCoreIn 2).subtype
    ⁅Z,K F⁆ ≤ B.val.map F.H.subtype ∧
      ⁅Z,K F⁆ ⊓ N.val.map F.H.subtype = ⊥ := by
  let P := (K F).pCoreIn 2
  let Z := (center P).map P.subtype
  have hZP : Z ≤ P := map_subtype_le _
  have hnZ : F.H ≤ normalizer (Z : Set G) := centerControl_normalized
  have hKZ := (show K F ≤ F.H from map_subtype_le _).trans hnZ
  have hDZ : ⁅Z,K F⁆ ≤ Z := le_normalizer_iff_commutator_le_left.mp hKZ
  have hZC : Z ≤ centralizer (F.U : Set G) := by
    have hz : Z ≤ centralizer (P : Set G) := by
      rw [show Z = P ⊓ centralizer (P : Set G) from map_center_subtype_eq_inf_centralizer P]
      exact inf_le_right
    exact hz.trans (centralizer_le (span_le_residual_core h hab))
  have hNN : F.H ≤ normalizer (N.val.map F.H.subtype : Set G) := by
    have hh := (map_mono (f := F.H.subtype)
      (show (⊤ : Subgroup F.H) ≤ normalizer (N.val : Set F.H) from le_normalizer_of_normal)).trans
        (N.val.le_normalizer_map F.H.subtype)
    simpa only [←MonoidHom.range_eq_map,range_subtype] using hh
  let A := Z ⊓ N.val.map F.H.subtype
  have hKA : K F ≤ normalizer (A : Set G) :=
    ((map_subtype_le _).trans (le_inf hnZ hNN)).trans inf_normalizer_le_normalizer_inf
  have hAP : A ≤ P := inf_le_left.trans hZP
  have hmove : ⁅A,K F⁆ ≤ F.Vi 1 := by
    rw [←extraspecial_core_center_inf_span h hab structural previous he]
    exact le_inf ((commutator_mono inf_le_right le_rfl).trans hlower)
      ((le_normalizer_iff_commutator_le_left.mp hKA).trans inf_le_left)
  have hpoint : F.Vi 1 ≤ centralizer (K F : Set G) :=
    (le_centralizer_iff.mp (normalizer_le_centralizer_of_card_two _
      (by simpa using F.card 1 (by decide)))).trans (centralizer_le (map_subtype_le _))
  have hid := commutator_isPPerfect_idempotent (K F) A
    (isPPerfect_embedded_pResidual 2 F.H) ((isPGroup_pCoreIn 2 _).to_le hAP) hKA
  have hAC : A ≤ centralizer (K F : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    rw [←hid]
    exact (commutator_mono hmove le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.mpr hpoint).le
  refine ⟨(commutator_mono hZC le_rfl).trans hupper,?_⟩
  apply le_bot_iff.mp
  exact (le_inf inf_le_left (le_inf (inf_le_left.trans hDZ)
    ((inf_le_inf hDZ le_rfl).trans hAC))).trans (centerControl_splitting he).2.le

omit [Finite G] in
private theorem centerControl_moved_normalized :
    F.H ≤ normalizer
      ((⁅(center ((K F).pCoreIn 2)).map ((K F).pCoreIn 2).subtype,K F⁆ : Subgroup G) : Set G) := by
  intro x hx
  have hk : (K F).map (MulAut.conj x).toMonoidHom = K F :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_embedded_pResidual 2 F.H hx)
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (centerControl_normalized hx)]
  exact congrArg (fun A : Subgroup G =>
    ⁅(center ((K F).pCoreIn 2)).map ((K F).pCoreIn 2).subtype,A⁆) hk

open NoncentralChiefRefinement in
omit [Finite G] in
private theorem centerControl_chief_coordinates
    (N B : NormalNode F.H) (hNB : N ⋖ B) (D : Subgroup G)
    (hDB : D ≤ B.val.map F.H.subtype) (hn : F.H ≤ normalizer (D : Set G))
    (hcap : D ⊓ N.val.map F.H.subtype = ⊥) (hne : D ≠ ⊥) :
    ∃ f : D →* Section N B, Function.Bijective f ∧
      ∀ (a : F.H) (d : D),
        f (D.normalizerMonoidHom (inclusion hn a) d) = sectionAction N B a (f d) := by
  have hBH : B.val.map F.H.subtype ≤ F.H := map_subtype_le _
  let j : D →* B.val := {
    toFun := fun d => ⟨⟨d,hBH (hDB d.property)⟩,
      (mem_map_iff_mem F.H.subtype_injective).mp (hDB d.property)⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let f := (QuotientGroup.mk' (N.val.subgroupOf B.val)).comp j
  have he (a : F.H) (d : D) :
      f (D.normalizerMonoidHom (inclusion hn a) d) = sectionAction N B a (f d) := rfl
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro d hd
    apply Subtype.ext
    have hdN : (d : G) ∈ N.val.map F.H.subtype := by
      have hh := (QuotientGroup.eq_one_iff (N := N.val.subgroupOf B.val) (j d)).mp hd
      exact mem_map_of_mem F.H.subtype hh
    have hh := hcap ▸ (show (d : G) ∈ D ⊓ N.val.map F.H.subtype from ⟨d.property,hdN⟩)
    exact hh
  have ht : f.range = ⊤ := by
    apply (chief_irreducible N B hNB f.range ?_).resolve_left
    · intro hb
      apply hne
      apply bot_unique
      intro d hd
      change d=1
      have hd1 : (⟨d,hd⟩ : D)=1 := hi (by
        have hh : f ⟨d,hd⟩ ∈ f.range := ⟨⟨d,hd⟩,rfl⟩
        rw [hb] at hh
        exact hh.trans (map_one f).symm)
      exact congrArg Subtype.val hd1
    · intro a x hx
      obtain ⟨d,rfl⟩ := hx
      exact ⟨D.normalizerMonoidHom (inclusion hn a) d,he a d⟩
  exact ⟨f,⟨hi,MonoidHom.range_eq_top.mp ht⟩,he⟩

open NoncentralChiefRefinement in
/-- If the original core center is not central in K, its moved subgroup
is the faithful six-dimensional chief factor itself, with its actual action.
This is the remaining obstruction in the center argument of 14.7.21(2). -/
theorem extraspecial_noncentral_core_center
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (hnc : ¬ (center ((K F).pCoreIn 2)).map ((K F).pCoreIn 2).subtype ≤
      (center (K F)).map (K F).subtype) :
    let Z := (center ((K F).pCoreIn 2)).map ((K F).pCoreIn 2).subtype
    let D := ⁅Z,K F⁆
    ∃ N B : NormalNode F.H, N ⋖ B ∧
      F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
      ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype ∧
      Nat.card (Section N B) = 64 ∧ (sectionAction N B).ker = pCore 2 F.H ∧
      D ≤ B.val.map F.H.subtype ∧ D ⊓ N.val.map F.H.subtype = ⊥ ∧
      Nat.card D = 64 ∧ IsElementaryAbelian 2 D ∧
      ∃ hn : F.H ≤ normalizer (D : Set G),
        (D.normalizerMonoidHom.comp (inclusion hn)).ker = pCore 2 F.H ∧
        ∃ e : D ≃* Section N B, ∀ (a : F.H) (d : D),
          e (D.normalizerMonoidHom (inclusion hn a) d) = sectionAction N B a (e d) := by
  let P := (K F).pCoreIn 2
  let Z := (center P).map P.subtype
  let D := ⁅Z,K F⁆
  have hne : D ≠ ⊥ := by
    intro hb
    apply hnc
    rw [map_center_subtype_eq_inf_centralizer (K F)]
    exact le_inf ((map_subtype_le _).trans (pCoreIn_le 2 _))
      (commutator_eq_bot_iff_le_centralizer.mp hb)
  obtain ⟨_,hc | ⟨N,B,hNB,hUN,hBC,hm,hcard,hker,hu,hl⟩⟩ :=
    extraspecial_centralizer_core_reduction_no_small_intervals h hab structural previous faithful he
  · exact (hnc (extraspecial_core_center_central_of_centralizer_central
      h hab structural previous he hc)).elim
  obtain ⟨hDB,hcap⟩ := extraspecial_moved_core_center_interval h hab structural previous he N B hu hl
  have hn : F.H ≤ normalizer (D : Set G) := centerControl_moved_normalized
  obtain ⟨f,hf,heq⟩ := centerControl_chief_coordinates N B hNB D hDB hn hcap hne
  let e := MulEquiv.ofBijective f hf
  have hDC : Nat.card D = 64 := (Nat.card_congr e.toEquiv).trans hcard
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  have hBQ : B.val.map F.H.subtype ≤ F.H.pCoreIn 2 := hBC.trans
    (centralizer_U_le_core_of_escape h structural (h.flag_escape F previous) s)
  have hBtwo : IsPGroup 2 B.val := by
    have hh := (isPGroup_pCoreIn 2 F.H).to_le hBQ
    apply hh.of_injective ((F.H.subtype).subgroupMap B.val)
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : B.val.map F.H.subtype => (x : G)) hab
  let : IsElementaryAbelian 2 (Section N B) := chief_elementary N B hNB hBtwo
  have hDe : IsElementaryAbelian 2 D := IsElementaryAbelian.of_injective f hf.1
  have hact : (D.normalizerMonoidHom.comp (inclusion hn)).ker = pCore 2 F.H := by
    rw [←hker]
    ext a
    change D.normalizerMonoidHom (inclusion hn a) = 1 ↔ sectionAction N B a = 1
    constructor
    · intro ha
      apply MulEquiv.ext
      intro w
      obtain ⟨d,rfl⟩ := hf.2 w
      exact (heq a d).symm.trans (congrArg f (DFunLike.congr_fun ha d))
    · intro ha
      apply MulEquiv.ext
      intro d
      apply hf.1
      rw [heq,ha]
      rfl
  exact ⟨N,B,hNB,hUN,hBC,hm,hcard,hker,hDB,hcap,hDC,hDe,hn,hact,e,heq⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
