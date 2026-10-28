module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.CommutatorBounds.Cyclic
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.ElementaryAbelian.Join

/-!
# The small cyclic pairing and its natural enlargement

Adjoin the actual Z-image to the cyclic commutator. The B-containment makes
this enlargement invariant under the component, while Q normalizes both factors.
The next commutator with Q has order at most two and is invariant under the whole
local group. It is therefore fixed and vanishes in the fixed-core quotient.
All groups and normalities remain in G_alpha/D_alpha. The small-commutator
and central-error proofs adapt the earlier calculations in
`Escape.EdgeTransfer.Extension.Groups` and `Escape.EdgeTransfer.Extension.Residual`.

Source: MS93, printed p.883, before the first application of (1.7)(i).
-/
public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
namespace CyclicLocalization

private theorem small_commutator {G : Type*} [Group G] [Finite G]
    (P A : Subgroup G) (hP : IsPGroup 2 P)
    (hAP : A ≤ P) (hn : P ≤ normalizer A) (hA : Nat.card A ≤ 4) :
    Nat.card (⁅A,P⁆ : Subgroup G) ≤ 2 := by
  have hKA : ⁅A,P⁆ ≤ A := le_normalizer_iff_commutator_le_left.mp hn
  by_cases hbot : A = ⊥
  · simp [hbot]
  have hne : ⁅A,P⁆ ≠ A := by
    intro heq
    let A₀ := A.subgroupOf P
    have hcomm : ⁅A₀, (⊤ : Subgroup P)⁆ = A₀ := by
      apply map_injective P.subtype_injective
      rw [map_commutator, map_subgroupOf_eq_of_le hAP, ← MonoidHom.range_eq_map,
        range_subtype, heq]
    have hz : A₀ ≤ ⊥ := le_normal_of_quotient_isPGroup_of_eq_commutator
      A₀ ⊤ ⊥ (hP.to_quotient ⊥) hcomm
    have hh := congrArg (Subgroup.map P.subtype) (le_bot_iff.mp hz)
    rw [map_subgroupOf_eq_of_le hAP, Subgroup.map_bot] at hh
    exact hbot hh
  have hlt : Nat.card (⁅A,P⁆ : Subgroup G) < Nat.card A := by
    by_contra! h
    exact hne (eq_of_le_of_card_ge hKA h)
  rcases (hP.to_le (hKA.trans hAP)).card_eq_or_dvd with h | h <;> omega

private theorem normalizer_centralizes_small {G : Type*} [Group G] [Finite G]
    (D : Subgroup G) (hD : Nat.card D ≤ 2) :
    normalizer (D : Set G) ≤ centralizer (D : Set G) := by
  by_cases hsmall : Nat.card D ≤ 1
  · rw [eq_bot_of_card_le D hsmall]
    intro g _ x hx
    have hxone : x = 1 := hx
    simp [hxone]
  · have htwo : Nat.card D = 2 := by omega
    obtain ⟨z, _, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : D)).mp htwo
    intro g hg x hx
    by_cases hxone : x = 1
    · simp [hxone]
    let xD : D := ⟨x, hx⟩
    let yD : D := ⟨g * x * g⁻¹, (hg x).mp hx⟩
    have hyne : yD ≠ 1 := by
      intro hy
      apply hxone
      have hy' : g * x * g⁻¹ = 1 := congrArg Subtype.val hy
      have hh := congrArg (fun a : G => g⁻¹ * a * g) hy'
      simpa [mul_assoc] using hh
    have heq : yD = xD := (hzuniq yD hyne).trans (hzuniq xD (by
      intro hx'; exact hxone (congrArg Subtype.val hx'))).symm
    have heq' : g * x * g⁻¹ = x := congrArg Subtype.val heq
    have hh := congrArg (fun a : G => a * g) heq'
    simpa [mul_assoc] using hh.symm

/-- Central errors disappear under a finite two-residual acting on a two-group. -/
private theorem centralizes_of_central_error {G : Type*} [Group G] [Finite G]
    (P E D : Subgroup G) [D.Normal] (hp : IsPGroup 2 P)
    (he : IsPPerfect 2 E) (hDP : D ≤ P) (hDE : ⁅D,E⁆ = ⊥)
    (x : G) (hx : x ∈ P) (hcomm : ∀ y ∈ E, ⁅x,y⁆ ∈ D) :
    x ∈ centralizer (E : Set G) := by
  let N := commutatorPreimage P E D
  have hDN : D ≤ N := le_commutatorPreimage hDP (hDE.le.trans bot_le)
  have hNE : ⁅N,E⁆ ≤ D := commutator_commutatorPreimage_le P E D le_normalizer_of_normal
  have hn : E ≤ normalizer N :=
    le_normalizer_iff_commutator_le_left.mpr (hNE.trans hDN)
  have hz : ⁅N,E⁆ = ⊥ := by
    rw [← commutator_isPPerfect_idempotent E N he
      (hp.to_le (commutatorPreimage_le P E D)) hn]
    exact le_bot_iff.mp ((commutator_mono hNE le_rfl).trans hDE.le)
  apply commutator_eq_bot_iff_le_centralizer.mp hz
  change x ∈ commutatorPreimage P E D
  rw [commutatorPreimage_eq_inf_comap_centralizer]
  refine ⟨hx, ?_⟩
  rintro _ ⟨y,hy,rfl⟩
  have hc : ⁅QuotientGroup.mk' D x, QuotientGroup.mk' D y⁆ = 1 := by
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (hcomm y hy)
  exact (commutatorElement_eq_one_iff_mul_comm.mp hc).symm

/-- A commutator bound into Z makes AZ invariant under the component. -/
private theorem sup_normal {G : Type*} [Group G] (A Z Q E : Subgroup G) [Z.Normal]
    (hgen : E ⊔ Q = ⊤) (hQE : Q ≤ normalizer A) (hAE : ⁅A,E⁆ ≤ Z) :
    (Z ⊔ A).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hgen]
  refine sup_le ?_ ((le_inf le_normalizer_of_normal hQE).trans
    (normalizer_inf_normalizer_le_normalizer_sup Z A))
  rw [le_normalizer_iff]
  intro e he x hx
  have hm : (Z ⊔ A).map (MulAut.conj e).toMonoidHom ≤ Z ⊔ A := by
    rw [Subgroup.map_sup]
    apply sup_le
    · rintro _ ⟨z,hz,rfl⟩
      exact (show Z ≤ Z ⊔ A from le_sup_left)
        ((mem_normalizer_iff.mp (show e ∈ normalizer Z from le_normalizer_of_normal (mem_top e)) z).mp hz)
    · rintro _ ⟨y,hy,rfl⟩
      change e * y * e⁻¹ ∈ Z ⊔ A
      have hc : ⁅e,y⁆ ∈ Z := hAE (by
        rw [commutator_comm]; exact commutator_mem_commutator he hy)
      rw [show e * y * e⁻¹ = ⁅e,y⁆ * y by simp [commutatorElement_def, mul_assoc]]
      exact (Z ⊔ A).mul_mem ((show Z ≤ Z ⊔ A from le_sup_left) hc) ((show A ≤ Z ⊔ A from le_sup_right) hy)
  exact hm (mem_map_of_mem _ hx)

/-- The small pairing's natural enlargement is centralized by Q. -/
private theorem sup_centralizes_kernel {G : Type*} [Group G] [Finite G]
    (A Z Q E : Subgroup G) [Q.Normal] [Z.Normal] [(Z ⊔ A).Normal]
    (hAQ : A ≤ Q) (hQ : IsPGroup 2 Q)
    (hQA : Q ≤ normalizer A) (hcard : Nat.card A ≤ 4)
    (hZcentral : Z ≤ centralizer (Q : Set G))
    (hfixed : Q ⊓ centralizer (E : Set G) = ⊥) :
    ⁅Z ⊔ A,Q⁆ = ⊥ := by
  have hcomm : ⁅Z ⊔ A,Q⁆ = ⁅A,Q⁆ := by
    rw [commutator_comm (Z ⊔ A), commutator_comm A]
    exact (commutator_eq_of_centralizing_sup rfl hZcentral
      (hAQ.trans Q.le_normalizer)).symm
  have hsmall : Nat.card (⁅Z ⊔ A,Q⁆ : Subgroup G) ≤ 2 := by
    rw [hcomm]
    exact small_commutator Q A hQ hAQ hQA hcard
  have hn : (⊤ : Subgroup G) ≤ normalizer (⁅Z ⊔ A,Q⁆ : Subgroup G) :=
    le_normalizer_of_normal
  have hc : ⁅Z ⊔ A,Q⁆ ≤ centralizer (E : Set G) :=
    (le_centralizer_iff.mp (hn.trans (normalizer_centralizes_small _ hsmall))).trans
      (centralizer_le le_top)
  apply le_bot_iff.mp
  rw [← hfixed]
  exact le_inf (commutator_le_right _ _) hc

open RankOnePairing
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {a : Vertex R} {f : FrameAt a}

/-- The fixed-core quotient has no residual-fixed element in its Q-image. -/
theorem quotient_Q_fixed_eq_bot (source : LocalSource L R) (ha : color R a = false)
    (f : FrameAt a) (flag : SL) :
    quotientImage a (Q R a) ⊓ centralizer (component (projection f) flag : Set _) = ⊥ := by
  let := finite_stabilizer R a
  rw [quotient_component (source := source) a ha f flag]
  apply bot_unique
  rintro x ⟨⟨q,hq,rfl⟩,hc⟩
  have hDE : ⁅denominator a,pResidual 2 (stabilizer R a)⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [denominator_eq]
    exact inf_le_right
  have hcomm : ∀ y ∈ pResidual 2 (stabilizer R a), ⁅q,y⁆ ∈ denominator a := by
    intro y hy
    apply (QuotientGroup.eq_one_iff _).mp
    change quotientMap a ⁅q,y⁆ = 1
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (hc _ (mem_map_of_mem _ (show y ∈ (Ltilde R a).subgroupOf (stabilizer R a) by
      rw [Ltilde_subgroupOf]; exact hy))).symm
  have hfix := centralizes_of_central_error ((Q R a).subgroupOf (stabilizer R a))
    (pResidual 2 (stabilizer R a)) (denominator a)
    (Q_isPGroup R source.two_group source.core_le a ha).comap_subtype
    (isPPerfect_pResidual 2) (by rw [denominator_eq]; exact inf_le_left) hDE q hq hcomm
  apply (QuotientGroup.eq_one_iff q).mpr
  rw [denominator_eq]
  exact ⟨hq,hfix⟩

/-- The two factors generating the actual local quotient. -/
theorem component_sup_Q (source : LocalSource L R) (ha : color R a = false)
    (f : FrameAt a) (flag : SL) :
    component (projection f) flag ⊔ quotientImage a (Q R a) = ⊤ := by
  rw [quotient_component (source := source) a ha f flag]
  have hg := congrArg (fun K => quotientImage a K) (source.local_generation a ha)
  simp only [quotientImage] at hg
  rw [subgroupOf_sup (Ltilde_le_stabilizer a)
    (show Q R a ≤ stabilizer R a from fun _ hx => hx.1), Subgroup.map_sup,
    subgroupOf_self, map_top_of_surjective _ (show Function.Surjective (quotientMap a) from QuotientGroup.mk'_surjective _)] at hg
  exact hg

end CyclicLocalization
open CyclicLocalization RankOnePairing
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {a : Vertex R} {f : FrameAt a}
namespace SelectedSeed
variable (s : SelectedSeed geometry a f)

/-- The literal cyclic commutator, before its parabolic closure. -/
@[expose] noncomputable def cyclicPairing : Subgroup (LocalQuotient a) :=
  ⁅zpowers (quotientMap a s.element),quotientImage a (Q R a)⁆

/-- Adjoin only the actual natural Z-image. -/
@[expose] noncomputable def cyclicLayer : Subgroup (LocalQuotient a) := quotientImage a (Z R a) ⊔ s.cyclicPairing

omit [Finite M] in
theorem cyclicPairing_le_Q :
    s.cyclicPairing ≤ quotientImage a (Q R a) := by
  let := quotientImage_normal a (Q R a) (Q_normalized R a)
  exact commutator_le_right _ _

theorem cyclicLayer_le_Q (hb : 2 < geometry.b R) (ha : color R a = false) :
    s.cyclicLayer ≤ quotientImage a (Q R a) :=
  sup_le (map_mono (comap_mono ((Z_le_VBall R a 2).trans (geometry.V_le_Q hb a ha))))
    (s.cyclicPairing_le_Q)

theorem cyclicPairing_component (source : LocalSource L R) (ha : color R a = false) :
    ⁅s.cyclicPairing,component (projection f) s.flag⁆ ≤ quotientImage a (Z R a) := by
  let := quotientImage_normal a (Z R a) (Z_normalized R a)
  rw [commutator_comm]
  apply commutator_le.mpr
  intro e he k hk
  exact (mem_centralizerModulo_iff.mp
    (quotientImage_B_le_fixed (geometry := geometry) source ha s.flag
      (s.cyclic_commutator_le_B hk))).2 e he

theorem cyclicLayer_normal (source : LocalSource L R) (ha : color R a = false) : s.cyclicLayer.Normal := by
  let := quotientImage_normal a (Z R a) (Z_normalized R a)
  exact sup_normal _ _ _ _ (component_sup_Q source ha f s.flag)
    s.cyclic_commutator_normalized_Q (s.cyclicPairing_component source ha)

omit [Finite M] in
include geometry in
theorem Z_centralizes_Q (ha : color R a = false) :
    quotientImage a (Z R a) ≤ centralizer (quotientImage a (Q R a) : Set _) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [← quotientImage_commutator a _ _ (Z_le_stabilizer R a)
    (show Q R a ≤ stabilizer R a from fun _ hx => hx.1),geometry.centralizes a ha]
  simp [quotientImage]

theorem cyclicLayer_centralizes_Q (source : LocalSource L R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (ha : color R a = false) :
    ⁅s.cyclicLayer,quotientImage a (Q R a)⁆ = ⊥ := by
  let := quotientImage_normal a (Q R a) (Q_normalized R a)
  let := quotientImage_normal a (Z R a) (Z_normalized R a)
  let : (quotientImage a (Z R a) ⊔ s.cyclicPairing).Normal := s.cyclicLayer_normal source ha
  exact sup_centralizes_kernel _ _ _ _ (s.cyclicPairing_le_Q)
    ((Q_isPGroup R source.two_group source.core_le a ha).comap_subtype.map (quotientMap a))
    s.cyclic_commutator_normalized_Q (s.cyclic_commutator_card_le_four source hb modules ha)
    (Z_centralizes_Q (geometry := geometry) ha) (quotient_Q_fixed_eq_bot source ha f s.flag)

theorem cyclicPairing_elementary (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (ha : color R a = false) : IsElementaryAbelian 2 s.cyclicPairing := by
  let : IsElementaryAbelian 2 (Z R s.neighbor) := by
    rw [← modules.X_eq_Z s.neighbor (moving_color ha s.moving)]
    exact omegaCenter_elementary _
  let : IsElementaryAbelian 2 ((Z R s.neighbor).subgroupOf (stabilizer R a)) :=
    IsElementaryAbelian.subgroupOf ((moving_Z_le_V s.moving).trans
      ((geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1)))
  let : IsElementaryAbelian 2 (quotientImage a (Z R s.neighbor)) :=
    IsElementaryAbelian.map _
  have hn : Q R a ≤ normalizer (Z R s.neighbor : Set (FreeAmalgam R)) :=
    (Q_le_stabilizer_of_dist_two R a s.neighbor ha s.moving.1).trans
      (Z_normalized R s.neighbor)
  have hn₀ : (Q R a).subgroupOf (stabilizer R a) ≤
      normalizer ((Z R s.neighbor).subgroupOf (stabilizer R a)) :=
    (comap_mono hn).trans (le_normalizer_comap _)
  have hnq : quotientImage a (Q R a) ≤ normalizer (quotientImage a (Z R s.neighbor)) :=
    (map_mono hn₀).trans (le_normalizer_map _)
  exact IsElementaryAbelian.of_le ((commutator_mono s.cyclic_le_neighbor_image le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp hnq))

theorem cyclicLayer_elementary (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (ha : color R a = false) : IsElementaryAbelian 2 s.cyclicLayer := by
  let := s.cyclicPairing_elementary hb modules ha
  let : IsElementaryAbelian 2 (Z R a) := by
    rw [← modules.X_eq_Z a ha]
    exact omegaCenter_elementary _
  let : IsElementaryAbelian 2 ((Z R a).subgroupOf (stabilizer R a)) :=
    IsElementaryAbelian.subgroupOf (Z_le_stabilizer R a)
  let : IsElementaryAbelian 2 (quotientImage a (Z R a)) :=
    IsElementaryAbelian.map _
  exact IsElementaryAbelian.sup_of_le_centralizer
    (le_centralizer_iff.mp ((Z_centralizes_Q (geometry := geometry) ha).trans
      (centralizer_le s.cyclicPairing_le_Q)))

end SelectedSeed

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
