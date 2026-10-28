module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.NaturalGeneration
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.CommutatorBounds.CyclicLocalization.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.CommutatorBounds.CyclicNormalization.SmallInvariant
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Selection.Sections
/-!
# Localization and exact rank-one transport for a single natural section

A selected nonzero fixed coordinate gives the seed Z joined with the actual
first parabolic closure of a cyclic group. Its opposite closure has natural
rank-one coordinates with kernel the source fixed preimage, because the
whole-section coordinate kernel is fixed modulo Z by the component.

The small cyclic displacement is first normalized by O²(P), then by P using
the natural-subgroup calculation. Adjoining Z produces an elementary normal
layer centralized by the quotient kernel. CyclicLocalization.small_layer_le_natural
therefore localizes the displacement in Z. Relative normal closure preserves
that same commutator, including its order and nontriviality.

The elementary layer arguments adapt the proofs in FirstPairing's
CyclicLocalization/Layer and CyclicNormalization; all inputs here concern the
supplied section, with no trapped-radius or counterexample premise.
Source: Meierfrankenfeld--Stellmacher (1993), (1.7)(i), pp.847--848,
the application on p.883, and the W-section application in (4.4.1), p.890.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Favorable
open RankOnePairing
open Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
open NaturalGeneration
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


private theorem normalizes_pairing_of_fixed_mod_centralizer
    {G : Type*} [Group G] (A Q Z T : Subgroup G) [Q.Normal]
    (hZQ : Z ≤ centralizer (Q : Set G)) (hAT : ⁅A, T⁆ ≤ Z) :
    T ≤ normalizer (⁅A, Q⁆ : Subgroup G) := by
  have hreduce := commutator_eq_of_centralizing_sup
    (B := Z ⊔ A) rfl hZQ
    (show A ≤ normalizer (Q : Set G) from le_normalizer_of_normal)
  apply le_normalizer_iff.mpr
  intro t ht k hk
  have hAmap : A.map (MulAut.conj t).toMonoidHom ≤ Z ⊔ A := by
    rintro y ⟨x, hx, rfl⟩
    have hcomm : ⁅t, x⁆ ∈ Z := by
      apply hAT
      rw [commutator_comm]
      exact commutator_mem_commutator ht hx
    have hh := (Z ⊔ A).mul_mem (mem_sup_left hcomm) (mem_sup_right hx)
    change t * x * t⁻¹ ∈ Z ⊔ A
    simpa only [commutatorElement_def, inv_mul_cancel_right] using hh
  have hQmap : Q.map (MulAut.conj t).toMonoidHom = Q :=
    mem_normalizer_iff_map_conj_eq.mp (show t ∈ normalizer (Q : Set G) from
      le_normalizer_of_normal (mem_top t))
  have hh := mem_map_of_mem (MulAut.conj t).toMonoidHom hk
  rw [map_commutator, hQmap] at hh
  have h := commutator_mono hAmap (le_refl Q) hh
  rw [commutator_comm (Z ⊔ A), ← hreduce, commutator_comm] at h
  exact h


variable {G : Type*} [Group G]
variable {π : G →* SL} {flag : SL} {i : Bool} {H N Z : Subgroup G} {x : G}
namespace Seed
variable (d : NaturalSeedData π flag i H N Z x)

theorem le_group [H.Normal] : d.seed ≤ H :=
  sup_le (d.z_le_fixed.trans d.fixed_le_group)
    (Incidence.localGenerated_le_of_normalizes _ _ H le_normalizer_of_normal
      (zpowers_le.mpr d.element_mem))

theorem le_kernel : d.seed ≤ π.ker :=
  sup_le d.z_le_kernel (Incidence.localGenerated_le_of_normalizes _ _ π.ker
    le_normalizer_of_normal (zpowers_le.mpr d.element_kernel))

theorem kernel_le_parabolic (j : Bool) : π.ker ≤ parabolic π flag j := by
  intro g hg
  change π g ∈ modelParabolic flag j
  rw [MonoidHom.mem_ker.mp hg]
  exact one_mem _

theorem cyclic_le : zpowers x ≤ d.seed :=
  le_trans (le_localGenerated _ _ ((zpowers_le.mpr d.element_kernel).trans
    (kernel_le_parabolic i))) le_sup_right

theorem normalized [Z.Normal] : parabolic π flag i ≤ normalizer (d.seed : Set G) :=
  (le_inf le_normalizer_of_normal (Incidence.localGenerated_normalized _ _)).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

include d in
theorem cyclic_fixed [H.Normal] [N.Normal] : ⁅zpowers x, parabolic π flag i⁆ ≤ N := by
  have hx : x ∈ centralizerModulo H (parabolic π flag i) N := by
    apply mem_centralizerModulo_iff.mpr
    refine ⟨d.element_mem, ?_⟩
    intro p hp
    let u : H := ⟨x, d.element_mem⟩
    let v : H := ⟨p*x*p⁻¹, (inferInstance : H.Normal).conj_mem x d.element_mem p⟩
    have he : d.natural.coordinates v = d.natural.coordinates u :=
      (d.natural.action p (mem_top _) u v rfl).trans (d.fixed (π p) hp)
    have hk : v * u⁻¹ ∈ d.natural.coordinates.ker := by
      simp only [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
    rw [d.natural.kernel] at hk
    exact hk
  rw [commutator_comm]
  apply commutator_le.mpr
  intro p hp z hz
  exact (mem_centralizerModulo_iff.mp (zpowers_le.mpr hx hz)).2 p hp

theorem seed_fixed_modulo [H.Normal] [N.Normal] [Z.Normal] : ⁅d.seed, parabolic π flag i⁆ ≤ N := by
  have hraw : ⁅localGenerated (parabolic π flag i) (zpowers x),
      parabolic π flag i⁆ ≤ N :=
    Incidence.localGenerated_commutator_bound _ _ _ _ (parabolic π flag i).le_normalizer
      (cyclic_fixed d)
  have hh : d.seed ≤ commutatorPreimage ⊤ (parabolic π flag i) N :=
    sup_le (le_commutatorPreimage le_top ((commutator_le_left _ _).trans d.z_le_fixed))
      (le_commutatorPreimage le_top hraw)
  exact (commutator_mono hh le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal)

theorem fixedPreimage_eq [Finite G] [H.Normal] [Z.Normal] (hN : ⁅N, component π flag⁆ ≤ Z) :
    fixedPreimage (component π flag) d.seed Z = generated d.seed ⊓ N := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgU, hgfix⟩ := (mem_fixedPreimage _ _ _ g).mp hg
    exact ⟨hgU, natural_fixed_modulo_le_kernel d.natural
      (component_map π d.projection_surjective flag) d.z_le_fixed
      (mem_centralizerModulo_iff.mpr
        ⟨generated_le _ _ (le_group d) hgU, hgfix⟩)⟩
  · rintro g ⟨hgU, hgN⟩
    apply (mem_fixedPreimage _ _ _ g).mpr
    refine ⟨hgU, ?_⟩
    intro l hl
    apply hN
    rw [commutator_comm]
    exact commutator_mem_commutator hl hgN

theorem seed_fixed [Finite G] [H.Normal] [N.Normal] [Z.Normal] (hN : ⁅N, component π flag⁆ ≤ Z) :
    ⁅d.seed, localResidual (parabolic π flag i)⁆ ≤
      fixedPreimage (component π flag) d.seed Z := by
  rw [fixedPreimage_eq d hN]
  exact le_inf ((commutator_mono le_normalClosure le_rfl).trans (commutator_le_left _ _))
    ((commutator_mono le_rfl (map_subtype_le _)).trans (seed_fixed_modulo d))

theorem rankOne_nonempty [Finite G] [H.Normal] [Z.Normal] (hN : ⁅N, component π flag⁆ ≤ Z) :
    Nonempty (RankOneFactor (localResidual (parabolic π flag (!i)))
      (localGenerated (parabolic π flag (!i)) d.seed)
      (fixedPreimage (component π flag) d.seed Z)) := by
  obtain ⟨c⟩ := planeCoordinates_nonempty d.natural.marking flag i d.vector d.nonzero d.fixed
  obtain ⟨n⟩ := d.rankOneFactor_nonempty c
  refine ⟨{ n with kernel := ?_ }⟩
  rw [n.kernel, fixedPreimage_eq d hN]
  ext y
  exact ⟨fun hy => ⟨localGenerated_le_generated _ _ y.property, hy⟩, fun hy => hy.2⟩


include d in
/-- The exact fixed quotient suffices to normalize the cyclic pairing. -/
theorem cyclic_normalized [Finite G] [H.Normal] [N.Normal] [Z.Normal]
    (hker : IsPGroup 2 π.ker) (hE : component π flag = pResidual 2 G)
    (hN : ⁅N, component π flag⁆ ≤ Z) (hHQ : ⁅H, π.ker⁆ ≤ N)
    (hZQ : Z ≤ centralizer (π.ker : Set G))
    (z : NaturalFactor π ⊤ Z ⊥)
    (hfixed : Z ⊓ centralizer (parabolic π flag i : Set G) ≠ ⊥)
    (hcard : Nat.card (⁅zpowers x, π.ker⁆ : Subgroup G) ≤ 4) :
    parabolic π flag i ≤ normalizer (⁅zpowers x, π.ker⁆ : Subgroup G) := by
  let P := parabolic π flag i
  let T := (pResidual 2 P).map P.subtype
  have hTP : T ≤ P := map_subtype_le _
  have hTE : T ≤ component π flag := by
    rw [hE]
    exact map_pResidual_le 2 P.subtype
  have hXT : ⁅d.seed, T⁆ ≤ Z := by
    rw [← commutator_isPPerfect_idempotent T d.seed
      (isPPerfect_embedded_pResidual 2 P) (hker.to_le (le_kernel d))
      (hTP.trans (normalized d))]
    exact (commutator_mono
      ((commutator_mono le_rfl hTP).trans (seed_fixed_modulo d)) hTE).trans hN
  apply CyclicNormalization.small_fixed_preimage_parabolic_normalized π
    d.projection_surjective hker flag i Z _ d.z_le_kernel z hfixed
    (commutator_le_right _ _) hcard
  · rw [← hE]
    exact (commutator_mono ((commutator_mono (zpowers_le.mpr d.element_mem) le_rfl).trans
      hHQ) le_rfl).trans hN
  · exact normalizer_commutator_ge_right _ _
  · exact normalizes_pairing_of_fixed_mod_centralizer _ _ Z T hZQ
      ((commutator_mono (cyclic_le d) le_rfl).trans hXT)

include d in
/-- Small cyclic displacement localizes in the actual natural subgroup. -/
theorem cyclic_le_natural [Finite G] [H.Normal] [N.Normal] [Z.Normal]
    [IsElementaryAbelian 2 H]
    (hker : IsPGroup 2 π.ker) (hE : component π flag = pResidual 2 G)
    (hH : H ≤ π.ker) (hN : ⁅N, component π flag⁆ ≤ Z) (hHQ : ⁅H, π.ker⁆ ≤ N)
    (hZQ : Z ≤ centralizer (π.ker : Set G))
    (hfaithful : π.ker ⊓ centralizer (component π flag : Set G) = ⊥)
    (z : NaturalFactor π ⊤ Z ⊥)
    (hfixed : Z ⊓ centralizer (parabolic π flag i : Set G) ≠ ⊥)
    (hcard : Nat.card (⁅zpowers x, π.ker⁆ : Subgroup G) ≤ 4) :
    ⁅zpowers x, π.ker⁆ ≤ Z := by
  let K := ⁅zpowers x, π.ker⁆
  have hKH : K ≤ H := (commutator_mono (zpowers_le.mpr d.element_mem) le_rfl).trans
    (commutator_le_left _ _)
  have hKE : ⁅K, component π flag⁆ ≤ Z :=
    (commutator_mono ((commutator_mono (zpowers_le.mpr d.element_mem) le_rfl).trans hHQ)
      le_rfl).trans hN
  have hgen : component π flag ⊔ π.ker = ⊤ := by
    rw [← comap_map_eq, component_map π d.projection_surjective flag, comap_top]
  let : (Z ⊔ K).Normal := sup_normal K Z π.ker (component π flag) hgen
    (normalizer_commutator_ge_right _ _) hKE
  let : IsElementaryAbelian 2 ↥(Z ⊔ K : Subgroup G) :=
    IsElementaryAbelian.of_le (sup_le (d.z_le_fixed.trans d.fixed_le_group) hKH)
  have hcentral : ⁅Z ⊔ K, π.ker⁆ = ⊥ := sup_centralizes_kernel K Z π.ker
    (component π flag) (commutator_le_right _ _) hker (normalizer_commutator_ge_right _ _)
      hcard hZQ hfaithful
  have hcomm : ⁅Z ⊔ K, component π flag⁆ ≤ Z := by
    have hh : Z ⊔ K ≤ commutatorPreimage ⊤ (component π flag) Z :=
      sup_le (le_commutatorPreimage le_top (commutator_le_left _ _))
        (le_commutatorPreimage le_top hKE)
    exact (commutator_mono hh le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal)
  exact CyclicLocalization.small_layer_le_natural π d.projection_surjective π.ker
    (component π flag) Z (Z ⊔ K) K rfl (component_map π d.projection_surjective flag)
    z le_sup_left le_sup_right (sup_le d.z_le_kernel (hKH.trans hH)) hcentral hcomm
    hfaithful flag i hcard (cyclic_normalized d hker hE hN hHQ hZQ z hfixed hcard)

/-- Taking the first parabolic closure preserves the literal cyclic commutator. -/
theorem commutator_eq_cyclic [Z.Normal]
    (hZQ : Z ≤ centralizer (π.ker : Set G))
    (hn : parabolic π flag i ≤ normalizer (⁅zpowers x, π.ker⁆ : Subgroup G)) :
    ⁅d.seed, π.ker⁆ = ⁅zpowers x, π.ker⁆ := by
  have hraw : ⁅localGenerated (parabolic π flag i) (zpowers x), π.ker⁆ =
      ⁅zpowers x, π.ker⁆ := by
    let P := parabolic π flag i
    let K := ⁅zpowers x, π.ker⁆
    have hAP : zpowers x ≤ P := (zpowers_le.mpr d.element_kernel).trans (kernel_le_parabolic i)
    have hQP : π.ker ≤ P := kernel_le_parabolic i
    let : (K.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hn
    have hKP : K ≤ P := (commutator_le_right _ _).trans hQP
    have hh : ⁅π.ker.subgroupOf P, (zpowers x).subgroupOf P⁆ ≤ K.subgroupOf P := by
      rw [commutator_comm, ← commutator_subgroupOf P _ _ hAP hQP]
    have hm := map_mono (f := P.subtype)
      (commutator_normalClosure_le_of_normal _ _ _ hh)
    rw [map_commutator, map_subgroupOf_eq_of_le hQP,
      map_subgroupOf_eq_of_le hKP, commutator_comm] at hm
    exact le_antisymm hm (commutator_mono (le_localGenerated P _ hAP) le_rfl)
  have he := commutator_eq_of_centralizing_sup
    (B := d.seed) rfl hZQ
    (show localGenerated (parabolic π flag i) (zpowers x) ≤ normalizer (π.ker : Set G)
      from le_normalizer_of_normal)
  rw [commutator_comm d.seed, ← he, commutator_comm, hraw]

end Seed
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Favorable
