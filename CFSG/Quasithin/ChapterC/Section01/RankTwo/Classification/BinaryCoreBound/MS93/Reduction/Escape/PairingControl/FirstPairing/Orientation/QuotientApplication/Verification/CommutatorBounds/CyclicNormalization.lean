module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.CommutatorBounds.Cyclic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.CommutatorBounds.CyclicNormalization.SmallInvariant
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Residual normalization of the selected cyclic pairing

In the binary extension the untilded residual O^{2′}(P) is P itself:
it contains the two-group kernel and maps onto the model parabolic.
This does not identify it with O²(P).

The selected seed is fixed modulo the component-fixed preimage C. The
component fixes C modulo Z. Idempotence of a two-perfect group's action
on a two-group therefore puts [X,O²(P)] in Z. Since Z centralizes Q,
conjugating the selected cyclic group by O²(P) leaves its Q-commutator
unchanged. This proves normalization by O²(P), before identifying that
cyclic commutator with the pairing of the parabolic closure.

The cyclic pairing K lies in B, has order at most four, and is normalized
by Q. Since B is fixed modulo Z by the global two-residual, [K,O²(G)]
lies in Z. The small-subgroup lifting argument for the actual marked
natural SL₃(2) action now upgrades O²(P)-normalization to P-normalization,
and hence to normalization by the untilded source residual. No containment
of K in Z or identification with [X,Q] is needed for this step.

Source: Meierfrankenfeld--Stellmacher (1993), printed p.883, immediately
before the first application of (1.7)(i), pp.847--848; residual conventions
on p.832.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
open RankOnePairing
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

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : Geometry R} {a : Vertex R} {f : FrameAt a}
namespace SelectedSeed
variable (s : SelectedSeed geometry a f)

/-- In this two-group-kernel extension the untilded residual is the whole parabolic. -/
theorem localResidual_eq_parabolic (source : LocalSource L R)
    (ha : color R a = false) :
    localResidual (parabolic (projection f) s.flag s.side) =
      parabolic (projection f) s.flag s.side := by
  let P := parabolic (projection f) s.flag s.side
  have hQ : quotientImage a (Q R a) ≤ localResidual P := by
    have hpQ : IsPGroup 2 (quotientImage a (Q R a)) :=
      (Q_isPGroup R source.two_group source.core_le a ha).comap_subtype.map (quotientMap a)
    have hp : IsPGroup 2 ((quotientImage a (Q R a)).subgroupOf P) := hpQ.comap_subtype
    have hh := map_mono (f := P.subtype) (le_primeToResidual_of_isPGroup hp)
    rw [map_subgroupOf_eq_of_le (s.Q_le_parabolic s.side)] at hh
    exact hh
  have hm := localResidual_map (s.extension source ha) s.side
  rw [s.localParabolic_extension source ha, s.extension_projection source ha,
    s.extension_flag source ha] at hm
  have hc : P = localResidual P ⊔ quotientImage a (Q R a) := by
    calc
      _ = ((localResidual P).map (projection f)).comap (projection f) := by rw [hm]; rfl
      _ = _ := by rw [comap_map_eq, projection, quotientProjection_kernel]
  exact le_antisymm (map_subtype_le _) (hc.le.trans (sup_le le_rfl hQ))

/-- The selected generator is fixed modulo Z by the parabolic two-residual. -/
theorem cyclic_twoResidual_commutator_le_Z
    (source : LocalSource L R) (hb : 2 < geometry.b R) (ha : color R a = false) :
    ⁅zpowers (quotientMap a s.element),
      (pResidual 2 (parabolic (projection f) s.flag s.side)).map
        (parabolic (projection f) s.flag s.side).subtype⁆ ≤ quotientImage a (Z R a) := by
  let P := parabolic (projection f) s.flag s.side
  let T := (pResidual 2 P).map P.subtype
  let := quotientImage_normal a (Z R a) (Z_normalized R a)
  have hT : T ≤ P := map_subtype_le _
  let := finite_stabilizer R a
  have hTc : T ≤ component (projection f) s.flag := by
    rw [quotient_component (source := source) a ha f s.flag,
      quotientImage, Ltilde_subgroupOf, quotientMap,
      map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)]
    exact le_pResidual_of_isPPerfect T (isPPerfect_embedded_pResidual 2 P)
  have hXT : ⁅s.X, T⁆ ≤ s.C := by
    apply (commutator_mono le_rfl ?_).trans (s.seed_fixed source hb ha)
    rw [s.localResidual_eq_parabolic source ha]
    exact hT
  have hCZ : ⁅s.C, T⁆ ≤ quotientImage a (Z R a) := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro t ht c hc
    exact (mem_fixedPreimage _ _ _ c |>.mp hc).2 t (hTc ht)
  have hXQ : IsPGroup 2 s.X :=
    (s.generated_X_isPGroup source hb ha).to_le le_normalClosure
  have hTX : T ≤ normalizer (s.X : Set (LocalQuotient a)) := by
    exact hT.trans ((normal_subgroupOf_iff_le_normalizer (s.X_le_parabolic hb ha s.side)).mp
      s.X_normal)
  have hXZ : ⁅s.X, T⁆ ≤ quotientImage a (Z R a) := by
    rw [← commutator_isPPerfect_idempotent T s.X
      (isPPerfect_embedded_pResidual 2 P) hXQ hTX]
    exact (commutator_mono hXT le_rfl).trans hCZ
  exact (commutator_mono (s.cyclic_le_X hb ha) le_rfl).trans hXZ

/-- The parabolic two-residual normalizes the original cyclic pairing.
This is weaker than normalization by the untilded source residual. -/
theorem cyclic_commutator_normalized_twoResidual
    (source : LocalSource L R) (hb : 2 < geometry.b R) (ha : color R a = false) :
    (pResidual 2 (parabolic (projection f) s.flag s.side)).map
        (parabolic (projection f) s.flag s.side).subtype ≤ normalizer
      (⁅zpowers (quotientMap a s.element), quotientImage a (Q R a)⁆ :
        Subgroup (LocalQuotient a)) := by
  let := quotientImage_normal a (Q R a) (Q_normalized R a)
  apply normalizes_pairing_of_fixed_mod_centralizer _ _ (quotientImage a (Z R a)) _
    _ (s.cyclic_twoResidual_commutator_le_Z source hb ha)
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [← quotientImage_commutator a _ _ (Z_le_stabilizer R a)
    (show Q R a ≤ stabilizer R a from fun _ hx => hx.1), geometry.centralizes a ha]
  simp [quotientImage]

/-- The untilded source residual normalizes the original cyclic pairing.
All small-subgroup lifting premises follow from the selected seed and the
actual marked natural section, before any localization of this pairing in Z. -/
theorem cyclic_commutator_normalized_residual
    (source : LocalSource L R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (ha : color R a = false) :
    localResidual (parabolic (projection f) s.flag s.side) ≤ normalizer
      (⁅zpowers (quotientMap a s.element), quotientImage a (Q R a)⁆ :
        Subgroup (LocalQuotient a)) := by
  let := quotientImage_normal a (Z R a) (Z_normalized R a)
  let := quotientImage_normal a (Q R a) (Q_normalized R a)
  have hπ : Function.Surjective (projection f) :=
    quotientProjection_surjective a _ f.natural_section.projection_surjective _
  have hker : (projection f).ker = quotientImage a (Q R a) :=
    quotientProjection_kernel a _ _
  have hcomponent : component (projection f) s.flag = pResidual 2 (LocalQuotient a) := by
    let := finite_stabilizer R a
    rw [projection, quotient_component (source := source) a ha f s.flag,
      quotientImage, Ltilde_subgroupOf, quotientMap,
      map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)]
  have hcomm : ⁅⁅zpowers (quotientMap a s.element), quotientImage a (Q R a)⁆,
      pResidual 2 (LocalQuotient a)⁆ ≤ quotientImage a (Z R a) := by
    rw [← hcomponent, commutator_comm]
    apply commutator_le.mpr
    intro l hl k hk
    exact (mem_centralizerModulo_iff.mp
      (quotientImage_B_le_fixed (geometry := geometry) source ha s.flag
        (s.cyclic_commutator_le_B hk))).2 l hl
  rw [s.localResidual_eq_parabolic source ha]
  apply CyclicNormalization.small_fixed_preimage_parabolic_normalized
    (projection f) hπ (quotientProjection_kernel_isPGroup source a ha _ _) s.flag s.side
    (quotientImage a (Z R a)) _ _ (naturalZ modules a ha f) _ _
    (s.cyclic_commutator_card_le_four source hb modules ha) hcomm _
    (s.cyclic_commutator_normalized_twoResidual source hb ha)
  · rw [hker]
    exact s.Z_le_X.trans (s.X_le_Q hb ha)
  · simpa only [s.localResidual_eq_parabolic source ha] using s.fixed_Z
  · rw [hker]
    exact commutator_le_right _ _
  · rw [hker]
    exact s.cyclic_commutator_normalized_Q

end SelectedSeed
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
