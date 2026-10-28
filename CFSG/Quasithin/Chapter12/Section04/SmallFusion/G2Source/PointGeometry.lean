module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.ResidualActor
public import Theory.Representation.G2BinaryPointCentralizer
public import Theory.Representation.G2NaturalExtensions.FixedSpaces
public import Theory.ElementaryAbelian.EightQuotientRank

/-!
# The source omega point in the full G₂ actor

The escaping omega center has order four and contains the fixed line of
the seven-dimensional module. A complementary involution gives a nonzero
point of the natural quotient whose stabilizer is the literal omega-center
centralizer. The binary point geometry then makes the moving elementary
eight self-centralizing in the full normalizer actor range.

Source: Aschbacher--Smith 3.3.28, printed p.601; B.4.6(13), printed p.90.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02 Chapter12.Section02.RecognitionSource
open Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
open ChapterB.QuasisimpleSource Atlas.G2.Natural
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
local notation "F" => ZMod 2
local notation "W" => TraceZero F

theorem exists_omega_point_for_full_g2_actor
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (b : V ≃* Multiplicative W)
    (ψ : normalizer (L : Set G) →* Atlas.G2.Model F)
    (hψ : ∀ (r : normalizer (L : Set G)) (x : W),
      (b.symm (Multiplicative.ofAdd
        (traceZeroAction F (ψ r) x)) : G) =
        (r : G) * (b.symm (Multiplicative.ofAdd x) : G) * (r : G)⁻¹) :
    ∃ v : Space F, v ≠ 0 ∧ ∀ r : normalizer (L : Set G),
      r ∈ (centralizer (omegaCenterIn (T : Subgroup G) : Set G)).subgroupOf
        (normalizer (L : Set G)) ↔ action F (ψ r) v = v := by
  classical
  let E := omegaCenterIn (T : Subgroup G)
  let U := V ⊓ centralizer (L : Set G)
  obtain ⟨hEV, hEc⟩ := omega_geometry_of_escape h D structural e hne hescape
  obtain ⟨z, _, hgen, hNz, _, hzE, _⟩ :=
    exists_fixed_involution_setup h D structural e hne
  have hUE : U ≤ E := by
    change V ⊓ centralizer (L : Set G) ≤ omegaCenterIn (T : Subgroup G)
    rw [hgen, omegaCenterIn_eq_omegaOneAmbient]
    exact zpowers_le_of_mem hzE
  have hUc : Nat.card U = 2 := fixed_card_eq_two D e hne
  have hnot : ¬ E ≤ U := by
    intro hh
    have heq : E = U := le_antisymm hh hUE
    have hc : Nat.card U = 4 := by rw [← heq]; exact hEc
    rw [hUc] at hc
    omega
  obtain ⟨x, hxE, hxU⟩ := SetLike.not_le_iff_exists.mp hnot
  have hxV : x ∈ V := hEV hxE
  have hjoin : E = U ⊔ zpowers x := by
    have hHE : U ⊔ zpowers x ≤ E := sup_le hUE (zpowers_le_of_mem hxE)
    have hlarge : 2 < Nat.card (U ⊔ zpowers x : Subgroup G) := by
      by_contra hn
      have he : U = U ⊔ zpowers x :=
        eq_of_le_of_card_ge le_sup_left (by omega)
      have hxSup : x ∈ U ⊔ zpowers x :=
        (show zpowers x ≤ U ⊔ zpowers x from le_sup_right) (mem_zpowers x)
      exact hxU (he ▸ hxSup)
    have hdvd : Nat.card (U ⊔ zpowers x : Subgroup G) ∣ 2 ^ 2 := by
      have hd := card_dvd_of_le hHE
      rw [hEc] at hd
      norm_num at hd ⊢
      exact hd
    obtain ⟨k, hk, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hc4 : Nat.card (U ⊔ zpowers x : Subgroup G) = 4 := by
      have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk' with rfl | rfl | rfl
      · norm_num at hc
        simp [hc] at hlarge
      · norm_num at hc
        omega
      · norm_num at hc ⊢
        exact hc
    have hcard_le : Nat.card (U ⊔ zpowers x : Subgroup G) ≤ 4 := by
      have hh := card_le_of_le hHE
      rw [hEc] at hh
      exact hh
    have hcard_ge : Nat.card E ≤ Nat.card (U ⊔ zpowers x : Subgroup G) := by
      rw [hEc, hc4]
    exact (eq_of_le_of_card_ge hHE hcard_ge).symm
  have hNU : normalizer (L : Set G) ≤ centralizer (U : Set G) := by
    have hgen' : U = zpowers z := hgen
    rw [hgen']
    intro r hr
    rw [zpowers_eq_closure, centralizer_closure]
    exact hNz ▸ hr
  let w : W := (b ⟨x, hxV⟩).toAdd
  have hfix_iff (r : normalizer (L : Set G)) :
      traceZeroAction F (ψ r) w = w ↔ (r : G) * x = x * (r : G) := by
    have hh := hψ r w
    have hb : (b.symm (Multiplicative.ofAdd w) : G) = x := by
      exact congrArg Subtype.val (b.symm_apply_apply ⟨x, hxV⟩)
    rw [hb] at hh
    constructor
    · intro hh'
      rw [hh', hb] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh.symm)
    · intro hc
      have hh' : (b.symm (Multiplicative.ofAdd (traceZeroAction F (ψ r) w)) : G) = x := by
        rw [hh, hc, mul_inv_cancel_right]
      have he := b.symm.injective (Subtype.ext (hh'.trans hb.symm))
      exact Multiplicative.ofAdd.injective he
  have hnonzero : mk F w ≠ 0 := by
    intro hz
    have hw : w ∈ scalarLine F := (Submodule.Quotient.mk_eq_zero _).mp hz
    have hfix (r : normalizer (L : Set G)) : traceZeroAction F (ψ r) w = w := by
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
      rw [← hc, map_smul, traceZeroAction_identity]
    apply hxU
    refine ⟨hxV, ?_⟩
    intro l hl
    simpa only using (hfix_iff ⟨l, L.le_normalizer hl⟩).mp (hfix _)
  refine ⟨mk F w, hnonzero, ?_⟩
  intro r
  have hn : action F (ψ r) (mk F w) = mk F w ↔ traceZeroAction F (ψ r) w = w :=
    ⟨Extensions.traceZero_fixed_of_natural_fixed _ _, fun hh => by rw [action_mk, hh]⟩
  rw [hn, hfix_iff]
  change (r : G) ∈ centralizer (E : Set G) ↔ _
  constructor
  · intro hr
    exact (hr x hxE).symm
  · intro hr
    have hx : (r : G) ∈ centralizer (zpowers x : Set G) := by
      rw [zpowers_eq_closure, centralizer_closure]
      exact mem_centralizer_singleton_iff.mpr hr
    have hu := hNU r.property
    rw [hjoin]
    exact (le_centralizer_iff.mp (sup_le
      (le_centralizer_iff.mpr (show zpowers (r : G) ≤ centralizer (U : Set G) from
        zpowers_le_of_mem hu))
      (le_centralizer_iff.mpr (show zpowers (r : G) ≤ centralizer (zpowers x : Set G) from
        zpowers_le_of_mem hx)))) (mem_zpowers (r : G))

/-- The escaping point gives the self-centralizing image required by the
source centralizer cover.  The point stabilizer is formed in the full
normalizer actor; it is then available for restriction to the intrinsic
residual core. -/
theorem full_actor_moved_image_selfcentralizing
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    {d : G} (hd : d ∈ normalizer (T : Set G))
    (b : V ≃* Multiplicative W)
    (ψ : normalizer (L : Set G) →* Atlas.G2.Model F)
    (hψ : ∀ (r : normalizer (L : Set G)) (x : W),
      (b.symm (Multiplicative.ofAdd (traceZeroAction F (ψ r) x)) : G) =
        (r : G) * (b.symm (Multiplicative.ofAdd x) : G) * (r : G)⁻¹)
    (hrange : commutator (Atlas.G2.Model F) ≤ ψ.range)
    (hcard : Nat.card (((V.map (MulAut.conj d).toMonoidHom).subgroupOf
      (normalizer (L : Set G))).map ψ) = 8) :
    ψ.range ⊓ centralizer
        ((((V.map (MulAut.conj d).toMonoidHom).subgroupOf
          (normalizer (L : Set G))).map ψ : Subgroup (Atlas.G2.Model F)) : Set _) ≤
      (((V.map (MulAut.conj d).toMonoidHom).subgroupOf
        (normalizer (L : Set G))).map ψ : Subgroup (Atlas.G2.Model F)) := by
  let N := normalizer (L : Set G)
  let E := omegaCenterIn (T : Subgroup G)
  let B := V.map (MulAut.conj d).toMonoidHom
  let C := (centralizer (E : Set G)).subgroupOf N
  let A := B.subgroupOf N
  let : IsElementaryAbelian 2 V := D.elementary
  obtain ⟨v, hv, hpoint⟩ := exists_omega_point_for_full_g2_actor h D structural e hne
    hescape b ψ hψ
  have hEV : E ≤ V := (omega_geometry_of_escape h D structural e hne hescape).1
  have hEd : E.map (MulAut.conj d).toMonoidHom = E :=
    mem_normalizer_iff_map_conj_eq.mp
      (normalizer_le_normalizer_omegaCenterIn (T : Subgroup G) hd)
  have hEVd : E ≤ B := by
    exact hEd ▸ map_mono hEV
  have hBN : B ≤ N := by
    have hBT : B ≤ (T : Subgroup G) := by
      rw [← mem_normalizer_iff_map_conj_eq.mp hd]
      exact map_mono D.le_sylow
    exact hBT.trans D.sylow_normalizes_component
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map
    (MulAut.conj d).toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hBN
  have hBC : B ≤ centralizer (E : Set G) := by
    let := D.elementary
    apply le_centralizer_iff.mpr
    exact hEVd.trans (show B ≤ centralizer (B : Set G) from B.le_centralizer)
  have hAC : A ≤ C := subgroupOf_mono N hBC
  have hCV : centralizer (E : Set G) ≤ normalizer (V : Set G) := by
    obtain ⟨_, _, _, _, hNV, _, _⟩ := exists_fixed_involution_setup h D structural e hne
    exact (omega_centralizer_le h D hne).trans hNV.le
  have hCd : (centralizer (E : Set G)).map (MulAut.conj d).toMonoidHom =
      centralizer (E : Set G) := mem_normalizer_iff_map_conj_eq.mp
    (sylow_normalizer_normalizes_omega_centralizer hd)
  have hCB : centralizer (E : Set G) ≤ normalizer (B : Set G) := by
    have hh := (map_mono (f := (MulAut.conj d).toMonoidHom) hCV).trans
      (V.le_normalizer_map (MulAut.conj d).toMonoidHom)
    rwa [hCd] at hh
  have hnorm : C ≤ normalizer (A : Set N) := by
    rw [← subgroupOf_normalizer_eq hBN]
    exact subgroupOf_mono N hCB
  have hpoint' : ∀ a : N, a ∈ C ↔ action F (ψ a) v = v := by
    intro a
    exact hpoint a
  have hself := Atlas.G2.Natural.BinaryPointFlag.point_eight_selfcentralizing
    ψ hrange C A hAC hnorm v hv hpoint' hcard
  rw [hself]
  exact inf_le_right

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
