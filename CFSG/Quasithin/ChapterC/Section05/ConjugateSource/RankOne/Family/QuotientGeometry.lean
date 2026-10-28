module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Family.QuotientBasic

/-!
# The two actual elementary cores in S/Φ(D)

The centralizer kernel remains Q after removing Φ(D), because fixed points
on U lift through that quotient. Its opposite VD is the conjugate core.
Both quotient cores are elementary and generate the full quotient. These
are the actual structural inputs for the B.2.21 counting argument.

Source: Aschbacher–Smith C.5.6(5), printed p.157.
-/

public section
open Subgroup
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] {R : Subgroup G} {T : Type*} [Group T]

private theorem image_centralizes (f : S R →* T) (A B : Subgroup G)
    (hc : A ≤ centralizer (B : Set G)) :
    baumannImage R f A ≤ centralizer (baumannImage R f B : Set T) := by
  rintro a ⟨s, hs, rfl⟩ b ⟨t, ht, rfl⟩
  exact (map_mul f t s).symm.trans
    ((congrArg f (Subtype.ext (hc hs t ht))).trans (map_mul f s t))

private theorem image_sup (f : S R →* T) (A B : Subgroup G) (hA : A ≤ S R) (hB : B ≤ S R) :
    baumannImage R f (A ⊔ B) = baumannImage R f A ⊔ baumannImage R f B := by
  rw [baumannImage, subgroupOf_sup hA hB, Subgroup.map_sup]
  rfl

private theorem image_top (f : S R →* T) (hf : Function.Surjective f) :
    baumannImage R f (S R) = ⊤ := by
  rw [baumannImage, subgroupOf_self, map_top_of_surjective f hf]

variable [Finite G] {L : Subgroup G} {F : Type*} [Field F]

/-- The original Frattini layer lies inside Q. -/
theorem Setup.phi_le_core (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G)) :
    Phi R L ≤ Q R L := by
  rw [← h.core_frattini hx hnc]
  exact map_subtype_le _

/-- The two literal quotient cores span the entire S/Φ(D). -/
theorem Setup.quotient_span (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G))
    (f : S R →* T) (hf : Function.Surjective f) :
    baumannImage R f (Q R L) ⊔
      baumannImage R f ((Q R L).map (MulAut.conj x⁻¹).toMonoidHom) = ⊤ := by
  rw [← image_sup f _ _ (h.core ▸ inf_le_left) ((h.conjugate_core hx).le.trans inf_le_left),
    ← h.core_span hx hnc, image_top f hf]

/-- The actual opposite quotient core is elementary. -/
theorem Setup.quotient_opposite_elementary (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G))
    (f : S R →* T) (hk : f.ker = (Phi R L).subgroupOf (S R)) :
    IsElementaryAbelian 2 (baumannImage R f ((Q R L).map (MulAut.conj x⁻¹).toMonoidHom)) := by
  let V := (U L).map (MulAut.conj x⁻¹).toMonoidHom
  have hp := h.factorization hx hnc
  let := h.elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 (V.subgroupOf (S R)) := IsElementaryAbelian.subgroupOf (h.conjugate_le hx)
  let : IsElementaryAbelian 2 (baumannImage R f V) := IsElementaryAbelian.map f
  let := h.quotient_core_elementary hx hnc f hk
  have hDQ : baumannImage R f (D R L) ≤ baumannImage R f (Q R L) :=
    map_mono (subgroupOf_mono _ (hp.core ▸ le_sup_right))
  let : IsElementaryAbelian 2 (baumannImage R f (D R L)) := IsElementaryAbelian.of_le hDQ
  rw [← h.opposite_eq_conjugate hx hnc, image_sup f _ _ (h.conjugate_le hx) inf_le_left]
  exact IsElementaryAbelian.sup_of_le_centralizer (image_centralizes f _ _ hp.centralizes)

/-- The core image is still self-centralizing after quotienting by Φ(D). -/
theorem Setup.quotient_core_selfcentralizing (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G))
    (f : S R →* T) (hf : Function.Surjective f)
    (hk : f.ker = (Phi R L).subgroupOf (S R)) :
    centralizer (baumannImage R f (Q R L) : Set T) = baumannImage R f (Q R L) := by
  let := h.quotient_core_elementary hx hnc f hk
  apply le_antisymm
  · intro z hz
    obtain ⟨s, rfl⟩ := hf z
    apply (baumannImage_mem_iff f hk _ (h.phi_le_core hx hnc) s).mpr
    rw [h.core]
    refine ⟨s.property, ?_⟩
    intro u hu
    have huQ : f (inclusion h.module_le ⟨u, hu⟩) ∈ baumannImage R f (Q R L) :=
      mem_map_of_mem f (h.module_le_core hu)
    have hfix : f (inclusion h.module_le
        (moduleConjugate h.coordinates.normalizes s ⟨u, hu⟩)) =
        f (inclusion h.module_le ⟨u, hu⟩) := by
      have hc := hz _ huQ
      change f (s * inclusion h.module_le ⟨u, hu⟩ * s⁻¹) = _
      rw [map_mul, map_mul, map_inv, ← hc, mul_inv_cancel_right]
    have he := congrArg Subtype.val (h.fixed_lift_mod_phi f hk s ⟨u, hu⟩ hfix)
    change (s : G) * u * (s : G)⁻¹ = u at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · exact le_centralizer _

/-- The two quotient cores are distinct; the original escaping module stays outside Q. -/
theorem Setup.quotient_opposite_not_le (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G))
    (f : S R →* T) (hk : f.ker = (Phi R L).subgroupOf (S R)) :
    ¬ baumannImage R f ((Q R L).map (MulAut.conj x⁻¹).toMonoidHom) ≤ baumannImage R f (Q R L) := by
  intro he
  apply hnc
  intro v hv
  let s : S R := ⟨v, h.conjugate_le hx hv⟩
  have hm := he (mem_map_of_mem f (show s ∈ ((Q R L).map (MulAut.conj x⁻¹).toMonoidHom).subgroupOf (S R) from
    map_mono h.module_le_core hv))
  exact (h.core ▸ inf_le_right) ((baumannImage_mem_iff f hk _ (h.phi_le_core hx hnc) s).mp hm)
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
end

public section
open Subgroup
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R L : Subgroup G} {F : Type*} [Field F]
variable {T : Type*} [Group T]

private theorem intersection_centralizes_top (A B : Subgroup T)
    [IsMulCommutative A] [IsMulCommutative B] (hspan : A ⊔ B = ⊤) :
    A ⊓ B ≤ center T := by
  intro z hz
  rw [mem_center_iff]
  intro t
  have hc : z ∈ centralizer ((A ⊔ B : Subgroup T) : Set T) := by
    rw [sup_eq_closure, centralizer_closure]
    intro a ha
    rcases ha with ha | ha
    · exact mem_centralizer_iff.mp (le_centralizer A hz.1) a ha
    · exact mem_centralizer_iff.mp (le_centralizer B hz.2) a ha
  rw [hspan] at hc
  exact hc t (mem_top _)

/-- D becomes central in the genuine S/Φ(D), without vanishing of Φ(D). -/
theorem Setup.quotient_centralizer_central (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G))
    (f : S R →* T) (hf : Function.Surjective f)
    (hk : f.ker = (Phi R L).subgroupOf (S R)) :
    baumannImage R f (D R L) ≤ center T := by
  let := h.quotient_core_elementary hx hnc f hk
  let := h.quotient_opposite_elementary hx hnc f hk
  apply (le_inf ?_ ?_).trans
    (intersection_centralizes_top _ _ (h.quotient_span hx hnc f hf))
  · exact map_mono (subgroupOf_mono _ ((h.factorization hx hnc).core ▸ le_sup_right))
  · exact map_mono (subgroupOf_mono _ ((h.opposite_eq_conjugate hx hnc).symm ▸ le_sup_right))

private theorem fixed_module_mem_conjugate (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G))
    (s : S R) (hsq : (s : G) ∉ Q R L) (u : U L)
    (hfix : moduleConjugate h.coordinates.normalizes s u = u) :
    (u : G) ∈ (U L).map (MulAut.conj x⁻¹).toMonoidHom := by
  have hparam : (h.coordinates.parameter s).toAdd ≠ 0 := by
    intro he
    apply hsq
    rw [h.core]
    exact ⟨s.property, (h.coordinates.parameter_kernel s).mp (Multiplicative.toAdd.injective he)⟩
  have hzero : (h.coordinates.projection u).toAdd 1 = 0 := by
    have hh := congrArg (fun v : Multiplicative (Fin 2 → F) => v.toAdd 0)
      (congrArg h.coordinates.projection hfix)
    rw [h.coordinates.equivariant] at hh
    have hz : (h.coordinates.parameter s).toAdd * (h.coordinates.projection u).toAdd 1 = 0 := by
      simpa using hh
    exact (mul_eq_zero.mp hz).resolve_left hparam
  have hc := centralizes_of_second_zero h.coordinates h.fixedLift u hzero
  have hu : (u : G) ∈ U L ⊓ centralizer ((U L).map (MulAut.conj x⁻¹).toMonoidHom : Set G) :=
    ⟨u.property, centralizer_le (h.conjugate_le hx) hc⟩
  rw [← (h.commutator_eq_fixed hx hnc).1, (h.commutator_eq_fixed hx hnc).2] at hu
  exact hu.2

/-- Uniform full fixed subgroups in the quotient, with lifting through Φ(D)
proved from the original natural cover. -/
theorem Setup.quotient_fixed_singleton (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G))
    (f : S R →* T) (hf : Function.Surjective f)
    (hk : f.ker = (Phi R L).subgroupOf (S R))
    (t : T) (ht : t ∉ baumannImage R f (Q R L)) :
    baumannImage R f (Q R L) ⊓ centralizer ({t} : Set T) =
      baumannImage R f (Q R L) ⊓
        baumannImage R f ((Q R L).map (MulAut.conj x⁻¹).toMonoidHom) := by
  obtain ⟨s, rfl⟩ := hf t
  have hsQ : (s : G) ∉ Q R L := fun hs => ht (mem_map_of_mem f hs)
  let Q' := (Q R L).map (MulAut.conj x⁻¹).toMonoidHom
  have hp := h.factorization hx hnc
  have hDQ' : D R L ≤ Q' :=
    (le_sup_right : D R L ≤ (U L).map (MulAut.conj x⁻¹).toMonoidHom ⊔ D R L).trans_eq
      (h.opposite_eq_conjugate hx hnc)
  let := h.quotient_core_elementary hx hnc f hk
  let := h.quotient_opposite_elementary hx hnc f hk
  apply le_antisymm
  · rintro z ⟨⟨q, hq, rfl⟩, hqfix⟩
    refine ⟨mem_map_of_mem f hq, ?_⟩
    have hqprod : (q : G) ∈ (U L : Set G) * (D R L : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right]
      · exact hp.core ▸ hq
      · exact (le_centralizer_iff.mp ((hp.core ▸ le_sup_right).trans
          (h.core ▸ inf_le_right))).trans (Subgroup.centralizer_le_normalizer _)
    obtain ⟨u, hu, d, hd, hud⟩ := hqprod
    let uS : S R := inclusion h.module_le ⟨u, hu⟩
    let dS : S R := ⟨d, hd.1⟩
    have hqeq : q = uS * dS := Subtype.ext hud.symm
    have hdcent : f dS ∈ center T :=
      h.quotient_centralizer_central hx hnc f hf hk (mem_map_of_mem f hd)
    have hdfix : f dS ∈ centralizer ({f s} : Set T) := by
      intro a ha
      exact mem_center_iff.mp hdcent a
    have hufix : f uS ∈ centralizer ({f s} : Set T) := by
      rw [hqeq, map_mul] at hqfix
      exact ((centralizer ({f s} : Set T)).mul_mem_cancel_right hdfix).mp hqfix
    have humod : f (inclusion h.module_le (moduleConjugate h.coordinates.normalizes s ⟨u, hu⟩)) =
        f (inclusion h.module_le ⟨u, hu⟩) := by
      change f (s * uS * s⁻¹) = f uS
      rw [map_mul, map_mul, map_inv, ← mem_centralizer_singleton_iff.mp hufix, mul_inv_cancel_right]
    have huV := fixed_module_mem_conjugate h hx hnc s hsQ ⟨u, hu⟩
      (h.fixed_lift_mod_phi f hk s ⟨u, hu⟩ humod)
    have huQ' : u ∈ Q' := map_mono h.module_le_core huV
    rw [hqeq, map_mul]
    exact mul_mem (mem_map_of_mem f huQ') (mem_map_of_mem f (hDQ' hd))
  · intro z hz
    refine ⟨hz.1, ?_⟩
    have hc := intersection_centralizes_top _ _ (h.quotient_span hx hnc f hf) hz
    intro a ha
    exact mem_center_iff.mp hc a
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
end
