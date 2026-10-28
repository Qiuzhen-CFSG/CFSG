module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Natural.Kernel.FixedSummand.Transport

/-!
# The genuine first-parabolic quotient and incident reflection

The marked quotient of the first parabolic is identified with SL₂(2), then
with the literal S₃. Its kernel is exactly the embedded parabolic two-core.
The incident opposite core is a two-group and normally generates the first
actor, so its image is a nontrivial two-subgroup of S₃, hence one reflection.
Surjective transport of the two-residual supplies a lift of the fixed cubic.

These facts concern the actual subgroups and quotient maps. All normal
closures are relative to the first full actor; the cubic lift is in the
separate tilded residual.

Source: Meierfrankenfeld--Stellmacher (1993), (1.7), printed pp.847--848,
and the incident configuration of (4.6.8)(3), printed pp.905--906.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Natural.Kernel
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The full first parabolic has its genuine binary rank-one quotient, with
exactly its own two-core as kernel. -/
theorem exists_barProjection (source : LocalSource L R) (i : Bool) :
    ∃ π : flagParabolic source i →* BinaryS3.Actor,
      Function.Surjective π ∧
      π.ker = (flagKernel source i).subgroupOf (flagParabolic source i) := by
  let P := parabolic source.projection source.flag i
  let T := modelParabolic source.flag i
  let q : P →* T := (source.projection.comp P.subtype).codRestrict T (fun x => x.property)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := source.projection_surjective y
    exact ⟨⟨x, by change source.projection x ∈ T; rw [hx]; exact y.property⟩,
      Subtype.ext hx⟩
  obtain ⟨e⟩ := source.weakBN.rank_one i
  obtain ⟨f⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let c := e.trans f
  let r := c.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 T)).comp q)
  have hr : Function.Surjective r :=
    c.surjective.comp ((QuotientGroup.mk'_surjective _).comp hq)
  have hk (x : P) : r x = 1 ↔ (x : M) ∈ P.pCoreIn 2 := by
    change c (QuotientGroup.mk' (pCore 2 T) (q x)) = 1 ↔ _
    rw [← c.map_one, c.injective.eq_iff, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    rw [Incident.parabolic_core_eq_comap source i]
    change q x ∈ pCore 2 T ↔ source.projection x ∈ T.pCoreIn 2
    rw [pCoreIn]
    exact ⟨fun h => ⟨q x, h, rfl⟩, fun ⟨y, hy, he⟩ =>
      (show y = q x from Subtype.ext he) ▸ hy⟩
  let j : P ≃* flagParabolic source i :=
    P.equivMapOfInjective (embedM R) (embedM_injective R)
  refine ⟨r.comp j.symm.toMonoidHom, hr.comp j.symm.surjective, ?_⟩
  ext x
  change r (j.symm x) = 1 ↔ (x : FreeAmalgam R) ∈ flagKernel source i
  rw [hk]
  change (j.symm x : M) ∈ P.pCoreIn 2 ↔
    (x : FreeAmalgam R) ∈ (P.pCoreIn 2).map (embedM R)
  have he : embedM R (j.symm x) = (x : FreeAmalgam R) :=
    congrArg Subtype.val (j.apply_symm_apply x)
  constructor
  · intro h
    exact ⟨j.symm x, h, he⟩
  · rintro ⟨y, hy, hyx⟩
    have hxy := embedM_injective R (hyx.trans he.symm)
    exact hxy ▸ hy

private theorem localFacts_bot (e : RankOnePairing.Extension (M := M)) :
    RankOnePairing.Incidence.LocalFacts e ⊥ where
  core_le := RankOnePairing.extensionCore_le_localParabolic e
  core_eq j := (RankOnePairing.selectedCore_eq_localCore e j).symm
  parabolic_image := RankOnePairing.localParabolic_map e
  residual_image := RankOnePairing.localResidual_map e
  core_image := RankOnePairing.localCore_map e
  generation := RankOnePairing.localParabolic_generation e
  component_normal := RankOnePairing.component_normal e
  component_image := RankOnePairing.component_map _ e.base.surjective _
  z_central := bot_le
  z_irreducible := fun _ h _ => Or.inl (bot_unique h)

/-- Conjugates of the incident opposite core inside the first full actor
generate that actor. Normality here is relative to the first parabolic. -/
theorem incidentCore_normally_generates (source : LocalSource L R) (i : Bool)
    (d : M) (hd : flagIncident source i 1 d) :
    flagParabolic source i ≤ RankOnePairing.localGenerated (flagParabolic source i)
      (localFlagKernel source (!i) d) := by
  let m := representative source i d hd
  let e := Transport.extension source
  let P := RankOnePairing.localParabolic e i
  let K := RankOnePairing.selectedCore e (!i)
  have hP : P ≤ RankOnePairing.localGenerated P K := by
    have h := RankOnePairing.Incidence.DualGeometry.residual_generation (localFacts_bot e) i
    rw [← RankOnePairing.selectedCore_eq_localCore] at h
    have hr : RankOnePairing.localResidual P = P := by
      rw [show P = parabolic source.projection source.flag i from pairing_parabolic source i,
        RankOnePairing.localResidual,
        primeToResidual_parabolic_eq_top source.projection source.projection_surjective
          (by rw [source.projection_kernel]; exact pCore_isPGroup),
        ← MonoidHom.range_eq_map, range_subtype]
    change RankOnePairing.localResidual P ≤ RankOnePairing.localGenerated P K at h
    rwa [hr] at h
  have hpullP : pull m (flagParabolic source i) = P := by
    rw [← map_first_actor source i d hd, pull_map]
  have hpullK : pull m (localFlagKernel source (!i) d) = K := by
    rw [← map_second_core source i d hd, pull_map]
  have hm := map_mono (f := embedding R m) hP
  have he := map_pull_localGenerated m _ _ (flagParabolic_le source i)
    (incidentKernel_le_flagParabolic source i d hd)
  rw [hpullP, hpullK] at he
  rw [he, map_first_actor source i d hd] at hm
  exact hm

private theorem perm_orders : ∀ x : BinaryS3.Actor, x ^ 2 = 1 ∨ x ^ 3 = 1 := by
  decide +kernel

private theorem perm_involutions : ∀ x y : BinaryS3.Actor,
    x ^ 2 = 1 → y ^ 2 = 1 → (x * y) ^ 2 = 1 → x = 1 ∨ y = 1 ∨ x = y := by
  decide +kernel

private theorem two_subgroup_reflection (H : Subgroup BinaryS3.Actor) (hp : IsPGroup 2 H)
    (hne : H ≠ ⊥) : ∃ t : BinaryS3.Actor, t ^ 2 = 1 ∧ t ≠ 1 ∧
      ∀ x, x ∈ H ↔ x = 1 ∨ x = t := by
  have hs (x : BinaryS3.Actor) (hx : x ∈ H) : x ^ 2 = 1 := by
    rcases perm_orders x with h | h
    · exact h
    · have hc := hp.orderOf_coprime (by decide : Nat.Coprime 2 3) (⟨x, hx⟩ : H)
      have hd : orderOf (⟨x, hx⟩ : H) ∣ 3 :=
        orderOf_dvd_of_pow_eq_one (show (⟨x, hx⟩ : H) ^ 3 = 1 from Subtype.ext h)
      have he : (⟨x, hx⟩ : H) = 1 :=
        orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc (dvd_refl _) hd)
      have he' : x = 1 := congrArg Subtype.val he
      simp [he']
  obtain ⟨t, ht, htn⟩ := (bot_or_exists_ne_one H).resolve_left hne
  refine ⟨t, hs t ht, htn, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · rcases perm_involutions t x (hs t ht) (hs x hx) (hs (t * x) (H.mul_mem ht hx)) with h | h | h
    · exact (htn h).elim
    · exact Or.inl h
    · exact Or.inr h.symm
  · rintro (rfl | rfl)
    · exact H.one_mem
    · exact ht

/-- The actual opposite core maps onto the two-element subgroup generated
by a nonidentity reflection in the genuine first rank-one quotient. -/
theorem exists_incident_reflection (source : LocalSource L R) (i : Bool)
    (d : M) (hd : flagIncident source i 1 d)
    (π : flagParabolic source i →* BinaryS3.Actor) (hπ : Function.Surjective π)
    (hker : π.ker = (flagKernel source i).subgroupOf (flagParabolic source i)) :
    ∃ t : BinaryS3.Actor, t ^ 2 = 1 ∧ t ≠ 1 ∧
      ∀ x, x ∈ ((localFlagKernel source (!i) d).subgroupOf (flagParabolic source i)).map π ↔
        x = 1 ∨ x = t := by
  let P := flagParabolic source i
  let K := localFlagKernel source (!i) d
  have hp : IsPGroup 2 K := by
    exact ((isPGroup_pCoreIn 2 (parabolic source.projection source.flag (!i))).map
      (embedM R)).map (MulAut.conj (embedM R d)).toMonoidHom
  apply two_subgroup_reflection _ (hp.comap_subtype.map π)
  intro hbot
  have hK : K ≤ flagKernel source i := by
    intro x hx
    let y : P := ⟨x, incidentKernel_le_flagParabolic source i d hd hx⟩
    have he : π y = 1 := mem_bot.mp (hbot ▸ mem_map_of_mem π (show y ∈ K.subgroupOf P from hx))
    have hh : y ∈ π.ker := he
    rw [hker] at hh
    exact hh
  have hP : P ≤ flagKernel source i :=
    (incidentCore_normally_generates source i d hd).trans
      (RankOnePairing.Incidence.localGenerated_le_of_normalizes _ _ _
        (flagKernel_normalized source i) hK)
  obtain ⟨x, hx⟩ := hπ BinaryS3.cubic
  have he : π x = 1 := MonoidHom.mem_ker.mp (hker ▸ hP x.property)
  have hn : BinaryS3.cubic ≠ 1 := by decide +kernel
  exact hn (hx.symm.trans he)

/-- A cubic in the rank-one image lifts from the tilded residual O²(P),
using surjective residual transport rather than full-actor membership alone. -/
theorem cubic_lift_of_surjective (source : LocalSource L R) (i : Bool)
    (π : flagParabolic source i →* BinaryS3.Actor) (hπ : Function.Surjective π) :
    ∃ r : flagParabolic source i,
      (r : FreeAmalgam R) ∈ flagResidual source i ∧ π r = BinaryS3.cubic := by
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite (flagParabolic source i) :=
    Finite.of_injective (inclusion (flagParabolic_le source i)) (inclusion_injective _)
  have hc : BinaryS3.cubic ∈ pResidual 2 BinaryS3.Actor :=
    mem_pResidual_of_orderOf_coprime ((by decide : Nat.Coprime 2 3).of_dvd_right
      (orderOf_dvd_of_pow_eq_one BinaryS3.cubic_cube))
  rw [← map_pResidual_of_surjective 2 π hπ] at hc
  obtain ⟨r, hr, he⟩ := hc
  exact ⟨r, (flagResidual_eq source i).symm ▸ mem_map_of_mem _ hr, he⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Natural.Kernel
