module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Generation.Escape.RecognitionInputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Generation.Escape.Recognition.Descent
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Generation.Escape.Recognition.Group

/-!
# Recognition of the trapped-span natural section

An elementary normal section with a marked SL3(2) quotient, trivial quotient-
kernel action, nontrivial whole-group action, and one displacement image of
order at most two is the sum of its fixed part and one actual natural module.

First descend conjugation faithfully and recognize the resulting transvection
representation. The quotient correspondence identifies its moving and fixed
subgroups with N[H,A] and the literal centralizer modulo N. The natural
coordinates pull back along the quotient map and retain the exact kernel and
conjugation equation. Since [H,ker π] lies in N, the radical is precisely N,
and normality also gives the required triple-commutator containment.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), c(U)=1 on printed p.881 and the inference in (4.6.8)(2), p.906.
-/

public section

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Generation
open Recognition
variable {A : Type*} [Group A] [Finite A] {π : A →* SL} {H N : Subgroup A}

/-- The algebraic small-displacement hypotheses yield the complete literal
split natural section, with no remaining representation premises. -/
theorem singleNaturalSection_of_smallDisplacement (d : SmallDisplacementData π H N) :
    Nonempty (Escape.SingleNaturalSection π π.ker (pResidual 2 A) H N) := by
  let := d.normal_group
  let := d.normal_kernel
  let := d.elementary
  obtain ⟨ρ, hf, hformula, t, htne, ht, hsmall⟩ := d.exists_faithful_action
  obtain ⟨e, marking, he, hcompl⟩ := group_split ρ hf t ht htne hsmall
  let E := H ⧸ N.subgroupOf H
  let q := QuotientGroup.mk' (N.subgroupOf H)
  let D := moved ρ
  let F := fixed ρ
  let K := ⁅H, (⊤ : Subgroup A)⁆
  let M := N ⊔ K
  have hKH : K ≤ H := commutator_le_left H ⊤
  have hMH : M ≤ H := sup_le d.kernel_le hKH
  have hHN : (⊤ : Subgroup A) ≤ normalizer (H : Set A) := by rw [normalizer_eq_top]
  let τ : (⊤ : Subgroup A) →* MulAut E := ρ.comp (π.comp (⊤ : Subgroup A).subtype)
  have hτ (a : (⊤ : Subgroup A)) (h : H) :
      τ a (q h) = q ⟨(a : A) * (h : A) * (a : A)⁻¹,
        (mem_normalizer_iff.mp (hHN a.property) h).mp h.property⟩ := hformula a h
  have hrange : ((⊤ : Subgroup A).subgroupOf ⊤).map τ = ρ.range := by
    apply le_antisymm
    · rintro _ ⟨a, _, rfl⟩
      exact ⟨π a, rfl⟩
    · rintro _ ⟨g, rfl⟩
      obtain ⟨a, rfl⟩ := d.projection_surjective g
      exact ⟨⟨a, mem_top a⟩, mem_top _, rfl⟩
  have hD : D = (K.subgroupOf H).map q := by
    change commutatorAction ρ.range E = _
    rw [← hrange]
    exact quotient_conjugation_commutatorAction_eq_image ⊤ H N ⊤ hHN le_rfl
      inferInstance τ hτ
  have hM : (D.comap q).map H.subtype = M := by
    rw [hD, comap_map_eq, Subgroup.map_sup,
      show q.ker = N.subgroupOf H from QuotientGroup.ker_mk' _]
    change (K.subgroupOf H).map H.subtype ⊔
      (N.subgroupOf H).map H.subtype = N ⊔ K
    rw [subgroupOf_map_subtype, subgroupOf_map_subtype,
      inf_eq_left.mpr hKH, inf_eq_left.mpr d.kernel_le, sup_comm]
  have hF : (F.comap q).map H.subtype = centralizerModulo H ⊤ N := by
    ext x
    constructor
    · rintro ⟨h, hh, rfl⟩
      apply mem_centralizerModulo_iff.mpr
      refine ⟨h.property, ?_⟩
      intro a _
      have hfix : ρ (π a) (q h) = q h := hh ⟨ρ (π a), π a, rfl⟩
      rw [hformula] at hfix
      have hc := QuotientGroup.eq_iff_div_mem.mp hfix
      change a * (h : A) * a⁻¹ / (h : A) ∈ N at hc
      simpa only [commutatorElement_def, div_eq_mul_inv, coe_subtype] using hc
    · intro hx
      obtain ⟨hxH, hx⟩ := mem_centralizerModulo_iff.mp hx
      refine ⟨⟨x, hxH⟩, ?_, rfl⟩
      intro g
      obtain ⟨s, hs⟩ := g.property
      obtain ⟨a, rfl⟩ := d.projection_surjective s
      change g.val (q ⟨x, hxH⟩) = q ⟨x, hxH⟩
      rw [← hs, hformula]
      apply QuotientGroup.eq_iff_div_mem.mpr
      change a * x * a⁻¹ / x ∈ N
      simpa only [commutatorElement_def, div_eq_mul_inv] using hx a (mem_top a)
  have hsup : M ⊔ centralizerModulo H ⊤ N = H := by
    have hh := congrArg (fun B : Subgroup E => (B.comap q).map H.subtype) hcompl.sup_eq_top
    change ((D ⊔ F).comap q).map H.subtype = _ at hh
    rw [← comap_sup_eq q D F (QuotientGroup.mk'_surjective _), Subgroup.map_sup, hM, hF,
      comap_top, ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh
  have hinf : M ⊓ centralizerModulo H ⊤ N = N := by
    have hh := congrArg (fun B : Subgroup E => (B.comap q).map H.subtype) hcompl.inf_eq_bot
    change ((D ⊓ F).comap q).map H.subtype = _ at hh
    rw [comap_inf, map_inf _ _ _ Subtype.val_injective, hM, hF] at hh
    rw [MonoidHom.comap_bot, show q.ker = N.subgroupOf H from QuotientGroup.ker_mk' _] at hh
    simpa only [subgroupOf_map_subtype, inf_eq_left.mpr d.kernel_le] using hh
  have hmem (h : H) : q h ∈ D ↔ (h : A) ∈ M := by
    constructor
    · intro hh
      rw [← hM]
      exact ⟨h, hh, rfl⟩
    · intro hh
      rw [← hM] at hh
      obtain ⟨z, hz, heq⟩ := hh
      exact (Subtype.ext heq : z = h) ▸ hz
  let f : M →* D := (q.comp (inclusion hMH)).codRestrict D
    (fun m => (hmem (inclusion hMH m)).mpr m.property)
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective (N.subgroupOf H) z.val
    have hm : (h : A) ∈ M := (hmem h).mp (hh ▸ z.property)
    refine ⟨⟨h, hm⟩, ?_⟩
    exact Subtype.ext hh
  have hker : (e.toMonoidHom.comp f).ker = N.subgroupOf M := by
    ext m
    change e (f m) = 1 ↔ (m : A) ∈ N
    rw [e.map_eq_one_iff]
    constructor
    · intro hm
      have hh : q (inclusion hMH m) = 1 := congrArg Subtype.val hm
      exact (QuotientGroup.eq_one_iff (N := N.subgroupOf H) (inclusion hMH m)).mp hh
    · intro hm
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (N := N.subgroupOf H) (inclusion hMH m)).mpr hm
  have hnatural : Nonempty (RankOnePairing.NaturalFactor π ⊤ M N) := by
    refine ⟨{
      marking := marking
      coordinates := e.toMonoidHom.comp f
      surjective := e.surjective.comp hsurj
      kernel := hker
      normalized := by rw [normalizer_eq_top]
      action := ?_ }⟩
    intro a _ x y hy
    apply he (π a) (f x) (f y)
    change q (inclusion hMH y) = ρ (π a) (q (inclusion hMH x))
    rw [hformula]
    congr 1
    exact Subtype.ext hy
  have hrad : Escape.radicalPreimage π.ker H N = N := sup_eq_left.mpr d.kernel_action
  have hmove : Escape.movingPreimage π.ker H N = M := by
    rw [Escape.movingPreimage, hrad]
  obtain ⟨natural⟩ := hnatural
  refine ⟨{
    projection_surjective := d.projection_surjective
    projection_kernel := rfl
    kernel_le := d.kernel_le
    normal_group := d.normal_group
    normal_kernel := d.normal_kernel
    elementary := d.elementary
    radical_normal := hrad.symm ▸ d.normal_kernel
    triple_le := (commutator_mono d.kernel_action le_rfl).trans (commutator_le_left N _)
    decomposition := ?_
    intersection := ?_
    natural := ?_ }⟩
  · simpa only [hmove, hrad] using hsup.symm
  · simpa only [hmove, hrad] using hinf
  · simpa only [hmove, hrad] using natural
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Generation
