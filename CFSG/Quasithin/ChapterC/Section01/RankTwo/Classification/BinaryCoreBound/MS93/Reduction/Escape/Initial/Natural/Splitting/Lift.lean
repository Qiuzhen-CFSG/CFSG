module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Splitting.Actions

/-!
# Lifting the radius-head splitting to a literal natural section

For normal local subgroups H, N and Q, put B = N[H,Q]. An intrinsic
fixed/moving splitting of the actual H/B action lifts through the quotient
correspondence to H = B[H,A] C_H(A mod B), with intersection B.
The moving coordinates pull back to B[H,A], have kernel exactly B, and
intertwine conjugation with the same marking of SL₃(2).

This transport lemma takes the head splitting and triple bound explicitly.
Its consumer constructs the splitting from the critical geometry and retains
only the authorized triple premise in the initial natural-section theorem.
The quotient-correspondence proof follows the existing trapped-span transport
in DistanceFour/Flags/RankOne/Triple/Preparatory/Propagation/Generation/Escape/
Recognition.lean, without importing or assuming that later source result.

Source: Meierfrankenfeld--Stellmacher (1993), the expanded definition of c(U)
on p.881 and (4.3.1)(iii), pp.882--883.
-/

public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Splitting
variable {A : Type*} [Group A]

/-- Lift the intrinsic head splitting through the actual quotient map. -/
theorem singleNaturalSection_of_head_splitting
    (H N Q K : Subgroup A) [H.Normal] [N.Normal] [Q.Normal]
    (π : A →* SL) (hπ : Function.Surjective π) (hker : π.ker = Q)
    (hNH : N ≤ H) (hE : IsElementaryAbelian 2 (H ⧸ N.subgroupOf H))
    (htriple : ⁅⁅H, Q⁆, K⁆ ≤ N)
    (s : NaturalActionSplitting (headAction H N Q π hπ hker)) :
    Nonempty (SingleNaturalSection π Q K H N) := by
  let B := radicalPreimage Q H N
  let E := H ⧸ B.subgroupOf H
  let q := QuotientGroup.mk' (B.subgroupOf H)
  let ρ := headAction H N Q π hπ hker
  let D := commutatorAction ρ.range E
  let F := FixedPoints.subgroup ρ.range E
  let C := ⁅H, (⊤ : Subgroup A)⁆
  let W := B ⊔ C
  have hBH : B ≤ H := sup_le hNH (commutator_le_left H Q)
  have hCH : C ≤ H := commutator_le_left H ⊤
  have hWH : W ≤ H := sup_le hBH hCH
  have hHN : (⊤ : Subgroup A) ≤ normalizer (H : Set A) := le_normalizer_of_normal
  let τ : (⊤ : Subgroup A) →* MulAut E := ρ.comp (π.comp (⊤ : Subgroup A).subtype)
  have hformula (a : A) (h : H) :
      ρ (π a) (q h) = q ⟨a * (h : A) * a⁻¹,
        (inferInstance : H.Normal).conj_mem h h.property a⟩ :=
    headAction_apply H N Q π hπ hker a h
  have hτ (a : (⊤ : Subgroup A)) (h : H) :
      τ a (q h) = q ⟨(a : A) * (h : A) * (a : A)⁻¹,
        (mem_normalizer_iff.mp (hHN a.property) h).mp h.property⟩ := hformula a h
  have hrange : ((⊤ : Subgroup A).subgroupOf ⊤).map τ = ρ.range := by
    apply le_antisymm
    · rintro _ ⟨a, _, rfl⟩
      exact ⟨π a, rfl⟩
    · rintro _ ⟨g, rfl⟩
      obtain ⟨a, rfl⟩ := hπ g
      exact ⟨⟨a, mem_top a⟩, mem_top _, rfl⟩
  have hD : D = (C.subgroupOf H).map q := by
    change commutatorAction ρ.range E = _
    rw [← hrange]
    exact quotient_conjugation_commutatorAction_eq_image ⊤ H B ⊤ hHN le_rfl
      inferInstance τ hτ
  have hW : (D.comap q).map H.subtype = W := by
    rw [hD, comap_map_eq, Subgroup.map_sup,
      show q.ker = B.subgroupOf H from QuotientGroup.ker_mk' _]
    change (C.subgroupOf H).map H.subtype ⊔
      (B.subgroupOf H).map H.subtype = B ⊔ C
    rw [subgroupOf_map_subtype, subgroupOf_map_subtype,
      inf_eq_left.mpr hCH, inf_eq_left.mpr hBH, sup_comm]
  have hF : (F.comap q).map H.subtype = centralizerModulo H ⊤ B := by
    ext x
    constructor
    · rintro ⟨h, hh, rfl⟩
      apply mem_centralizerModulo_iff.mpr
      refine ⟨h.property, ?_⟩
      intro a _
      have hfix : ρ (π a) (q h) = q h := hh ⟨ρ (π a), π a, rfl⟩
      rw [hformula] at hfix
      have hc := QuotientGroup.eq_iff_div_mem.mp hfix
      change a * (h : A) * a⁻¹ / (h : A) ∈ B at hc
      simpa only [commutatorElement_def, div_eq_mul_inv, coe_subtype] using hc
    · intro hx
      obtain ⟨hxH, hx⟩ := mem_centralizerModulo_iff.mp hx
      refine ⟨⟨x, hxH⟩, ?_, rfl⟩
      intro g
      obtain ⟨t, ht⟩ := g.property
      obtain ⟨a, rfl⟩ := hπ t
      change g.val (q ⟨x, hxH⟩) = q ⟨x, hxH⟩
      rw [← ht, hformula]
      apply QuotientGroup.eq_iff_div_mem.mpr
      change a * x * a⁻¹ / x ∈ B
      simpa only [commutatorElement_def, div_eq_mul_inv] using hx a (mem_top a)
  have hsup : W ⊔ centralizerModulo H ⊤ B = H := by
    have hh := congrArg (fun T : Subgroup E => (T.comap q).map H.subtype) s.decomposition
    change ((D ⊔ F).comap q).map H.subtype = _ at hh
    rw [← comap_sup_eq q D F (QuotientGroup.mk'_surjective _), Subgroup.map_sup, hW, hF,
      comap_top, ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh
  have hinf : W ⊓ centralizerModulo H ⊤ B = B := by
    have hh := congrArg (fun T : Subgroup E => (T.comap q).map H.subtype) s.disjoint.eq_bot
    change ((D ⊓ F).comap q).map H.subtype = _ at hh
    rw [comap_inf, map_inf _ _ _ Subtype.val_injective, hW, hF] at hh
    rw [MonoidHom.comap_bot, show q.ker = B.subgroupOf H from QuotientGroup.ker_mk' _] at hh
    simpa only [subgroupOf_map_subtype, inf_eq_left.mpr hBH] using hh
  have hmem (h : H) : q h ∈ D ↔ (h : A) ∈ W := by
    constructor
    · intro hh
      rw [← hW]
      exact ⟨h, hh, rfl⟩
    · intro hh
      rw [← hW] at hh
      obtain ⟨z, hz, heq⟩ := hh
      exact (Subtype.ext heq : z = h) ▸ hz
  let f : W →* D := (q.comp (inclusion hWH)).codRestrict D
    (fun w => (hmem (inclusion hWH w)).mpr w.property)
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective (B.subgroupOf H) z.val
    have hw : (h : A) ∈ W := (hmem h).mp (hh ▸ z.property)
    refine ⟨⟨h, hw⟩, ?_⟩
    exact Subtype.ext hh
  have hcoords : (s.coordinates.toMonoidHom.comp f).ker = B.subgroupOf W := by
    ext w
    change s.coordinates (f w) = 1 ↔ (w : A) ∈ B
    rw [s.coordinates.map_eq_one_iff]
    constructor
    · intro hw
      have hh : q (inclusion hWH w) = 1 := congrArg Subtype.val hw
      exact (QuotientGroup.eq_one_iff (N := B.subgroupOf H) (inclusion hWH w)).mp hh
    · intro hw
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (N := B.subgroupOf H) (inclusion hWH w)).mpr hw
  have hnatural : Nonempty (RankOnePairing.NaturalFactor π ⊤ W B) := by
    refine ⟨{
      marking := s.marking
      coordinates := s.coordinates.toMonoidHom.comp f
      surjective := s.coordinates.surjective.comp hsurj
      kernel := hcoords
      normalized := by rw [normalizer_eq_top]
      action := ?_ }⟩
    intro a _ x y hy
    apply s.action (π a) (f x) (f y)
    change q (inclusion hWH y) = ρ (π a) (q (inclusion hWH x))
    rw [hformula]
    congr 1
    exact Subtype.ext hy
  exact ⟨{
    projection_surjective := hπ
    projection_kernel := hker
    kernel_le := hNH
    normal_group := inferInstance
    normal_kernel := inferInstance
    elementary := hE
    radical_normal := inferInstance
    triple_le := htriple
    decomposition := hsup.symm
    intersection := hinf
    natural := hnatural.some }⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Splitting
