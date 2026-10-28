module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.TerminalRudvalis.Residual
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Inspection.CubicKernel
public import Theory.SpecificGroups.Rudvalis.TransitiveSixtyFourCentralizer
public import Theory.Representation.G2BinaryImageThompson
public import Theory.GroupTheory.ElementaryThompsonElementaryCore
public import Theory.GroupTheory.ThompsonNormalizerGrowth
public import Theory.AtlasPort.LinearGroups.G2.OrderChecks

/-!
# The full natural action in the terminal Rudvalis component

The actual residual fuses the nonidentity vectors. Ambient cubic exclusion
and the native quintic obstruction identify the full module centralizer.
The original natural coordinates then identify the elementary Thompson
subgroup of every containing residual subgroup. The larger native Sylow
forces strict module-normalizer growth. Its faithful ambient automizer
embeds in G₂(2), so this growth forces the full G₂(2) action and the point
stabilizer order 12288.

All maps use the given component marking and the whole original module.
No failure of residual uniqueness or pushing-up configuration is assumed.
Source: Aschbacher--Smith 4.4.3 case (c), p.623, referring to the Ru
calculation in 4.2.13, pp.611--612.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 ChapterE Stellmacher
open Chapter4.Section02.Unitary OriginalPlaneCentralizers Chapter12.Section02
open Atlas.G2.Natural.BinaryNormalizer
open scoped Pointwise IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The actual native residual and its full module centralizer. -/
theorem unitary_terminal_native_centralizer (s : Context T L V)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (J : Subgroup G) (j : J ≃* Rudvalis.Model)
    (hV : V ≤ J) (hR : oddActorResidual L A ≤ J) :
    let E := (V.subgroupOf J).map j.toMonoidHom
    let B := ((oddActorResidual L A).subgroupOf J).map j.toMonoidHom
    IsElementaryAbelian 2 E ∧ Nat.card E = 64 ∧ Nat.card B = 64 * 6048 ∧
      B.pCoreIn 2 = E ∧ E ≤ B ∧ B ≤ normalizer (E : Set Rudvalis.Model) ∧
      (∀ x ∈ E, ∀ y ∈ E, x ≠ 1 → y ≠ 1 → ∃ b ∈ B, b*x*b⁻¹ = y) ∧
      centralizer (E : Set Rudvalis.Model) = E := by
  let R := oddActorResidual L A
  let i : R →* Rudvalis.Model := j.toMonoidHom.comp (inclusion hR)
  have hi := j.injective.comp (inclusion_injective hR)
  let E := (V.subgroupOf J).map j.toMonoidHom
  let B := (R.subgroupOf J).map j.toMonoidHom
  have h12 := (unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient).toHypothesis1221
  have hVR : V ≤ R := (chosen_oddActorResidual_cover h12 s.chosen A hAN hcomm hodd hAV).2.2.1.trans
    (pCoreIn_le 2 R)
  have hsub : (V.subgroupOf R).map (inclusion hR) = V.subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le hV]
    exact map_subgroupOf_eq_of_le hVR
  have hE : (V.subgroupOf R).map i = E := by
    rw [show i = j.toMonoidHom.comp (inclusion hR) from rfl,←map_map,hsub]
  have hB : i.range = B := by
    ext x
    constructor
    · rintro ⟨r,rfl⟩
      exact ⟨inclusion hR r,r.property,rfl⟩
    · rintro ⟨r,hr,rfl⟩
      exact ⟨⟨r,hr⟩,rfl⟩
  obtain ⟨_,_,hel,hcard,hcore,hcardB,_⟩ :=
    unitary_original_terminal_rudvalis_residual s A hAN hcomm hodd hAV i hi
  rw [hE] at hel hcard hcore
  rw [hB] at hcore hcardB
  let : IsElementaryAbelian 2 E := hel
  have hEB : E ≤ B := map_mono (subgroupOf_mono J hVR)
  have hBE : B ≤ normalizer (E : Set Rudvalis.Model) := by
    rw [←hcore]
    exact B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  have ht : ∀ x ∈ E, ∀ y ∈ E, x ≠ 1 → y ≠ 1 → ∃ b ∈ B, b*x*b⁻¹ = y := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ hx1 hy1
    obtain ⟨r,hr,he⟩ := unitary_original_terminal_residual_fusion s A hAN hcomm hodd hAV
      x hx y hy
      (fun hh => hx1 ((congrArg j (Subtype.ext hh)).trans (map_one j)))
      (fun hh => hy1 ((congrArg j (Subtype.ext hh)).trans (map_one j)))
    let rJ : J := ⟨r,hR hr⟩
    refine ⟨j rJ,mem_map_of_mem j.toMonoidHom hr,?_⟩
    simpa only [map_mul,map_inv,MulEquiv.coe_toMonoidHom] using congrArg j (show rJ*x*rJ⁻¹ = y from Subtype.ext he)
  have hC (x : centralizer (E : Set Rudvalis.Model)) :
      (j.symm x : G) ∈ centralizer (V : Set G) := by
    intro v hv
    let vJ : J := ⟨v,hV hv⟩
    have he := x.property (j vJ) (mem_map_of_mem j.toMonoidHom hv)
    have he' : vJ*j.symm x = j.symm x*vJ := by
      apply j.injective
      simpa only [map_mul,j.apply_symm_apply] using he
    exact congrArg J.subtype he'
  let k : centralizer (E : Set Rudvalis.Model) →* centralizer (V : Set G) :=
    ((J.subtype.comp j.symm.toMonoidHom).comp (centralizer (E : Set Rudvalis.Model)).subtype).codRestrict _ hC
  have hk : Function.Injective k := by
    intro x y he
    have hh : (j.symm (x : Rudvalis.Model) : G) = (j.symm (y : Rudvalis.Model) : G) :=
      congrArg (fun w : centralizer (V : Set G) => (w : G)) he
    exact Subtype.ext (j.symm.injective (J.subtype_injective hh))
  have hthree : Nat.Coprime 3 (Nat.card (centralizer (E : Set Rudvalis.Model))) :=
    s.module_centralizer_coprime_three.of_dvd_right (card_dvd_of_injective k hk)
  exact ⟨hel,hcard,hcardB,hcore,hEB,hBE,ht,
    Rudvalis.transitive_sixtyFour_centralizer B E hEB hBE hcard hcardB hcore ht hthree⟩

/-- The original derived natural action identifies the residual Thompson subgroup. -/
theorem unitary_terminal_native_thompson (s : Context T L V)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (J : Subgroup G) (j : J ≃* Rudvalis.Model)
    (hV : V ≤ J) (hR : oddActorResidual L A ≤ J) :
    let E := (V.subgroupOf J).map j.toMonoidHom
    let B := ((oddActorResidual L A).subgroupOf J).map j.toMonoidHom
    ∀ P : Subgroup B, E.subgroupOf B ≤ P → elementaryAbelianMaxJ P = E.subgroupOf B := by
  let R := oddActorResidual L A
  let E := (V.subgroupOf J).map j.toMonoidHom
  let B := (R.subgroupOf J).map j.toMonoidHom
  change ∀ P : Subgroup B, E.subgroupOf B ≤ P → elementaryAbelianMaxJ P = E.subgroupOf B
  obtain ⟨hel,_,_,hcore,hEB,_,_,hcent⟩ :=
    unitary_terminal_native_centralizer s A hAN hcomm hodd hAV J j hV hR
  let : IsElementaryAbelian 2 E := hel
  have h12 := (unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient).toHypothesis1221
  have hVR : V ≤ R := (chosen_oddActorResidual_cover h12 s.chosen A hAN hcomm hodd hAV).2.2.1.trans
    (pCoreIn_le 2 R)
  have hRL : R ≤ L := (oddActorResidual_le L A).trans inf_le_left
  let U := V.subgroupOf R
  let : U.Normal := normal_subgroupOf_of_le_normalizer (hRL.trans s.chosen.normalizes)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hVR
  let i : R →* Rudvalis.Model := j.toMonoidHom.comp (inclusion hR)
  let t : R →* B := i.codRestrict _ (fun r => mem_map_of_mem j.toMonoidHom r.property)
  have ht : Function.Surjective t := by
    rintro ⟨x,y,hy,rfl⟩
    exact ⟨⟨y,hy⟩,rfl⟩
  have hti : Function.Injective t := by
    intro x y he
    exact (inclusion_injective hR) (j.injective (congrArg Subtype.val he))
  have hmap : U.map t = E.subgroupOf B := by
    ext x
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact mem_map_of_mem j.toMonoidHom hv
    · rintro ⟨v,hv,he⟩
      refine ⟨⟨v,hVR hv⟩,hv,?_⟩
      exact Subtype.ext he
  let n : R →* normalizer (V : Set G) := inclusion (hRL.trans s.chosen.normalizes)
  let a : R →* inducedAutomizer V L :=
    (V.normalizerMonoidHom.rangeRestrict.comp n).codRestrict _
      (fun r => mem_map_of_mem V.normalizerMonoidHom.rangeRestrict (hRL r.property))
  let q : R →* Full := Derived.subtype.comp (s.actor.toMonoidHom.comp a)
  let d : U ≃* V := subgroupOfEquivOfLe hVR
  let ed : Additive U ≃ₗ[ZMod 2] Additive V :=
    { d.toAdditive with map_smul' := ZMod.map_smul d.toAdditive }
  have he (x : R) (v : U) :
      (ed.trans s.coordinates) (Additive.ofMul (MulAut.conjNormal x v)) =
        Atlas.G2.Natural.action (ZMod 2) (q x) ((ed.trans s.coordinates) (Additive.ofMul v)) :=
    s.equivariant (a x) (ed (Additive.ofMul v))
  intro P hEP
  have hJ := image_thompson_centralizes U q (ed.trans s.coordinates) he
    (by rintro _ ⟨x,rfl⟩; exact (s.actor (a x)).property)
    t ht (by rw [(MonoidHom.ker_eq_bot_iff t).mpr hti]; exact bot_le)
    (hti.comp U.subtype_injective) P (hmap.symm ▸ hEP)
  rw [hmap] at hJ
  have hcentral : centralizer (E.subgroupOf B : Set B) ≤ E.subgroupOf B := by
    intro b hb
    apply hcent.le
    intro z hz
    exact congrArg B.subtype (hb ⟨z,hEB hz⟩ hz)
  let : IsElementaryAbelian 2 (E.subgroupOf B) := IsElementaryAbelian.subgroupOf hEB
  exact elementaryAbelianMaxJ_eq_of_elementary_overgroup P (E.subgroupOf B)
    (hJ.trans hcentral) hEP inferInstance


/-- The whole native module normalizer acts as the full natural G₂(2),
with the original six-space as kernel and the actual ambient coordinates. -/
theorem unitary_terminal_native_full_action (s : Context T L V)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (J : Subgroup G) (j : J ≃* Rudvalis.Model)
    (hV : V ≤ J) (hR : oddActorResidual L A ≤ J) :
    let E := (V.subgroupOf J).map j.toMonoidHom
    let N := normalizer (E : Set Rudvalis.Model)
    ∃ (a : N →* Full) (d : E ≃* V),
      Function.Surjective a ∧ a.ker = E.subgroupOf N ∧
      (∀ v : E, (d v : G) = (j.symm v : G)) ∧
      (∀ (x : N) (v : E),
        s.coordinates (Additive.ofMul (d (E.normalizerMonoidHom x v))) =
          Atlas.G2.Natural.action (ZMod 2) (a x) (s.coordinates (Additive.ofMul (d v)))) ∧
      Nat.card N = 64 * 12096 ∧
      ∀ z : E, z ≠ 1 →
        Nat.card ((centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)).subgroupOf N) = 12288 := by
  let R := oddActorResidual L A
  let E := (V.subgroupOf J).map j.toMonoidHom
  let B := (R.subgroupOf J).map j.toMonoidHom
  let N := normalizer (E : Set Rudvalis.Model)
  obtain ⟨hel,hE,hB,hcore,hEB,hBE,ht,hcent⟩ :=
    unitary_terminal_native_centralizer s A hAN hcomm hodd hAV J j hV hR
  change B.pCoreIn 2 = E at hcore
  change Nat.card E = 64 at hE
  change Nat.card B = 64 * 6048 at hB
  let : IsElementaryAbelian 2 E := hel
  let d : E ≃* V := (j.subgroupMap (V.subgroupOf J)).symm.trans (subgroupOfEquivOfLe hV)
  have hd (v : E) : (d v : G) = (j.symm v : G) := rfl
  have hNj : N = ((normalizer (V : Set G)).subgroupOf J).map j.toMonoidHom := by
    dsimp only [N,E]
    rw [←map_normalizer_eq_of_bijective _ j.bijective,←subgroupOf_normalizer_eq hV]
  have hn (x : N) : (j.symm x : G) ∈ normalizer (V : Set G) := by
    obtain ⟨w,hw,he⟩ := hNj.le x.property
    have heq : j.symm x = w := by rw [←he]; exact j.symm_apply_apply w
    rw [heq]
    exact hw
  let n : N →* normalizer (V : Set G) :=
    ((J.subtype.comp j.symm.toMonoidHom).comp N.subtype).codRestrict _ hn
  let b : N →* Automizer V := V.normalizerMonoidHom.rangeRestrict.comp n
  have hact (x : N) (v : E) :
      V.normalizerMonoidHom (n x) (d v) = d (E.normalizerMonoidHom x v) := by
    apply Subtype.ext
    change (j.symm (x : Rudvalis.Model) : G) * (j.symm (v : Rudvalis.Model) : G) *
      (j.symm (x : Rudvalis.Model) : G)⁻¹ =
        (j.symm ((x : Rudvalis.Model) * (v : Rudvalis.Model) * (x : Rudvalis.Model)⁻¹) : G)
    simp only [map_mul,map_inv]
    rfl
  let I := inducedAutomizer V L
  obtain ⟨_,hNL⟩ := unitary_original_module_normalizers s.hypothesis s.maximal
    s.quotient s.chosen s.structural
  let : (L.subgroupOf (normalizer (V : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer s.chosen.normalizes).mpr hNL
  let : I.Normal := Subgroup.Normal.map inferInstance V.normalizerMonoidHom.rangeRestrict
    V.normalizerMonoidHom.rangeRestrict_surjective
  obtain ⟨f,hf,_,he⟩ := ambient_embedding (automizerRepresentation V) I s.actor
    s.coordinates s.equivariant (automizerRepresentation_injective V)
  let a : N →* Full := f.comp b
  have hker : a.ker = E.subgroupOf N := by
    ext x
    change f (b x) = 1 ↔ (x : Rudvalis.Model) ∈ E
    rw [←map_one f,hf.eq_iff]
    have hb : b x = 1 ↔ E.normalizerMonoidHom x = 1 := by
      constructor
      · intro hx
        apply MulEquiv.ext
        intro v
        apply d.injective
        rw [←hact]
        have hh : V.normalizerMonoidHom (n x) = 1 := congrArg Subtype.val hx
        rw [hh]; rfl
      · intro hx
        apply Subtype.ext
        apply MulEquiv.ext
        intro w
        obtain ⟨v,rfl⟩ := d.surjective w
        change V.normalizerMonoidHom (n x) (d v) = d v
        rw [hact,hx]; rfl
    rw [hb]
    change x ∈ E.normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker]
    change (x : Rudvalis.Model) ∈ centralizer (E : Set Rudvalis.Model) ↔ _
    rw [hcent]
  have hkerCard : Nat.card a.ker = 64 := by
    rw [hker,Nat.card_congr (subgroupOfEquivOfLe E.le_normalizer).toEquiv,hE]
  have hcard : Nat.card N = 64 * Nat.card a.range := by
    have hh := a.ker.card_mul_index
    rw [index_ker,hkerCard] at hh
    exact hh.symm
  obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := B)
  have hES : E.subgroupOf B ≤ (S : Subgroup B) := by
    have hh : E ≤ (S : Subgroup B).map B.subtype := hcore ▸ B.pCoreIn_le_sylow S
    intro x hx
    obtain ⟨y,hy,he⟩ := hh hx
    exact B.subtype_injective he ▸ hy
  have hJ := unitary_terminal_native_thompson s A hAN hcomm hodd hAV J j hV hR
    (S : Subgroup B) hES
  have hJmap : (elementaryAbelianMaxJ (S : Subgroup B)).map B.subtype = E := by
    rw [hJ,map_subgroupOf_eq_of_le hEB]
  obtain ⟨P,hP⟩ := (S.isPGroup'.map B.subtype).exists_le_sylow
  have hproper : (S : Subgroup B).map B.subtype < (P : Subgroup Rudvalis.Model) := by
    apply lt_of_le_of_ne hP
    intro he
    have hd := card_dvd_of_le (map_subtype_le (S : Subgroup B))
    rw [he,Rudvalis.InvolutionCentralizers.sylow_card P,hB] at hd
    norm_num at hd
  have hlt := lt_normalizer_of_sylow_thompson B E hBE S hJmap P hproper
  have hdiv : Nat.card a.range ∣ 12096 := by
    have hh := a.range.card_subgroup_dvd_card
    rwa [Atlas.G2.OrderChecks.binary_order] at hh
  have hsize : Nat.card a.range = 12096 := by
    have hle := Nat.le_of_dvd (by decide : 0 < 12096) hdiv
    have hbig : 6048 < Nat.card a.range := by
      by_contra hn
      have heq : B = N := eq_of_le_of_card_ge hlt.le (by rw [hB,hcard]; omega)
      exact hlt.ne heq
    obtain ⟨m,hm⟩ := hdiv
    have hm0 : m ≠ 0 := by intro hh; rw [hh,mul_zero] at hm; omega
    have hm1 : m = 1 := by nlinarith
    simpa only [hm1,mul_one] using hm.symm
  have hsurj : Function.Surjective a := by
    apply MonoidHom.surjective_of_card_ker_le_div
    rw [hkerCard,hcard,hsize,Atlas.G2.OrderChecks.binary_order]
  have hN : Nat.card N = 64 * 12096 := by rw [hcard,hsize]
  refine ⟨a,d,hsurj,hker,hd,?_,hN,?_⟩
  · intro x v
    rw [←hact]
    exact he (b x) (Additive.ofMul (d v))
  · intro z hz
    have htN : ∀ x ∈ E, ∀ y ∈ E, x ≠ 1 → y ≠ 1 → ∃ b ∈ N, b*x*b⁻¹ = y := by
      intro x hx y hy hx1 hy1
      obtain ⟨b,hb,he⟩ := ht x hx y hy hx1 hy1
      exact ⟨b,hBE hb,he⟩
    have hh := Theory.GroupAction.centralizer_card_mul_pred_of_transitive N E le_rfl htN z hz
    rw [hE,hN] at hh
    change Nat.card ((centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)).subgroupOf N) = 12288
    omega

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
