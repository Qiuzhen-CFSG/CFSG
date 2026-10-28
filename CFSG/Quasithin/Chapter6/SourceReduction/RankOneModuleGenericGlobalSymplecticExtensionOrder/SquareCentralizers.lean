module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder
public import Theory.SpecificGroups.SymplecticFour.SuzukiBorelPlacement

/-!
# Nonroot square centralizers in both full source normalizers

A nonidentity square of the native symplectic Sylow has that exact Sylow
as its full centralizer. The compatible pure amalgam identifies the source
Sylow with the native Sylow on both endpoints. Thus its centralizer inside
each pure source parabolic is precisely the original S.

The actual products Mᵢ = Lᵢ D then determine the centralizer in each full
normalizer. If x = l b centralizes a square z, with b in D = N_G(S), then
l carries the square zᵇ back to z. Their pure parabolic centralizers are
both S, so l normalizes S and x lies in the whole middle D. Consequently
C_G(z) ∩ Mᵢ = C_G(z) ∩ D, including every outer centralizer element.

This proves the last local step of Aschbacher–Smith F.4.39, printed p.294
of `refs/quasithin.pdf`, on the prepared pair of 5.3.1–3, pp.658–659.
It does not prove C_G(z) ≤ Mᵢ: the preceding global argument still requires
ambient fusion and the elimination of the even outer part. The native
centralizer calculation is reused from `SuzukiBorelPlacement`; its general
square theorem has no Suzuki hypothesis. Both pure orientations are included.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem square_centralizer_transport
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {S P : Subgroup G} (hSP : S ≤ P)
    (f : P →* Sp F) (hf : Function.Injective f)
    (hSU : (S.subgroupOf P).map f = unipotent)
    (z : S) (hz : z ≠ 1) (hsq : ∃ y : S, y^2=z) :
    centralizer ({z.val} : Set G) ⊓ P = S := by
  let zP : P := ⟨z.val,hSP z.property⟩
  obtain ⟨y,hy⟩ := hsq
  let yP : P := ⟨y.val,hSP y.property⟩
  have hyU : f yP ∈ unipotent := hSU ▸ mem_map_of_mem f y.property
  let u : unipotent (F := F) := ⟨f yP,hyU⟩
  have he : (u.val)^2 = f zP := by
    rw [←map_pow]
    exact congrArg f (show yP^2=zP from Subtype.ext (congrArg (fun v : S => v.val) hy))
  have hu : u^2 ≠ 1 := by
    intro hu
    apply hz
    apply Subtype.ext
    have hh : f zP = 1 := he.symm.trans (congrArg Subtype.val hu)
    exact congrArg (fun v : P => v.val) (hf (hh.trans (map_one f).symm))
  have hc : centralizer ({f zP} : Set (Sp F)) = unipotent := by
    rw [←he]
    exact centralizer_square_eq_unipotent u hu
  ext x
  constructor
  · rintro ⟨hx,hxP⟩
    have hxU : f ⟨x,hxP⟩ ∈ unipotent := by
      rw [←hc,mem_centralizer_singleton_iff]
      rw [←map_mul,←map_mul]
      exact congrArg f (show (⟨x,hxP⟩ : P)*zP=zP*⟨x,hxP⟩ from
        Subtype.ext (mem_centralizer_singleton_iff.mp hx))
    obtain ⟨a,ha,heq⟩ := hSU.symm ▸ hxU
    have heq' : a.val=x := congrArg (fun v : P => v.val) (hf heq)
    exact heq' ▸ ha
  · intro hxS
    refine ⟨mem_centralizer_singleton_iff.mpr ?_,hSP hxS⟩
    have hxU : f ⟨x,hSP hxS⟩ ∈ unipotent := hSU ▸ mem_map_of_mem f hxS
    rw [←hc,mem_centralizer_singleton_iff] at hxU
    have hh : (⟨x,hSP hxS⟩ : P)*zP=zP*⟨x,hSP hxS⟩ :=
      hf (by simpa only [map_mul] using hxU)
    exact congrArg (fun v : P => v.val) hh

private theorem square_pair_transport
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hF : Nat.card F = 2^m) (hm : 0 < m)
    {P Q C S : Subgroup G} (hCP : C ≤ P) (hCQ : C ≤ Q) (hSC : S ≤ C)
    (hs : Chapter1.IsSylowIn 2 S C)
    (e : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P C Q hCP hCQ)
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) :
    ∀ z : S, z ≠ 1 → (∃ y : S, y^2=z) →
      centralizer ({z.val} : Set G) ⊓ P = S ∧
      centralizer ({z.val} : Set G) ⊓ Q = S := by
  obtain ⟨R,hR⟩ := hs
  have hRS : (R : Subgroup C) = S.subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [hR,map_subgroupOf_eq_of_le hSC]
  let U := (unipotentSylow hF hm).subtype unipotent_le_borel
  let : (U : Subgroup (borel (F := F))).Normal := unipotent_normal_in_borel
  let := Sylow.unique_of_normal U (inferInstance : U.Normal)
  have hSU : (S.subgroupOf C).map e.middle.toMonoidHom = unipotent.subgroupOf borel := by
    rw [←hRS]
    exact congrArg Sylow.toSubgroup (Subsingleton.elim
      (R.mapSurjective (f := e.middle.toMonoidHom) e.middle.surjective) U)
  have hU : (S.subgroupOf C).map (borel.subtype.comp e.middle.toMonoidHom) = unipotent := by
    rw [←map_map,hSU,map_subgroupOf_eq_of_le unipotent_le_borel]
  have hl : (S.subgroupOf P).map (pointParabolic.subtype.comp e.left.toMonoidHom) = unipotent := by
    rw [←hU]
    ext x
    constructor
    · rintro ⟨s,hs,rfl⟩
      refine ⟨⟨s.val,hSC hs⟩,hs,?_⟩
      exact (congrArg Subtype.val (e.left_commutes ⟨s.val,hSC hs⟩)).symm
    · rintro ⟨s,hs,rfl⟩
      refine ⟨⟨s.val,hCP s.property⟩,hs,?_⟩
      exact congrArg Subtype.val (e.left_commutes s)
  have hr : (S.subgroupOf Q).map (planeParabolic.subtype.comp e.right.toMonoidHom) = unipotent := by
    rw [←hU]
    ext x
    constructor
    · rintro ⟨s,hs,rfl⟩
      refine ⟨⟨s.val,hSC hs⟩,hs,?_⟩
      exact (congrArg Subtype.val (e.right_commutes ⟨s.val,hSC hs⟩)).symm
    · rintro ⟨s,hs,rfl⟩
      refine ⟨⟨s.val,hCQ s.property⟩,hs,?_⟩
      exact congrArg Subtype.val (e.right_commutes s)
  intro z hz hsq
  exact ⟨square_centralizer_transport (hSC.trans hCP) _
    (pointParabolic.subtype_injective.comp e.left.injective) hl z hz hsq,
    square_centralizer_transport (hSC.trans hCQ) _
    (planeParabolic.subtype_injective.comp e.right.injective) hr z hz hsq⟩

/-- In either pure source parabolic, the centralizer of a nonidentity
square of S is exactly S. The compatible middle fixes the same Sylow on
both endpoints, including when the amalgam comparison is reversed. -/
theorem Preparation.symplectic_square_parabolic_centralizers
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (i : Fin 2) (z : sourceS L H) (hz : z ≠ 1)
    (hsq : ∃ y : sourceS L H, y^2=z) :
    centralizer ({z.val} : Set G) ⊓
      ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i = sourceS L H := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let C := P 0 ⊓ P 1
  have hf := d.hypothesisF11 h hTH
  have hSC : sourceS L H ≤ C := le_inf (le_sup_right.trans le_sup_left)
    (le_sup_right.trans le_sup_left)
  have hs : Chapter1.IsSylowIn 2 (sourceS L H) C := by
    change Chapter1.IsSylowIn 2 (sourceS L H) (P 0 ⊓ P 1)
    rw [show P 0 ⊓ P 1 = ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) from
      ChapterF.Source.lemma_F_1_3_6 hf]
    exact hf.sylow_commonBorel
  have hc : centralizer ({z.val} : Set G) ⊓ P 0 = sourceS L H ∧
      centralizer ({z.val} : Set G) ⊓ P 1 = sourceS L H := by
    rcases he with he | he <;> obtain ⟨e⟩ := he
    · exact square_pair_transport hF hm inf_le_left inf_le_right hSC hs e z hz hsq
    · exact (square_pair_transport hF hm inf_le_right inf_le_left hSC hs e.reverse z hz hsq).symm
  fin_cases i
  · exact hc.1
  · exact hc.2

private theorem square_centralizer_product
    {S P L M D : Subgroup G} (hSP : S ≤ P) (hLP : L ≤ P)
    (hD : D = normalizer (S : Set G))
    (hprod : ∀ x ∈ M, ∃ l ∈ L, ∃ b ∈ D, x=l*b)
    (hc : ∀ z : S, z ≠ 1 → (∃ y : S, y^2=z) →
      centralizer ({z.val} : Set G) ⊓ P = S)
    (z : S) (hz : z ≠ 1) (hsq : ∃ y : S, y^2=z) :
    centralizer ({z.val} : Set G) ⊓ M ≤ D := by
  rintro x ⟨hxC,hxM⟩
  obtain ⟨l,hl,b,hb,rfl⟩ := hprod x hxM
  have hbN : b ∈ normalizer (S : Set G) := hD ▸ hb
  let a := S.normalizerMonoidHom ⟨b,hbN⟩
  let w := a z
  have hw : w ≠ 1 := a.map_ne_one_iff.mpr hz
  have hwsq : ∃ y : S, y^2=w := by
    obtain ⟨y,hy⟩ := hsq
    exact ⟨a y,by rw [←map_pow,hy]⟩
  have hlw : l*w.val*l⁻¹=z.val := by
    change l*(b*z.val*b⁻¹)*l⁻¹=z.val
    have he := mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hxC)
    simpa only [mul_inv_rev,mul_assoc] using he
  have hlN : l ∈ normalizer (S : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨s,hs,rfl⟩
      rw [←hc z hz hsq]
      refine ⟨mem_centralizer_singleton_iff.mpr ?_,
        P.mul_mem (P.mul_mem (hLP hl) (hSP hs)) (P.inv_mem (hLP hl))⟩
      have hsw := mem_centralizer_singleton_iff.mp
        ((hc w hw hwsq).symm ▸ hs : s ∈ centralizer ({w.val} : Set G) ⊓ P).1
      have he := congrArg (MulAut.conj l) hsw
      change l*s*l⁻¹ * z.val = z.val * (l*s*l⁻¹)
      simpa only [map_mul,MulAut.conj_apply,hlw] using he
    · rw [card_map_of_injective (MulAut.conj l).injective]
  rw [hD]
  exact (normalizer (S : Set G)).mul_mem hlN hbN

/-- The nonroot centralizer inside either full normalizer lies in the whole
intersection. This is the local final step of F.4.39; no outer extension or
ambient equality S = T is assumed. -/
theorem Preparation.symplectic_square_full_normalizer_centralizers
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (i : Fin 2) (z : sourceS L H) (hz : z ≠ 1)
    (hsq : ∃ y : sourceS L H, y^2=z) :
    centralizer ({z.val} : Set G) ⊓ normalizer (![L,residual H] i : Set G) =
      centralizer ({z.val} : Set G) ⊓
        (normalizer (L : Set G) ⊓ normalizer (residual H : Set G)) := by
  have hlocal := d.symplectic_normalizer_local_conditions h hH hp F hm hF he
  have hsL : sourceS L H ≤ L := (d.symplectic_sourceS_le_factors h hH.1.1.2 hp F hm hF he) 0
  have hs : sourceS L H = (T : Subgroup G) ⊓ L :=
    (inf_eq_left.mpr hsL).symm.trans d.left_intersection
  have hD : normalizer (L : Set G) ⊓ normalizer (residual H : Set G) =
      normalizer (sourceS L H : Set G) := by
    rw [hs]
    exact hlocal.normalizer_eq_middle.symm
  have hprod : ∀ x ∈ normalizer (![L,residual H] i : Set G),
      ∃ l ∈ ![L,residual H] i, ∃ b ∈ normalizer (L : Set G) ⊓ normalizer (residual H : Set G),
        x=l*b := by
    fin_cases i
    · exact hlocal.factor_left
    · exact hlocal.factor_right
  have hc := square_centralizer_product
    (show sourceS L H ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i from
      le_sup_right.trans le_sup_left)
    (show ![L,residual H] i ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i from
      le_sup_left.trans le_sup_left)
    hD hprod (d.symplectic_square_parabolic_centralizers h hH.1.1.2 F hm hF he i) z hz hsq
  apply le_antisymm (le_inf inf_le_left hc)
  apply inf_le_inf_left
  fin_cases i
  · exact inf_le_left
  · exact inf_le_right

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
