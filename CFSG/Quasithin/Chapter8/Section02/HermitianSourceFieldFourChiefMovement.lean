module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourChiefNatural
public import Theory.Representation.BinaryConjugationSection.InvariantImages
public import Theory.Representation.HomogeneousNormalizerSeed
public import Theory.Representation.TensorInvolutionDisplacement
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The natural moved space and homogeneous original chief section

The surviving B₀/U embeds in the actual chief quotient with its original
SL₂(4) coordinates. Its binary irreducibility identifies every nonzero
commuting displacement confined to this image with the entire image. Thus
the marked involution moves exactly four binary dimensions and the chief
section has dimension at least eight.

Commuting pair generators preserve the natural type, while the original
Sylow subgroup preserves the actual seed. Clifford theory therefore gives
coordinates on the whole chief section as repeated copies of this natural
module. The field remains the original four-element field. The companion
Chapter12 theorem supplies all inputs on the same selected pair and section.

Source: Aschbacher–Smith 8.2.9, printed p.721, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree
open scoped IsMulCommutative commutatorElement MatrixGroups MonoidAlgebra Matrix
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open Normalizer.SmallOvergroups
variable {G : Type*} [Group G]
set_option backward.isDefEq.respectTransparency false

variable {J N Z R B U : Subgroup G}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) J W}

/-- The literal image of a normalized subgroup in a binary section. -/
@[expose] def sectionImage (c : BinaryConjugationSection J N Z ρ)
    (hRJ : R ≤ J) (hRB : R ≤ normalizer (B : Set G)) :
    Subrepresentation (ρ.comp (inclusion hRJ)) where
  toSubmodule := c.imageSpace B
  apply_mem_toSubmodule r w hw := c.imageSpace_apply_mem B (inclusion hRJ r)
    (hRB r.property) w hw

/-- The original B₀/U coordinates descend to its exact image in the section. -/
theorem NaturalSectionAction.image_coordinates
    (h : NaturalSectionAction R B U) (c : BinaryConjugationSection J N Z ρ)
    (hRJ : R ≤ J) (hBN : B ≤ N) (hBZ : B ⊓ Z = U) :
    ∃ eR : (R ⧸ pCore 2 R) ≃* SL(2,E 1),
      ∃ e : (sectionImage c hRJ h.choose).toSubmodule ≃ₗ[ZMod 2] (Fin 2 → E 1),
        ∀ r w, e ((sectionImage c hRJ h.choose).toRepresentation r w) =
          (eR (QuotientGroup.mk' (pCore 2 R) r)).val *ᵥ (e w) := by
  obtain ⟨hRB,hRU,hBU,eB,eR,he⟩ := h
  let := hBU
  let S := sectionImage c hRJ hRB
  let f : B →* Multiplicative S.toSubmodule := {
    toFun b := Multiplicative.ofAdd ⟨(c.coordinates (inclusion hBN b)).toAdd,
      (c.mem_imageSpace_iff B _).mpr ⟨inclusion hBN b,b.property,rfl⟩⟩
    map_one' := by apply Subtype.ext; exact c.coordinates.map_one
    map_mul' b a := by
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd (c.coordinates.map_mul (inclusion hBN b) (inclusion hBN a)) }
  have hf : Function.Surjective f := by
    intro w
    obtain ⟨b,hb,he⟩ := (c.mem_imageSpace_iff B _).mp w.toAdd.property
    exact ⟨⟨b,hb⟩,Subtype.ext he⟩
  have hk : f.ker = U.subgroupOf B := by
    ext b
    change f b = 1 ↔ (b : G) ∈ U
    rw [Subtype.ext_iff]
    change c.coordinates (inclusion hBN b) = 1 ↔ _
    rw [c.coordinates_eq_one_iff,←hBZ]
    exact ⟨fun hz => ⟨b.property,hz⟩,fun hb => hb.2⟩
  let a : (B ⧸ U.subgroupOf B) ≃* Multiplicative S.toSubmodule :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  let b := a.symm.trans eB
  let e : S.toSubmodule ≃ₗ[ZMod 2] (Fin 2 → E 1) :=
    LinearEquiv.ofBijective ((AddMonoidHom.toMultiplicative.symm b.toMonoidHom).toZModLinearMap 2)
      b.bijective
  have hef (x : B) : e (f x).toAdd = (eB (QuotientGroup.mk' (U.subgroupOf B) x)).toAdd := by
    change eB (a.symm (a (QuotientGroup.mk' (U.subgroupOf B) x))) = _
    rw [a.symm_apply_apply]
    rfl
  refine ⟨eR,e,?_⟩
  intro r w
  obtain ⟨x,hx⟩ := hf (Multiplicative.ofAdd w)
  have hw : (f x).toAdd = w := hx
  rw [←hw]
  let y : B := B.normalizerMonoidHom (inclusion hRB r) x
  have hy : S.toRepresentation r (f x).toAdd = (f y).toAdd := by
    apply Subtype.ext
    exact (c.equivariant (inclusion hRJ r) (inclusion hBN x)).symm
  rw [hy,hef,hef]
  exact congrArg Multiplicative.toAdd (he r (QuotientGroup.mk' (U.subgroupOf B) x))

/-- The surviving natural image is irreducible of binary dimension four. -/
theorem NaturalSectionAction.image_irreducible
    (h : NaturalSectionAction R B U) (c : BinaryConjugationSection J N Z ρ)
    (hRJ : R ≤ J) (hBN : B ≤ N) (hBZ : B ⊓ Z = U) :
    IsIrreducible (sectionImage c hRJ h.choose).toRepresentation ∧
      Module.finrank (ZMod 2) (sectionImage c hRJ h.choose).toSubmodule = 4 := by
  obtain ⟨eR,e,he⟩ := h.image_coordinates c hRJ hBN hBZ
  let S := sectionImage c hRJ h.choose
  have hn : Nontrivial S.toSubmodule := e.toEquiv.nontrivial
  have hirr : IsIrreducible S.toRepresentation := by
    refine { exists_pair_ne := ⟨⊥,⊤,bot_ne_top⟩, eq_bot_or_eq_top := ?_ }
    intro D
    by_cases hd : D = ⊥
    · exact Or.inl hd
    right
    apply top_unique
    intro w _
    by_cases hw : w = 0
    · rw [hw]; exact D.toSubmodule.zero_mem
    have hd' : D.toSubmodule ≠ ⊥ := fun hh => hd (Subrepresentation.toSubmodule_injective hh)
    obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hd'
    obtain ⟨g,hg⟩ := Matrix.SL2.exists_mulVec_eq (E 1) (e v) (e w)
      (fun hh => hv0 (e.map_eq_zero_iff.mp hh)) (fun hh => hw (e.map_eq_zero_iff.mp hh))
    obtain ⟨r,hr⟩ := (eR.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 R))) g
    change eR (QuotientGroup.mk' (pCore 2 R) r) = g at hr
    have hrv : S.toRepresentation r v = w := by
      apply e.injective
      rw [he,hr,hg]
    exact hrv ▸ D.apply_mem_toSubmodule r hv
  refine ⟨hirr,?_⟩
  have hdE : Module.finrank (ZMod 2) (E 1) = 2 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E 1)
    rw [card_E,Nat.card_zmod] at hh
    exact hh.symm
  rw [e.finrank_eq,Module.finrank_pi_fintype]
  simp only [hdE,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]

/-- A nonzero commuting displacement confined to B₀/U fills that natural image. -/
theorem NaturalSectionAction.moved_space
    (h : NaturalSectionAction R B U) (c : BinaryConjugationSection J N Z ρ)
    (hRJ : R ≤ J) (hBN : B ≤ N) (hBZ : B ⊓ Z = U)
    (v : J) (hne : ρ v ≠ 1)
    (hcomm : ∀ r : R, Commute (ρ v) (ρ (inclusion hRJ r)))
    (hmove : ∀ x : N, ⁅(v : G),(x : G)⁆ ∈ B) :
    LinearMap.range (ρ v - 1) = c.imageSpace B ∧
      Module.finrank (ZMod 2) (LinearMap.range (ρ v - 1)) = 4 := by
  let S := sectionImage c hRJ h.choose
  obtain ⟨hirr,hdim⟩ := h.image_irreducible c hRJ hBN hBZ
  let D : Subrepresentation (ρ.comp (inclusion hRJ)) := {
    toSubmodule := LinearMap.range (ρ v-1)
    apply_mem_toSubmodule r w hw := by
      obtain ⟨x,rfl⟩ := hw
      refine ⟨ρ (inclusion hRJ r) x,?_⟩
      change ρ v (ρ (inclusion hRJ r) x) - ρ (inclusion hRJ r) x =
        ρ (inclusion hRJ r) (ρ v x-x)
      rw [map_sub]
      exact congrArg (fun z => z - ρ (inclusion hRJ r) x)
        (LinearMap.congr_fun (hcomm r).eq x) }
  have hDS : D ≤ S := by
    rintro _ ⟨x,rfl⟩
    obtain ⟨a,ha⟩ := c.onto (Multiplicative.ofAdd x)
    let b : N := N.normalizerMonoidHom (inclusion c.normalized v) a
    refine (c.mem_imageSpace_iff B _).mpr ⟨b*a⁻¹,hmove a,?_⟩
    rw [map_mul,map_inv]
    simp only [toAdd_mul,toAdd_inv,←sub_eq_add_neg]
    change (c.coordinates b).toAdd - (c.coordinates a).toAdd = ρ v x-x
    have hb : (c.coordinates b).toAdd = ρ v (c.coordinates a).toAdd := c.equivariant v a
    rw [hb,ha]
    rfl
  have hDne : D ≠ ⊥ := by
    intro hd
    apply hne
    apply sub_eq_zero.mp
    apply LinearMap.range_eq_bot.mp
    exact congrArg Subrepresentation.toSubmodule hd
  have he : D = S := by
    exact not_ne_iff.mp (fun hne => hDne
      (((Subrepresentation.irreducible_iff_isAtom S).mp hirr).ne_iff_eq_bot hDS |>.mp hne))
  have hr : LinearMap.range (ρ v-1) = c.imageSpace B :=
    congrArg Subrepresentation.toSubmodule he
  exact ⟨hr,hr.symm ▸ hdim⟩

/-- The local kernel on U controls commutation on any section killing O₂(R). -/
theorem section_images_commute_of_fixed_kernel
    {A : Subgroup G} (hAJ : A ≤ J) (hRJ : R ≤ J)
    (hAR : A ≤ normalizer (R : Set G)) (hRU : R ≤ normalizer (U : Set G))
    (hAU : A ≤ centralizer (U : Set G))
    (hker : R ⊓ centralizer (U : Set G) = R.pCoreIn 2)
    (hkill : (R.pCoreIn 2).subgroupOf J ≤ ρ.ker) :
    ∀ (a : A) (r : R), Commute (ρ (inclusion hAJ a)) (ρ (inclusion hRJ r)) := by
  have hC : ⁅R,A⁆ ≤ R.pCoreIn 2 := by
    rw [←hker]
    exact le_inf (le_normalizer_iff_commutator_le_left.mp hAR)
      ((commutator_mono le_rfl hAU).trans
        (le_normalizer_iff_commutator_le_right.mp
          (hRU.trans (normalizer_le_normalizer_centralizer U))))
  intro a r
  have hc : Commute (ρ.asGroupHom (inclusion hAJ a)) (ρ.asGroupHom (inclusion hRJ r)) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    apply Units.ext
    change ρ ⁅inclusion hAJ a,inclusion hRJ r⁆ = 1
    apply hkill
    rw [commutator_comm] at hC
    exact hC (commutator_mem_commutator a.property r.property)
  exact congrArg Units.val hc.eq

/-- The natural moved image forces at least eight binary dimensions. -/
theorem NaturalSectionAction.moved_dimension [FiniteDimensional (ZMod 2) W]
    (h : NaturalSectionAction R B U) (c : BinaryConjugationSection J N Z ρ)
    (hRJ : R ≤ J) (hBN : B ≤ N) (hBZ : B ⊓ Z = U)
    (v : J) (hv : v^2 = 1) (hne : ρ v ≠ 1)
    (hcomm : ∀ r : R, Commute (ρ v) (ρ (inclusion hRJ r)))
    (hmove : ∀ x : N, ⁅(v : G),(x : G)⁆ ∈ B) :
    8 ≤ Module.finrank (ZMod 2) W := by
  have hm := (h.moved_space c hRJ hBN hBZ v hne hcomm hmove).2
  have hh := TensorInvolutionDisplacement.twice_displacement_le (ρ v)
    (by rw [←map_mul,←pow_two,hv,map_one])
  change 2 * Module.finrank (ZMod 2) (LinearMap.range (ρ v-1)) ≤ _ at hh
  rw [hm] at hh
  exact hh

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] {J N Z R B U C P : Subgroup G}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) J W} [ρ.IsIrreducible]
set_option backward.isDefEq.respectTransparency false

/-- Clifford homogeneity on the original natural seed, including the normalizing supplement. -/
theorem NaturalSectionAction.homogeneous_coordinates
    (h : NaturalSectionAction R B U) (c : BinaryConjugationSection J N Z ρ)
    (hRJ : R ≤ J) (hCJ : C ≤ J) (hPJ : P ≤ J)
    (hJR : J ≤ normalizer (R : Set G)) (hgen : (R ⊔ C) ⊔ P = J)
    (hBN : B ≤ N) (hBZ : B ⊓ Z = U)
    (hC : ∀ c : C, ∀ r : R, Commute (ρ (inclusion hCJ c)) (ρ (inclusion hRJ r)))
    (hP : P ≤ normalizer (B : Set G)) :
    ∃ m : ℕ, ∃ eR : (R ⧸ pCore 2 R) ≃* SL(2,E 1),
      ∃ e : W ≃ₗ[ZMod 2] (Fin m → (Fin 2 → E 1)),
        (∀ r w, e (ρ (inclusion hRJ r) w) =
          fun i => (eR (QuotientGroup.mk' (pCore 2 R) r)).val *ᵥ (e w i)) ∧
        Module.finrank (ZMod 2) W = m*4 := by
  let R₀ := R.subgroupOf J
  let C₀ := C.subgroupOf J
  let P₀ := P.subgroupOf J
  let : R₀.Normal := normal_subgroupOf_of_le_normalizer hJR
  let S := sectionImage c hRJ h.choose
  let S₀ : Subrepresentation (ρ.comp R₀.subtype) := {
    toSubmodule := S.toSubmodule
    apply_mem_toSubmodule r w hw := S.apply_mem_toSubmodule ⟨r,r.property⟩ hw }
  have hS := (h.image_irreducible c hRJ hBN hBZ).1
  have hS₀ : S₀.toRepresentation.IsIrreducible :=
    (irreducible_comp_surjective_iff (subgroupOfEquivOfLe hRJ).toMonoidHom
      (subgroupOfEquivOfLe hRJ).surjective S.toRepresentation).mpr hS
  have hgen₀ : (R₀ ⊔ C₀) ⊔ P₀ = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,Subgroup.map_sup,map_subgroupOf_eq_of_le hRJ,
      map_subgroupOf_eq_of_le hCJ,map_subgroupOf_eq_of_le hPJ,hgen,
      ←MonoidHom.range_eq_map,range_subtype]
  have hC₀ : ∀ c ∈ C₀, ∀ r : R₀, Commute (ρ c) (ρ r) := by
    intro a ha r
    exact hC ⟨a,ha⟩ ⟨r,r.property⟩
  have hP₀ : ∀ p ∈ P₀, S₀.toSubmodule.map (ρ p) = S₀.toSubmodule := by
    intro p hp
    apply le_antisymm
    · rintro _ ⟨w,hw,rfl⟩
      exact c.imageSpace_apply_mem B p (hP hp) w hw
    · intro w hw
      refine ⟨ρ p⁻¹ w,c.imageSpace_apply_mem B p⁻¹ (hP (P.inv_mem hp)) w hw,?_⟩
      exact ρ.self_inv_apply p w
  obtain ⟨m,a,ha⟩ := Representation.homogeneous_coordinates_of_commuting_and_stable
    ρ R₀ C₀ P₀ hgen₀ S₀ hS₀ hC₀ hP₀
  obtain ⟨eR,b,hb⟩ := h.image_coordinates c hRJ hBN hBZ
  let e : W ≃ₗ[ZMod 2] (Fin m → (Fin 2 → E 1)) :=
    a.trans (LinearEquiv.piCongrRight fun _ => b)
  refine ⟨m,eR,e,?_,?_⟩
  · intro r w
    have hh := ha (⟨inclusion hRJ r,r.property⟩ : R₀) w
    change a (ρ (inclusion hRJ r) w) = _ at hh
    funext i
    change b (a (ρ (inclusion hRJ r) w) i) = _
    rw [hh]
    exact hb r (a w i)
  · have hd : Module.finrank (ZMod 2) S.toSubmodule = 4 := (h.image_irreducible c hRJ hBN hBZ).2
    rw [a.finrank_eq,Module.finrank_pi_fintype]
    change (∑ _ : Fin m, Module.finrank (ZMod 2) S.toSubmodule) = m*4
    simp only [hd,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
