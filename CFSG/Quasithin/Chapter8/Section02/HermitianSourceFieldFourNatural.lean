module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourSection
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.ResidualAction
public import Theory.Representation.HermitianTensorThree.PlaneSection.Natural
/-!
# Natural coordinates on the original Hermitian section B₀/U

The hyperplane and corner marking gives a surjective last-column homomorphism
on the original B₀, with kernel exactly U. Its first-isomorphism equivalence
therefore identifies the literal quotient B₀/U with F₄². The matrix calculation
in PlaneSection.Natural makes every residual action a natural determinant-one
transformation. The previously computed full kernel and residual quotient
show that all of SL₂(4) occurs. No abstract four-space is substituted for B₀/U.

The Chapter 12 consumer constructs this marking for its original selected
pair. This is the H.4.6(2) natural-module input to 8.2.8(4–5), printed
pp.382,718–719, refs/quasithin.pdf (1 March 2004 manuscript).
-/
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative commutatorElement MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic.Construction Normalizer.SmallOvergroups
public noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G]

/-- Natural SL₂(4) coordinates on the literal section, retaining its original
normalizers, full residual kernel, and quotient representatives. -/
@[expose] def NaturalSectionAction (R B U : Subgroup G) : Prop :=
  ∃ hRB : R ≤ normalizer (B : Set G),
    ∃ hRU : R ≤ normalizer (U : Set G),
      ∃ hBU : (U.subgroupOf B).Normal, letI := hBU
        ∃ eB : (B ⧸ U.subgroupOf B) ≃* Multiplicative (Fin 2 → E 1),
          ∃ eR : (R ⧸ pCore 2 R) ≃* SL(2,E 1),
            ∀ (r : R) (b : B ⧸ U.subgroupOf B),
              eB (sectionAction R B U hRB hRU r b) =
                Matrix.SL2.naturalAction (E 1) (eR (QuotientGroup.mk' (pCore 2 R) r)) (eB b)

/-- The source hyperplane and corner markings induce the natural action on
B/U. The section coordinates are the actual last-column map. -/
theorem field_four_section_natural
    (V L B U R : Subgroup G) [IsElementaryAbelian 2 V]
    (hBV : B ≤ V) (hRL : R ≤ L)
    (hLN : L ≤ normalizer (V : Set G))
    (hRB : R ≤ normalizer (B : Set G)) (hRU : R ≤ normalizer (U : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Space 1) (q : L →* binaryImage 1)
    (he : ∀ (l : L) v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) v) = (q l).val (e v))
    (hU : ∀ v : Additive V, (v.toMul : G) ∈ U ↔ e v ∈ PlaneSection.Corner)
    (hB : ∀ v : Additive V, (v.toMul : G) ∈ B ↔ (e v).val 2 2 = 0)
    (hker : ∀ r : R, (∀ b : B, ⁅(r : G),(b : G)⁆ ∈ U) ↔ r ∈ pCore 2 R)
    (hR : Nonempty ((R ⧸ pCore 2 R) ≃* SL(2,E 1))) :
    ∃ hBU : (U.subgroupOf B).Normal, letI := hBU
      ∃ eB : (B ⧸ U.subgroupOf B) ≃* Multiplicative (Fin 2 → E 1),
        (∀ b : B, eB (QuotientGroup.mk' (U.subgroupOf B) b) =
          Multiplicative.ofAdd (PlaneSection.column (e (Additive.ofMul ⟨b,hBV b.property⟩)))) ∧
        ∃ eR : (R ⧸ pCore 2 R) ≃* SL(2,E 1),
          ∀ (r : R) (b : B ⧸ U.subgroupOf B),
            eB (sectionAction R B U hRB hRU r b) =
              Matrix.SL2.naturalAction (E 1) (eR (QuotientGroup.mk' (pCore 2 R) r)) (eB b) := by
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le hBV
  let hBU : (U.subgroupOf B).Normal := inferInstance
  let := hBU
  let ι := (inclusion hBV).toAdditive.toZModLinearMap 2
  let p : B →* Multiplicative (Fin 2 → E 1) :=
    (PlaneSection.column.comp (e.toLinearMap.comp ι)).toAddMonoidHom.toMultiplicative
  have hp : Function.Surjective p := by
    intro v
    obtain ⟨X,hX,hc⟩ := PlaneSection.column_surjective v.toAdd
    let x := e.symm X
    have hx : (x.toMul : G) ∈ B := (hB x).mpr (by rw [e.apply_symm_apply]; exact hX)
    refine ⟨⟨x.toMul,hx⟩,?_⟩
    change PlaneSection.column (e x) = v.toAdd
    rw [e.apply_symm_apply]
    exact hc
  have hpk : p.ker = U.subgroupOf B := by
    ext b
    change PlaneSection.column (e (ι (Additive.ofMul b))) = 0 ↔ (b : G) ∈ U
    rw [PlaneSection.column_eq_zero_iff _ ((hB (ι (Additive.ofMul b))).mp b.property)]
    exact (hU _).symm
  let eB : (B ⧸ U.subgroupOf B) ≃* Multiplicative (Fin 2 → E 1) :=
    (QuotientGroup.quotientMulEquivOfEq hpk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective p hp)
  have heB (b : B) : eB (QuotientGroup.mk' (U.subgroupOf B) b) = p b := rfl
  let f := sectionAction R B U hRB hRU
  have lifts (r : R) : ∃ t : SL(2,E 1), ∀ b : B ⧸ U.subgroupOf B,
      eB (f r b) = Matrix.SL2.naturalAction (E 1) t (eB b) := by
    let l : L := inclusion hRL r
    obtain ⟨a,ha⟩ := (q l).property
    have hpres : ∀ X ∈ PlaneSection.Corner, binaryActionHom 1 a X ∈ PlaneSection.Corner := by
      intro X hX
      obtain ⟨v,rfl⟩ := e.surjective X
      have hu := (mem_normalizer_iff.mp (hRU r.property) _).mp ((hU v).mpr hX)
      have hh := (hU (automizerRepresentation V
        (V.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) v)).mp hu
      rw [he,←ha] at hh
      exact hh
    obtain ⟨t,ht⟩ := PlaneSection.column_action a hpres
    refine ⟨t,?_⟩
    intro b
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf B) b
    change p (B.normalizerMonoidHom (inclusion hRB r) b) =
      Matrix.SL2.naturalAction (E 1) t (p b)
    apply Multiplicative.toAdd.injective
    change PlaneSection.column (e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) (ι (Additive.ofMul b)))) = _
    rw [he,←ha]
    exact ht _ ((hB (ι (Additive.ofMul b))).mp b.property)
  choose t ht using lifts
  have unique (a d : SL(2,E 1))
      (h : ∀ b, Matrix.SL2.naturalAction (E 1) a (eB b) =
        Matrix.SL2.naturalAction (E 1) d (eB b)) : a = d := by
    apply Matrix.SL2.naturalAction_injective
    ext v : 1
    obtain ⟨b,rfl⟩ := eB.surjective v
    exact h b
  let φ : R →* SL(2,E 1) := {
    toFun := t
    map_one' := by
      apply unique
      intro b
      rw [←ht,map_one,map_one]
      rfl
    map_mul' := by
      intro r s
      apply unique
      intro b
      rw [←ht,map_mul,map_mul]
      change eB (f r (f s b)) = _
      rw [ht,ht]
      rfl }
  have hφ : φ.ker = pCore 2 R := by
    ext r
    rw [←hker r]
    change φ r = 1 ↔ _
    rw [←mem_sectionAction_ker R B U hRB hRU r]
    change φ r = 1 ↔ f r = 1
    constructor
    · intro hr
      ext b
      apply eB.injective
      rw [ht,show t r = 1 from hr,map_one]
      rfl
    · intro hr
      apply unique
      intro b
      change Matrix.SL2.naturalAction (E 1) (t r) (eB b) = _
      rw [←ht,hr,map_one]
      rfl
  let e0 := QuotientGroup.quotientMulEquivOfEq hφ.symm
  let φq := (QuotientGroup.kerLift φ).comp e0.toMonoidHom
  have hi : Function.Injective φq := (QuotientGroup.kerLift_injective φ).comp e0.injective
  have hs : Function.Bijective φq := (Nat.bijective_iff_injective_and_card φq).mpr
    ⟨hi,Nat.card_congr hR.some.toEquiv⟩
  let eR : (R ⧸ pCore 2 R) ≃* SL(2,E 1) := MulEquiv.ofBijective φq hs
  refine ⟨hBU,eB,heB,eR,?_⟩
  exact ht
end
end CFSG.Quasithin.Chapter8.Section02.HermitianSource
