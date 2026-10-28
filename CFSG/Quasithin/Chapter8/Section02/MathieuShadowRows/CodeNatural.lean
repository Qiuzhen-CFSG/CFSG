module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CodeSection
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.ResidualAction
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextetFactors

/-!
# The natural hexacode action on the original code section

Recovery on the even code hyperplane descends through the full four-space
kernel to the literal quotient B/U. It intertwines original conjugation with
the natural binary hexacode action. A covering of the native residual then
identifies the full action kernel as O₂(R), and R/O₂(R) as the genuine 3.A6.
The cubic center remains present in this action.

The Chapter12 application constructs all markings on its same selected pair.
Source: Aschbacher--Smith H.16.1(3) and 8.2.8(4--5), printed pp.402,718--719,
refs/quasithin.pdf. The imported native recovery uses the licensed ATLAS
Golay and hexacode construction; see LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open MathieuCode.SextetLayers.CoordinateTransport Atlas.Codes
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterE Normalizer.SmallOvergroups
variable {G : Type*} [Group G]

/-- The actual residual preserves the original even intersection. -/
theorem marked_code_even_normalizes
    (V B R : Subgroup G) [IsElementaryAbelian 2 V]
    (hBV : B ≤ V) (hRV : R ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Code) (S : Sextet)
    (r : R →* sextetStabilizer S)
    (he : ∀ (x : R) v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hRV x)) v) =
      codeRepresentation (r x).val (e v))
    (hB : ∀ v : Additive V, (v.toMul : G) ∈ B ↔
      e v ∈ NormalizedShadowRows.CodeSection.evenSpace S) :
    R ≤ normalizer (B : Set G) := by
  apply le_normalizer_iff.mpr
  intro x hx b hb
  let v : Additive V := Additive.ofMul ⟨b,hBV hb⟩
  have hc := NormalizedShadowRows.CodeSection.evenSpace_invariant S (r ⟨x,hx⟩)
    ((hB v).mp hb)
  rw [←he ⟨x,hx⟩ v] at hc
  exact (hB _).mpr hc

/-- Recovery gives natural coordinates on the literal B/U. -/
theorem marked_code_section_natural
    (V B U R : Subgroup G) [IsElementaryAbelian 2 V]
    (hBV : B ≤ V) (hRV : R ≤ normalizer (V : Set G))
    (hRB : R ≤ normalizer (B : Set G)) (hRU : R ≤ normalizer (U : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Code) (S : Sextet)
    (r : R →* sextetStabilizer S)
    (he : ∀ (x : R) v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hRV x)) v) =
      codeRepresentation (r x).val (e v))
    (hU : ∀ v : Additive V, (v.toMul : G) ∈ U ↔ e v ∈ CodeFlags.sextetCodeSpace S)
    (hB : ∀ v : Additive V, (v.toMul : G) ∈ B ↔ e v ∈ NormalizedShadowRows.CodeSection.evenSpace S) :
    ∃ hBU : (U.subgroupOf B).Normal, letI := hBU
      ∃ eB : (B ⧸ U.subgroupOf B) ≃* Multiplicative hexacode,
        (∀ b : B, eB (QuotientGroup.mk' (U.subgroupOf B) b) =
          Multiplicative.ofAdd (NormalizedShadowRows.CodeSection.recover S
            (e (Additive.ofMul ⟨b,hBV b.property⟩)))) ∧
        ∀ (x : R) (b : B ⧸ U.subgroupOf B),
          eB (sectionAction R B U hRB hRU x b) =
            Multiplicative.ofAdd (hexAction (nativeQuotient S (r x)) (eB b).toAdd) := by
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le hBV
  let hBU : (U.subgroupOf B).Normal := inferInstance
  let := hBU
  let ι := (inclusion hBV).toAdditive.toZModLinearMap 2
  let p : B →* Multiplicative hexacode :=
    ((NormalizedShadowRows.CodeSection.recover S).comp (e.toLinearMap.comp ι)).toAddMonoidHom.toMultiplicative
  have hp : Function.Surjective p := by
    intro h
    obtain ⟨w,hw,hr⟩ := NormalizedShadowRows.CodeSection.recover_surjective S h.toAdd
    let v := e.symm w
    have hv : (v.toMul : G) ∈ B := (hB v).mpr (by rw [e.apply_symm_apply]; exact hw)
    refine ⟨⟨v.toMul,hv⟩,?_⟩
    change NormalizedShadowRows.CodeSection.recover S (e v) = h.toAdd
    rw [e.apply_symm_apply]
    exact hr
  have hk : p.ker = U.subgroupOf B := by
    ext b
    change NormalizedShadowRows.CodeSection.recover S (e (ι (Additive.ofMul b))) = 0 ↔ (b : G) ∈ U
    rw [NormalizedShadowRows.CodeSection.recover_kernel S
      ((hB (ι (Additive.ofMul b))).mp b.property)]
    exact (hU _).symm
  let eB : (B ⧸ U.subgroupOf B) ≃* Multiplicative hexacode :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective p hp)
  refine ⟨hBU,eB,fun _ => rfl,?_⟩
  intro x b
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf B) b
  change p (B.normalizerMonoidHom (inclusion hRB x) b) =
    Multiplicative.ofAdd (hexAction (nativeQuotient S (r x)) (p b).toAdd)
  apply Multiplicative.toAdd.injective
  change NormalizedShadowRows.CodeSection.recover S (e (automizerRepresentation V
    (V.normalizerMonoidHom.rangeRestrict (inclusion hRV x)) (ι (Additive.ofMul b)))) = _
  rw [he]
  exact NormalizedShadowRows.CodeSection.recover_equivariant S (r x)
    ((hB (ι (Additive.ofMul b))).mp b.property)

/-- The natural action has its full original two-core kernel and quotient
3.A6, retaining the nontrivial cubic center. -/
theorem marked_code_section_residual
    (V B U R : Subgroup G) [IsElementaryAbelian 2 V]
    (hBV : B ≤ V) (hRV : R ≤ normalizer (V : Set G))
    (hRB : R ≤ normalizer (B : Set G)) (hRU : R ≤ normalizer (U : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Code) (S : Sextet)
    (r : R →* sextetStabilizer S)
    (he : ∀ (x : R) v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hRV x)) v) =
      codeRepresentation (r x).val (e v))
    (hU : ∀ v : Additive V, (v.toMul : G) ∈ U ↔ e v ∈ CodeFlags.sextetCodeSpace S)
    (hB : ∀ v : Additive V, (v.toMul : G) ∈ B ↔ e v ∈ NormalizedShadowRows.CodeSection.evenSpace S)
    (hrange : r.range = solvableResidual (sextetStabilizer S))
    (hrker : IsPGroup 2 r.ker)
    (hrcore : (pCore 2 R).map r = (nativeQuotient S).ker) :
    ∃ hBU : (U.subgroupOf B).Normal, letI := hBU
      ∃ eB : (B ⧸ U.subgroupOf B) ≃* Multiplicative hexacode,
        (∀ b : B, eB (QuotientGroup.mk' (U.subgroupOf B) b) =
          Multiplicative.ofAdd (NormalizedShadowRows.CodeSection.recover S
            (e (Additive.ofMul ⟨b,hBV b.property⟩)))) ∧
        ∃ eR : (R ⧸ pCore 2 R) ≃* HexEvenAutomorphisms,
          (∀ x : R, (eR (QuotientGroup.mk' (pCore 2 R) x)).val = nativeQuotient S (r x)) ∧
          (∀ (x : R) (b : B ⧸ U.subgroupOf B),
            eB (sectionAction R B U hRB hRU x b) =
              Multiplicative.ofAdd (hexAction
                (eR (QuotientGroup.mk' (pCore 2 R) x)).val (eB b).toAdd)) ∧
          (sectionAction R B U hRB hRU).ker = pCore 2 R := by
  obtain ⟨hBU,eB,heB,hequiv⟩ := marked_code_section_natural V B U R hBV hRV hRB hRU e S r he hU hB
  let := hBU
  obtain ⟨p,hp,hpval⟩ := Chapter7.NormalizedSource.MathieuSextet.marked_even_quotient S r hrange
  have hr0 : r.ker ≤ pCore 2 R := le_sSup ⟨inferInstance,hrker⟩
  have ht : ((nativeQuotient S).comp r).ker = pCore 2 R := by
    change ((nativeQuotient S).ker).comap r = _
    rw [←hrcore,Subgroup.comap_map_eq_self hr0]
  have hpk : p.ker = pCore 2 R := by
    rw [←ht]
    ext x
    change p x = 1 ↔ nativeQuotient S (r x) = 1
    exact ⟨fun hx => (hpval x).symm.trans (congrArg Subtype.val hx),
      fun hx => Subtype.ext ((hpval x).trans hx)⟩
  let eR : (R ⧸ pCore 2 R) ≃* HexEvenAutomorphisms :=
    (QuotientGroup.quotientMulEquivOfEq hpk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective p hp)
  have heR (x : R) : (eR (QuotientGroup.mk' (pCore 2 R) x)).val = nativeQuotient S (r x) := hpval x
  refine ⟨hBU,eB,heB,eR,heR,?_,?_⟩
  · intro x b
    rw [heR]
    exact hequiv x b
  · rw [←hpk]
    ext x
    change sectionAction R B U hRB hRU x = 1 ↔ p x = 1
    constructor
    · intro hx
      apply Subtype.ext
      apply hexAction_injective
      ext v : 1
      obtain ⟨b,hb⟩ := eB.surjective (Multiplicative.ofAdd v)
      have hh := hequiv x b
      rw [hx,hb,←hpval] at hh
      change eB b = Multiplicative.ofAdd (hexAction (p x).val v) at hh
      change hexAction (p x).val v = v
      rw [hb] at hh
      exact (congrArg Multiplicative.toAdd hh).symm
    · intro hx
      ext b
      apply eB.injective
      rw [hequiv,←hpval,hx]
      simp only [Subgroup.coe_one,map_one]
      rfl

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
