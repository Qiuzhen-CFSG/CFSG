module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeSection
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeFiveAction
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CoreFactors
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.ResidualAction
/-!
# The actual five-dimensional section of an M22-code pair

For the original degree-one pair, [A,B] lies in U by E.2.10. The quintet
transvection criterion puts the marked B in V9. Both have dimension nine,
so this is equality, in the same code coordinates that mark U by V4.
The original residual preserves B, and the induced isomorphism B/U to the
native quintet kernel intertwines the full original normalizer action.
The equation on quotient representatives retains the literal quotient maps.

Source: Aschbacher--Smith E.2.10(2), H.16.3(3), and 8.2.8(4--5),
printed pp.222,403,718--719, refs/quasithin.pdf. The native geometric and
licensed ATLAS calculations are attributed in NormalizedShadowRows.M22CodeSection.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open MathieuCode.M22Quintet MathieuCode.M22Quintet.CocodeTransfer
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterE HermitianSource Offenders.Parabolic Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]
  {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
  {H M I : Subgroup G} {i : I} {S : Sylow 2 I}

/-- The literal B and U have the even-space and four-space markings in
one set of code coordinates. -/
theorem selected_m22_code_section_coordinates
    (s : Selected H T M V I 1 i S)
    (e : Additive V ≃ₗ[ZMod 2] M22Code) (p : Automizer V →* m22PairStabilizer)
    (he : ∀ a v, e (automizerRepresentation V a v) = m22OuterCodeRepresentation (p a) (e v))
    (hAN : V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 ≤ normalizer (V : Set G))
    (hfix : V ⊓ centralizer
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G) =
      V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hc : (inducedAutomizer V
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2)).map p = M22Quintet.K)
    (hfour : rank (V ⊓ centralizer
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)) = 4) :
    (∀ v : Additive V, (v.toMul : G) ∈ V ⊓ centralizer
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G) ↔
      e v ∈ M22Quintet.V4) ∧
    (∀ v : Additive V, (v.toMul : G) ∈ V ⊓ I.pCoreIn 2 ↔
      e v ∈ M22Quintet.V9) := by
  let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2
  let B := V ⊓ I.pCoreIn 2
  let U := V ⊓ centralizer (A : Set G)
  have hmark (v : Additive V) : (v.toMul : G) ∈ U ↔
      e v ∈ M22Quintet.V4 := by
    have hf := fixedSpace_map_equivariant (automizerRepresentation V) m22OuterCodeRepresentation p e he
      (inducedAutomizer V A)
    rw [hc] at hf
    have hd : Module.finrank (ZMod 2) (fixedSpace m22OuterCodeRepresentation M22Quintet.K) = 4 := by
      rw [←hf,LinearEquiv.finrank_map_eq]
      have hs := fixedCodim_add_finrank (automizerRepresentation V) (inducedAutomizer V A)
      have hcod := fixedCodim_inducedAutomizer V A hAN
      have hsum := offender_corank_add (W := V) (A := U) (B := ⊥) bot_le inf_le_left
      have hsum' : rank V = subgroupCorank V U + rank U := by
        simpa only [subgroupCorank,relIndex_bot_left,rank] using hsum
      have hv := Chapter7.log_card_eq_finrank V
      change rank V = Module.finrank (ZMod 2) (Additive V) at hv
      change rank U = 4 at hfour
      change fixedCodim (automizerRepresentation V) (inducedAutomizer V A) = subgroupCorank V U at hcod
      rw [hcod,←hv] at hs
      exact (Nat.add_left_cancel (hs.trans hsum')).trans hfour
    rw [NormalizedShadowRows.M22CodeFourSpace.fixed_eq_of_finrank hd] at hf
    rw [←hf]
    constructor
    · intro hv
      exact ⟨v,(mem_fixedSpace_inducedAutomizer V A hAN v).mpr hv.2,rfl⟩
    · rintro ⟨w,hw,hwv⟩
      have hwv' := e.injective hwv
      rw [hwv'] at hw
      exact ⟨v.toMul.property,(mem_fixedSpace_inducedAutomizer V A hAN v).mp hw⟩
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hbmap : (TwoConjugate.B (V.subgroupOf I) (M.subgroupOf I)).map I.subtype = B := by
    rw [s.twoConjugate.B_eq_twoCore_inf,map_inf _ _ _ I.subtype_injective,
      map_subgroupOf_eq_of_le hVI,inf_comm]
    rfl
  have hcomm : ⁅A,B⁆ ≤ U := by
    have hh := map_mono (f := I.subtype) s.twoConjugate.commutator_A_B_le_Z
    rw [map_commutator,selected_actor_image I M V hVI S i s.twoConjugate,hbmap,
      selected_intersection_image I V hVI i,←hfix] at hh
    exact hh
  have hB (v : Additive V) (hv : (v.toMul : G) ∈ B) :
      e v ∈ M22Quintet.V9 := by
    apply (NormalizedShadowRows.M22CodeSection.displacement_iff _).mp
    intro t
    obtain ⟨a,ha,hat⟩ := (show t.val ∈ (inducedAutomizer V A).map p by
      rw [hc]
      exact t.property)
    obtain ⟨a,ha,rfl⟩ := ha
    have hdisp : (automizerRepresentation V (V.normalizerMonoidHom.rangeRestrict a) v - v).toMul.val ∈ U := by
      change (a.val * (v.toMul : G) * a.val⁻¹) / (v.toMul : G) ∈ U
      simpa only [Subgroup.subtype_apply,commutatorElement_def,div_eq_mul_inv] using
        hcomm (commutator_mem_commutator ha hv)
    have hh := (hmark _).mp hdisp
    rw [map_sub,he,hat] at hh
    exact hh
  have hdim : rank V = 10 := by
    rw [rank,show Nat.card V = Nat.card (Additive V) from rfl,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      e.finrank_eq,finrank_m22Code,Nat.log_pow Nat.one_lt_two]
  have hcor : subgroupCorank V B = 1 := by
    change subgroupCorank V (V ⊓ (pCore 2 I).map I.subtype) = 1
    rw [←quotient_rank_eq_core_corank I V hVI]
    exact s.rank_eq
  have hrB : rank B = 9 := by
    have hh := offender_corank_add (W := V) (A := B) bot_le inf_le_left
    have hh' : rank V = subgroupCorank V B + rank B := by
      simpa only [subgroupCorank,relIndex_bot_left,rank] using hh
    omega
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le (show B ≤ V from inf_le_left)
  have hcard : Nat.card B = 2^9 := by
    obtain ⟨a,ha⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_card_eq
    have hh : rank B = a := by rw [rank,ha,Nat.log_pow Nat.one_lt_two]
    rw [ha]
    congr 1
    omega
  let f : B → M22Quintet.V9 :=
    fun b => ⟨e (Additive.ofMul ⟨b,b.property.1⟩),hB _ b.property⟩
  have hfi : Function.Injective f := by
    intro b d hbd
    have hh := e.injective (congrArg Subtype.val hbd)
    exact Subtype.ext (congrArg (fun v : Additive V => (v.toMul : G)) hh)
  have hfs : Function.Surjective f := (hfi.bijective_of_nat_card_le (by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      NormalizedShadowRows.M22CodeSection.nine_dim,hcard])).2
  refine ⟨hmark,fun v => ⟨hB v,?_⟩⟩
  intro hv
  obtain ⟨b,hb⟩ := hfs ⟨e v,hv⟩
  have hh := e.injective (congrArg Subtype.val hb)
  have hbv : (b : G) = (v.toMul : G) := congrArg (fun v : Additive V => (v.toMul : G)) hh
  exact hbv ▸ b.property

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode MathieuCode.M22Quintet MathieuCode.M22Quintet.CocodeTransfer
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterE Normalizer.SmallOvergroups
variable {G : Type*} [Group G]

/-- The original normalizer preserves the actual nine-space preimage. -/
theorem marked_m22_nine_normalizes
    (V B R : Subgroup G) [IsElementaryAbelian 2 V]
    (hBV : B ≤ V) (hRV : R ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] M22Code) (f : R →* Q)
    (he : ∀ (x : R) v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hRV x)) v) =
        m22OuterCodeRepresentation (f x).val (e v))
    (hB : ∀ v : Additive V, (v.toMul : G) ∈ B ↔ e v ∈ V9) :
    R ≤ normalizer (B : Set G) := by
  apply le_normalizer_iff.mpr
  intro x hx b hb
  let v : Additive V := Additive.ofMul ⟨b,hBV hb⟩
  have hc := NormalizedShadowRows.M22CodeSection.nine_invariant (f ⟨x,hx⟩) _ ((hB v).mp hb)
  rw [←he ⟨x,hx⟩ v] at hc
  exact (hB _).mpr hc

/-- The literal B/U is marked by the five-dimensional quintet kernel,
with its original normalizer action and quotient representatives retained. -/
private theorem quotient_coordinates
    (V B U : Subgroup G) [IsElementaryAbelian 2 V]
    (hBV : B ≤ V) (e : Additive V ≃ₗ[ZMod 2] M22Code)
    (hU : ∀ v : Additive V, (v.toMul : G) ∈ U ↔ e v ∈ V4)
    (hB : ∀ v : Additive V, (v.toMul : G) ∈ B ↔ e v ∈ V9) :
    ∃ hBU : (U.subgroupOf B).Normal, letI := hBU
      ∃ eB : (B ⧸ U.subgroupOf B) ≃* M22Quintet.K,
        (∀ (b : B), Additive.ofMul (eB (QuotientGroup.mk' (U.subgroupOf B) b)) =
          NormalizedShadowRows.M22CodeSection.axisMarking
            ⟨V4.mkQ (e (Additive.ofMul ⟨b,hBV b.property⟩)),
              ⟨e (Additive.ofMul ⟨b,hBV b.property⟩),(hB _).mp b.property,rfl⟩⟩) := by
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le hBV
  let hBU : (U.subgroupOf B).Normal := inferInstance
  let := hBU
  let ι := (inclusion hBV).toAdditive.toZModLinearMap 2
  let q : Additive B →ₗ[ZMod 2] DualAction.codeAxis := {
    toFun b := ⟨V4.mkQ (e (ι b)),⟨e (ι b),(hB _).mp b.toMul.property,rfl⟩⟩
    map_add' _ _ := Subtype.ext (by simp only [map_add]; rfl)
    map_smul' _ _ := Subtype.ext (by simp only [map_smul]; rfl) }
  let p : B →* M22Quintet.K :=
    ((NormalizedShadowRows.M22CodeSection.axisMarking.toLinearMap.comp q).toAddMonoidHom).toMultiplicative
  have hp : Function.Surjective p := by
    intro k
    let w := NormalizedShadowRows.M22CodeSection.axisMarking.symm (Additive.ofMul k)
    obtain ⟨v,hv,heq⟩ := w.property
    let b := e.symm v
    have hb : (b.toMul : G) ∈ B := (hB b).mpr (by rw [e.apply_symm_apply]; exact hv)
    refine ⟨⟨b.toMul,hb⟩,?_⟩
    apply Additive.ofMul.injective
    change NormalizedShadowRows.M22CodeSection.axisMarking (q (Additive.ofMul ⟨b.toMul,hb⟩)) = _
    rw [←NormalizedShadowRows.M22CodeSection.axisMarking.apply_symm_apply (Additive.ofMul k)]
    congr 1
    apply Subtype.ext
    change V4.mkQ (e b) = w.val
    rw [e.apply_symm_apply]
    exact heq
  have hk : p.ker = U.subgroupOf B := by
    ext b
    change NormalizedShadowRows.M22CodeSection.axisMarking (q (Additive.ofMul b)) = 0 ↔ (b : G) ∈ U
    rw [LinearEquiv.map_eq_zero_iff,Subtype.ext_iff]
    change V4.mkQ (e (ι (Additive.ofMul b))) = 0 ↔ _
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
    exact (hU _).symm
  let eB : (B ⧸ U.subgroupOf B) ≃* M22Quintet.K :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective p hp)
  exact ⟨hBU,eB,fun _ => rfl⟩

/-- The literal B/U is marked by the five-dimensional quintet kernel,
with its original normalizer action and quotient representatives retained. -/
theorem marked_m22_section_action
    (V B U R : Subgroup G) [IsElementaryAbelian 2 V]
    (hBV : B ≤ V) (hRV : R ≤ normalizer (V : Set G))
    (hRB : R ≤ normalizer (B : Set G)) (hRU : R ≤ normalizer (U : Set G))
    (e : Additive V ≃ₗ[ZMod 2] M22Code) (f : R →* Q)
    (he : ∀ (x : R) v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hRV x)) v) =
        m22OuterCodeRepresentation (f x).val (e v))
    (hU : ∀ v : Additive V, (v.toMul : G) ∈ U ↔ e v ∈ V4)
    (hB : ∀ v : Additive V, (v.toMul : G) ∈ B ↔ e v ∈ V9) :
    ∃ hBU : (U.subgroupOf B).Normal, letI := hBU
      ∃ eB : (B ⧸ U.subgroupOf B) ≃* M22Quintet.K,
        (∀ (b : B), Additive.ofMul (eB (QuotientGroup.mk' (U.subgroupOf B) b)) =
          NormalizedShadowRows.M22CodeSection.axisMarking
            ⟨V4.mkQ (e (Additive.ofMul ⟨b,hBV b.property⟩)),
              ⟨e (Additive.ofMul ⟨b,hBV b.property⟩),(hB _).mp b.property,rfl⟩⟩) ∧
        ∀ (x : R) (b : B ⧸ U.subgroupOf B),
          Additive.ofMul (eB (sectionAction R B U hRB hRU x b)) =
            kernelConjugation (f x) (Additive.ofMul (eB b)) := by
  obtain ⟨hBU,eB,hmark⟩ := quotient_coordinates V B U hBV e hU hB
  let := hBU
  refine ⟨hBU,eB,hmark,?_⟩
  intro x b
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf B) b
  rw [sectionAction_apply,hmark,hmark]
  have hh := NormalizedShadowRows.M22CodeSection.axisMarking_mk_equivariant (f x)
    (e (Additive.ofMul ⟨b,hBV b.property⟩)) ((hB _).mp b.property)
  refine Eq.trans ?_ hh
  apply congrArg NormalizedShadowRows.M22CodeSection.axisMarking
  apply Subtype.ext
  exact congrArg V4.mkQ (he x (Additive.ofMul ⟨b,hBV b.property⟩))

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode MathieuCode.M22Quintet MathieuCode.M22Quintet.CocodeTransfer
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterE Normalizer.SmallOvergroups
variable {G : Type*} [Group G]

/-- The literal quotient action, including its original quintet map, exact
kernel and the dimensions needed for the subsequent two-copy argument. -/
@[expose] def M22FiveSection (R B U : Subgroup G) (f : R →* Q) : Prop :=
  ∃ hRB : R ≤ normalizer (B : Set G), ∃ hRU : R ≤ normalizer (U : Set G),
    ∃ hBU : (U.subgroupOf B).Normal, letI := hBU
      ∃ (r : R →* alternatingGroup (Fin 5)) (eB : (B ⧸ U.subgroupOf B) ≃* M22Quintet.K),
        Function.Surjective r ∧ r.ker = pCore 2 R ∧
        (∀ x, (r x).val = NaturalQuotient.q (f x)) ∧
        (∀ (x : R) (b : B ⧸ U.subgroupOf B),
          Additive.ofMul (eB (sectionAction R B U hRB hRU x b)) =
            NormalizedShadowRows.M22CodeSection.fiveAction (r x) (Additive.ofMul (eB b))) ∧
        (sectionAction R B U hRB hRU).ker = pCore 2 R ∧
        ∃ hEl : IsElementaryAbelian 2 (B ⧸ U.subgroupOf B), letI := hEl
          ∃ ρ : Representation (ZMod 2) R (Additive (B ⧸ U.subgroupOf B)),
            (∀ x b, ρ x (Additive.ofMul b) = Additive.ofMul (sectionAction R B U hRB hRU x b)) ∧
            Module.finrank (ZMod 2) (Additive (B ⧸ U.subgroupOf B)) = 5 ∧
            Module.finrank (ZMod 2) (Coinvariants.ker ρ) = 4 ∧
            Module.finrank (ZMod 2) (Coinvariants ρ) = 1

/-- The supplied original A5 residual quotient acts faithfully on B/U.
All markings and dimensions are constructed from the same code coordinates. -/
theorem marked_m22_section_residual [Finite G]
    (V B U R : Subgroup G) [IsElementaryAbelian 2 V]
    (hBV : B ≤ V) (hRV : R ≤ normalizer (V : Set G))
    (hRU : R ≤ normalizer (U : Set G))
    (e : Additive V ≃ₗ[ZMod 2] M22Code) (f : R →* Q)
    (he : ∀ (x : R) v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hRV x)) v) =
        m22OuterCodeRepresentation (f x).val (e v))
    (hU : ∀ v : Additive V, (v.toMul : G) ∈ U ↔ e v ∈ V4)
    (hB : ∀ v : Additive V, (v.toMul : G) ∈ B ↔ e v ∈ V9)
    (r : R →* alternatingGroup (Fin 5)) (hrsur : Function.Surjective r)
    (hrc : r.ker = pCore 2 R) (hrval : ∀ x, (r x).val = NaturalQuotient.q (f x)) :
    M22FiveSection R B U f := by
  have hRB := marked_m22_nine_normalizes V B R hBV hRV e f he hB
  obtain ⟨hBU,eB,heB,hact⟩ := marked_m22_section_action V B U R hBV hRV hRB hRU e f he hU hB
  let := hBU
  have hact' (x : R) (b : B ⧸ U.subgroupOf B) :
      Additive.ofMul (eB (sectionAction R B U hRB hRU x b)) =
        NormalizedShadowRows.M22CodeSection.fiveAction (r x) (Additive.ofMul (eB b)) := by
    rw [hact]
    change kernelConjugation (f x) _ = M22ChapterH.Quintet.kernelS5Conjugation (r x).val _
    rw [hrval,M22ChapterH.Quintet.kernelS5Conjugation_q]
  have hkernel : (sectionAction R B U hRB hRU).ker = pCore 2 R := by
    rw [←hrc]
    ext x
    change sectionAction R B U hRB hRU x = 1 ↔ r x = 1
    constructor
    · intro hx
      apply NormalizedShadowRows.M22CodeSection.fiveAction_faithful
      rw [map_one]
      ext v : 1
      obtain ⟨b,rfl⟩ := eB.surjective v.toMul
      have hh := hact' x b
      rw [hx] at hh
      exact hh.symm
    · intro hx
      ext b
      apply eB.injective
      apply Additive.ofMul.injective
      rw [hact',hx,map_one]
      rfl
  exact ⟨hRB,hRU,hBU,r,eB,hrsur,hrc,hrval,hact',hkernel,
    NormalizedShadowRows.M22CodeSection.dimensions_of_group_marking
      (sectionAction R B U hRB hRU) r hrsur eB hact'⟩
end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
