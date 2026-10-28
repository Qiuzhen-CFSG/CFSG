module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeMultiplicity
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourTensor
public import Theory.Representation.ScalarMultiplicity.FixedVectors
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourTensor

/-!
# The original M22-code cubic tensor

The faithful binary multiplicity action makes the selected cubic fixed-point
free on the literal P/U. A nontrivial element of V modulo O₂(I) is marked as
its inverter, fixing the original B/U inclusion. The cubic tensor theorem
then gives a natural binary plane tensor B/U, with both original R and I
actions and the original quotient representatives retained.

Source: Aschbacher--Smith 8.2.8(5), printed pp.718--719, refs/quasithin.pdf.
-/

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement MatrixGroups TensorProduct
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterE HermitianSource Offenders.Parabolic.Construction Normalizer.SmallOvergroups Normalizer.TensorRecognition
public noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem multiplicity_pair_fixed_eq_one
    {E Q : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Group Q]
    (eP : Multiplicative E × Multiplicative E ≃* Q) (f : MulAut Q)
    (μ : Module.End (ZMod 2) (Fin 2 → ZMod 2))
    (h : ∀ (c : Fin 2 → ZMod 2) (v : E),
      f (eP (Multiplicative.ofAdd (c 0 • v), Multiplicative.ofAdd (c 1 • v))) =
      eP (Multiplicative.ofAdd (μ c 0 • v), Multiplicative.ofAdd (μ c 1 • v)))
    (hf : ∀ c, μ c = c → c = 0) (q : Q) (hq : f q = q) : q = 1 := by
  let e : Multiplicative (Fin 2 → E) ≃* Q :=
    (LinearEquiv.finTwoArrow (ZMod 2) E).toAddEquiv.toMultiplicative.trans
      ((MulEquiv.prodMultiplicative _ _).trans eP)
  let a := MulAut.congr e.symm f
  let T : Module.End (ZMod 2) (Fin 2 → E) :=
    (AddMonoidHom.toMultiplicative.symm a.toMonoidHom).toZModLinearMap 2
  have hT (x : Fin 2 → E) :
      e (Multiplicative.ofAdd (T x)) = f (e (Multiplicative.ofAdd x)) := by
    change e (e.symm _) = _
    exact e.apply_symm_apply _
  have hact (c : Fin 2 → ZMod 2) (v : E) :
      T (fun j => c j • v) = fun j => μ c j • v := by
    apply Multiplicative.ofAdd.injective
    apply e.injective
    rw [hT]
    exact h c v
  obtain ⟨x, rfl⟩ := e.surjective q
  have hx : T x.toAdd = x.toAdd := by
    apply Multiplicative.ofAdd.injective
    apply e.injective
    exact (hT x.toAdd).trans hq
  have hz := ScalarMultiplicity.fixed_eq_zero_of_multiplicity T μ hact hf x.toAdd hx
  have hx1 : x = 1 := congrArg Multiplicative.ofAdd hz
  rw [hx1, map_one]

variable {G J : Type*} [Group G] [Finite G] [Group J]

private theorem m22_pair_tensor_preparation
    {R I V U : Subgroup G} [IsElementaryAbelian 2 V] {i : I}
    (hp : M22CodePairProductAction R I V U)
    {fq : R →* MathieuCode.M22Quintet.Q} (hm : M22CodePairMultiplicityAction R I V U i fq)
    (hcomm : ⁅R,I⁆ ≤ R.pCoreIn 2)
    (eI : (I ⧸ pCore 2 I) ≃* J)
    (r t : J) (m : ℕ) (ho : Odd m) (hr : r^m=1) (hrn : r≠1)
    (v : V) (hvI : (v : G) ∈ I)
    (hv : eI (QuotientGroup.mk' (pCore 2 I) ⟨v,hvI⟩) = t)
    :
    PairTensorPreparation R I V U r t := by
  obtain ⟨hYP,hYU,hUP,hBU,eB,rA,eP,μ,hrsur,hrker,hrval,hμ,heP,hR,hact⟩ := hm
  let := hUP
  let := hBU
  obtain ⟨_,_,_,hP,hcard,hker,hcore,hRker,hIker,hRB,_,heq,_⟩ := hp
  let := hP
  let B := V ⊓ I.pCoreIn 2
  let P := I.pCoreIn 2
  let Y := R ⊔ I
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le (show B ≤ V from inf_le_left)
  let : IsElementaryAbelian 2 (B ⧸ U.subgroupOf B) := inferInstance
  let f := sectionAction Y P U hYP hYU
  let fq := QuotientGroup.lift (pCore 2 I) (f.comp (inclusion le_sup_right)) hIker.ge
  let σ := binaryAction (fq.comp eI.symm.toMonoidHom)
  let κ := binaryAction (f.comp (inclusion le_sup_left))
  let τ := binaryAction (sectionAction R B U hRB (le_sup_left.trans hYU))
  have hσ (a : I) (p : CoreSection I U) :
      σ (eI (QuotientGroup.mk' (pCore 2 I) a)) p =
        Additive.ofMul (f (inclusion le_sup_right a) p.toMul) := by
    change Additive.ofMul (fq (eI.symm (eI _)) p.toMul) = _
    rw [eI.symm_apply_apply]
    rfl
  have hc (a : R) (g : J) (p : CoreSection I U) : κ a (σ g p) = σ g (κ a p) := by
    obtain ⟨b,hb⟩ := QuotientGroup.mk'_surjective (pCore 2 I) (eI.symm g)
    have hg : eI (QuotientGroup.mk' (pCore 2 I) b) = g := by rw [hb,eI.apply_symm_apply]
    rw [←hg,hσ,hσ]
    have hfc : Commute (f (inclusion le_sup_left a)) (f (inclusion le_sup_right b)) := by
      apply commutatorElement_eq_one_iff_mul_comm.mp
      rw [←map_commutatorElement]
      apply MonoidHom.mem_ker.mp
      rw [hker]
      have hm : (⁅(a : G),(b : G)⁆ : G) ∈ Y.pCoreIn 2 := by
        rw [hcore]
        exact mem_sup_right (hcomm (commutator_mem_commutator a.property b.property))
      obtain ⟨z,hz,he⟩ := hm
      have he' : z = ⁅inclusion (show R ≤ Y from le_sup_left) a,
          inclusion (show I ≤ Y from le_sup_right) b⁆ := Subtype.ext he
      exact he' ▸ hz
    exact congrArg (fun z : MulAut (P ⧸ U.subgroupOf P) => Additive.ofMul (z p.toMul)) hfc.eq
  have hf (p : CoreSection I U) (hfix : σ r p = p) : p = 0 := by
    obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective (pCore 2 I) (eI.symm r)
    have har : eI (QuotientGroup.mk' (pCore 2 I) a) = r := by rw [ha,eI.apply_symm_apply]
    have hfree (c : Fin 2 → ZMod 2) (hc : μ (QuotientGroup.mk' (pCore 2 I) a) c = c) : c = 0 := by
      apply ScalarMultiplicity.binary_plane_odd_fixed_eq_zero μ hμ
        (QuotientGroup.mk' (pCore 2 I) a) m ho
      · apply eI.injective
        rw [map_pow, har, hr, map_one]
      · intro he
        exact hrn (har.symm.trans (he ▸ eI.map_one))
      · exact hc
    apply Additive.toMul.injective
    apply multiplicity_pair_fixed_eq_one
      ((MulEquiv.toMultiplicative_toAdditive.prodCongr
        MulEquiv.toMultiplicative_toAdditive).trans eP) (f (inclusion le_sup_right a))
      (μ (QuotientGroup.mk' (pCore 2 I) a)) (hact a) hfree
    have hh := hσ a p
    rw [har,hfix] at hh
    exact congrArg Additive.toMul hh.symm
  have hfixed (b : IntersectionSection I V U) :
      σ t (intersectionInclusion I V U b) = intersectionInclusion I V U b := by
    rw [←hv,hσ]
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf B) b.toMul
    change Additive.ofMul (QuotientGroup.mk' (U.subgroupOf P)
      ⟨(v : G)*(b : G)*(v : G)⁻¹,_⟩) =
        Additive.ofMul (QuotientGroup.mk' (U.subgroupOf P) ⟨b,b.property.2⟩)
    congr 2
    apply Subtype.ext
    have hvb : (v : G)*(b : G) = (b : G)*(v : G) :=
      congrArg Subtype.val (mul_comm v (⟨b,b.property.1⟩ : V))
    change (v : G)*(b : G)*(v : G)⁻¹ = (b : G)
    rw [hvb,mul_inv_cancel_right]
  have hdim : Module.finrank (ZMod 2) (CoreSection I U) =
      2 * Module.finrank (ZMod 2) (IntersectionSection I V U) := by
    have hpc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := CoreSection I U)
    have hbc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := IntersectionSection I V U)
    have hbc' : Nat.card (IntersectionSection I V U) = 2^5 := by
      change Nat.card (B ⧸ U.subgroupOf B) = _
      rw [Nat.card_congr eB.toEquiv]
      change Nat.card (Additive MathieuCode.M22Quintet.K) = _
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
        Sporadic.Mathieu.M22ChapterH.Quintet.kernel_finrank]
    have hpc' : Nat.card (CoreSection I U) = 2^10 := hcard
    simp only [Nat.card_zmod,hpc'] at hpc
    simp only [Nat.card_zmod,hbc'] at hbc
    have hdP := Nat.pow_right_injective (by decide : 1 < 2) hpc
    have hdB := Nat.pow_right_injective (by decide : 1 < 2) hbc
    omega
  exact ⟨hYP,hYU,hUP,hBU,hP,inferInstance,eI,σ,κ,τ,hσ,fun _ _ => rfl,hc,
    fun a b => congrArg Additive.ofMul (heq a b.toMul),hf,hfixed,hdim⟩


/-- The same selected pair has its marked binary tensor on the original P/U. -/
theorem selected_m22_code_source_tensor
    {V H M I R U : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 1 i S)
    {fq : R →* MathieuCode.M22Quintet.Q}
    (hp : M22CodePairProductAction R I V U)
    (hm : M22CodePairMultiplicityAction R I V U i fq)
    (hcomm : ⁅R,I⁆ ≤ R.pCoreIn 2)
    (hc : Nonempty ((I ⧸ pCore 2 I) ≃* PSL(2,ZMod 2))) :
    PairCubicTensor R I V U := by
  have hv : ∃ a : I, (a : G) ∈ V ∧ QuotientGroup.mk' (pCore 2 I) a ≠ 1 := by
    by_contra hn
    push Not at hn
    have hz : coreImage I V = ⊥ := by
      apply bot_unique
      rintro _ ⟨a,ha,rfl⟩
      exact hn a ha
    have hh := s.rank_eq
    rw [hz,Representation.BinaryOffender.rank_bot] at hh
    omega
  obtain ⟨a,ha,han⟩ := hv
  let v : V := ⟨a,ha⟩
  have hap : (QuotientGroup.mk' (pCore 2 I) a)^2 = 1 := by
    rw [←map_pow]
    have hh : a^2=1 := Subtype.ext
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) (a : G) ha)
    rw [hh,map_one]
  obtain ⟨e⟩ := hc
  let d := e.trans Theory.SpecificGroups.BinaryDihedral.dihedralThreeEquivPSL2Two.symm
  let e₀ := d.trans nonempty_dihedralThreeEquivPerm.some
  have hsmall : ∀ g : InvertedCubicTensor.S₃, g ≠ 1 → g*g=1 →
      ∃ c : InvertedCubicTensor.S₃, c*g*c⁻¹ = InvertedCubicTensor.inverter := by
    decide +kernel
  obtain ⟨c,hc⟩ := hsmall (e₀ (QuotientGroup.mk' (pCore 2 I) a))
    (fun hh => han (e₀.injective (hh.trans e₀.map_one.symm)))
    (by rw [←pow_two,←map_pow,hap,map_one])
  let eI := e₀.trans (MulAut.conj c)
  exact pair_cubic_tensor (m22_pair_tensor_preparation hp hm hcomm eI
    InvertedCubicTensor.cubic InvertedCubicTensor.inverter 3 (by decide)
    (by decide +kernel) (by decide +kernel) v a.property hc)

end
end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
