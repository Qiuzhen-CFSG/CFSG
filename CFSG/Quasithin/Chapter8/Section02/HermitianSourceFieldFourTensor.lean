module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourMultiplicity
public import Theory.Representation.DihedralPlaneFour.FixedVectors
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.Cubic
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.Dihedral
public import Theory.GroupTheory.OddInvolutionEndpointModels
/-!
# The source tensors on the original Hermitian pair

The faithful F₄ multiplicity plane has fixed-point-free odd rotations.
Its pure-vector action formula transfers fixed-point-freeness to the original
P/U. A nontrivial element of the selected image of V is a reflection; adjusting
the quotient marking by an inner automorphism makes it the standard inverter.
It fixes the literal B₀/U, which has half the dimension of P/U.

The marked inverted-cubic and inverted-quintic constructions now give the
source tensors on those same quotient carriers. The cubic tensor is over F₂.
The quintic rotation constructs F₄ scalars, including their action on B₀/U.
Both tensor formulas retain the original quotient maps and product conjugation
action. No reflection lift, rotation fixedness or tensor witness is assumed.
The Chapter12 consumer discharges the selection and commutator hypotheses.

This proves the Hermitian tensor step of Aschbacher–Smith 8.2.8(5), printed
pp.718–719, refs/quasithin.pdf (1 March 2004 manuscript). Equality R=K and
the remaining source exclusion are separate obligations.
-/

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree
open scoped IsMulCommutative commutatorElement MatrixGroups TensorProduct
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic.Construction Normalizer.SmallOvergroups Normalizer.TensorRecognition
public noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem pure_pair_fixed_eq_one {F Q : Type*} [Field F] [CommGroup Q]
    (e : (Multiplicative (Fin 2 → F)) × (Multiplicative (Fin 2 → F)) ≃* Q)
    (f : MulAut Q) (μ : Module.End F (Fin 2 → F))
    (h : ∀ c v, f (e (Multiplicative.ofAdd (c 0 • v),Multiplicative.ofAdd (c 1 • v))) =
      e (Multiplicative.ofAdd (μ c 0 • v),Multiplicative.ofAdd (μ c 1 • v)))
    (hf : ∀ c, μ c = c → c = 0) (q : Q) (hq : f q = q) : q = 1 := by
  obtain ⟨⟨x,y⟩,rfl⟩ := e.surjective q
  let b₀ : Fin 2 → F := ![1,0]
  let b₁ : Fin 2 → F := ![0,1]
  let c₀ : Fin 2 → F := ![x.toAdd 0,y.toAdd 0]
  let c₁ : Fin 2 → F := ![x.toAdd 1,y.toAdd 1]
  have hpair : (x,y) =
      (Multiplicative.ofAdd (c₀ 0 • b₀),Multiplicative.ofAdd (c₀ 1 • b₀)) *
      (Multiplicative.ofAdd (c₁ 0 • b₁),Multiplicative.ofAdd (c₁ 1 • b₁)) := by
    apply Prod.ext <;> apply Multiplicative.toAdd.injective <;> funext j <;>
      fin_cases j <;> simp [b₀,b₁,c₀,c₁]
  have he :
      (Multiplicative.ofAdd (μ c₀ 0 • b₀),Multiplicative.ofAdd (μ c₀ 1 • b₀)) *
      (Multiplicative.ofAdd (μ c₁ 0 • b₁),Multiplicative.ofAdd (μ c₁ 1 • b₁)) = (x,y) := by
    apply e.injective
    rw [map_mul,←h,←h,←map_mul,←map_mul,←hpair]
    exact hq
  have hc₀ : μ c₀ = c₀ := by
    have hx := congrArg (fun z => z.1.toAdd 0) he
    have hy := congrArg (fun z => z.2.toAdd 0) he
    funext j
    fin_cases j
    · simpa [b₀,b₁,c₀] using hx
    · simpa [b₀,b₁,c₀] using hy
  have hc₁ : μ c₁ = c₁ := by
    have hx := congrArg (fun z => z.1.toAdd 1) he
    have hy := congrArg (fun z => z.2.toAdd 1) he
    funext j
    fin_cases j
    · simpa [b₀,b₁,c₁] using hx
    · simpa [b₀,b₁,c₁] using hy
  have hz₀ := hf c₀ hc₀
  have hz₁ := hf c₁ hc₁
  have hxy : (x,y) = 1 := by
    rw [hpair,hz₀,hz₁]
    simp
  rw [hxy,map_one]

private def binaryAction {A Q : Type*} [Group A] [Group Q] [IsElementaryAbelian 2 Q]
    (f : A →* MulAut Q) : Representation (ZMod 2) A (Additive Q) where
  toFun a := (f a).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext; intro x
    change Additive.ofMul (f 1 x.toMul) = x
    rw [map_one]; rfl
  map_mul' a b := by
    apply LinearMap.ext; intro x
    change Additive.ofMul (f (a*b) x.toMul) = _
    rw [map_mul]; rfl

/-- Original quotient actions, a marked inverter and the literal B₀/U inclusion.
The odd rotation is fixed-point-free, and P/U has twice the binary dimension of B₀/U. -/
@[expose] def PairTensorPreparation {G J : Type*} [Group G] [Group J]
    (R I V U : Subgroup G) (r t : J) : Prop :=
  ∃ hYP : R ⊔ I ≤ normalizer (I.pCoreIn 2 : Set G),
    ∃ hYU : R ⊔ I ≤ normalizer (U : Set G),
      ∃ hUP : (U.subgroupOf (I.pCoreIn 2)).Normal, letI := hUP
        ∃ hBU : (U.subgroupOf (V ⊓ I.pCoreIn 2)).Normal, letI := hBU
          ∃ hP : IsElementaryAbelian 2 (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)), letI := hP
            ∃ hB : IsElementaryAbelian 2 ((V ⊓ I.pCoreIn 2 : Subgroup G) ⧸ U.subgroupOf (V ⊓ I.pCoreIn 2)), letI := hB
              ∃ eI : (I ⧸ pCore 2 I) ≃* J,
                ∃ σ : Representation (ZMod 2) J (CoreSection I U),
                  ∃ κ : Representation (ZMod 2) R (CoreSection I U),
                    ∃ τ : Representation (ZMod 2) R (IntersectionSection I V U),
                      (∀ (a : I) p, σ (eI (QuotientGroup.mk' (pCore 2 I) a)) p =
                        Additive.ofMul (sectionAction (R ⊔ I) (I.pCoreIn 2) U hYP hYU
                          (inclusion le_sup_right a) p.toMul)) ∧
                      (∀ (a : R) p, κ a p =
                        Additive.ofMul (sectionAction (R ⊔ I) (I.pCoreIn 2) U hYP hYU
                          (inclusion le_sup_left a) p.toMul)) ∧
                      (∀ a g p, κ a (σ g p) = σ g (κ a p)) ∧
                      (∀ a b, intersectionInclusion I V U (τ a b) = κ a (intersectionInclusion I V U b)) ∧
                      (∀ p, σ r p = p → p = 0) ∧
                      (∀ b, σ t (intersectionInclusion I V U b) = intersectionInclusion I V U b) ∧
                      Module.finrank (ZMod 2) (CoreSection I U) =
                        2 * Module.finrank (ZMod 2) (IntersectionSection I V U)

variable {G J : Type*} [Group G] [Finite G] [Group J]

private theorem pair_tensor_preparation
    {R I V U : Subgroup G} [IsElementaryAbelian 2 V] {i : I}
    (hp : PairProductAction R I V U) (hm : PairMultiplicityAction R I V U i)
    (hcomm : ⁅R,I⁆ ≤ R.pCoreIn 2)
    (eI : (I ⧸ pCore 2 I) ≃* J)
    (r t : J) (m : ℕ) (ho : Odd m) (hr : r^m=1) (hrn : r≠1)
    (v : V) (hvI : (v : G) ∈ I)
    (hv : eI (QuotientGroup.mk' (pCore 2 I) ⟨v,hvI⟩) = t)
    (d : ℕ) (eD : (I ⧸ pCore 2 I) ≃* DihedralGroup d) :
    PairTensorPreparation R I V U r t := by
  obtain ⟨hYP,hYU,hUP,hBU,eB,eR,eP,μ,hμ,heP,hR,hact⟩ := hm
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
    let ν : Representation (E 1) (DihedralGroup d) (Fin 2 → E 1) := μ.comp eD.symm.toMonoidHom
    have hν : Function.Injective ν.asGroupHom := by
      intro x y hxy
      apply eD.symm.injective
      apply hμ
      apply Units.ext
      have hh := congrArg (fun z : (Module.End (E 1) (Fin 2 → E 1))ˣ => z.val) hxy
      exact hh
    have hfree (c : Fin 2 → E 1) (hc : μ (QuotientGroup.mk' (pCore 2 I) a) c = c) : c = 0 := by
      apply dihedral_plane_four_odd_fixed_eq_zero (by rw [card_E]; norm_num) ν hν
        (eD (QuotientGroup.mk' (pCore 2 I) a)) m ho
      · apply eD.symm.injective
        simp only [map_pow,eD.symm_apply_apply,map_one]
        apply eI.injective
        rw [map_pow,har,hr,map_one]
      · intro he
        have he' := eD.injective (he.trans eD.map_one.symm)
        exact hrn (har.symm.trans (he' ▸ eI.map_one))
      · change μ (eD.symm (eD _)) c = c
        rwa [eD.symm_apply_apply]
    apply Additive.toMul.injective
    apply pure_pair_fixed_eq_one eP (f (inclusion le_sup_right a))
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
    have hbc' : Nat.card (IntersectionSection I V U) = 2^4 := by
      change Nat.card (B ⧸ U.subgroupOf B) = _
      rw [Nat.card_congr eB.toEquiv]
      change Nat.card (Fin 2 → E 1) = _
      rw [Nat.card_fun,Nat.card_fin,card_E]
      norm_num
    have hpc' : Nat.card (CoreSection I U) = 2^8 := hcard
    simp only [Nat.card_zmod,hpc'] at hpc
    simp only [Nat.card_zmod,hbc'] at hbc
    have hdP := Nat.pow_right_injective (by decide : 1 < 2) hpc
    have hdB := Nat.pow_right_injective (by decide : 1 < 2) hbc
    omega
  exact ⟨hYP,hYU,hUP,hBU,hP,inferInstance,eI,σ,κ,τ,hσ,fun _ _ => rfl,hc,
    fun a b => congrArg Additive.ofMul (heq a b.toMul),hf,hfixed,hdim⟩

/-- The selected cubic or quintic quotient supplies a reflection lifted from V.
Both resulting actions retain the original quotient and section maps. -/
theorem selected_one_tensor_preparation
    {V H M I R U : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 1 i S)
    (hp : PairProductAction R I V U) (hm : PairMultiplicityAction R I V U i)
    (hcomm : ⁅R,I⁆ ≤ R.pCoreIn 2)
    (hc : Nonempty ((I ⧸ pCore 2 I) ≃* PSL(2,ZMod 2)) ∨
      Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup 5)) :
    PairTensorPreparation R I V U InvertedCubicTensor.cubic InvertedCubicTensor.inverter ∨
      PairTensorPreparation R I V U InvertedFiveTensor.rot InvertedFiveTensor.invt := by
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
    have hh : a^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (a : G) ha)
    rw [hh,map_one]
  rcases hc with hc | hc
  · obtain ⟨e⟩ := hc
    let d := e.trans Theory.SpecificGroups.BinaryDihedral.dihedralThreeEquivPSL2Two.symm
    let e₀ := d.trans nonempty_dihedralThreeEquivPerm.some
    have hsmall : ∀ g : InvertedCubicTensor.S₃, g ≠ 1 → g*g=1 →
        ∃ c : InvertedCubicTensor.S₃, c*g*c⁻¹ = InvertedCubicTensor.inverter := by decide +kernel
    obtain ⟨c,hc⟩ := hsmall (e₀ (QuotientGroup.mk' (pCore 2 I) a))
      (fun hh => han (e₀.injective (hh.trans e₀.map_one.symm)))
      (by rw [←pow_two,←map_pow,hap,map_one])
    let eI := e₀.trans (MulAut.conj c)
    exact Or.inl (pair_tensor_preparation hp hm hcomm eI
      InvertedCubicTensor.cubic InvertedCubicTensor.inverter 3 (by decide)
      (by decide +kernel) (by decide +kernel) v a.property hc 3 d)
  · obtain ⟨e⟩ := hc
    have hsmall : ∀ g : DihedralGroup 5, g ≠ 1 → g*g=1 →
        ∃ c : DihedralGroup 5, c*g*c⁻¹ = InvertedFiveTensor.invt := by decide +kernel
    obtain ⟨c,hc⟩ := hsmall (e (QuotientGroup.mk' (pCore 2 I) a))
      (fun hh => han (e.injective (hh.trans e.map_one.symm)))
      (by rw [←pow_two,←map_pow,hap,map_one])
    let eI := e.trans (MulAut.conj c)
    exact Or.inr (pair_tensor_preparation hp hm hcomm eI
      InvertedFiveTensor.rot InvertedFiveTensor.invt 5 (by decide)
      (by decide +kernel) (by decide +kernel) v a.property hc 5 e)

/-- The binary cubic tensor on the literal P/U, marked by the original B₀/U inclusion. -/
@[expose] def PairCubicTensor (R I V U : Subgroup G) : Prop :=
  ∃ hYP : R ⊔ I ≤ normalizer (I.pCoreIn 2 : Set G),
    ∃ hYU : R ⊔ I ≤ normalizer (U : Set G),
      ∃ hUP : (U.subgroupOf (I.pCoreIn 2)).Normal, letI := hUP
        ∃ hBU : (U.subgroupOf (V ⊓ I.pCoreIn 2)).Normal, letI := hBU
          ∃ hP : IsElementaryAbelian 2 (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)), letI := hP
            ∃ hB : IsElementaryAbelian 2 ((V ⊓ I.pCoreIn 2 : Subgroup G) ⧸ U.subgroupOf (V ⊓ I.pCoreIn 2)), letI := hB
              ∃ eI : (I ⧸ pCore 2 I) ≃* InvertedCubicTensor.S₃,
                ∃ σ : Representation (ZMod 2) InvertedCubicTensor.S₃ (CoreSection I U),
                  ∃ τ : Representation (ZMod 2) R (IntersectionSection I V U),
                    let f := sectionAction (R ⊔ I) (I.pCoreIn 2) U hYP hYU
                    (∀ (a : I) p, σ (eI (QuotientGroup.mk' (pCore 2 I) a)) p =
                      Additive.ofMul (f (inclusion le_sup_right a) p.toMul)) ∧
                    (∀ (a : R) b, intersectionInclusion I V U (τ a b) =
                      Additive.ofMul (f (inclusion le_sup_left a) (intersectionInclusion I V U b).toMul)) ∧
                    ∃ e : BinaryPermutation.core (Fin 3) ⊗[ZMod 2] IntersectionSection I V U ≃ₗ[ZMod 2] CoreSection I U,
                      (∀ n b, e (n ⊗ₜ[ZMod 2] b) = n.val 0 • intersectionInclusion I V U b +
                        n.val 2 • σ InvertedCubicTensor.cubic (intersectionInclusion I V U b)) ∧
                      ∀ (a : R) (b : I) z,
                        e (TensorProduct.map (BinaryPermutation.coreRepresentation (Fin 3)
                          (eI (QuotientGroup.mk' (pCore 2 I) b))) (τ a) z) =
                            Additive.ofMul (f (inclusion le_sup_left a * inclusion le_sup_right b) (e z).toMul)

/-- The quintic tensor constructs F₄ scalars on the original P/U and B₀/U.
Its pure-tensor formula and product action retain the actual quotient maps. -/
@[expose] def PairQuinticTensor (R I V U : Subgroup G) : Prop :=
  ∃ hYP : R ⊔ I ≤ normalizer (I.pCoreIn 2 : Set G),
    ∃ hYU : R ⊔ I ≤ normalizer (U : Set G),
      ∃ hUP : (U.subgroupOf (I.pCoreIn 2)).Normal, letI := hUP
        ∃ hBU : (U.subgroupOf (V ⊓ I.pCoreIn 2)).Normal, letI := hBU
          ∃ hP : IsElementaryAbelian 2 (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)), letI := hP
            ∃ hB : IsElementaryAbelian 2 ((V ⊓ I.pCoreIn 2 : Subgroup G) ⧸ U.subgroupOf (V ⊓ I.pCoreIn 2)), letI := hB
              ∃ eI : (I ⧸ pCore 2 I) ≃* DihedralGroup 5,
                ∃ σ : Representation (ZMod 2) (DihedralGroup 5) (CoreSection I U),
                  let f := sectionAction (R ⊔ I) (I.pCoreIn 2) U hYP hYU
                  (∀ (a : I) p, σ (eI (QuotientGroup.mk' (pCore 2 I) a)) p =
                    Additive.ofMul (f (inclusion le_sup_right a) p.toMul)) ∧
                  ∃ hf : ∀ p, σ InvertedFiveTensor.rot p = p → p = 0,
                    letI := InvertedFiveTensor.fieldModule σ hf
                    ∃ mB : Module InvertedFiveTensor.F (IntersectionSection I V U), letI := mB
                      IsScalarTower (ZMod 2) InvertedFiveTensor.F (IntersectionSection I V U) ∧
                      ∃ τ : Representation InvertedFiveTensor.F R (IntersectionSection I V U),
                        (∀ (a : R) b, intersectionInclusion I V U (τ a b) =
                          Additive.ofMul (f (inclusion le_sup_left a) (intersectionInclusion I V U b).toMul)) ∧
                        ∃ e : (Fin 2 → InvertedFiveTensor.F) ⊗[InvertedFiveTensor.F] IntersectionSection I V U
                            ≃ₗ[InvertedFiveTensor.F] CoreSection I U,
                          (∀ n b, e (n ⊗ₜ[InvertedFiveTensor.F] b) = n 0 • intersectionInclusion I V U b +
                            n 1 • σ InvertedFiveTensor.rot (intersectionInclusion I V U b)) ∧
                          (∀ b : ↥(V ⊓ I.pCoreIn 2),
                            e (![1,0] ⊗ₜ[InvertedFiveTensor.F]
                              Additive.ofMul (QuotientGroup.mk' (U.subgroupOf (V ⊓ I.pCoreIn 2)) b)) =
                                Additive.ofMul (QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2)) ⟨b,b.property.2⟩)) ∧
                          ∀ (a : R) (b : I) z,
                            e (TensorProduct.map (InvertedFiveTensor.natural
                              (eI (QuotientGroup.mk' (pCore 2 I) b))) (τ a) z) =
                                Additive.ofMul (f (inclusion le_sup_left a * inclusion le_sup_right b) (e z).toMul)

/-- The preparation discharges every additional premise of the marked cubic tensor. -/
theorem pair_cubic_tensor {R I V U : Subgroup G}
    (h : PairTensorPreparation R I V U InvertedCubicTensor.cubic InvertedCubicTensor.inverter) :
    PairCubicTensor R I V U := by
  obtain ⟨hYP,hYU,hUP,hBU,hP,hB,eI,σ,κ,τ,hσ,hκ,hc,he,hf,hfix,hd⟩ := h
  let := hUP
  let := hBU
  let := hP
  let := hB
  obtain ⟨e,ht,heq⟩ := cubic_marked_tensor I V U σ κ τ hc he hf hfix hd
  refine ⟨hYP,hYU,hUP,hBU,hP,hB,eI,σ,τ,hσ,?_,e,ht,?_⟩
  · intro a b
    rw [he,hκ]
  · intro a b z
    rw [heq,hκ,hσ,map_mul]
    rfl

/-- The preparation constructs the field-four scalars and discharges every additional premise of the marked quintic tensor. -/
theorem pair_quintic_tensor {R I V U : Subgroup G}
    (h : PairTensorPreparation R I V U InvertedFiveTensor.rot InvertedFiveTensor.invt) :
    PairQuinticTensor R I V U := by
  obtain ⟨hYP,hYU,hUP,hBU,hP,hB,eI,σ,κ,τ,hσ,hκ,hc,he,hf,hfix,hd⟩ := h
  let := hUP
  let := hBU
  let := hP
  let := hB
  obtain ⟨mB,hT,τF,hτ,e,ht,hm,heq⟩ := dihedral_marked_tensor I V U σ κ τ hc he hf hfix hd
  let := InvertedFiveTensor.fieldModule σ hf
  let := mB
  refine ⟨hYP,hYU,hUP,hBU,hP,hB,eI,σ,hσ,hf,mB,hT,τF,?_,e,ht,hm,?_⟩
  · intro a b
    rw [hτ,he,hκ]
  · intro a b z
    rw [heq,hκ,hσ,map_mul]
    rfl

/-- Both source-specific tensor rows are constructed on the original selected P/U.
The cubic row uses F₂; the quintic row constructs F₄ on the same quotients. -/
theorem selected_one_source_tensor
    {V H M I R U : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 1 i S)
    (hp : PairProductAction R I V U) (hm : PairMultiplicityAction R I V U i)
    (hcomm : ⁅R,I⁆ ≤ R.pCoreIn 2)
    (hc : Nonempty ((I ⧸ pCore 2 I) ≃* PSL(2,ZMod 2)) ∨
      Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup 5)) :
    PairCubicTensor R I V U ∨ PairQuinticTensor R I V U := by
  rcases selected_one_tensor_preparation s hp hm hcomm hc with h | h
  · exact Or.inl (pair_cubic_tensor h)
  · exact Or.inr (pair_quintic_tensor h)

end
end CFSG.Quasithin.Chapter8.Section02.HermitianSource
