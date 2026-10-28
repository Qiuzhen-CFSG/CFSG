module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.CentralCoverCore
public import Theory.GroupTheory.Commutator.CentralExtensionPairing

/-!
# Abelian cores in central covers of the HS normalizer

Commutators of lifts of the concrete C₄³ core define an alternating additive
pairing into the covering center. The original order-seven normalizer word
acts on the three fourth-root generators with columns (3,1,2), (2,1,1),
(3,2,2) over Z/4. Its invariance gives three equations forcing every pairing
coefficient to vanish. Thus the full core preimage is abelian, with no
assumption on the size of the central covering kernel.

The word and permutation certificates below are reused from
`Concrete/Action.lean`; the additional root-action certificate checks only
three permutations on 100 letters. The original coordinates and source
marking are preserved. This supplies the central-cover step in the HS
exclusion of Aschbacher--Smith 15.1.22, printed p.1100 of refs/quasithin.pdf;
the concrete local structure is GLS3 Table 5.3m.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace Sporadic.LeechRelated.HS.BlockNormalizer.CentralCoverAbelian
open EvenLocalCandidates EvenLocalCandidates.SylowCatalogueData CoreGeometry
private def aMap (i : Fin 100) : Fin 100 :=
  ⟨(3838723257997737152524899170929934947202430479706805946343499194866484018493252410823467695167791695081756400242119444822672887673306494670569625348565932927976040876586221373003419306020058828375383269105214395 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def aInvMap (i : Fin 100) : Fin 100 :=
  ⟨(3838723257997737152524899170929934947202430479706805946343499194866484018493252410823467695167791695081756400242119444822672887673306494670569625348565932927976040876586221373003419306020058828375383269105214395 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem aLeft : ∀ i, aInvMap (aMap i) = i := by
  apply allFin
  decide +kernel

private def aPerm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm aMap aInvMap aLeft
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin aLeft)

private theorem aPerm_eq_generator : aPerm = generatorA := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private def a : Carrier := ⟨aPerm, aPerm_eq_generator.symm ▸
  Subgroup.subset_closure (by simp)⟩

private def bMap (i : Fin 100) : Fin 100 :=
  ⟨(1584088533044622539624716012360915100311113938083754946662587072801676726706164344372852891441442777957300990173557581617101002762039959730741693432191260900145476108926406488416286385789713123784992907581461166 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def bInvMap (i : Fin 100) : Fin 100 :=
  ⟨(852881488533531112336995551220226122361210863663080587750664607485875722147280441807057556633165462885474069200795003754517913050689892735891088239319177696223676845175972313037682728934689958756512102884170325 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem bLeft : ∀ i, bInvMap (bMap i) = i := by
  apply allFin
  decide +kernel

private def bPerm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm bMap bInvMap bLeft
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin bLeft)

private theorem bPerm_eq_generator : bPerm = generatorB := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private def b : Carrier := ⟨bPerm, bPerm_eq_generator.symm ▸
  Subgroup.subset_closure (by simp)⟩

private def sevenMap (i : Fin 100) : Fin 100 :=
  ⟨(1136742900769022640185733578659955024891157537247565748203960254312220454731536736652853152609354060788253494270830305769461046276601535240770691501804434786843916798425948482847283264758968354154974714668253376 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def sevenInvMap (i : Fin 100) : Fin 100 :=
  ⟨(1603845743149177324658917020195331319918192695436596618294581098675217573189454653125713458098507917946884519913902583349450934598826787072159804240440370395088972910559834414883069951722061996889481449984458882 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem sevenLeft : ∀ i, sevenInvMap (sevenMap i) = i := by
  apply allFin
  decide +kernel

private def sevenPerm : Equiv.Perm (Fin 100) :=
  tablePerm sevenMap sevenInvMap sevenLeft (rightInverse_of_leftInverse_fin sevenLeft)

private def sevenWord : Carrier := b⁻¹ * a⁻¹ * (b ^ 2) * a⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ * b⁻¹ * a * b⁻¹ * a * (b ^ 2) * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ * b⁻¹ * a⁻¹ * (b⁻¹ ^ 2) * a * b⁻¹ * a * (b⁻¹ ^ 2) * a * (b ^ 2) * a * (b⁻¹ ^ 2) * a * (b⁻¹ ^ 3) * a⁻¹ * b * a⁻¹ * (b ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b⁻¹ ^ 4) * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * (b⁻¹ ^ 2)

private theorem sevenPerm_eq_word : sevenPerm = (sevenWord : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private def seven : Carrier := ⟨sevenPerm, by
  rw [sevenPerm_eq_word]
  exact sevenWord.property⟩

private theorem seven_conjugation (j : Fin 3) :
    seven * elementaryGenerator j * seven⁻¹ = small (![3, 6, 1] j) := by
  have h : ∀ (j : Fin 3) (x : Fin 100),
      ((seven * elementaryGenerator j * seven⁻¹ : Carrier) : Equiv.Perm (Fin 100)) x =
        (small (![3, 6, 1] j) : Equiv.Perm (Fin 100)) x := by
    apply allFin₂
    decide +kernel
  exact Subtype.ext (Equiv.ext (h j))

private theorem seven_mem : seven ∈ baseNormalizer := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply Subgroup.eq_of_le_of_card_ge
  · rw [elementary, MonoidHom.map_closure]
    apply (closure_le _).mpr
    rintro x ⟨y, ⟨j, hj, rfl⟩, rfl⟩
    change seven * elementaryGenerator j * seven⁻¹ ∈ elementary 2
    rw [seven_conjugation]
    exact small_mem_elementary _ 2 (![3, 6, 1] j : Fin 8).isLt
  · exact le_of_eq (Nat.card_congr ((MulAut.conj seven).subgroupMap
      baseElementary).toEquiv)


private def v (i : Fin 3) : Fin 3 → ZMod 4 := Pi.single i 1

private def u : Multiplicative (Fin 3 → ZMod 4) →* baseNormalizer :=
  (pCore 2 baseNormalizer).subtype.comp coreCoordinates

private theorem u_basis (i : Fin 3) : (u (.ofAdd (v i)) : Carrier) = root i := by
  rw [show (u (.ofAdd (v i)) : Carrier) = ((coreCoordinates (.ofAdd (v i))).val : Carrier) from rfl,
    coreCoordinates_apply]
  fin_cases i
  · change root 0 ^ 1 * root 1 ^ 0 * root 2 ^ 0 = root 0
    simp only [pow_one,pow_zero,mul_one]
  · change root 0 ^ 0 * root 1 ^ 1 * root 2 ^ 0 = root 1
    simp only [pow_one,pow_zero,mul_one,one_mul]
  · change root 0 ^ 0 * root 1 ^ 0 * root 2 ^ 1 = root 2
    simp only [pow_one,pow_zero,one_mul]

private theorem seven_root (i : Fin 3) :
    seven * root i * seven⁻¹ =
      ![root 0 ^ 3 * root 1 * root 2 ^ 2,
        root 0 ^ 2 * root 1 * root 2,
        root 0 ^ 3 * root 1 ^ 2 * root 2 ^ 2] i := by
  have h : ∀ (i : Fin 3) (x : Fin 100),
      ((seven * root i * seven⁻¹ : Carrier) : Equiv.Perm (Fin 100)) x =
      ((![root 0 ^ 3 * root 1 * root 2 ^ 2,
        root 0 ^ 2 * root 1 * root 2,
        root 0 ^ 3 * root 1 ^ 2 * root 2 ^ 2] i : Carrier) : Equiv.Perm (Fin 100)) x := by
    apply allFin₂
    decide +kernel
  exact Subtype.ext (Equiv.ext (h i))

private def imageVector : Fin 3 → (Fin 3 → ZMod 4) :=
  ![3 • v 0 + v 1 + 2 • v 2, 2 • v 0 + v 1 + v 2, 3 • v 0 + 2 • v 1 + 2 • v 2]

private theorem seven_u (i : Fin 3) :
    (⟨seven,seven_mem⟩ : baseNormalizer) * u (.ofAdd (v i)) *
      (⟨seven,seven_mem⟩ : baseNormalizer)⁻¹ = u (.ofAdd (imageVector i)) := by
  apply Subtype.ext
  change seven * (u (.ofAdd (v i)) : Carrier) * seven⁻¹ = _
  rw [u_basis,seven_root]
  change _ = ((coreCoordinates (.ofAdd (imageVector i))).val : Carrier)
  rw [coreCoordinates_apply]
  fin_cases i
  · change root 0 ^ 3 * root 1 * root 2 ^ 2 = root 0 ^ 3 * root 1 ^ 1 * root 2 ^ 2
    rw [pow_one]
  · change root 0 ^ 2 * root 1 * root 2 = root 0 ^ 2 * root 1 ^ 1 * root 2 ^ 1
    simp only [pow_one]
  · rfl

private theorem vector_expand (x : Fin 3 → ZMod 4) :
    x = (x 0).val • v 0 + (x 1).val • v 1 + (x 2).val • v 2 := by
  funext i
  simp only [Pi.add_apply,Pi.smul_apply]
  fin_cases i <;> simp [v,nsmul_eq_mul]

private theorem invariant_pairing_zero {A : Type*} [AddCommGroup A]
    (B : (Fin 3 → ZMod 4) →+ (Fin 3 → ZMod 4) →+ A)
    (halt : ∀ x, B x x = 0)
    (hinv : ∀ i j, B (imageVector i) (imageVector j) = B (v i) (v j)) :
    ∀ x y, B x y = 0 := by
  have hskew (x y) : B y x = - B x y := by
    have hh := halt (x+y)
    simp only [map_add,AddMonoidHom.add_apply,halt,zero_add,add_zero] at hh
    exact eq_neg_of_add_eq_zero_left hh
  have h4 : 4 • B (v 0) (v 2) = 0 := by
    rw [←map_nsmul]
    have he : 4 • v 2 = 0 := by
      funext i
      change (4 : ℕ) • v 2 i = 0
      rw [nsmul_eq_mul]
      change (0 : ZMod 4) * v 2 i = 0
      exact zero_mul _
    rw [he,map_zero]
  have h01 := hinv 0 1
  have h02 := hinv 0 2
  have h12 := hinv 1 2
  change B (3 • v 0 + v 1 + 2 • v 2) (2 • v 0 + v 1 + v 2) = B (v 0) (v 1) at h01
  change B (3 • v 0 + v 1 + 2 • v 2) (3 • v 0 + 2 • v 1 + 2 • v 2) = B (v 0) (v 2) at h02
  change B (2 • v 0 + v 1 + v 2) (3 • v 0 + 2 • v 1 + 2 • v 2) = B (v 1) (v 2) at h12
  simp only [map_add,map_nsmul,AddMonoidHom.add_apply,AddMonoidHom.smul_apply,halt,
    hskew (v 0) (v 1),hskew (v 0) (v 2),hskew (v 1) (v 2)] at h01 h02 h12
  have he01 : B (v 0) (v 1) - B (v 0) (v 2) - B (v 1) (v 2) = B (v 0) (v 1) := by
    calc
      _ = _ := by abel
      _ = _ := h01
  have he02 : 3 • B (v 0) (v 1) - 2 • B (v 1) (v 2) = B (v 0) (v 2) := by
    calc
      _ = _ := by abel
      _ = _ := h02
  have he12 : B (v 0) (v 1) + B (v 0) (v 2) = B (v 1) (v 2) := by
    calc
      _ = _ := by abel
      _ = _ := h12
  have hw : B (v 1) (v 2) = -B (v 0) (v 2) := by
    apply eq_neg_of_add_eq_zero_left
    calc
      _ = B (v 0) (v 1) - (B (v 0) (v 1) - B (v 0) (v 2) - B (v 1) (v 2)) := by abel
      _ = 0 := by rw [he01,sub_self]
  have hu : B (v 0) (v 1) = -(2 • B (v 0) (v 2)) := by
    calc
      _ = (B (v 0) (v 1) + B (v 0) (v 2)) - B (v 0) (v 2) := by abel
      _ = _ := by rw [he12,hw]; abel
  have hv : B (v 0) (v 2) = 0 := by
    calc
      _ = 3 • B (v 0) (v 1) - 2 • B (v 1) (v 2) := he02.symm
      _ = -(4 • B (v 0) (v 2)) := by rw [hu,hw]; abel
      _ = 0 := by rw [h4,neg_zero]
  have hu0 : B (v 0) (v 1) = 0 := by rw [hu,hv,smul_zero,neg_zero]
  have hw0 : B (v 1) (v 2) = 0 := by rw [hw,hv,neg_zero]
  have hall (i j : Fin 3) : B (v i) (v j) = 0 := by
    fin_cases i <;> fin_cases j
    · exact halt _
    · exact hu0
    · exact hv
    · exact (hskew (v 0) (v 1)).trans (by rw [hu0,neg_zero])
    · exact halt _
    · exact hw0
    · exact (hskew (v 0) (v 2)).trans (by rw [hv,neg_zero])
    · exact (hskew (v 1) (v 2)).trans (by rw [hw0,neg_zero])
    · exact halt _
  intro x y
  rw [vector_expand x,vector_expand y]
  simp only [map_add,map_nsmul,AddMonoidHom.add_apply,AddMonoidHom.smul_apply,
    hall,smul_zero,add_zero]



/-- The full preimage of the concrete C₄³ core in any central extension of
its normalizer is abelian. The order-seven action kills the alternating
commutator pairing, including every possible central covering kernel. -/
theorem core_preimage_abelian {X : Type*} [Group X]
    (f : X →* baseNormalizer) (hf : Function.Surjective f)
    (hz : f.ker ≤ center X) : IsMulCommutative ((pCore 2 baseNormalizer).comap f) := by
  obtain ⟨B,hB⟩ := CentralExtension.exists_lift_commutator_pairing f hf hz u
  have halt (x) : B x x = 0 := by
    obtain ⟨a,ha⟩ := hf (u (.ofAdd x))
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((B x x).toMul : X) = 1
    simpa only [commutatorElement_self] using hB x x a a ha ha
  have hinv (i j : Fin 3) : B (imageVector i) (imageVector j) = B (v i) (v j) := by
    obtain ⟨a,ha⟩ := hf (u (.ofAdd (v i)))
    obtain ⟨b,hb⟩ := hf (u (.ofAdd (v j)))
    obtain ⟨m,hm⟩ := hf (⟨seven,seven_mem⟩ : baseNormalizer)
    have hai : f (m*a*m⁻¹) = u (.ofAdd (imageVector i)) := by
      rw [map_mul,map_mul,map_inv,hm,ha,seven_u]
    have hbj : f (m*b*m⁻¹) = u (.ofAdd (imageVector j)) := by
      rw [map_mul,map_mul,map_inv,hm,hb,seven_u]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hB _ _ _ _ hai hbj,←conjugate_commutatorElement,←hB _ _ _ _ ha hb]
    rw [mem_center_iff.mp (B (v i) (v j)).toMul.property m,mul_inv_cancel_right]
  have hzero := invariant_pairing_zero B halt hinv
  apply IsMulCommutative.of_comm
  intro a b
  obtain ⟨x,hx⟩ := coreCoordinates_bijective.2 (⟨f a,a.property⟩ : pCore 2 baseNormalizer)
  obtain ⟨y,hy⟩ := coreCoordinates_bijective.2 (⟨f b,b.property⟩ : pCore 2 baseNormalizer)
  have ha : f a = u x := (congrArg Subtype.val hx).symm
  have hb : f b = u y := (congrArg Subtype.val hy).symm
  apply Subtype.ext
  apply commutatorElement_eq_one_iff_mul_comm.mp
  have hh := hB x.toAdd y.toAdd a b ha hb
  rw [hzero] at hh
  exact hh.symm

/-- A central two-kernel covering retains an abelian intrinsic two-core. -/
theorem core_abelian {X : Type*} [Group X] [Finite X]
    (f : X →* baseNormalizer) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (hz : f.ker ≤ center X) : IsMulCommutative (pCore 2 X) := by
  rw [←f.comap_pCore_of_ker_isPGroup hf hk]
  exact core_preimage_abelian f hf hz

end Sporadic.LeechRelated.HS.BlockNormalizer.CentralCoverAbelian
