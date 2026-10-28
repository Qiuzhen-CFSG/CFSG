module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoOuterQuotients
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.NormalizerAction.RadicalAction
public import Theory.GroupTheory.CoprimeSubgroupCentralizer

/-!
# An actual outer involution above the reduced Hall–Janko pair

A checked cubic in the concrete second endpoint is fixed-point-free on its
order-64 core and is inverted modulo the core by a marked inner involution.
Transport retains the actual reduced inclusion and the unchanged original
core. Under the marked S₃ × S₃ quotient, the cubic lies in the first factor.
Coprime centralizer lifting therefore lifts a transposition of the second
factor. Its square is a core element fixed by the cubic, so is the identity.
Sylow conjugacy puts an outer involution in the same original S outside S₀.

The finite checks use the existing ATLAS J2G1-p100B0 tables in PairNormalizer;
only the 64-element radical and one inversion identity are checked here.
The reduced comparison remains an actual ParabolicEquiv input. This supplies
an outer involution, not yet the particular source Cartan marking, its action
on all endpoint generators, or the order-12 product needed to identify
Aut(J₂). No parabolic equivalence is inferred from the quotient or order.

Source: DGS, Groups and Graphs (1985), (15.3), pp.229–231, especially the
fixed-point-free cubic in (i) and the outer-involution choice on p.230.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo
open Sporadic.LeechRelated.J2
open ExceptionalParabolics Seed PairNormalizer
open PairNormalizer.RadicalData PairNormalizer.QuotientData PairNormalizer.SylowData
open GeneratorPair.SecondOrbitCertificate

private theorem fixed_check : ∀ i : Fin 64,
    (oddTable 0 * qTable i) 0 = (qTable i * oddTable 0) 0 →
    (oddTable 0 * qTable i) 1 = (qTable i * oddTable 0) 1 → i = 0 := by
  apply allFin
  decide +kernel

private theorem cubic_core_fixed {x : Carrier} (hx : x ∈ q₂)
    (hc : oddGenerator 0 * x = x * oddGenerator 0) : x = 1 := by
  obtain ⟨i,hi⟩ := exists_qElement hx
  have hh := congrArg inclusion hc
  rw [← hi,map_mul,map_mul,oddGenerator_inclusion,qElement_inclusion] at hh
  have hi0 := fixed_check i (congrArg (fun a : Equiv.Perm (Fin 100) => a 0) hh)
    (congrArg (fun a : Equiv.Perm (Fin 100) => a 1) hh)
  subst i
  exact hi.symm

private theorem inversion_check :
    sGenTable 3 * oddTable 0 * (sGenTable 3)⁻¹ * oddTable 0 = qTable 12 := by
  decide +kernel

private theorem cubic_inverted_mod_core :
    sGenerator 3 * oddGenerator 0 * (sGenerator 3)⁻¹ * oddGenerator 0 ∈ q₂ := by
  have hh : sGenerator 3 * oddGenerator 0 * (sGenerator 3)⁻¹ * oddGenerator 0 = qElement 12 := by
    apply Sporadic.LeechRelated.J2.inclusion_injective
    rw [map_mul,map_mul,map_mul,map_inv,sGenerator_inclusion,oddGenerator_inclusion,
      qElement_inclusion]
    exact inversion_check
  rw [hh]
  exact qElement_mem _

open SuzukiContainment GreenBook
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

@[expose] def reducedCubic (j : Fin 2)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1) :
    parabolic L (reducedSylow L S) j :=
  (f.trans (MulEquiv.subgroupCongr HallJanko.j2Model_P_one)).symm
    ⟨oddGenerator 0,oddGenerator_mem_p₂ 0⟩

@[expose] def originalCubic (h : HypothesisF11 L S) (j : Fin 2)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1) :
    parabolic L S j := inclusion (reduced_parabolic_le h j) (reducedCubic j f)

/-- The chosen cubic is transported through the literal reduced inclusion. -/
theorem originalCubic_cube (h : HypothesisF11 L S) (j : Fin 2)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1) :
    originalCubic h j f ^ 3 = 1 := by
  have hh : reducedCubic j f ^ 3 = 1 := by
    apply (f.trans (MulEquiv.subgroupCongr HallJanko.j2Model_P_one)).injective
    simp only [map_pow,map_one,reducedCubic,MulEquiv.apply_symm_apply]
    exact Subtype.ext (NormalizerAction.oddGenerator_cube 0)
  simpa only [originalCubic,← map_pow,map_one] using
    congrArg (inclusion (reduced_parabolic_le h j)) hh

private def modelCubic : p₂ := ⟨oddGenerator 0,oddGenerator_mem_p₂ 0⟩

private def modelInverter : p₂ := ⟨sGenerator 3,s_le_p₂ (subset_closure ⟨3,rfl⟩)⟩

private theorem model_inversion_core : modelInverter * modelCubic * modelInverter⁻¹ * modelCubic ∈ pCore 2 p₂ := by
  rw [PairNormalizer.p₂_core_eq_q₂ SecondParabolic.l₂_core_card]
  change ((modelInverter * modelCubic * modelInverter⁻¹ * modelCubic : p₂) : Carrier) ∈ q₂
  simp only [Subgroup.coe_mul,Subgroup.coe_inv]
  exact cubic_inverted_mod_core

private theorem modelCubic_core_fixed (x : p₂) (hx : x ∈ pCore 2 p₂)
    (hc : modelCubic*x=x*modelCubic) : x=1 := by
  have hxq : (x : Carrier) ∈ q₂ := by
    rw [PairNormalizer.p₂_core_eq_q₂ SecondParabolic.l₂_core_card] at hx
    exact hx
  have hh := congrArg (fun z : p₂ => (z : Carrier)) hc
  change oddGenerator 0 * (x : Carrier) = (x : Carrier) * oddGenerator 0 at hh
  have hx1 : (x : Carrier) = 1 := cubic_core_fixed hxq hh
  exact Subtype.ext hx1

private theorem reducedCubic_core_fixed (j : Fin 2)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (x : parabolic L (reducedSylow L S) j)
    (hx : x ∈ pCore 2 (parabolic L (reducedSylow L S) j))
    (hc : reducedCubic j f*x=x*reducedCubic j f) : x=1 := by
  let g := f.trans (MulEquiv.subgroupCongr HallJanko.j2Model_P_one)
  have ha : g (reducedCubic j f) = modelCubic := g.apply_symm_apply _
  have hxg : g x ∈ pCore 2 p₂ := by
    rw [← pCore_map_iso 2 g]
    exact mem_map_of_mem _ hx
  have hcg : modelCubic * g x = g x * modelCubic := by
    have hh := congrArg g hc
    rw [map_mul,map_mul,ha] at hh
    exact hh
  exact g.injective ((modelCubic_core_fixed (g x) hxg hcg).trans g.map_one.symm)

private theorem core_fixed_transfer {Y : Type*} [Group Y]
    (P R : Subgroup Y) (hR : R ≤ P) (hQ : twoCore R = twoCore P)
    (a : R) (hf : ∀ z : R, z ∈ pCore 2 R → a*z=z*a → z=1)
    (x : P) (hx : x ∈ pCore 2 P) (hc : Subgroup.inclusion hR a * x = x * Subgroup.inclusion hR a) : x=1 := by
  have hxY : (x : Y) ∈ twoCore R := by rw [hQ]; exact mem_map_of_mem _ hx
  obtain ⟨z,hz,hzx⟩ := hxY
  change (z : Y) = (x : Y) at hzx
  have hzcomm : a*z=z*a := by
    apply Subtype.ext
    change (a : Y)*(z : Y)=(z : Y)*(a : Y)
    rw [hzx]
    exact congrArg Subtype.val hc
  exact Subtype.ext (hzx.symm.trans (congrArg Subtype.val (hf z hz hzcomm)))

/-- It fixes only the identity in the same original two-core. -/
theorem originalCubic_core_fixed (h : HypothesisF11 L S) (j : Fin 2)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (x : parabolic L S j) (hx : x ∈ pCore 2 (parabolic L S j))
    (hc : originalCubic h j f * x = x * originalCubic h j f) : x = 1 :=
  core_fixed_transfer _ _ (reduced_parabolic_le h j) (reduced_parabolic_core h j)
    (reducedCubic j f) (reducedCubic_core_fixed j f) x hx hc

/-- The marked original element has order exactly three. -/
theorem originalCubic_order (h : HypothesisF11 L S) (j : Fin 2)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1) :
    orderOf (originalCubic h j f) = 3 := by
  apply orderOf_eq_prime (originalCubic_cube h j f)
  intro ha
  have hQ : pCore 2 (parabolic L S j) = ⊥ := by
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    apply originalCubic_core_fixed h j f x hx
    rw [ha,one_mul,mul_one]
  have hc := original_second_core_card h j f
  rw [hQ,card_bot] at hc
  contradiction

/-- The fixed-point-free cubic lies in the S₃ factor, not the central odd
factor, under the reduced quotient coordinates. -/
theorem reducedCubic_second_coordinate (j : Fin 2)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1) :
    (reducedSecondQuotientEquiv j f (QuotientGroup.mk' _ (reducedCubic j f))).2 = 1 := by
  let g := f.trans (MulEquiv.subgroupCongr HallJanko.j2Model_P_one)
  let t : parabolic L (reducedSylow L S) j :=
    g.symm ⟨sGenerator 3,s_le_p₂ (subset_closure ⟨3,rfl⟩)⟩
  let a := reducedCubic j f
  have hw : t*a*t⁻¹*a ∈ pCore 2 (parabolic L (reducedSylow L S) j) := by
    rw [← mem_map_iff_mem (f := g.toMonoidHom) g.injective,pCore_map_iso]
    have ht : g t = modelInverter := g.apply_symm_apply _
    have ha : g a = modelCubic := g.apply_symm_apply _
    rw [map_mul,map_mul,map_mul,map_inv,MulEquiv.coe_toMonoidHom,ht,ha]
    exact model_inversion_core
  let r : parabolic L (reducedSylow L S) j →* Multiplicative (ZMod 3) :=
    (MonoidHom.snd _ _).comp ((reducedSecondQuotientEquiv j f).toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 (parabolic L (reducedSylow L S) j))))
  have hr : r (t*a*t⁻¹*a) = 1 := by
    change (reducedSecondQuotientEquiv j f (QuotientGroup.mk' _ (t*a*t⁻¹*a))).2 = 1
    have he : (QuotientGroup.mk' (pCore 2 (parabolic L (reducedSylow L S) j))) (t*a*t⁻¹*a) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hw
    rw [he,map_one]
    rfl
  have hr2 : r a ^ 2 = 1 := by
    rw [map_mul,map_mul,map_mul,map_inv] at hr
    exact (show ∀ u v : Multiplicative (ZMod 3), u*v*u⁻¹*v=1 → v^2=1 by decide +kernel) _ _ hr
  exact (show ∀ z : Multiplicative (ZMod 3), z ^ 2 = 1 → z = 1 by decide +kernel) _ hr2


private theorem coreQuotientMap_mk' (h : HypothesisF11 L S) (j : Fin 2)
    (x : parabolic L (reducedSylow L S) j) :
    coreQuotientMap h j (QuotientGroup.mk' (pCore 2 (parabolic L (reducedSylow L S) j)) x) =
      QuotientGroup.mk' (pCore 2 (parabolic L S j)) (Subgroup.inclusion (reduced_parabolic_le h j) x) :=
  coreQuotientMap_mk h j x

/-- A genuine outer involution in the original second parabolic, centralizing
the marked reduced cubic. Coprime centralizer lifting has trivial kernel
because this cubic fixes no nonidentity original core element. -/
theorem exists_original_outer_involution (h : HypothesisF11 L S) (i j : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (hne : S ≠ reducedSylow L S) :
    ∃ x : parabolic L S j, x ^ 2 = 1 ∧
      (x : G) ∉ parabolic L (reducedSylow L S) j ∧
      originalCubic h j f * x = x * originalCubic h j f := by
  let := h.finite_parabolic j
  let P := parabolic L S j
  let a := originalCubic h j f
  let q := QuotientGroup.mk' (pCore 2 P)
  obtain ⟨d,c,hci,hd⟩ := original_second_quotient_marked_of_ne h i j e f hne
  let v := d.toMonoidHom.comp q
  have hv : Function.Surjective v := d.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : v.ker = pCore 2 P := by
    rw [MonoidHom.ker_comp_of_injective _ _ d.injective,QuotientGroup.ker_mk']
  let D := zpowers a
  have hD : IsPGroup 3 D :=
    (IsElementaryAbelian.zpowers_of_pow_eq_one (originalCubic_cube h j f)).isPGroup 3 _
  have hcop : Nat.Coprime 3 (Nat.card v.ker) := by
    rw [hk,original_second_core_card h j f]
    decide
  let y : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) := (1,Equiv.swap 0 1)
  have ha : v a = ((reducedSecondQuotientEquiv j f (QuotientGroup.mk' _ (reducedCubic j f))).1,1) := by
    have hh := hd (QuotientGroup.mk' _ (reducedCubic j f))
    rw [reducedCubic_second_coordinate,map_one] at hh
    rw [coreQuotientMap_mk'] at hh
    exact hh
  have hy : y ∈ centralizer (D.map v : Set (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
    rw [MonoidHom.map_zpowers]
    apply mem_centralizer_iff.mpr
    intro z hz
    have hcomm : Commute (v a) y := by rw [ha]; exact Prod.ext (by simp [y]) (by simp [y])
    obtain ⟨n,rfl⟩ := hz
    exact (hcomm.zpow_left n).eq
  rw [← map_centralizer_eq_of_isPGroup_of_surjective_coprime 3 D hD v hv hcop] at hy
  obtain ⟨x,hx,hxy⟩ := hy
  have hcomm : a*x=x*a := mem_centralizer_iff.mp hx a (mem_zpowers a)
  have hsquare : x ^ 2 = 1 := by
    have hv2 : v (x ^ 2) = 1 := by rw [map_pow,hxy]; simp [y,pow_two]
    have hcore : x ^ 2 ∈ pCore 2 P := hk ▸ (show x ^ 2 ∈ v.ker from hv2)
    exact originalCubic_core_fixed h j f (x ^ 2) hcore
      ((show Commute a x from hcomm).pow_right 2).eq
  refine ⟨x,hsquare,?_,hcomm⟩
  intro hxr
  let z : parabolic L (reducedSylow L S) j := ⟨x,hxr⟩
  have hh := hd (QuotientGroup.mk' _ z)
  rw [coreQuotientMap_mk'] at hh
  have hvx : v x = ((reducedSecondQuotientEquiv j f (QuotientGroup.mk' _ z)).1,
      c (reducedSecondQuotientEquiv j f (QuotientGroup.mk' _ z)).2) := hh
  have hcubic : ∀ u : Multiplicative (ZMod 3), (c u)^3=1 := by
    intro u
    rw [←map_pow,show u^3=1 from (by decide +kernel : ∀ z : Multiplicative (ZMod 3), z^3=1) u,map_one]
  have hh3 := hcubic (reducedSecondQuotientEquiv j f (QuotientGroup.mk' _ z)).2
  have hyc := congrArg Prod.snd (hxy.symm.trans hvx)
  change Equiv.swap (0 : Fin 3) 1 = c (reducedSecondQuotientEquiv j f (QuotientGroup.mk' _ z)).2 at hyc
  rw [← hyc] at hh3
  exact (by decide : (Equiv.swap (0 : Fin 3) 1)^3 ≠ 1) hh3


/-- A proper original enlargement has an actual involution in the same
original S outside S₀. This does not impose the still-needed Cartan marking. -/
theorem exists_original_sylow_outer_involution (h : HypothesisF11 L S) (i j : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (hne : S ≠ reducedSylow L S) :
    ∃ x ∈ S, x ^ 2 = 1 ∧ x ∉ reducedSylow L S := by
  let P := parabolic L S j
  let := h.finite_parabolic j
  obtain ⟨x,hx2,hxr,_⟩ := exists_original_outer_involution h i j e f hne
  have hxP : IsPGroup 2 (zpowers x) :=
    (IsElementaryAbelian.zpowers_of_pow_eq_one hx2).isPGroup 2 _
  obtain ⟨U,hU⟩ := hxP.exists_le_sylow
  obtain ⟨T,hT⟩ := h.sylow_parabolic j
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq P U T
  let y := g*x*g⁻¹
  have hyT : y ∈ (T : Subgroup P) := by
    rw [← hg]
    change y ∈ (U : Subgroup P).map (MulAut.conj g).toMonoidHom
    exact mem_map_of_mem _ (hU (mem_zpowers x))
  have hyS : (y : G) ∈ S := hT ▸ mem_map_of_mem P.subtype hyT
  have hy2 : y ^ 2 = 1 := by
    change (MulAut.conj g x)^2=1
    rw [←map_pow,hx2,map_one]
  refine ⟨y,hyS,congrArg Subtype.val hy2,?_⟩
  intro hyR
  let N := (parabolic L (reducedSylow L S) j).subgroupOf P
  let : N.Normal := reduced_parabolic_normal h j
  have hyN : y ∈ N := (show reducedSylow L S ≤ parabolic L (reducedSylow L S) j from
    le_sup_right.trans le_sup_left) hyR
  have hxN := (inferInstance : N.Normal).conj_mem y hyN g⁻¹
  have hxN' : x ∈ N := by simpa only [y,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_inv,inv_mul_cancel,mul_one] using hxN
  exact hxr hxN'

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo
