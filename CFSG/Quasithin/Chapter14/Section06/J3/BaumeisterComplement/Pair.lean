module
public import CFSG.Quasithin.Chapter14.Section06.J3.BaumeisterComplement.ProjectivePair
public import CFSG.Quasithin.Chapter14.Section06.J3.BaumeisterComplement.FieldSplitting
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.Pair

/-!
# The literal second parabolic is S₃ × D₁₀

Lift the outer involution centralizing the quotient D₁₀ through the
already proved complement to the same cubic kernel. Coprime orders remove
any cubic correction on the original dihedral factor of L₁₂. The lifted
involution and the cubic generate S₃, commuting with that D₁₀. Their
trivial intersection and the proved order sixty identify the full literal
normalizer N_G(L₁₂), without replacing the field embedding or quotient.

This proves Baumeister, *A geometry for groups of J₃-type* (2007),
Lemma 2.5, p.496. The final assembly discharges the pair and overlap inputs
of OriginalMarking; its remaining triangle premise is exactly Lemma 2.6.
`PairApplication` applies the result to both original terminal planes.
-/

open Subgroup
namespace CFSG.Quasithin.Janko23.J3Recognition.Ambient.BaumeisterComplement
public noncomputable section
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.SingerField hiding normalizer
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics
variable {G : Type*} [Group G]

private theorem ten_fiber_unique (s c d : G) (hs : orderOf s = 3)
    (hd : Commute s d) (hc10 : c^10 = 1) (hd10 : d^10 = 1)
    (hcd : c / d ∈ zpowers s) : c = d := by
  have hkd : Commute (c/d) d := by
    obtain ⟨n,hn⟩ := mem_zpowers_iff.mp hcd
    rw [← hn]
    exact hd.zpow_left n
  have hcomm : Commute c d := by
    have hh := hkd.mul_left (Commute.refl d)
    simpa only [div_mul_cancel] using hh
  have h10 : (c/d)^10 = 1 := by
    rw [div_eq_mul_inv,(hcomm.inv_right).mul_pow,hc10,inv_pow,hd10,inv_one,mul_one]
  have h3 : orderOf (c/d) ∣ 3 := by
    simpa only [Nat.card_zpowers,hs] using (zpowers s).orderOf_dvd_natCard hcd
  have h1 := Nat.dvd_gcd h3 (orderOf_dvd_of_pow_eq_one h10)
  have he : c/d = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  exact div_eq_one.mp he

/-- Involutions outside the cubic centralizer invert its generator. -/
private theorem cubic_inversion [Finite G] (s r : G) (hs : orderOf s = 3)
    (hr : r ∈ normalizer (zpowers s : Set G))
    (hrC : r ∉ centralizer ({s} : Set G)) : r*s*r⁻¹=s⁻¹ := by
  classical
  have hm : r*s*r⁻¹ ∈ zpowers s := (mem_normalizer_iff.mp hr s).mp (mem_zpowers s)
  rw [mem_zpowers_iff_mem_range_orderOf,hs] at hm
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hm
  have hn3 : n < 3 := Finset.mem_range.mp hn
  interval_cases n
  · have he1 : s=1 := (MulAut.conj r).injective (by simpa using he.symm)
    simp [he1] at hs
  · exact (hrC (mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp (by simpa using he.symm)))).elim
  · exact he.symm.trans (eq_inv_of_mul_eq_one_left (by
      rw [← pow_succ]
      simpa only [hs] using pow_orderOf_eq_one s))

/-- The literal dihedral factor of the fixed field complement. -/
def dihedralFactor (j : Model →* G) (hj : Function.Injective j) :
    DihedralGroup 5 →* G :=
  (overlap j).subtype.comp ((overlapEquiv j hj).symm.toMonoidHom.comp
    (MonoidHom.inr (Multiplicative (ZMod 3)) (DihedralGroup 5)))

theorem dihedralFactor_injective (j : Model →* G) (hj : Function.Injective j) :
    Function.Injective (dihedralFactor j hj) :=
  (overlap j).subtype_injective.comp ((overlapEquiv j hj).symm.injective.comp
    (fun _ _ hh => congrArg Prod.snd hh))

theorem dihedralFactor_mem (j : Model →* G) (hj : Function.Injective j)
    (d : DihedralGroup 5) : dihedralFactor j hj d ∈ overlap j :=
  ((overlapEquiv j hj).symm (1,d)).property

variable [Finite G]

/-- The literal pair normalizer contains an involution inverting the same cubic
and centralizing the specified dihedral factor of L₁₂. -/
theorem field_pair_actor {D : LocalSixteen.Seed G}
    (P : LocalSixteen.ReturningPair D) (hc : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R)
    (j : Model →* G) (hj : Function.Injective j) :
    ∃ r : G, r ∈ Seventeen.second (overlap j) ∧ orderOf r = 2 ∧
      r * j cubic * r⁻¹ = (j cubic)⁻¹ ∧
      ∀ d : DihedralGroup 5, Commute r (dihedralFactor j hj d) := by
  let s := j cubic
  let N := normalizer (zpowers s : Set G)
  let q := QuotientGroup.mk' (cubicNormalizerKernel s)
  let B := (overlap j).subgroupOf N
  let L := (cubicQuotientInclusion s).range
  have hs : orderOf s = 3 := (orderOf_injective j hj cubic).trans cubic_order
  obtain ⟨e6⟩ := field_cubic_quotient (z := D.z) D.localType hc j hj
  obtain ⟨M,eQ,eM,hM,heM⟩ := field_cubic_normalizer_complement P hc A hA hAR j hj
  have hk : q.ker ≤ B := by
    rw [QuotientGroup.ker_mk']
    exact fun _ hx => cubic_le_overlap j hx
  have hB : Nat.card B = 30 :=
    (Nat.card_congr (subgroupOfEquivOfLe
      ((overlap j).le_normalizer.trans (overlap_normalizer_le_cubic j hj))).toEquiv).trans
      (overlap_card j hj)
  have him : Nat.card (B.map q) = 10 := by
    have hh := (q.ker.subgroupOf B).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hk).toEquiv,
      show Nat.card q.ker = 3 by rw [QuotientGroup.ker_mk',cubicNormalizerKernel_card s hs],hB] at hh
    change q.ker.relIndex B * 3 = 30 at hh
    rw [relIndex_ker] at hh
    omega
  have hBL : B.map q ≤ L := by
    rintro _ ⟨b,hb,rfl⟩
    exact (cubicQuotientInclusion_preimage s b).mpr (overlap_le_cubic_centralizer j hb)
  obtain ⟨a,ha,haout,hBa⟩ := ten_actor_of_projective L (B.map q)
    (cubicQuotientInclusion_index (z := D.z) D.localType hc s hs e6) hBL him eQ
  let rM : M := eM.symm (eQ a)
  let rN : N := rM.val
  have hqr : q rN = a := eQ.injective ((heM rM).symm.trans (eM.apply_symm_apply _))
  have hr : orderOf (rN : G) = 2 := (orderOf_coe rN).trans
    ((orderOf_coe rM).trans ((eM.orderOf_eq rM).symm.trans (by simp [rM,ha])))
  have hrC : (rN : G) ∉ centralizer ({s} : Set G) := by
    intro hh
    apply haout
    rw [← hqr]
    exact (cubicQuotientInclusion_preimage s rN).mpr hh
  have hnorm : a ∈ normalizer (B.map q : Set _) := by
    apply Subgroup.centralizer_le_normalizer _
    exact mem_centralizer_iff.mpr (fun x hx => mem_centralizer_singleton_iff.mp (hBa hx))
  have hrL : (rN : G) ∈ Seventeen.second (overlap j) := by
    have hh : rN ∈ (normalizer (B.map q : Set _)).comap q := by
      change q rN ∈ normalizer (B.map q : Set _)
      rw [hqr]
      exact hnorm
    rw [field_pair_quotient_preimage j hj] at hh
    exact hh
  refine ⟨rN,hrL,hr,cubic_inversion s rN hs rN.property hrC,?_⟩
  intro d
  let dN : N := ⟨dihedralFactor j hj d,
    (overlap_normalizer_le_cubic j hj) ((overlap j).le_normalizer (dihedralFactor_mem j hj d))⟩
  have hdB : dN ∈ B := dihedralFactor_mem j hj d
  have hcomm : Commute (q dN) (q rN) := by
    rw [hqr]
    exact mem_centralizer_singleton_iff.mp (hBa (mem_map_of_mem q hdB))
  have hqeq : q (rN * dN * rN⁻¹) = q dN := by
    rw [map_mul,map_mul,map_inv,← hcomm.eq,mul_inv_cancel_right]
  have hmem : (rN * dN * rN⁻¹) / dN ∈ cubicNormalizerKernel s :=
    QuotientGroup.eq_iff_div_mem.mp hqeq
  have hd10 : (dihedralFactor j hj d)^10 = 1 := by
    rw [← map_pow,show d^10=1 from orderOf_dvd_iff_pow_eq_one.mp (by simpa only [DihedralGroup.nat_card] using orderOf_dvd_natCard d),map_one]
  have hconj : (rN : G) * dihedralFactor j hj d * (rN : G)⁻¹ = dihedralFactor j hj d :=
    ten_fiber_unique s _ _ hs
      ((mem_centralizer_singleton_iff.mp (overlap_le_cubic_centralizer j
        (dihedralFactor_mem j hj d))).symm)
      (by simpa using congrArg (MulAut.conj (rN : G)) hd10) hd10 hmem
  exact mul_inv_eq_iff_eq_mul.mp hconj
/-- Baumeister 2.5 on the literal normalizer of the original field overlap. -/
theorem field_pair_equiv {D : LocalSixteen.Seed G}
    (P : LocalSixteen.ReturningPair D) (hc : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R)
    (j : Model →* G) (hj : Function.Injective j) :
    Nonempty (Seventeen.second (overlap j) ≃* Seventeen.PairGroup) := by
  obtain ⟨r,hrL,hr2,hinv,hrd⟩ := field_pair_actor P hc A hA hAR j hj
  let s := j cubic
  let C := zpowers s
  let S := C ⊔ zpowers r
  let d := dihedralFactor j hj
  let E := d.range
  have hs : orderOf s = 3 := (orderOf_injective j hj cubic).trans cubic_order
  have hsd (x : DihedralGroup 5) : Commute s (d x) :=
    (mem_centralizer_singleton_iff.mp (overlap_le_cubic_centralizer j
      (dihedralFactor_mem j hj x))).symm
  have hrout : r ∉ C := by
    intro hh
    obtain ⟨n,hn⟩ := mem_zpowers_iff.mp hh
    have hsr : Commute r s := hn ▸ (Commute.refl s).zpow_left n
    have he : s=s⁻¹ := by rw [hsr.eq,mul_inv_cancel_right] at hinv; exact hinv
    have hh2 : s^2=1 := by
      rw [pow_two]
      nth_rw 1 [he]
      exact inv_mul_cancel s
    have hh := orderOf_dvd_of_pow_eq_one hh2
    norm_num [hs] at hh
  have hrpow : r^2=1 := hr2 ▸ pow_orderOf_eq_one r
  have hinvC (x : G) (hx : x ∈ C) : r*x*r⁻¹=x⁻¹ := by
    obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hx
    change (MulAut.conj r) (s^n) = (s^n)⁻¹
    rw [map_zpow,show (MulAut.conj r) s = s⁻¹ from hinv,inv_zpow]
  obtain ⟨eS⟩ := nonempty_mulEquiv_dihedralGroup_of_cyclic_inverted C r inferInstance hrpow hrout hinvC
  have hc3 : Nat.card C = 3 := (Nat.card_zpowers s).trans hs
  have eS3 : Nonempty (S ≃* DihedralGroup 3) := by
    have he : Nonempty (S ≃* DihedralGroup (Nat.card C)) := ⟨eS⟩
    rw [hc3] at he
    exact he
  obtain ⟨eS3⟩ := eS3
  let eE : E ≃* DihedralGroup 5 := (MonoidHom.ofInjective (dihedralFactor_injective j hj)).symm
  have hSE : S ≤ centralizer (E : Set G) := by
    apply sup_le <;> apply zpowers_le.mpr <;> apply mem_centralizer_iff.mpr
    · rintro _ ⟨x,rfl⟩
      exact (hsd x).symm.eq
    · rintro _ ⟨x,rfl⟩
      exact (hrd x).symm.eq
  have hdis : Disjoint S E := by
    apply disjoint_def.mpr
    intro x hxS hxE
    obtain ⟨x0,rfl⟩ := hxE
    have hz : x0 ∈ center (DihedralGroup 5) := by
      apply mem_center_iff.mpr
      intro y
      apply dihedralFactor_injective j hj
      rw [map_mul,map_mul]
      exact hSE hxS (d y) ⟨y,rfl⟩
    rw [DihedralGroup.center_eq_bot_of_odd_ne_one (by decide) (by decide),mem_bot] at hz
    simp [hz]
  obtain ⟨eProd,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting S E hdis hSE
  have hle : S ⊔ E ≤ Seventeen.second (overlap j) := by
    apply sup_le
    · exact sup_le ((cubic_le_overlap j).trans (overlap j).le_normalizer)
        (zpowers_le.mpr hrL)
    · rintro _ ⟨x,rfl⟩
      exact (overlap j).le_normalizer (dihedralFactor_mem j hj x)
  have hcard : Nat.card (S ⊔ E : Subgroup G) = 60 := by
    rw [← Nat.card_congr eProd.toEquiv,Nat.card_prod,
      Nat.card_congr eS3.toEquiv,Nat.card_congr eE.toEquiv,
      DihedralGroup.nat_card,DihedralGroup.nat_card]
  have heq : S ⊔ E = Seventeen.second (overlap j) := eq_of_le_of_card_ge hle (by
    rw [hcard,field_pair_card (z := D.z) D.localType hc j hj])
  exact ⟨(MulEquiv.subgroupCongr heq.symm).trans (eProd.symm.trans
    (MulEquiv.prodCongr
      (eS3.trans Seventeen.ModelAmalgam.CyclicCoordinates.trianglePermEquiv) eE))⟩

/-- All literal intersection models are now discharged except the third
parabolic itself. The retained premise is precisely Baumeister 2.6. -/
noncomputable def field_original_marking_of_triangle {D : LocalSixteen.Seed G}
    (P : LocalSixteen.ReturningPair D) (hc : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R)
    (j : Model →* G) (hj : Function.Injective j)
    (e3 : Seventeen.third j.range (overlap j) (j fieldElement) ≃* Seventeen.TriangleGroup) :
    Seventeen.OriginalMarking j.range (overlap j) (j fieldElement) :=
  BaumeisterParabolics.original_marking_of_pair_triangle j hj
    (Classical.choice (field_pair_equiv P hc A hA hAR j hj)) e3

end
end CFSG.Quasithin.Janko23.J3Recognition.Ambient.BaumeisterComplement
