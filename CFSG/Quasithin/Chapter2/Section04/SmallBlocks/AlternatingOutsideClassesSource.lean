module
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.OutsideClasses
public import Theory.GroupTheory.SubgroupCenterImageBound
public import Theory.GroupTheory.SylowKernelCore
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingResidualFactorsSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSignSource
/-!
# The original single-A5 outside classes

Under the original trivial-centralizer hypotheses, the actual two-core of M is
an extraspecial quaternion central product. Its full orthogonal action identifies
the original S with the factor-sign kernel in T. The intrinsic transvection and
quaternion calculations therefore give representatives y and ya for the outside
involutions, using the already selected generator z of the center.

The SL2(3) factor centralized by y and its central two-core marking are retained
for the ambient fusion argument. When ya is an involution, its fixed noncentral
involution lies in the literal original core P. All conjugators are in M.

Source: Aschbacher--Smith, (2.4.29), printed p.546.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

private theorem intrinsic_sign_kernel
    {S : Subgroup G} {T : Sylow 2 G} (c : AlternatingResidualSetup M S T)
    (hi : S.relIndex (T:Subgroup G)=2)
    (hs : S.subgroupOf M ≤ (BinaryFourPlus.factorSign.comp c.action).ker) :
    S.subgroupOf M=(c.intrinsicSylow:Subgroup M) ⊓
      (BinaryFourPlus.factorSign.comp c.action).ker := by
  let Si := S.subgroupOf M
  let Ti : Subgroup M := c.intrinsicSylow
  let K := Ti ⊓ (BinaryFourPlus.factorSign.comp c.action).ker
  have hST : Si≤Ti := by
    simpa only [Ti,c.intrinsicSylow_coe] using subgroupOf_mono M c.sylow_le
  have hSK : Si≤K := le_inf hST hs
  have hidx : Si.relIndex Ti=2 := by
    simpa only [Ti,c.intrinsicSylow_coe] using (relIndex_subgroupOf c.ambient_le).trans hi
  obtain ⟨y,hy,_,hyout⟩ := BinaryFourPlus.TransvectionCoset.exists_sylow_outside_kernel
    c.action c.action_surjective c.intrinsicSylow
  have hkne : K.relIndex Ti≠1 := fun hh=>hyout (relIndex_eq_one.mp hh hy)
  have hh : Si.relIndex K*K.relIndex Ti=2 :=
    (relIndex_mul_relIndex Si K Ti hSK inf_le_left).trans hidx
  have hd : K.relIndex Ti∣2 := ⟨Si.relIndex K,by simpa only [Nat.mul_comm] using hh.symm⟩
  have hk2 : K.relIndex Ti=2 := ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left hkne
  have hs1 : Si.relIndex K=1 := by rw [hk2] at hh; omega
  exact le_antisymm hSK (relIndex_eq_one.mp hs1)

/-- The source outside representatives retain the selected central involution.
No choice of affine coordinates or replacement of that marking is made. -/
theorem MinimalBlockSetup.single_alternating_outside_classes_of_center_mark
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T:Subgroup G)≤M)
    (hu : ∀N:Subgroup G, IsMaximalTwoLocal N→(T:Subgroup G)≤N→N=M)
    (hST : (d.S:Subgroup d.H).map d.H.subtype<(T:Subgroup G))
    (hsingle : d.L0=d.block)
    (hA : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hD : (T:Subgroup G) ⊓ centralizer (d.block.map d.H.subtype:Set G)=⊥) :
    let P := ((pResidual 2 (M ⊓ d.block.map d.H.subtype:Subgroup G)).map
      (M ⊓ d.block.map d.H.subtype).subtype).pCoreIn 2
    let S := (d.S:Subgroup d.H).map d.H.subtype
    ∀z:G, orderOf z=2 → (center P).map P.subtype=zpowers z →
    ∃y a:G, ∃L:Subgroup G,
      y∈(T:Subgroup G) ∧ y∉S ∧ y^2∈(center P).map P.subtype ∧
      a∈P ∧ orderOf a=4 ∧ a^2=z ∧ Commute y a ∧
      L≤M ∧ IsPPerfect 2 L ∧ z∈L.pCoreIn 2 ∧ L≤centralizer ({y}:Set G) ∧
      (∀i∈(T:Subgroup G), i∉S → orderOf i=2 →
        (∃m∈M,m*i*m⁻¹=y) ∨ (∃m∈M,m*i*m⁻¹=y*a)) ∧
      (orderOf (y*a)=2 → ∃b∈P, orderOf b=2 ∧
        b∉(center P).map P.subtype ∧ (y*a)*b=b*(y*a)) := by
  intro P S z hz2 hZ
  obtain ⟨c⟩ := d.single_alternating_residual_factors hG T hM hTM hu hST hsingle hA hD
  let Q := pCore 2 M
  have hcore : Q.map M.subtype=P :=
    (d.single_alternating_maximal_core_of_centralizer_bot hG T hM hTM hu hST hsingle hA hD).1
  have hcenter : ((center Q).map Q.subtype).map M.subtype=(center P).map P.subtype := by
    rw [map_subgroup_center_eq M.subtype M.subtype_injective Q,hcore]
  have hz : z∈(center P).map P.subtype := hZ ▸ mem_zpowers z
  obtain ⟨zM,hzM,hzval⟩ := hcenter.symm ▸ hz
  have hzM1 : zM≠1 := by
    intro hh
    have hz1 : z=1 := by rw [←hzval,hh]; rfl
    rw [hz1,orderOf_one] at hz2
    omega
  have hSi := intrinsic_sign_kernel c
    (d.single_alternating_sylow_index_source hG T hM hTM hu hST hsingle hA).1
    (by simpa only [c.action_def] using
      d.single_alternating_factorSign_source hG T hM hTM hu hST hsingle hA hD c.data)
  rw [c.action_def] at hSi
  have hf : Function.Surjective (c.data.quotientWreathAction.comp
      (MulAut.conjNormal:M→*MulAut Q)) := by
    rw [←c.action_def]
    exact c.action_surjective
  obtain ⟨y,a,L,hy,hyout,hy2,haQ,ha4,ha2,hay,hp,hzL,hyL,hclass,hfixed⟩ :=
    c.data.outside_square_classes_and_fixed_involution Q c.selfcentralizing c.factors
      c.intrinsicSylow (S.subgroupOf M) hf hSi zM hzM hzM1
  have hyG : (y:G)∈(T:Subgroup G) := by
    rw [c.intrinsicSylow_coe] at hy
    exact hy
  have haP : (a:G)∈P := hcore ▸ mem_map_of_mem M.subtype haQ
  have hy2G : (y:G)^2∈(center P).map P.subtype := by
    rw [←hcenter]
    exact mem_map_of_mem M.subtype hy2
  have ha2G : (a:G)^2=z := (congrArg Subtype.val ha2).trans hzval
  have ha4G : orderOf (a:G)=4 :=
    (orderOf_injective M.subtype M.subtype_injective a).trans ha4
  have hpG : IsPPerfect 2 (L.map M.subtype) := hp.of_surjective
    (M.subtype.subgroupMap L) (M.subtype.subgroupMap_surjective L)
  have hzLG : z∈(L.map M.subtype).pCoreIn 2 := by
    rw [←map_pCoreIn_of_injective 2 L M.subtype M.subtype_injective]
    exact ⟨zM,hzL,hzval⟩
  have hyLG : L.map M.subtype≤centralizer ({(y:G)}:Set G) := by
    rintro _ ⟨l,hl,rfl⟩
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hyL l hl)
  refine ⟨y,a,L.map M.subtype,hyG,hyout,hy2G,haP,ha4G,ha2G,hay.map M.subtype,
    map_subtype_le L,hpG,hzLG,hyLG,?_,?_⟩
  · intro i hi hiout hi2
    let iM : M := ⟨i,hTM hi⟩
    have hiM2 : iM^2=1 := by
      apply M.subtype_injective
      change i^2=1
      simpa only [hi2] using pow_orderOf_eq_one i
    have hiMi : iM∈(c.intrinsicSylow:Subgroup M) := by
      rw [c.intrinsicSylow_coe]
      exact hi
    have hci := hclass iM hiMi hiout (hiM2 ▸ one_mem _)
    rcases hci with hc|hc
    · obtain ⟨m,hm⟩ := isConj_iff.mp hc
      exact Or.inl ⟨m,m.property,congrArg Subtype.val hm⟩
    · obtain ⟨m,hm⟩ := isConj_iff.mp hc
      exact Or.inr ⟨m,m.property,congrArg Subtype.val hm⟩
  · intro hv2
    have hvM2 : orderOf (y*a)=2 :=
      (orderOf_injective M.subtype M.subtype_injective (y*a)).symm.trans hv2
    obtain ⟨b,hb,hb2,hbn,hbc⟩ := hfixed hvM2
    have hbP : (b:G)∈P := hcore ▸ mem_map_of_mem M.subtype hb
    have hbnG : (b:G)∉(center P).map P.subtype := by
      rintro ⟨bP,hbPz,he⟩
      apply hbn
      intro q hq
      apply M.subtype_injective
      have hqP : (q:G)∈P := hcore ▸ mem_map_of_mem M.subtype hq
      change (q:G)*(b:G)=(b:G)*(q:G)
      have hh := congrArg Subtype.val (mem_center_iff.mp hbPz ⟨q,hqP⟩)
      change (q:G)*(bP:G)=(bP:G)*(q:G) at hh
      change (bP:G)=(b:G) at he
      simpa only [he] using hh
    exact ⟨b,hbP,(orderOf_injective M.subtype M.subtype_injective b).trans hb2,hbnG,
      congrArg Subtype.val hbc⟩
end CFSG.Quasithin.Chapter2
