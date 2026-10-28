module
public import Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCentralReflection
public import Theory.GroupTheory.WeakBNPair.RegularTree.NaturalActor
public import Theory.GroupTheory.DisjointConjugateCenter

/-!
# Whole-Cartan correction in a central natural extension

A full nonbinary diagonal complement has centralizer contained in its product
with the actor center. Consequently an actor reflection normalizing its Cartan
intersection normalizes the product of the whole Cartan with that center.
Hall conjugacy corrects it by an element of the center. The argument requires
only finite local subgroups, so the ambient completion can be infinite.

When the actual kernel has exponent two, the corrected reflection is again
an involution and retains its quotient braid matrix. Its conjugacy formula
records the central factor explicitly: this does not assert fusion to the
original chosen root involution. Finally the normal triangular image of the
full local permutation kernel is trivial, giving the full-kernel Cartan
centralization clause independently of injective natural coordinates.

Source: DGS, *Groups and Graphs* (1985), (10.5), pp.155--157, and the
normalizer correction in (14.2), pp.210--211. The source root-conjugacy
selection and the binary Cartan case remain separate obligations.
-/

@[expose] public noncomputable section
open Subgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups Pointwise
namespace Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCubic
variable {F X : Type*} [Field F] [CharP F 2] [Group X]

/-- The centralizer of a full diagonal complement is contained in its product
with the actual actor center. -/
theorem NaturalCentralKernel.centralizer_diagonal_le {π : X →* SL(2,F)}
    (d : NaturalCentralKernel π) (D : Subgroup X) [IsMulCommutative D]
    (hfull : ∀ a : F, ∀ ha : a≠0, diag2 a ha∈D.map π)
    (b : F) (hb : b≠0) (hb1 : b≠1) :
    centralizer (D : Set X)≤D⊔center X := by
  obtain ⟨k,hk,hπk⟩ := hfull b hb
  intro z hz
  have hcomm : Commute (π z) (diag2 b hb) := by
    rw [←hπk]
    exact (show Commute z k from (mem_centralizer_iff.mp hz k hk).symm).map π
  obtain ⟨a,ha,hπz⟩ := diagonal_of_commute (π z) b hb hb1 hcomm
  obtain ⟨u,hu,hπu⟩ := hfull a ha
  have he : z*u⁻¹∈π.ker := by
    change π (z*u⁻¹)=1
    rw [map_mul,map_inv,hπz,hπu,mul_inv_cancel]
  have hc : z*u⁻¹∈centralizer (D : Set X) :=
    (centralizer (D : Set X)).mul_mem hz
      ((centralizer (D : Set X)).inv_mem (D.le_centralizer hu))
  have hzC : z*u⁻¹∈center X := d.central ⟨z*u⁻¹,he⟩
    (d.coordinates_eq_one_of_commute_diagonal ⟨z*u⁻¹,he⟩ k b hb hb1 hπk
      (mem_centralizer_iff.mp hc k hk))
  have hh := (D⊔center X).mul_mem ((show center X≤D⊔center X from le_sup_right) hzC)
    ((show D≤D⊔center X from le_sup_left) hu)
  simpa only [inv_mul_cancel_right, mul_inv_cancel_right] using hh

/-- Centralization in a normalized supplement is controlled by the actor center. -/
theorem centralizer_actor_cartan_eq_center (A K : Subgroup X) [IsMulCommutative K]
    (hn : K≤normalizer (A : Set X))
    (hself : centralizer (K.subgroupOf A : Set A)≤K.subgroupOf A⊔center A) :
    (A⊔K)⊓centralizer ((A⊓K : Subgroup X) : Set X)=centerIn A⊔K := by
  apply le_antisymm
  · intro x hx
    have hprod : x∈(A : Set X)*(K : Set X) := by
      rw [←coe_mul_of_right_le_normalizer_left A K hn]
      exact hx.1
    obtain ⟨a,ha,k,hk,rfl⟩ := hprod
    have hkC : k∈centralizer ((A⊓K : Subgroup X) : Set X) :=
      (centralizer_le inf_le_right) (K.le_centralizer hk)
    have haC : a∈centralizer ((A⊓K : Subgroup X) : Set X) := by
      simpa only [mul_inv_cancel_right] using
        (centralizer ((A⊓K : Subgroup X) : Set X)).mul_mem hx.2
          ((centralizer ((A⊓K : Subgroup X) : Set X)).inv_mem hkC)
    have haC' : (⟨a,ha⟩ : A)∈centralizer (K.subgroupOf A : Set A) := by
      apply mem_centralizer_iff.mpr
      intro z hz
      apply Subtype.ext
      exact mem_centralizer_iff.mp haC z ⟨z.property,hz⟩
    have hh := mem_map_of_mem A.subtype (hself haC')
    rw [Subgroup.map_sup,subgroupOf_map_subtype,←centerIn_eq_map_center] at hh
    have hle : K⊓A⊔centerIn A≤centerIn A⊔K :=
      sup_le (inf_le_left.trans le_sup_right) le_sup_left
    exact (centerIn A⊔K).mul_mem (hle hh)
      ((show K≤centerIn A⊔K from le_sup_right) hk)
  · apply sup_le
    · exact le_inf ((show centerIn A≤A from inf_le_left).trans le_sup_left)
        ((show centerIn A≤centralizer (A : Set X) from inf_le_right).trans
          (centralizer_le inf_le_left))
    · exact le_inf le_sup_right (K.le_centralizer.trans (centralizer_le inf_le_right))

/-- Hall conjugacy corrects a normalizer by the finite normal two-subgroup;
the ambient group may be infinite. -/
theorem exists_two_correction (C K : Subgroup X) [Finite C] [Finite K]
    [Group.IsSolvable K] (hC : IsPGroup 2 C) (hodd : Nat.Coprime 2 (Nat.card K))
    (hn : K≤normalizer (C : Set X)) (t : X)
    (ht : t∈normalizer ((C⊔K : Subgroup X) : Set X)) :
    ∃ z∈C, z*t∈normalizer (K : Set X) := by
  let E := C⊔K
  have hfinite : (E : Set X).Finite := by
    rw [show (E : Set X)=(C : Set X)*(K : Set X) from
      coe_mul_of_right_le_normalizer_left C K hn]
    exact (Set.toFinite (C : Set X)).mul (Set.toFinite (K : Set X))
  let : Finite E := hfinite.to_subtype
  let := hC.isNilpotent
  have hsolv : Group.IsSolvable E := Group.isSolvable_sup_of_normalizes C K hn
  have hhall : IsHallSubgroup OddHall.oddPrimes (K.subgroupOf E) :=
    OddHall.oddHall_of_normalized_sup hC hodd hn rfl
  have heE : E.map (MulAut.conj t).toMonoidHom=E := mem_normalizer_iff_map_conj_eq.mp ht
  let a : MulAut E := ((MulAut.conj t).subgroupMap E).trans (MulEquiv.subgroupCongr heE)
  obtain ⟨b,hb⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable hsolv hhall (hhall.map_mulAut a)
  have hmap : K.map (MulAut.conj t).toMonoidHom=K.map (MulAut.conj (b:X)).toMonoidHom := by
    have he := congrArg (Subgroup.map E.subtype) hb
    rw [map_map,map_map] at he
    have hl : E.subtype.comp a.toMonoidHom=(MulAut.conj t).toMonoidHom.comp E.subtype := rfl
    have hr : E.subtype.comp (MulAut.conj b).toMonoidHom=
        (MulAut.conj (b:X)).toMonoidHom.comp E.subtype := rfl
    simpa only [hl,hr,←map_map,map_subgroupOf_eq_of_le (show K≤E from le_sup_right)] using he
  have hbN : (b:X)⁻¹*t∈normalizer (K : Set X) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change K.map (MulAut.conj ((b:X)⁻¹*t)).toMonoidHom=K
    have he := congrArg (Subgroup.map (MulAut.conj (b:X)⁻¹).toMonoidHom) hmap
    simp only [map_map] at he
    have hl : (MulAut.conj (b:X)⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom=
        (MulAut.conj ((b:X)⁻¹*t)).toMonoidHom := by ext z; simp [mul_assoc]
    have hr : (MulAut.conj (b:X)⁻¹).toMonoidHom.comp (MulAut.conj (b:X)).toMonoidHom=
        MonoidHom.id X := by ext z; simp [mul_assoc]
    simpa only [hl,hr,map_id] using he
  have hbprod : (b:X)∈(C : Set X)*(K : Set X) := by
    rw [←coe_mul_of_right_le_normalizer_left C K hn]
    exact b.property
  obtain ⟨z,hz,k,hk,he⟩ := hbprod
  refine ⟨z⁻¹,C.inv_mem hz,?_⟩
  have hh := (normalizer (K : Set X)).mul_mem (K.le_normalizer hk) hbN
  rw [←he,_root_.mul_inv_rev] at hh
  simpa only [mul_assoc,mul_inv_cancel_left] using hh

/-- An actor reflection can be corrected by the actual actor center to
normalize the full Cartan. -/
theorem exists_central_full_cartan_correction (A K : Subgroup X)
    [Finite A] [Finite K] [IsMulCommutative K]
    (hn : K≤normalizer (A : Set X))
    (hself : centralizer (K.subgroupOf A : Set A)≤K.subgroupOf A⊔center A)
    (hC : IsPGroup 2 (centerIn A)) (hodd : Nat.Coprime 2 (Nat.card K))
    (t : A) (ht : t∈normalizer (K.subgroupOf A : Set A)) :
    ∃ z∈centerIn A, z*(t:X)∈normalizer (K : Set X) := by
  let : Finite (centerIn A) := Finite.of_injective
    (inclusion (show centerIn A≤A from inf_le_left)) (inclusion_injective _)
  let : Group.IsSolvable K := Group.isSolvable_of_comm (mul_comm' (M := K))
  have htN := (K.subgroupOf A).le_normalizer_map A.subtype (mem_map_of_mem A.subtype ht)
  rw [subgroupOf_map_subtype,inf_comm] at htN
  have htC : (t:X)∈normalizer (centralizer ((A⊓K : Subgroup X) : Set X) : Set X) := by
    have hh := normal_subgroupOf_centralizer_normalizer ((A⊓K : Subgroup X) : Set X)
    exact (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer _)).mp hh htN
  have htE : (t:X)∈normalizer ((centerIn A⊔K : Subgroup X) : Set X) := by
    rw [←centralizer_actor_cartan_eq_center A K hn hself]
    exact inf_normalizer_le_normalizer_inf
      ⟨(A⊔K).le_normalizer ((show A≤A⊔K from le_sup_left) t.property),htC⟩
  exact exists_two_correction (centerIn A) K hC hodd (normalizes_centerIn hn) t htE

/-- A central correction gives a whole-Cartan reflection. Its root conjugacy
retains the central factor, rather than claiming fusion to an arbitrary lift. -/
theorem NaturalCentralKernel.exists_full_cartan_reflection
    (A K : Subgroup X) [Finite A] [Finite K] [IsMulCommutative K]
    (π : A →* SL(2,F)) (d : NaturalCentralKernel π) (honto : Function.Surjective π)
    (hn : K≤normalizer (A : Set X)) (hodd : Nat.Coprime 2 (Nat.card K))
    (hcenter : center A≤π.ker) (hsquare : ∀ z : π.ker, z*z=1)
    (hdiag : ∀ k : A, (k:X)∈K → ∃ b : F, ∃ hb : b≠0, π k=diag2 b hb)
    (hfull : ∀ b : F, ∀ hb : b≠0, diag2 b hb∈(K.subgroupOf A).map π)
    (b : F) (hb : b≠0) (hb1 : b≠1)
    (x : A) (hx : x*x=1) (a : F) (ha : a≠0) (hπx : π x=upper a) :
    ∃ t : A, (t:X)∈normalizer (K : Set X) ∧ t*t=1 ∧ orderOf t=2 ∧
      π t=upper a*lower a⁻¹*upper a ∧
      ∃ z : A, z∈center A ∧ z∈π.ker ∧ ∃ g : A, g*(z*x)*g⁻¹=t := by
  let D := K.subgroupOf A
  let : IsMulCommutative D := IsMulCommutative.of_comm fun x y => by
    apply Subtype.ext
    apply Subtype.ext
    exact setLike_mul_comm (show (x:A).val∈K from x.property)
      (show (y:A).val∈K from y.property)
  let : Group.IsSolvable D := Group.isSolvable_of_comm (mul_comm' (M := D))
  have hoddD : Nat.Coprime 2 (Nat.card D) := hodd.of_dvd_right (by
    have he := card_map_of_injective (f := A.subtype) (K := D) A.subtype_injective
    rw [←he,subgroupOf_map_subtype]
    exact card_dvd_of_le inf_le_left)
  obtain ⟨t,ht,htsq,_,hπt,g,hg⟩ := d.exists_diagonal_cartan_reflection honto D hoddD
    hdiag x hx a ha hπx
  have hC : IsPGroup 2 (centerIn A) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro z
    have hz : (⟨(z:X),z.property.1⟩ : A)∈center A := by
      apply Subgroup.mem_center_iff.mpr
      intro y
      exact Subtype.ext (z.property.2 y y.property)
    have he := congrArg (fun v : π.ker => ((v:A):X))
      (hsquare ⟨⟨z,z.property.1⟩,hcenter hz⟩)
    exact ⟨1,Subtype.ext (by simpa only [pow_one,pow_two,Subgroup.coe_mul,Subgroup.coe_one] using he)⟩
  obtain ⟨z,hz,hnorm⟩ := exists_central_full_cartan_correction A K hn
    (d.centralizer_diagonal_le D hfull b hb hb1) hC hodd t ht
  let zA : A := ⟨z,hz.1⟩
  have hzA : zA∈center A := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    exact Subtype.ext (hz.2 y y.property)
  have hzker := hcenter hzA
  have hzsq : zA*zA=1 := congrArg (fun v : π.ker => (v:A)) (hsquare ⟨zA,hzker⟩)
  let u := zA*t
  have husq : u*u=1 := by
    change (zA*t)*(zA*t)=1
    rw [mul_assoc,←mul_assoc t,Subgroup.mem_center_iff.mp hzA t]
    calc
      zA*(zA*t*t)=(zA*zA)*(t*t) := by group
      _ = 1 := by rw [hzsq,htsq,one_mul]
  have hπu : π u=upper a*lower a⁻¹*upper a := by
    change π (zA*t)=_
    rw [map_mul,show π zA=1 from hzker,one_mul,hπt]
  refine ⟨u,hnorm,husq,?_,hπu,zA,hzA,hzker,g,?_⟩
  · apply orderOf_eq_prime (show u^2=1 by simpa only [pow_two] using husq)
    intro he
    have hh := congrArg (fun v : SL(2,F) => v.val 0 1) hπu
    rw [he,map_one,braid_matrix a ha] at hh
    exact ha hh.symm
  · change g*(zA*x)*g⁻¹=zA*t
    calc
      g*(zA*x)*g⁻¹=(g*zA)*(x*g⁻¹) := by group
      _ = (zA*g)*(x*g⁻¹) := by rw [Subgroup.mem_center_iff.mp hzA g]
      _ = zA*(g*x*g⁻¹) := by group
      _ = zA*t := by rw [hg]

/-- The actor's natural two-kernel controls the full local permutation
kernel: a Cartan-normalizing actor centralizes its intersection with K. -/
theorem NaturalCentralKernel.commutes_cartan_localKernel
    (A K M : Subgroup X) [Finite A] [Finite K]
    (π : A →* SL(2,F)) (d : NaturalCentralKernel π) (honto : Function.Surjective π)
    (hK : K ≤ normalizer (A : Set X)) (hM : A ≤ normalizer (M : Set X))
    (hodd : Nat.Coprime 2 (Nat.card K))
    (htri : ∀ z : A, (z:X)∈M → (π z).val 1 0=0)
    (t : A) (ht : (t:X)∈normalizer (K : Set X))
    (z : X) (hzK : z∈K) (hzM : z∈M) : Commute (t:X) z := by
  let MA := M.subgroupOf A
  let : MA.Normal := normal_subgroupOf_of_le_normalizer hM
  let : (MA.map π).Normal := by
    constructor
    rintro y ⟨x,hx,rfl⟩ g
    obtain ⟨u,rfl⟩ := honto g
    exact ⟨u*x*u⁻¹,(inferInstance : MA.Normal).conj_mem x hx u,
      by simp only [map_mul,map_inv]⟩
  have hzero : MA.map π=⊥ := by
    apply normal_triangular_eq_bot
    rintro y ⟨x,hx,rfl⟩
    exact htri x hx
  let w := (t:X)*z*(t:X)⁻¹*z⁻¹
  have hwA : w∈A := by
    have he := (mem_normalizer_iff.mp (hK hzK) (t:X)⁻¹).mp (A.inv_mem t.property)
    simpa only [w,mul_assoc] using A.mul_mem t.property he
  have hwM : w∈M := M.mul_mem
    ((mem_normalizer_iff.mp (hM t.property) z).mp hzM) (M.inv_mem hzM)
  have hwK : w∈K := K.mul_mem
    ((mem_normalizer_iff.mp ht z).mp hzK) (K.inv_mem hzK)
  have hwQ : (⟨w,hwA⟩ : A)∈π.ker :=
    (Subgroup.map_eq_bot_iff MA).mp hzero hwM
  have hcard : Nat.card (K.subgroupOf A) ∣ Nat.card K := by
    have he := card_map_of_injective (f := A.subtype) (K := K.subgroupOf A) A.subtype_injective
    rw [←he,subgroupOf_map_subtype]
    exact card_dvd_of_le inf_le_left
  have hoddD := hodd.of_dvd_right hcard
  have hdis : K.subgroupOf A ⊓ π.ker=⊥ := by
    obtain ⟨m,hm⟩ := d.isTwo.exists_card_eq
    exact (disjoint_of_coprime_natCard (by rw [hm]; exact hoddD.symm.pow_right m)).eq_bot
  have he : (⟨w,hwA⟩ : A)∈K.subgroupOf A ⊓ π.ker := ⟨hwK,hwQ⟩
  rw [hdis] at he
  have hw : w=1 := congrArg Subtype.val (show (⟨w,hwA⟩ : A)=1 from he)
  have heq : (t:X)*z*(t:X)⁻¹=z := mul_inv_eq_one.mp hw
  have hh := congrArg (·*(t:X)) heq
  exact (by simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh : (t:X)*z=z*(t:X))

end Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCubic
