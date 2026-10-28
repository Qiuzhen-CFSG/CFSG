module
public import Theory.GroupTheory.WeakBNPair.RegularTree.NaturalReflection

/-!
# Natural reflections in an actor and the whole Cartan

In characteristic two a nonidentity diagonal matrix has diagonal centralizer.
A full diagonal complement in a natural extension is therefore self-centralizing:
its kernel centralizer vanishes on the natural plane. If an abelian K normalizes
an actor A, this identifies K with the centralizer of A ∩ K inside AK. An
actor reflection normalizing A ∩ K consequently normalizes the entire K.
The reflection retains its conjugacy to the prescribed root involution inside A.

Only A modulo its actual kernel is identified with SL₂. The full endpoint
quotient may be larger. The full local permutation kernel is kept distinct:
its intersection with A has normal triangular image, hence trivial image.
Coprime orders then make the reflection centralize its intersection with K.
The full diagonal marking and a nonidentity diagonal parameter are explicit;
the binary and nontrivial-center profiles require their separate arguments.

Source: DGS, *Groups and Graphs* (1985), (10.5), pp.155--157, and the
reflection selection (14.2), pp.210--211.
-/

@[expose] public noncomputable section
open Subgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups Pointwise
namespace Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCubic
variable {F X : Type*} [Field F] [CharP F 2] [Group X]

/-- Read natural coordinates on the actual embedded kernel without changing
the actor or its quotient homomorphism. -/
def naturalKernelOfCoordinates (A Q : Subgroup X) (hQA : Q≤A)
    (π : A →* SL(2,F)) (hker : π.ker=Q.subgroupOf A)
    (φ : Q →* Multiplicative (Fin 2 → F)) (hφ : Function.Bijective φ)
    (heq : ∀ (a : A) (x : Q), ∃ y : Q,
      (y:X)=(a:X)*(x:X)*(a:X)⁻¹ ∧
      (φ y).toAdd=(π a).val *ᵥ (φ x).toAdd) : NaturalKernel π := by
  let e : π.ker ≃* Q := (MulEquiv.subgroupCongr hker).trans (subgroupOfEquivOfLe hQA)
  refine ⟨e.trans (MulEquiv.ofBijective φ hφ),?_⟩
  intro a z
  obtain ⟨y,hy,hye⟩ := heq a (e z)
  have he : e ⟨a*z*a⁻¹,(inferInstance : π.ker.Normal).conj_mem z z.property a⟩=y := by
    apply Subtype.ext
    exact hy.symm
  change φ (e ⟨a*z*a⁻¹,_⟩)=Matrix.SL2.naturalAction F (π a) (φ (e z))
  rw [he]
  exact Multiplicative.toAdd.injective hye

/-- An isomorphism of actual actors transports the natural kernel and retains
the composed quotient map on every representative. -/
def NaturalKernel.ofEquiv {Y : Type*} [Group Y]
    {π : X →* SL(2,F)} (d : NaturalKernel π) (e : Y ≃* X) :
    NaturalKernel (π.comp e.toMonoidHom) := by
  let f : (π.comp e.toMonoidHom).ker →* π.ker :=
    { toFun z := ⟨e z,z.property⟩
      map_one' := Subtype.ext e.map_one
      map_mul' x y := Subtype.ext (e.map_mul x y) }
  have hf : Function.Bijective f := by
    constructor
    · intro x y he
      exact Subtype.ext (e.injective (congrArg Subtype.val he))
    · intro z
      refine ⟨⟨e.symm z,?_⟩,Subtype.ext (e.apply_symm_apply z)⟩
      change π (e (e.symm z))=1
      rw [e.apply_symm_apply]
      exact z.property
  refine ⟨(MulEquiv.ofBijective f hf).trans d.coords,?_⟩
  intro g z
  change d.coords (f ⟨g*z*g⁻¹,_⟩)=Matrix.SL2.naturalAction F (π (e g)) (d.coords (f z))
  have hz : g*z*g⁻¹∈(π.comp e.toMonoidHom).ker :=
    (inferInstance : (π.comp e.toMonoidHom).ker.Normal).conj_mem z z.property g
  have he : f ⟨g*z*g⁻¹,hz⟩=
      ⟨e g*f z*(e g)⁻¹,(inferInstance : π.ker.Normal).conj_mem (f z) (f z).property (e g)⟩ := by
    apply Subtype.ext
    exact map_mul e _ _ |>.trans (by rw [map_mul,map_inv]; rfl)
  rw [he,d.equivariant]

/-- The centralizer of a nonidentity binary diagonal matrix is diagonal. -/
theorem diagonal_of_commute (g : SL(2,F)) (b : F) (hb : b≠0) (hb1 : b≠1)
    (hcomm : Commute g (diag2 b hb)) :
    ∃ a : F, ∃ ha : a≠0, g=diag2 a ha := by
  have hne : b≠b⁻¹ := by
    intro he
    have hs : b^2=1 := by rw [pow_two]; calc b*b = b*b⁻¹ := congrArg (b*·) he
                                         _ = 1 := mul_inv_cancel₀ hb
    rcases sq_eq_one_iff.mp hs with he | he
    · exact hb1 he
    · exact hb1 (by simpa only [CharTwo.neg_eq] using he)
  have h01 : g.val 0 1=0 := by
    have he := congrArg (fun z : SL(2,F) => z.val 0 1) hcomm.eq
    have hh : g.val 0 1*b⁻¹=g.val 0 1*b := by
      simpa [SpecialLinearGroup.coe_mul,diag2_coe',Matrix.mul_apply,Fin.sum_univ_two,mul_comm] using he
    by_contra hz
    exact hne (mul_left_cancel₀ hz hh).symm
  have h10 : g.val 1 0=0 := by
    have he := congrArg (fun z : SL(2,F) => z.val 1 0) hcomm.eq
    have hh : g.val 1 0*b=g.val 1 0*b⁻¹ := by
      simpa [SpecialLinearGroup.coe_mul,diag2_coe',Matrix.mul_apply,Fin.sum_univ_two,mul_comm] using he
    by_contra hz
    exact hne (mul_left_cancel₀ hz hh)
  have hd : g.val 0 0*g.val 1 1=1 := by
    simpa only [Matrix.det_fin_two,h01,zero_mul,sub_zero] using g.property
  have ha : g.val 0 0≠0 := left_ne_zero_of_mul_eq_one hd
  refine ⟨g.val 0 0,ha,?_⟩
  apply Subtype.ext
  have h11 : g.val 1 1=(g.val 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hd
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag2_coe',h01,h10,h11]

/-- A full diagonal complement is self-centralizing in a natural extension
when the field has a nonidentity nonzero element. -/
theorem NaturalKernel.centralizer_diagonal_eq {π : X →* SL(2,F)}
    (d : NaturalKernel π) (D : Subgroup X) [IsMulCommutative D]
    (hfull : ∀ a : F, ∀ ha : a≠0, diag2 a ha∈D.map π)
    (b : F) (hb : b≠0) (hb1 : b≠1) :
    centralizer (D : Set X)=D := by
  obtain ⟨k,hk,hπk⟩ := hfull b hb
  have hc := d.diagonal_centralizer D k hk b hb hb1 hπk
  apply le_antisymm ?_ D.le_centralizer
  intro z hz
  have hcomm : Commute (π z) (diag2 b hb) := by
    rw [←hπk]
    exact (show Commute z k from (mem_centralizer_iff.mp hz k hk).symm).map π
  obtain ⟨a,ha,hπz⟩ := diagonal_of_commute (π z) b hb hb1 hcomm
  obtain ⟨u,hu,hπu⟩ := hfull a ha
  have he : z*u⁻¹∈π.ker ⊓ centralizer (D : Set X) := by
    refine ⟨?_,(centralizer (D : Set X)).mul_mem hz
      ((centralizer (D : Set X)).inv_mem (D.le_centralizer hu))⟩
    change π (z*u⁻¹)=1
    rw [map_mul,map_inv,hπz,hπu,mul_inv_cancel]
  rw [hc] at he
  have hzu : z=u := mul_inv_eq_one.mp he
  exact hzu ▸ hu

/-- Centralization in a normalized supplement is detected inside the actor.
The full abelian complement, including its factors outside the actor, remains. -/
theorem centralizer_actor_cartan_eq (A K : Subgroup X) [IsMulCommutative K]
    (hn : K ≤ normalizer (A : Set X))
    (hself : centralizer (K.subgroupOf A : Set A)=K.subgroupOf A) :
    (A⊔K) ⊓ centralizer ((A⊓K : Subgroup X) : Set X)=K := by
  apply le_antisymm ?_ (le_inf le_sup_right (K.le_centralizer.trans (centralizer_le inf_le_right)))
  intro x hx
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
  rw [hself] at haC'
  exact K.mul_mem haC' hk

/-- Normalizing the actor part of the Cartan therefore normalizes the full Cartan. -/
theorem normalizes_full_cartan (A K : Subgroup X) [IsMulCommutative K]
    (hn : K ≤ normalizer (A : Set X))
    (hself : centralizer (K.subgroupOf A : Set A)=K.subgroupOf A)
    (t : A) (ht : t∈normalizer (K.subgroupOf A : Set A)) :
    (t:X)∈normalizer (K : Set X) := by
  have htN := (K.subgroupOf A).le_normalizer_map A.subtype
    (mem_map_of_mem A.subtype ht)
  rw [subgroupOf_map_subtype,inf_comm] at htN
  have hc := centralizer_actor_cartan_eq A K hn hself
  rw [←hc]
  have htC : (t:X)∈normalizer (centralizer ((A⊓K : Subgroup X) : Set X) : Set X) := by
    have hh := (normal_subgroupOf_centralizer_normalizer ((A⊓K : Subgroup X) : Set X))
    apply mem_normalizer_iff.mpr
    intro k
    constructor
    · intro hk
      exact hh.conj_mem ⟨k,centralizer_le_normalizer _ hk⟩ hk ⟨t,htN⟩
    · intro hk
      have he := hh.conj_mem
        ⟨(t:X)*k*(t:X)⁻¹,centralizer_le_normalizer _ hk⟩ hk
        ⟨(t:X)⁻¹,(normalizer ((A⊓K : Subgroup X) : Set X)).inv_mem htN⟩
      change (t:X)⁻¹*((t:X)*k*(t:X)⁻¹)*((t:X)⁻¹)⁻¹∈centralizer ((A⊓K : Subgroup X) : Set X) at he
      simpa only [inv_inv,inv_mul_cancel_left,mul_inv_cancel_right,mul_assoc,inv_mul_cancel,mul_one] using he
  exact inf_normalizer_le_normalizer_inf ⟨(A⊔K).le_normalizer ((show A≤A⊔K from le_sup_left) t.property),htC⟩

/-- Construct an actor reflection normalizing the whole abelian Cartan.
Only the actor quotient is SL₂; no full-endpoint quotient is assumed. -/
theorem NaturalKernel.exists_actor_cartan_reflection
    (A K : Subgroup X) [Finite A] [Finite K] [IsMulCommutative K]
    (π : A →* SL(2,F)) (d : NaturalKernel π) (honto : Function.Surjective π)
    (hn : K ≤ normalizer (A : Set X))
    (hodd : Nat.Coprime 2 (Nat.card K))
    (hdiag : ∀ k : A, (k:X)∈K → ∃ b : F, ∃ hb : b≠0, π k=diag2 b hb)
    (hfull : ∀ b : F, ∀ hb : b≠0, diag2 b hb∈(K.subgroupOf A).map π)
    (b : F) (hb : b≠0) (hb1 : b≠1)
    (x : A) (hx : x*x=1) (a : F) (ha : a≠0) (hπx : π x=upper a) :
    ∃ t : A, (t:X)∈normalizer (K : Set X) ∧ t*t=1 ∧ orderOf t=2 ∧
      π t=upper a*lower a⁻¹*upper a ∧ ∃ g : A, g*x*g⁻¹=t := by
  let D := K.subgroupOf A
  let : IsMulCommutative D := IsMulCommutative.of_comm fun x y => by
    apply Subtype.ext
    apply Subtype.ext
    exact setLike_mul_comm (show (x:A).val∈K from x.property)
      (show (y:A).val∈K from y.property)
  let : Group.IsSolvable D := Group.isSolvable_of_comm (mul_comm' (M := D))
  have hoddD : Nat.Coprime 2 (Nat.card D) := hodd.of_dvd_right
    (by
      have he : Nat.card D = Nat.card (K⊓A : Subgroup X) := by
        have he := card_map_of_injective (f := A.subtype) (K := D) A.subtype_injective
        rw [←he]
        rw [subgroupOf_map_subtype]
      rw [he]
      exact card_dvd_of_le inf_le_left)
  obtain ⟨t,ht,hsq,ho,hπt,g,hg⟩ := d.exists_diagonal_cartan_reflection honto D hoddD
    hdiag x hx a ha hπx
  exact ⟨t,normalizes_full_cartan A K hn
    (d.centralizer_diagonal_eq D hfull b hb hb1) t ht,hsq,ho,hπt,g,hg⟩

/-- The actor's natural two-kernel controls the full local permutation
kernel: a Cartan-normalizing actor centralizes its intersection with K. -/
theorem NaturalKernel.commutes_cartan_localKernel
    (A K M : Subgroup X) [Finite A] [Finite K]
    (π : A →* SL(2,F)) (d : NaturalKernel π) (honto : Function.Surjective π)
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
