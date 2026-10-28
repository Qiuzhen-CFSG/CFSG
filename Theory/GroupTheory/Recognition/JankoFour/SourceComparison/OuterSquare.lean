module
public import Theory.Mathieu.M22.Properties.OuterCentralizers.Coverage
public import Theory.Mathieu.M22.CentralCoverPrelude.InvolutionSquares
public import Theory.GroupTheory.CentralExtensionCommutingPair
public import Theory.GroupTheory.PerfectCentralCoverSquareObstruction
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Two outer-involution representatives with a commuting square-root link

The existing certified 256-element Sylow subgroup supplies two outer
representatives, rows 8 and 109. Words in the original M22 generators
conjugate every outer involution row to one of these. Row 18 is an inner
square root linking the representatives. All identities below are checked
by kernel reduction on the existing degree-22 permutation tables.

This is the finite input for the split six-cover comparison in
Aschbacher–Segev (1991), (8.3), p.606. Discovery uses only the existing
M22CubicInverters tables; it adds no group-order or simplicity certificate.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OuterSquare
open Sporadic.Mathieu M22CubicInverters

private def conjugatingWord : Fin 36 → List (Fin 3) :=
  ![
    [0,2,0,1,0,1,1],
    [0,1,0,2,0,2,0,1,0,2],
    [],
    [2,0,1,1,0,2,0],
    [0,1,0,2,0,1,0,1,0,1,0,2,0],
    [0,1,0,1,0,1,1],
    [2,0,1,0,1,1,0,1,0,1,1],
    [1,0,2,0,1,1,0,2,0,2,0,1],
    [0,1,1,0,2,0,2,0,1,0,2,0,1,0,1],
    [0,2,0,1,0,2,0,1,0],
    [0,1,0,1,1,0,2,0],
    [0,2,0,2,0,2,0,1,0,1,0,1,0,1,0],
    [0,1,0,1,1,0,2,0],
    [0,2,0,2,0,1],
    [0,1,1,0,2,0,1,0,1,1],
    [0,1,1,0,1,0,2,0,1],
    [],
    [0,2,0,2,0,1,0,1,0,1,1,0,1],
    [0,2,0,1,1,0,2,0],
    [0,2,0,1,1,0,2,0],
    [1,0,2,0,1],
    [1,0,2,0,1,0,1,0,1,1,0,1],
    [0,1,0,2,0,1,1,0,2,0],
    [1,1,0,1,0,2,0,1,0,1,1],
    [0,1,1,0,1,0,1,0,2,0,1,1,0,2],
    [1,0,1,1,0,2,0,1,0,1,1,0,1],
    [2,0,1,0,1,0,1,0,2],
    [2,0,1,0,1,0,2,0,2],
    [2,0,1,1,0,2,0,1,1,0,2,0,2,0],
    [1,1,0,2,0,2,0,1,1,0,1,0],
    [2,0,2,0,1,0,1,0,1,0,2,0],
    [0,1,1,0,2,0,1,1,0,2,0],
    [2,0,2,0,1,1,0,1,0],
    [0,1,1,0,1,1,0],
    [0,2,0,1,0,1,0,2,0,1,0,2],
    [1,0,1,1,0,2,0,2,0,1,1,0,1,0,1]]

private def wordIndex (i : Fin 256) : Fin 36 :=
  match i.val with
  | 2 => 0
  | 6 => 1
  | 8 => 2
  | 11 => 3
  | 13 => 4
  | 15 => 5
  | 24 => 6
  | 43 => 7
  | 61 => 8
  | 79 => 9
  | 88 => 10
  | 91 => 11
  | 93 => 12
  | 95 => 13
  | 104 => 14
  | 107 => 15
  | 109 => 16
  | 111 => 17
  | 112 => 18
  | 124 => 19
  | 131 => 20
  | 138 => 21
  | 147 => 22
  | 158 => 23
  | 174 => 24
  | 186 => 25
  | 192 => 26
  | 201 => 27
  | 209 => 28
  | 212 => 29
  | 216 => 30
  | 219 => 31
  | 221 => 32
  | 223 => 33
  | 236 => 34
  | 249 => 35
  | _ => 0

private def representativeIndex (i : Fin 256) : Fin 256 :=
  if (Finset.univ.filter fun x => rowTable i x = x).card = 8 then 8 else 109

set_option maxRecDepth 100000 in
private theorem row_cases (i : Fin 256) :
    (∃ x, rowTable i (rowTable i x) ≠ x) ∨
    ((Finset.univ.filter fun x => rowTable i x = x).card ≠ 8 ∧
      (Finset.univ.filter fun x => rowTable i x = x).card ≠ 0) ∨
    (∀ x, rowTable i (innerWordAction (conjugatingWord (wordIndex i)) x) =
      innerWordAction (conjugatingWord (wordIndex i)) (rowTable (representativeIndex i) x)) := by
  revert i
  decide +kernel

/-- The actual outer representatives in the existing native Sylow. -/
noncomputable def first : m22DesignAut := rowElement 8
noncomputable def second : m22DesignAut := rowElement 109
noncomputable def root : m22DesignAut := rowElement 18

private theorem root_word : root = M22ValueBound.Concrete.inclusion
    (innerWord (generatorWord 1) * innerWord (generatorWord 2) *
      innerWord (generatorWord 0) * innerWord (generatorWord 2)) := by
  change M22ValueBound.Concrete.inclusion (innerWord (generatorWord 1)) *
    (M22ValueBound.Concrete.inclusion (innerWord (generatorWord 2)) *
    (M22ValueBound.Concrete.inclusion (innerWord (generatorWord 0)) *
    (M22ValueBound.Concrete.inclusion (innerWord (generatorWord 2)) * 1))) = _
  simp only [map_mul,mul_one,mul_assoc]

/-- The linking square root lies in the original inner M22. -/
theorem root_inner : root.val ∈ M22 := by
  rw [root_word]
  exact (innerWord (generatorWord 1) * innerWord (generatorWord 2) *
    innerWord (generatorWord 0) * innerWord (generatorWord 2)).property

private theorem relations_of_tables (s t r : m22DesignAut)
    (hs : ∀ x, s.val x = rowTable 8 x)
    (ht : ∀ x, t.val x = rowTable 109 x)
    (hr : ∀ x, r.val x = rowTable 18 x) :
    s ^ 2 = 1 ∧ t ^ 2 = 1 ∧ r ^ 4 = 1 ∧
      Commute r s ∧ r ^ 2 * s = t := by
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals apply Subtype.ext; apply Equiv.ext; intro x
  all_goals simp only [pow_succ,pow_zero,Subgroup.coe_mul,Subgroup.coe_one,
    Equiv.Perm.mul_apply,Equiv.Perm.one_apply,hs,ht,hr]
  all_goals revert x; decide +kernel

/-- The representative squares and commuting square-root link. -/
theorem representative_relations :
    first ^ 2 = 1 ∧ second ^ 2 = 1 ∧ root ^ 4 = 1 ∧
      Commute root first ∧ root ^ 2 * first = second :=
  relations_of_tables first second root (rowElement_apply 8) (rowElement_apply 109)
    (rowElement_apply 18)

open Subgroup M22OuterCentralizers

private theorem conjugate_of_mem_standard (s : m22DesignAut)
    (hs : orderOf s = 2) (hcount : (fixedPoints s).card = 8 ∨ (fixedPoints s).card = 0)
    (hmem : s ∈ standardSylow) :
    ∃ g : m22DesignAut, g * first * g⁻¹ = s ∨ g * second * g⁻¹ = s := by
  obtain ⟨i, hi⟩ := rowSylow_surjective ⟨s,hmem⟩
  have he : rowElement i = s := (M22ConjugateGeneration.rowSylow_val i).symm.trans
    (congrArg Subtype.val hi)
  subst s
  rcases row_cases i with hsquare | hfix | hconj
  · obtain ⟨x,hx⟩ := hsquare
    have hp : rowElement i ^ 2 = 1 := hs ▸ pow_orderOf_eq_one _
    have hf := congrArg (fun g : m22DesignAut => g.val x) hp
    change (rowElement i).val ((rowElement i).val x) = x at hf
    simp only [rowElement_apply] at hf
    exact (hx hf).elim
  · have he : (fixedPoints (rowElement i)).card =
        (Finset.univ.filter fun x => rowTable i x = x).card := by
      simp only [fixedPoints,rowElement_apply]
    rw [he] at hcount
    exact (hcount.elim hfix.1 hfix.2).elim
  · let u := innerWord (conjugatingWord (wordIndex i))
    let g : m22DesignAut := ⟨u.val,M22_le_m22DesignAut u.property⟩
    have hg : g * rowElement (representativeIndex i) * g⁻¹ = rowElement i := by
      apply mul_inv_eq_iff_eq_mul.mpr
      apply Subtype.ext
      apply Equiv.ext
      intro x
      change u.val ((rowElement (representativeIndex i)).val x) = (rowElement i).val (u.val x)
      simp only [rowElement_apply,u,innerWord_apply]
      exact (hconj x).symm
    refine ⟨g,?_⟩
    unfold representativeIndex at hg
    split_ifs at hg with hi8
    · exact Or.inl hg
    · exact Or.inr hg

/-- Every outer involution is conjugate to one of the two linked representatives. -/
theorem exists_representative_conjugator (s : m22DesignAut) (hs : orderOf s = 2)
    (ho : s.val ∉ M22) :
    ∃ g : m22DesignAut, g * first * g⁻¹ = s ∨ g * second * g⁻¹ = s := by
  have hz : IsPGroup 2 (zpowers s) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,hs,pow_one])
  obtain ⟨Q,hQ⟩ := hz.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq m22DesignAut Q standardSylow
  let e : MulAut m22DesignAut := MulAut.conj g
  have hmem : e s ∈ standardSylow := by
    rw [←hg]
    change e s ∈ (Q : Subgroup m22DesignAut).map e.toMonoidHom
    exact mem_map_of_mem e.toMonoidHom (hQ (mem_zpowers s))
  have hcount : (fixedPoints (e s)).card = 8 ∨ (fixedPoints (e s)).card = 0 := by
    simpa only [e,MulAut.conj_apply,fixedPoints_card_conj]
      using outer_involution_fixedPoints_card s hs ho
  obtain ⟨k,hk⟩ := conjugate_of_mem_standard (e s) ((e.orderOf_eq s).trans hs) hcount hmem
  refine ⟨g⁻¹*k,?_⟩
  have hc (r : m22DesignAut) (hr : k*r*k⁻¹=e s) :
      (g⁻¹*k)*r*(g⁻¹*k)⁻¹=s := by
    calc
      _ = g⁻¹*(k*r*k⁻¹)*g := by group
      _ = s := by rw [hr]; dsimp [e,MulAut.conj_apply]; group
  exact hk.elim (fun h => Or.inl (hc first h)) (fun h => Or.inr (hc second h))

variable {E : Type*} [Group E] [Finite E]

omit [Finite E] in
private theorem kernel_square {B : Type*} [Group B] (f : E →* B)
    (hk : Nat.card f.ker = 2) (x : E) (hx : x ∈ f.ker) : x ^ 2 = 1 := by
  have he := pow_card_eq_one' (x := (⟨x,hx⟩ : f.ker))
  rw [hk] at he
  exact congrArg Subtype.val he

private theorem inner_square (f : E →* M22) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : Nat.card f.ker = 2)
    (x : E) (hx : (f x)^2=1) : x^2=1 := by
  by_cases hx1 : f x=1
  · exact kernel_square f hk x hx1
  let A := m22HexadPointwiseKernel m22Hexad123
  let : IsElementaryAbelian 2 A := m22HexadPointwiseKernel_elementaryAbelian m22Hexad123_mem
  obtain ⟨a,ha,_,han⟩ := DoubleCoverInvolutionLifting.exists_involution_above_elementary_subgroup
    f hf hk A (by rw [m22HexadPointwiseKernel_card m22Hexad123_mem]; decide)
  have hao : orderOf (f a)=2 := orderOf_eq_prime_iff.mpr ⟨by
    rw [←map_pow,←ha,pow_orderOf_eq_one,map_one],han⟩
  obtain ⟨y,hy,hyo⟩ := DoubleCoverInvolutionLifting.involution_lift_of_isConj f hf ha
    (m22_involutions_isConj _ _ hao (orderOf_eq_prime_iff.mpr ⟨hx,hx1⟩))
  rw [PerfectCentralCovering.square_eq_of_map_eq_of_kernel_exponent_two f hc
    (kernel_square f hk) hy.symm,←hyo,pow_orderOf_eq_one]

/-- Internal involutions have involutory lifts in every central double cover
of the full design group, through the literal projection. -/
theorem inner_square_one (f : E →* m22DesignAut) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : Nat.card f.ker = 2)
    (x : E) (hx : (f x)^2=1) (hi : (f x).val ∈ M22) : x^2=1 := by
  let P := (M22.subgroupOf m22DesignAut).comap f
  let g : P →* M22 := {
    toFun p := ⟨(f p.val).val,p.property⟩
    map_one' := Subtype.ext (by simp only [Subgroup.coe_one,map_one])
    map_mul' p q := Subtype.ext (by simp only [Subgroup.coe_mul,map_mul]) }
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x,hx⟩ := hf ⟨y.val,M22_le_m22DesignAut y.property⟩
    refine ⟨⟨x,?_⟩,Subtype.ext ?_⟩
    · change (f x).val ∈ M22
      rw [hx]
      exact y.property
    · change (f x).val=y.val
      exact congrArg Subtype.val hx
  have hgk : g.ker = f.ker.subgroupOf P := by
    ext p
    change (⟨(f p.val).val,p.property⟩ : M22)=1 ↔ f p.val=1
    rw [Subtype.ext_iff,Subtype.ext_iff]
    rfl
  have hgc : g.ker ≤ center P := by
    rw [hgk]
    exact fun p hp => mem_center_iff.mpr (fun q =>
      Subtype.ext (mem_center_iff.mp (hc hp) q.val))
  have hcard : Nat.card g.ker = 2 := by
    rw [hgk,Nat.card_congr (subgroupOfEquivOfLe (f.ker_le_comap _)).toEquiv,hk]
  have hsq : (g ⟨x,hi⟩)^2=1 := by
    apply Subtype.ext
    change (f x).val^2=1
    exact congrArg Subtype.val hx
  exact congrArg Subtype.val (inner_square g hg hgc hcard ⟨x,hi⟩ hsq)

omit [Finite E] in
private theorem square_of_conjugate (f : E →* m22DesignAut)
    (hf : Function.Surjective f) (hc : f.ker ≤ center E) (hk : Nat.card f.ker = 2)
    (x y : E) (hs : (f x)^2=1)
    (a : m22DesignAut) (ha : a*f x*a⁻¹=f y) : x^2=y^2 := by
  obtain ⟨b,rfl⟩ := hf a
  have hz : x^2 ∈ center E := hc (by rw [MonoidHom.mem_ker,map_pow,hs])
  have hconj : (b*x*b⁻¹)^2=x^2 := by
    calc
      _ = b*x^2*b⁻¹ := by simp only [pow_two]; group
      _ = x^2 := by rw [mem_center_iff.mp hz b,mul_inv_cancel_right]
  rw [←hconj]
  exact PerfectCentralCovering.square_eq_of_map_eq_of_kernel_exponent_two f hc
    (kernel_square f hk) (by simpa only [map_mul,map_inv] using ha)

private theorem linked_square (f : E →* m22DesignAut) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : Nat.card f.ker = 2)
    (x y : E) (hx : f x=first) (hy : f y=second) : x^2=y^2 := by
  obtain ⟨r,hr⟩ := hf (root^2)
  have hr2 : r^2=1 := inner_square_one f hf hc hk r
    (by rw [hr,←pow_mul]; exact representative_relations.2.2.1)
    (by rw [hr]; exact M22.pow_mem root_inner 2)
  have hcomm : Commute r x := CentralExtension.commute_lifts_of_commuting_square_root
    f hf hc (root^2) first root rfl representative_relations.1
    representative_relations.2.2.2.1 r x hr hx
  have hmul : f (r*x)=f y := by
    rw [map_mul,hr,hx,hy,representative_relations.2.2.2.2]
  calc
    x^2 = (r*x)^2 := by rw [hcomm.mul_pow,hr2,one_mul]
    _ = y^2 := PerfectCentralCovering.square_eq_of_map_eq_of_kernel_exponent_two f hc
      (kernel_square f hk) hmul

/-- All outer-involution fibers have the same square in every central double
cover of the full M22 design automorphism group. This includes both classes. -/
theorem outer_square_eq (f : E →* m22DesignAut) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : Nat.card f.ker = 2)
    (x y : E) (hx : orderOf (f x)=2) (hy : orderOf (f y)=2)
    (hxo : (f x).val ∉ M22) (hyo : (f y).val ∉ M22) : x^2=y^2 := by
  obtain ⟨r,hr⟩ := hf first
  obtain ⟨t,ht⟩ := hf second
  have hrt := linked_square f hf hc hk r t hr ht
  have he (a : E) (ha : orderOf (f a)=2) (hao : (f a).val ∉ M22) : r^2=a^2 := by
    obtain ⟨g,hg|hg⟩ := exists_representative_conjugator (f a) ha hao
    · exact square_of_conjugate f hf hc hk r a
        (by rw [hr]; exact representative_relations.1) g (by rw [hr]; exact hg)
    · exact hrt.trans (square_of_conjugate f hf hc hk t a
        (by rw [ht]; exact representative_relations.2.1) g (by rw [ht]; exact hg))
  exact (he x hx hxo).symm.trans (he y hy hyo)

/-- A single involutory outer lift forces involutory lifts for every outer
involution of the literal quotient, not only its conjugacy class. -/
theorem outer_square_one (f : E →* m22DesignAut) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : Nat.card f.ker = 2)
    (s : E) (hs : s^2=1) (hso : (f s).val ∉ M22)
    (x : E) (hx : orderOf (f x)=2) (hxo : (f x).val ∉ M22) : x^2=1 := by
  have hn : f s ≠ 1 := fun he => hso (he ▸ M22.one_mem)
  have ho : orderOf (f s)=2 := orderOf_eq_prime_iff.mpr
    ⟨by rw [←map_pow,hs,map_one],hn⟩
  exact (outer_square_eq f hf hc hk x s hx ho hxo hso).trans hs

/-- The same result for the abstract automorphism group with its literal
inner subgroup: one split outer involution determines every involution fiber. -/
theorem aut_square_one (f : E →* MulAut M22) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : Nat.card f.ker = 2)
    (s : E) (hs : s^2=1) (hso : f s ∉ MulAut.innerSubgroup M22)
    (x : E) (hx : (f x)^2=1) : x^2=1 := by
  let d : m22DesignAut ≃* MulAut M22 :=
    MulEquiv.ofBijective m22DesignAutToAut
      ⟨m22DesignAutToAut_injective,m22DesignAutToAut_surjective⟩
  let g := d.symm.toMonoidHom.comp f
  have hg : Function.Surjective g := d.symm.surjective.comp hf
  have hgker : g.ker=f.ker := MonoidHom.ker_comp_of_injective _ _ d.symm.injective
  have hgc : g.ker ≤ center E := hgker ▸ hc
  have hgk : Nat.card g.ker=2 := hgker ▸ hk
  have hgi (a : E) : (g a).val ∈ M22 ↔ f a ∈ MulAut.innerSubgroup M22 := by
    rw [← induced_inner_iff]
    have he : m22DesignAutToAut (g a)=f a := d.apply_symm_apply (f a)
    rw [he]
    constructor
    · rintro ⟨b,hb⟩
      exact ⟨b,hb.symm⟩
    · rintro ⟨b,hb⟩
      exact ⟨b,hb.symm⟩
  have hxs : (g x)^2=1 := by
    change (d.symm (f x))^2=1
    rw [←map_pow,hx,map_one]
  by_cases hi : (g x).val ∈ M22
  · exact inner_square_one g hg hgc hgk x hxs hi
  · have hxn : g x ≠ 1 := fun he => hi (he ▸ M22.one_mem)
    exact outer_square_one g hg hgc hgk s hs (fun he => hso ((hgi s).mp he)) x
      (orderOf_eq_prime_iff.mpr ⟨hxs,hxn⟩) hi

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OuterSquare
