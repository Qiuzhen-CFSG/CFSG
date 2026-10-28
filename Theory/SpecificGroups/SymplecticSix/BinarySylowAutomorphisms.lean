module
public import Theory.SpecificGroups.SymplecticSix.BinaryFrattiniSixteen
public import Theory.GroupAction.FaithfulSixteen
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel

/-!
# The binary symplectic six-space Sylow automorphism obstruction

A Sylow subgroup of Sp₆(2) is parametrized by an upper unitriangular three-block
A and a symmetric three-block S, acting as [[A,AS],[0,A⁻ᵀ]]. The nine binary
coordinates give an injective group map with image of order 512, hence Sylow.
The four-coordinate quotient is elementary abelian of order sixteen; the
existing Frattini upper bound identifies its kernel with the actual Frattini
subgroup.

The centralizer of that characteristic subgroup has a nontrivial proper image
in the Frattini quotient: the middle diagonal shear lies outside the kernel,
whereas commuting with a particular kernel element forces the first coordinate
to vanish. Every automorphism preserves this image. A faithful factor-five
action on sixteen elements is irreducible, and the Burnside basis kernel is a
two-group, so five cannot divide the Sylow automorphism order. The final result
transports through the literal binary field and projective model marking.

This is the Sylow restriction needed for Aschbacher--Smith 4.4.10--11 and 12.1.9,
printed pp.621 and 793. It does not require a classification of automorphisms.
-/

open Subgroup Matrix
namespace Theory.SpecificGroups.SymplecticSix.BinarySylowAutomorphisms
@[ext] structure Parameters where
  val : Fin 9 → ZMod 2
  deriving Fintype, DecidableEq
instance : CoeFun Parameters (fun _ => Fin 9 → ZMod 2) := ⟨Parameters.val⟩
def coord : Fin 3 ⊕ Fin 3 → Fin 6 :=
  Sum.elim (fun i => ⟨i, by omega⟩) (fun i => ⟨i + 3, by omega⟩)
def matrix (x : Parameters) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  fun i j => (
    ![![1,x 0,x 1,x 3+x 0*x 4+x 1*x 5,x 4+x 0*x 6+x 1*x 7,x 5+x 0*x 7+x 1*x 8],
      ![0,1,x 2,x 4+x 2*x 5,x 6+x 2*x 7,x 7+x 2*x 8],
      ![0,0,1,x 5,x 7,x 8],
      ![0,0,0,1,0,0],
      ![0,0,0,x 0,1,0],
      ![0,0,0,x 1+x 0*x 2,x 2,1]] : Fin 6 → Fin 6 → ZMod 2) (coord i) (coord j)
def product (x y : Parameters) : Parameters :=
  ⟨![x 0+y 0,x 1+y 1+x 0*y 2,x 2+y 2,
    y 3+x 3+(y 0)^2*x 6+(y 1+y 0*y 2)^2*x 8,
    y 4+x 4+y 2*x 5+y 0*x 6+y 1*x 7+(y 1+y 0*y 2)*y 2*x 8,
    y 5+x 5+y 0*x 7+(y 1+y 0*y 2)*x 8,
    y 6+x 6+(y 2)^2*x 8,y 7+x 7+y 2*x 8,y 8+x 8]⟩
def inverse (x : Parameters) : Parameters :=
  ⟨![x 0,x 1+x 0*x 2,x 2,x 3+(x 0)^2*x 6+(x 1)^2*x 8,
    x 4+x 2*x 5+x 0*x 6+(x 0*x 2+x 1)*x 7+x 1*x 2*x 8,
    x 5+x 0*x 7+x 1*x 8,x 6+(x 2)^2*x 8,x 7+x 2*x 8,x 8]⟩
private theorem matrix_injective : Function.Injective matrix := by
  intro x y h
  have h0 := congrFun (congrFun h (.inl 0)) (.inl 1)
  have h1 := congrFun (congrFun h (.inl 0)) (.inl 2)
  have h2 := congrFun (congrFun h (.inl 1)) (.inl 2)
  have h5 := congrFun (congrFun h (.inl 2)) (.inr 0)
  have h7 := congrFun (congrFun h (.inl 2)) (.inr 1)
  have h8 := congrFun (congrFun h (.inl 2)) (.inr 2)
  have h4 := congrFun (congrFun h (.inl 1)) (.inr 0)
  have h6 := congrFun (congrFun h (.inl 1)) (.inr 1)
  have h3 := congrFun (congrFun h (.inl 0)) (.inr 0)
  change x 0 = y 0 at h0
  change x 1 = y 1 at h1
  change x 2 = y 2 at h2
  change x 5 = y 5 at h5
  change x 7 = y 7 at h7
  change x 8 = y 8 at h8
  change x 4 + x 2*x 5 = y 4+y 2*y 5 at h4
  change x 6 + x 2*x 7 = y 6+y 2*y 7 at h6
  change x 3+x 0*x 4+x 1*x 5 = y 3+y 0*y 4+y 1*y 5 at h3
  have he4 : x 4 = y 4 := by simpa only [h2,h5,add_left_inj] using h4
  have he6 : x 6 = y 6 := by simpa only [h2,h7,add_left_inj] using h6
  have he3 : x 3 = y 3 := by simpa only [h0,h1,h5,he4,add_left_inj] using h3
  apply Parameters.ext
  funext i
  fin_cases i <;> assumption
private theorem matrix_zero : matrix (⟨fun _ => 0⟩ : Parameters) = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;> simp [matrix,coord]
private theorem matrix_product (x y : Parameters) :
    matrix (product x y) = matrix x * matrix y := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [matrix,product,coord,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_succ] <;>
    ring_nf <;>
    simp only [show (2 : ZMod 2) = 0 from rfl,
      mul_zero,add_zero,ZMod.pow_card] <;> ring_nf <;>
    simp [show (2 : ZMod 2) = 0 from rfl]
private theorem inverse_product (x : Parameters) : product (inverse x) x = (⟨fun _ => 0⟩ : Parameters) := by
  apply Parameters.ext
  funext i
  fin_cases i <;> simp [product,inverse] <;> ring_nf <;>
    simp only [show (2 : ZMod 2) = 0 from rfl, show (4 : ZMod 2) = 0 from rfl,
      mul_zero,add_zero,zero_add,ZMod.pow_card]
  ring_nf
  simp [show (2 : ZMod 2) = 0 from rfl]
instance : Group Parameters where
  one := ⟨fun _ => 0⟩
  mul := product
  inv := inverse
  mul_assoc x y z := by
    apply matrix_injective
    change matrix (product (product x y) z) = matrix (product x (product y z))
    simp only [matrix_product,mul_assoc]
  one_mul x := by
    apply matrix_injective
    change matrix (product (⟨fun _ => 0⟩ : Parameters) x) = matrix x
    rw [matrix_product,matrix_zero,one_mul]
  mul_one x := by
    apply matrix_injective
    change matrix (product x (⟨fun _ => 0⟩ : Parameters)) = matrix x
    rw [matrix_product,matrix_zero,mul_one]
  inv_mul_cancel x := by exact inverse_product x
private theorem matrix_mem (x : Parameters) : matrix x ∈ symplecticGroup (Fin 3) (ZMod 2) := by
  change matrix x * Matrix.J _ _ * (matrix x).transpose = Matrix.J _ _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [matrix,coord,Matrix.J,Matrix.fromBlocks,Matrix.mul_apply,Matrix.one_apply,
      Fintype.sum_sum_type,Fin.sum_univ_succ] <;> ring_nf <;>
    simp [show (2 : ZMod 2) = 0 from rfl, show (4 : ZMod 2) = 0 from rfl]
def embedding : Parameters →* Sp (ZMod 2) where
  toFun x := ⟨matrix x,by exact matrix_mem x⟩
  map_one' := by exact Subtype.ext matrix_zero
  map_mul' x y := by exact Subtype.ext (matrix_product x y)
theorem embedding_injective : Function.Injective embedding :=
  fun _ _ h => matrix_injective (congrArg Subtype.val h)
theorem card_parameters : Nat.card Parameters = 512 := by
  rw [Nat.card_congr (show Parameters ≃ (Fin 9 → ZMod 2) from
    ⟨Parameters.val,Parameters.mk,fun _ => rfl,fun _ => rfl⟩)]
  simp
theorem parameters_two : IsPGroup 2 Parameters :=
  IsPGroup.of_card (p := 2) (n := 9) card_parameters
noncomputable def sylow : Sylow 2 (Sp (ZMod 2)) :=
  (parameters_two.of_surjective embedding.rangeRestrict embedding.rangeRestrict_surjective).toSylow (by
    have hc := embedding.range.index_mul_card
    rw [Nat.card_congr (MonoidHom.ofInjective embedding_injective).toEquiv.symm,
      card_parameters,card_sp_of_card_two (by simp)] at hc
    omega)
noncomputable def sylowEquiv : Parameters ≃* sylow :=
  MonoidHom.ofInjective embedding_injective

private abbrev E := Multiplicative (Fin 4 → ZMod 2)
private def quotientMap : Parameters →* E where
  toFun x := Multiplicative.ofAdd ![x 0,x 2,x 8,x 6+x 7]
  map_one' := by
    apply Equiv.injective Multiplicative.toAdd
    funext i
    fin_cases i <;> rfl
  map_mul' x y := by
    apply Equiv.injective Multiplicative.toAdd
    funext i
    change (![ (product x y) 0,(product x y) 2,(product x y) 8,
      (product x y) 6+(product x y) 7] : Fin 4 → ZMod 2) i =
      (![x 0,x 2,x 8,x 6+x 7] + ![y 0,y 2,y 8,y 6+y 7]) i
    fin_cases i <;> simp [product]
    · exact add_comm _ _
    · calc
        _ = (x 6+x 7+(y 6+y 7)) + (y 2*x 8+y 2*x 8) := by abel
        _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]
private theorem quotientMap_surjective : Function.Surjective quotientMap := by
  intro x
  refine ⟨⟨![x.toAdd 0,0,x.toAdd 1,0,0,0,x.toAdd 3,0,x.toAdd 2]⟩,?_⟩
  apply Equiv.injective Multiplicative.toAdd
  funext i
  fin_cases i <;> simp [quotientMap]
private theorem elementary_E : IsElementaryAbelian 2 E where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro x
    apply Equiv.injective Multiplicative.toAdd
    funext i
    change (2 • x.toAdd) i = 0
    simp [two_smul,CharTwo.add_self_eq_zero])
private theorem frattini_eq_kernel : frattini Parameters = quotientMap.ker := by
  let : IsElementaryAbelian 2 E := elementary_E
  let : Fact (IsPGroup 2 E) := ⟨IsPGroup.of_card (p := 2) (n := 4) (by simp [E])⟩
  have hle : frattini Parameters ≤ quotientMap.ker := by
    have hh := frattini_le_comap_frattini_of_surjective (φ := quotientMap) quotientMap_surjective
    rw [frattini_eq_bot_of_isElementaryAbelian (R := E) (p := 2)] at hh
    intro x hx
    exact hh hx
  have hquot : Nat.card (Parameters ⧸ frattini Parameters) ≤ 16 := by
    rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr sylowEquiv]
    exact BinaryFrattiniSixteen.frattini_card_le_sixteen sylow
  have hcard := card_eq_card_quotient_mul_card_subgroup (frattini Parameters)
  rw [card_parameters] at hcard
  have hker := card_eq_card_quotient_mul_card_subgroup quotientMap.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective quotientMap
    quotientMap_surjective).toEquiv,card_parameters] at hker
  have hE : Nat.card E = 16 := by simp [E]
  rw [hE] at hker
  apply eq_of_le_of_card_ge hle
  nlinarith
private theorem frattini_card : Nat.card (Parameters ⧸ frattini Parameters) = 16 := by
  rw [frattini_eq_kernel,Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
    quotientMap quotientMap_surjective).toEquiv]
  simp [E]
private theorem kernel_mem (x : Parameters) : x ∈ quotientMap.ker ↔
    x 0 = 0 ∧ x 2 = 0 ∧ x 8 = 0 ∧ x 6+x 7 = 0 := by
  change Multiplicative.ofAdd ![x 0,x 2,x 8,x 6+x 7] = 1 ↔ _
  constructor
  · intro h
    have he := congrArg Multiplicative.toAdd h
    exact ⟨congrFun he 0,congrFun he 1,congrFun he 2,congrFun he 3⟩
  · rintro ⟨h0,h2,h8,h67⟩
    apply Equiv.injective Multiplicative.toAdd
    funext i
    fin_cases i <;> simp [h0,h2,h8,h67]
private def centralElement : Parameters := ⟨![0,0,0,0,0,0,1,0,0]⟩
private theorem centralElement_mem : centralElement ∈ centralizer (frattini Parameters : Set Parameters) := by
  rw [mem_centralizer_iff]
  intro x hx
  rw [frattini_eq_kernel] at hx
  have hx := (kernel_mem x).mp hx
  change product x centralElement = product centralElement x
  apply Parameters.ext
  funext i
  fin_cases i <;> simp [product,centralElement,hx.1,hx.2.1,add_comm]
private theorem centralElement_not_mem : centralElement ∉ frattini Parameters := by
  rw [frattini_eq_kernel,kernel_mem]
  simp [centralElement]
private theorem centralizer_first_zero (x : Parameters)
    (hx : x ∈ centralizer (frattini Parameters : Set Parameters)) : x 0 = 0 := by
  let y : Parameters := ⟨![0,0,0,0,0,0,1,1,0]⟩
  have hy : y ∈ frattini Parameters := by
    rw [frattini_eq_kernel,kernel_mem]
    decide
  have he := congrArg (fun z : Parameters => z 5) ((mem_centralizer_iff.mp hx) y hy)
  change (product y x) 5 = (product x y) 5 at he
  simpa [product,y] using he

private theorem not_five_dvd_parameters_aut : ¬5 ∣ Nat.card (MulAut Parameters) := by
  let C := centralizer (frattini Parameters : Set Parameters)
  let π := QuotientGroup.mk' (frattini Parameters)
  let D := C.map π
  let α := quotientAut (frattini Parameters)
  have hD (a : MulAut Parameters) (v : Parameters ⧸ frattini Parameters)
      (hv : v ∈ D) : α a v ∈ D := by
    obtain ⟨x,hx,rfl⟩ := hv
    rw [quotientAut_apply_mk]
    exact mem_map_of_mem _
      ((characteristic_iff_map_le.mp (inferInstance : C.Characteristic) a) (mem_map_of_mem _ hx))
  have hbot : D ≠ ⊥ := by
    intro h
    have hv : π centralElement ∈ D := mem_map_of_mem _ centralElement_mem
    rw [h,mem_bot] at hv
    exact centralElement_not_mem ((QuotientGroup.eq_one_iff _).mp hv)
  have htop : D ≠ ⊤ := by
    intro h
    let z : Parameters := ⟨![1,0,0,0,0,0,0,0,0]⟩
    have hz : π z ∈ D := h ▸ mem_top _
    obtain ⟨x,hx,he⟩ := hz
    have hx0 := centralizer_first_zero x hx
    have heq : quotientMap x = quotientMap z := congrArg
      (QuotientGroup.lift (frattini Parameters) quotientMap frattini_eq_kernel.le) he
    have he0 := congrArg (fun t : E => t.toAdd 0) heq
    change x 0 = 1 at he0
    exact zero_ne_one (hx0.symm.trans he0)
  intro h5
  have hcount : Nat.card α.ker * Nat.card α.range = Nat.card (MulAut Parameters) := by
    rw [←index_ker]
    exact α.ker.card_mul_index
  obtain ⟨k,hk⟩ := (isPGroup_quotientAut_frattini_kernel parameters_two).exists_card_eq
  have hc : Nat.Coprime 5 (Nat.card α.ker) := by
    rw [hk]
    exact (by decide : Nat.Coprime 5 2).pow_right k
  have himage : 5 ∣ Nat.card α.range := by
    rw [←hcount] at h5
    exact hc.dvd_of_dvd_mul_left h5
  rcases Theory.GroupAction.invariant_eq_bot_or_top_of_image_five α himage frattini_card D
    (fun a v => ⟨hD a v,fun hv => by
      have hh := hD a⁻¹ (α a v) hv
      simpa only [map_inv,MulAut.inv_apply_self] using hh⟩) with hb | ht
  · exact hbot hb
  · exact htop ht

/-- The Sylow automorphism group of Sp₆(2) has no factor five: its action
on the order-sixteen Frattini quotient preserves a proper nontrivial subgroup. -/
public theorem not_five_dvd_sylow_aut (P : Sylow 2 (Sp (ZMod 2))) :
    ¬5 ∣ Nat.card (MulAut P) := by
  let e : P ≃* Parameters := (P.equiv sylow).trans sylowEquiv.symm
  rw [Nat.card_congr (MulAut.congr e).toEquiv]
  exact not_five_dvd_parameters_aut

/-- The obstruction transports through the literal projective model and binary field. -/
public theorem not_five_dvd_sylow_aut_of_equiv {A F : Type*}
    [Group A] [Finite A] [Field F] [Finite F]
    (hF : Nat.card F = 2) (e : A ≃* PSp F) (P : Sylow 2 A) :
    ¬5 ∣ Nat.card (MulAut P) := by
  let a : A ≃* Sp (ZMod 2) :=
    (e.trans (pspFieldEquivZModTwo F hF)).trans EvenProjective.equiv.symm
  let Q := P.mapSurjective (f := a.toMonoidHom) a.surjective
  let b : P ≃* Q := a.subgroupMap (P : Subgroup A)
  rw [Nat.card_congr (MulAut.congr b).toEquiv]
  exact not_five_dvd_sylow_aut Q

end Theory.SpecificGroups.SymplecticSix.BinarySylowAutomorphisms
