module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Thompson
public import Theory.GroupTheory.TwoPlaneCover
/-! # Commutator rows in the binary symplectic Sylow group
The four actual root coordinates identify each noncentral involution
centralizer as a wing. Its index and commutator row have order q. The same
calculation holds through a cover with elementary wing preimages.
Source: Aschbacher--Smith 2.5.7, printed pp.555--556.
-/
public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry
variable {F:Type*} [Field F] [Finite F] [CharP F 2]
private def outerPair : unipotent (F:=F)→*Multiplicative (F×F) where
  toFun x:=Multiplicative.ofAdd (x.val.val (.inl 0) (.inl 1),x.val.val (.inl 1) (.inr 1))
  map_one':=rfl
  map_mul' x y:=by
    obtain ⟨⟨b,u,w,v⟩,rfl⟩:=element_surjective x
    obtain ⟨⟨c,z,t,a⟩,rfl⟩:=element_surjective y
    change Multiplicative.ofAdd ((element b u w v*element c z t a).val.val (.inl 0) (.inl 1),
      (element b u w v*element c z t a).val.val (.inl 1) (.inr 1))=_
    rw [element_mul]
    simp only [element_matrix]
    rfl
private theorem outerPair_element (b u w v:F) : outerPair (element b u w v)=Multiplicative.ofAdd (b,v) := by
  change Multiplicative.ofAdd ((element b u w v).val.val (.inl 0) (.inl 1),
    (element b u w v).val.val (.inl 1) (.inr 1))=_
  rw [element_matrix]
  rfl
private theorem outerPair_ker : (outerPair (F:=F)).ker=center (unipotent (F:=F)) := by
  ext a
  obtain ⟨⟨b,u,w,v⟩,rfl⟩:=element_surjective a
  rw [mem_center_iff_coordinates]
  change outerPair (element b u w v)=1 ↔ _
  rw [outerPair_element]
  change (b,v)=(0,0) ↔ _
  exact Prod.mk_inj

theorem class_two : _root_.commutator (unipotent (F:=F))≤center (unipotent (F:=F)) := by
  rw [←outerPair_ker]
  apply commutator_le.mpr
  intro a _ b _
  change outerPair ⁅a,b⁆=1
  rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

theorem center_le_wings : center (unipotent (F:=F))≤wing false⊓wing true := by
  intro a ha
  obtain ⟨⟨b,u,w,v⟩,rfl⟩:=element_surjective a
  obtain ⟨rfl,rfl⟩:=(mem_center_iff_coordinates b u w v).mp ha
  exact ⟨(element_mem_wing _ _ _ _ _).mpr rfl,(element_mem_wing _ _ _ _ _).mpr rfl⟩

theorem centralizer_involution (a:unipotent (F:=F)) (ha:a^2=1)
    (hz:a∉center (unipotent (F:=F))) :
    centralizer ({a}:Set (unipotent (F:=F)))=wing false ∨
      centralizer ({a}:Set (unipotent (F:=F)))=wing true := by
  obtain ⟨⟨b,u,w,v⟩,rfl⟩:=element_surjective a
  rw [element_square,theta,←element_zero,element_eq_iff] at ha
  have hbv:b=0∨v=0:=mul_eq_zero.mp ha.2.2.1
  rw [mem_center_iff_coordinates] at hz
  rcases hbv with rfl|rfl
  · right
    have hv:v≠0:=fun h=>hz ⟨rfl,h⟩
    ext x
    obtain ⟨⟨c,z,t,d⟩,rfl⟩:=element_surjective x
    rw [mem_centralizer_singleton_iff,element_mem_wing,element_mul,element_mul,element_eq_iff]
    simp only [↓reduceIte,zero_add,add_zero,zero_mul,mul_zero]
    constructor
    · intro h
      have hh:v*c=0:=by linear_combination -h.2.2.1
      exact (mul_eq_zero.mp hh).resolve_left hv
    · rintro rfl
      simp [add_comm]
  · left
    have hb:b≠0:=fun h=>hz ⟨h,rfl⟩
    ext x
    obtain ⟨⟨c,z,t,d⟩,rfl⟩:=element_surjective x
    rw [mem_centralizer_singleton_iff,element_mem_wing,element_mul,element_mul,element_eq_iff]
    simp only [Bool.false_eq_true,↓reduceIte,zero_add,add_zero,zero_mul,mul_zero]
    constructor
    · intro h
      have hh:d*b=0:=by linear_combination h.2.2.1
      exact (mul_eq_zero.mp hh).resolve_right hb
    · rintro rfl
      simp [add_comm,add_left_comm,add_assoc,mul_comm]

theorem involution_centralizer_index (a:unipotent (F:=F)) (ha:a^2=1)
    (hz:a∉center (unipotent (F:=F))) :
    (centralizer ({a}:Set (unipotent (F:=F)))).index=Nat.card F := by
  have hcard:Nat.card (centralizer ({a}:Set (unipotent (F:=F))))=Nat.card F^3:=by
    rcases centralizer_involution a ha hz with h|h <;> rw [h,card_wing]
  have hc:0<Nat.card F^3:=pow_pos Nat.card_pos 3
  apply Nat.eq_of_mul_eq_mul_left hc
  rw [←hcard,Subgroup.card_mul_index,card_unipotent,hcard]
  ring

variable {E:Type*} [Group E] [Finite E]
/-- The source central-cover calculation keeps the exact marked kernel. -/
theorem cover_involution_commutator
    (f:E→*unipotent (F:=F)) (hf:Function.Surjective f)
    [IsElementaryAbelian 2 ((wing (F:=F) false).comap f)]
    [IsElementaryAbelian 2 ((wing (F:=F) true).comap f)]
    (a:E) (ha:a^2=1) (hz:a∉center E) :
    _root_.commutator E≤center E ∧
      centralizer ({a}:Set E)=(centralizer ({f a}:Set (unipotent (F:=F)))).comap f ∧
      Nat.card (⁅zpowers a,⊤⁆:Subgroup E)=Nat.card F ∧
      Disjoint (⁅zpowers a,⊤⁆:Subgroup E) f.ker := by
  have hz:f a∉center _:=by
    intro hh
    apply hz
    rw [Subgroup.TwoPlaneCover.center_eq_comap f hf (wing (F:=F) false) (wing (F:=F) true)
      wings_generate center_le_wings]
    exact hh
  have hc:=Subgroup.TwoPlaneCover.class_two f hf (wing (F:=F) false) (wing (F:=F) true)
    wings_generate center_le_wings class_two
  have hp:(f a)^2=1:=by rw [←map_pow,ha,map_one]
  have he:centralizer ({a}:Set E)=(centralizer ({f a}:Set (unipotent (F:=F)))).comap f:=by
    have hplanes:=centralizer_involution (f a) hp hz
    rcases hplanes with h|h
    all_goals
      have hi:IsMulCommutative ((centralizer ({f a}:Set (unipotent (F:=F)))).comap f):=by
        rw [h];infer_instance
      let :=hi
      exact Subgroup.TwoPlaneCover.centralizer_eq_comap f a
  exact ⟨hc,he,(Subgroup.TwoPlaneCover.commutator_card f hf hc a he).trans
    (involution_centralizer_index (f a) hp hz),Subgroup.TwoPlaneCover.commutator_disjoint_kernel f hc a he⟩
end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry
