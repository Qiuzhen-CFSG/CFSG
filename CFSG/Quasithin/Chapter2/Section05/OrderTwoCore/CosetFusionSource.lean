module
public import Theory.SpecificGroups.PSL2.InvolutionFusion
public import CFSG.Quasithin.Chapter2.Section05.OrderTwoCore.DerivedMarkSource
/-!
# The two involution classes in the order-two core branch

The actual crossing conjugates the core involution t to tz. All involutions
of a component marked as PSL₂(F) are conjugate inside that component. Since
t centralizes it, internal conjugation transports tz to every involution
of tK. Thus the component involutions lie in zᴳ and the coset involutions
lie in tᴳ, retaining the source nonfusion of those two classes.

The model-specific consumer supplies z∈K from the proved derived-line
argument, so it assumes no fusion or crossing witness.
Source: Aschbacher--Smith 2.5.21, printed p.565.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement ClassificationModels
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {H K M : Subgroup G}
  {S : Sylow 2 H} {z : G}

theorem MathieuSourceSetup.linear_core_coset_involution_fusion
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    (hgen : H=K⊔(S:Subgroup H).map H.subtype)
    (hb : ¬IsBenderModel K) (hzK : z∈K)
    (F : Type*) [Field F] [Finite F] (e : K≃*PSL(2,F)) :
    ∃t:G,orderOf t=2 ∧ t∈twoCore H ∧ H≤centralizer ({t}:Set G) ∧
      ¬IsConj t z ∧ IsConj t (t*z) ∧
      (∀k∈K,orderOf k=2→IsConj z k) ∧
      (∀k∈K,orderOf (t*k)=2→IsConj t (t*k)) := by
  obtain ⟨t,k,ht,_,htC,hline,_,_,_,hfour,_,htH,_,_,_,hnt⟩ :=
    MathieuSourceSetup.source_central_marks c hG hempty hgen hb
  have htZ : t∈centerIn ((S:Subgroup H).map H.subtype) :=
    (show t∈centerIn ((S:Subgroup H).map H.subtype)⊓twoCore H from
      hline.symm ▸ mem_zpowers t).1
  obtain ⟨x,hxT,hxS,hxN,_⟩ := exists_outside_normalizer_square_mem
    ((S:Subgroup H).map H.subtype) (c.T:Subgroup G) c.T.isPGroup' c.sylow_lt
  have hxt := (MathieuSourceSetup.source_crossing_on_center c hgen t ht htC htZ hfour).2
    x hxT hxN hxS
  have htz : IsConj t (t*z) := isConj_iff.mpr ⟨x⁻¹,by simpa only [inv_inv] using hxt⟩
  have hf (a:G) (ha:a∈K) (ho:orderOf a=2) :
      ∃u∈K,u*z*u⁻¹=a := by
    let za:K := ⟨z,hzK⟩
    let aa:K := ⟨a,ha⟩
    have hz : orderOf (e za)=2 := (e.orderOf_eq za).trans ((orderOf_coe za).symm.trans c.involution)
    have hao : orderOf (e aa)=2 := (e.orderOf_eq aa).trans ((orderOf_coe aa).symm.trans ho)
    have hi : IsConj za aa := by
      have hh := e.symm.toMonoidHom.map_isConj (Theory.PSL2.involutions_isConj (e za) (e aa) hz hao)
      simpa only [MulEquiv.coe_toMonoidHom,e.symm_apply_apply] using hh
    obtain ⟨u,hu⟩ := isConj_iff.mp hi
    exact ⟨u,u.property,congrArg Subtype.val hu⟩
  refine ⟨t,ht,htC,htH,hnt,htz,?_,?_⟩
  · intro a ha ho
    obtain ⟨u,_,hu⟩ := hf a ha ho
    exact isConj_iff.mpr ⟨u,hu⟩
  · intro a ha ho
    by_cases ha1:a=1
    · simpa only [ha1,mul_one] using (IsConj.refl t)
    have hcomm : Commute t a := (mem_centralizer_singleton_iff.mp (htH (c.component_le ha))).symm
    have ht2:t^2=1 := ht ▸ pow_orderOf_eq_one t
    have ha2:a^2=1 := by
      have hh : (t*a)^2=1 := ho ▸ pow_orderOf_eq_one (t*a)
      rwa [hcomm.mul_pow,ht2,one_mul] at hh
    obtain ⟨u,hu,he⟩ := hf a ha (orderOf_eq_prime_iff.mpr ⟨ha2,ha1⟩)
    apply htz.trans
    apply isConj_iff.mpr
    refine ⟨u,?_⟩
    have hut : u*t=t*u := mem_centralizer_singleton_iff.mp (htH (c.component_le hu))
    calc
      u*(t*z)*u⁻¹ = t*(u*z*u⁻¹) := by rw [←mul_assoc,hut];group
      _ = t*a := by rw [he]
/-- Literal PGL source consumer: the fixed-line and fusion conclusions are internal. -/
theorem MathieuSourceSetup.pgl_order_two_core_fusion
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    (hgen : H=K⊔(S:Subgroup H).map H.subtype)
    (hb : ¬IsBenderModel K) (hcore : Nat.card (twoCore H)=2)
    (F : Type*) [Field F] [Finite F]
    (hodd : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (eK : K≃*PSL(2,F)) (eQ : (H⧸pCore 2 H)≃*GorensteinWalter.PGL2 F) :
    ∃t:G,orderOf t=2 ∧ t∈twoCore H ∧ H≤centralizer ({t}:Set G) ∧
      ¬IsConj t z ∧ IsConj t (t*z) ∧
      (∀k∈K,orderOf k=2→IsConj z k) ∧
      (∀k∈K,orderOf (t*k)=2→IsConj t (t*k)) :=
  MathieuSourceSetup.linear_core_coset_involution_fusion c hG hempty hgen hb
    (MathieuSourceSetup.pgl_central_mark_mem_component_of_core_card_two
      c hG hempty hgen hb hcore F hodd eK eQ) F eK

/-- The M₁₀ source uses the actual PSL₂(9) coordinates of its A₆ component. -/
theorem MathieuSourceSetup.m10_order_two_core_fusion
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    (hgen : H=K⊔(S:Subgroup H).map H.subtype)
    (hb : ¬IsBenderModel K) (hcore : Nat.card (twoCore H)=2)
    (eK : K≃*AlternatingSix.ShadowLocal.A6)
    (eQ : (H⧸pCore 2 H)≃*AlternatingSix.M10.extension) :
    ∃t:G,orderOf t=2 ∧ t∈twoCore H ∧ H≤centralizer ({t}:Set G) ∧
      ¬IsConj t z ∧ IsConj t (t*z) ∧
      (∀k∈K,orderOf k=2→IsConj z k) ∧
      (∀k∈K,orderOf (t*k)=2→IsConj t (t*k)) :=
  MathieuSourceSetup.linear_core_coset_involution_fusion c hG hempty hgen hb
    (MathieuSourceSetup.m10_central_mark_mem_component_of_core_card_two
      c hG hempty hgen hb hcore eK eQ) Atlas.Comparisons.Exceptional.Nine.F
    (eK.trans Atlas.Comparisons.Exceptional.psl2NineCoordinatesEquivAlt6.symm)

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
