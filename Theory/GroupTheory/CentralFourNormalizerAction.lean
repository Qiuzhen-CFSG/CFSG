module
public import Theory.GroupTheory.CenterPairMarks
public import Theory.GroupTheory.TwoGroupSquareChoice
/-! # The crossing action on a central four-group
When the t-centralizer inside a two-group is S and Z(S) is a four-group,
an outside normalizer element fixes the ambient central mark z and exchanges
t with tz. The same calculation gives |N_T(S):S|=2.
Source: Aschbacher--Smith 2.5.13(1), printed p.558.
-/
public section
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
omit [Finite G] in
theorem normalizer_crossing_on_central_four
    (S T:Subgroup G) (hST:S≤T) [IsKleinFour (centerIn S)]
    (t z:G) (ht:orderOf t=2) (hz:orderOf z=2)
    (htS:t∈centerIn S) (hzT:z∈centerIn T) (htz:t≠z)
    (hCt:T⊓centralizer ({t}:Set G)=S)
    (x:G) (hxT:x∈T) (hxN:x∈normalizer (S:Set G)) (hxS:x∉S) :
    x⁻¹*t*x=t*z := by
  have hzS:z∈centerIn S:=⟨(hCt ▸ ⟨hzT.1,mem_centralizer_singleton_iff.mpr
    ((hzT.2 t (hST htS.1)).symm)⟩),fun a ha=>hzT.2 a (hST ha)⟩
  have hxZ:x⁻¹∈normalizer (centerIn S:Set G):=
    normalizes_centerIn (S:=S) (A:=normalizer (S:Set G)) le_rfl
      ((normalizer (S:Set G)).inv_mem hxN)
  have hwZ:x⁻¹*t*x∈centerIn S:=by
    have hh:x⁻¹*t*x⁻¹⁻¹∈centerIn S:=(hxZ t).mp htS
    rwa [inv_inv] at hh
  have ht1:t≠1:=by intro h;rw [h,orderOf_one] at ht;omega
  have hz1:z≠1:=by intro h;rw [h,orderOf_one] at hz;omega
  have hw1:x⁻¹*t*x≠1:=by
    intro h
    apply ht1
    calc t=x*(x⁻¹*t*x)*x⁻¹:=by group
         _=1:=by rw [h];group
  have hwt:x⁻¹*t*x≠t:=by
    intro h
    apply hxS
    rw [←hCt]
    refine ⟨hxT,mem_centralizer_singleton_iff.mpr ?_⟩
    have hh:=congrArg (fun a=>x*a) h
    simpa only [mul_assoc,mul_inv_cancel_left] using hh.symm
  have hwz:x⁻¹*t*x≠z:=by
    intro h
    apply htz
    calc t=x*(x⁻¹*t*x)*x⁻¹:=by group
         _=z:=by rw [h,hzT.2 x hxT,mul_inv_cancel_right]
  have he:=IsKleinFour.eq_mul_of_ne_all
    (x:=(⟨t,htS⟩:centerIn S)) (y:=(⟨z,hzS⟩:centerIn S)) (z:=(⟨x⁻¹*t*x,hwZ⟩:centerIn S))
    (fun h=>ht1 (congrArg Subtype.val h)) (fun h=>hz1 (congrArg Subtype.val h))
    (fun h=>htz (congrArg Subtype.val h)) (fun h=>hw1 (congrArg Subtype.val h))
    (fun h=>hwt (congrArg Subtype.val h)) (fun h=>hwz (congrArg Subtype.val h))
  exact congrArg Subtype.val he

theorem normalizer_index_two_of_central_four
    (S T:Subgroup G) (hT:IsPGroup 2 T) (hST:S<T) [IsKleinFour (centerIn S)]
    (t z:G) (ht:orderOf t=2) (hz:orderOf z=2)
    (htS:t∈centerIn S) (hzT:z∈centerIn T) (htz:t≠z)
    (hCt:T⊓centralizer ({t}:Set G)=S) :
    S.relIndex (T⊓normalizer (S:Set G))=2 := by
  obtain ⟨x,hxT,hxS,hxN,_⟩:=exists_outside_normalizer_square_mem S T hT hST
  have hx:=normalizer_crossing_on_central_four S T hST.le t z ht hz htS hzT htz hCt x hxT hxN hxS
  apply relIndex_eq_two_iff_exists_notMem_and'.mpr
  refine ⟨x,⟨hxT,hxN⟩,hxS,?_⟩
  intro b hb
  by_cases hbs:b∈S
  · exact Or.inr hbs
  apply Or.inl
  rw [←hCt]
  refine ⟨T.mul_mem hxT hb.1,mem_centralizer_singleton_iff.mpr ?_⟩
  have hb':=normalizer_crossing_on_central_four S T hST.le t z ht hz htS hzT htz hCt b hb.1 hb.2 hbs
  have hzz:z*z=1:=by
    have hh:z^2=1:=by rw [←hz];exact pow_orderOf_eq_one z
    simpa only [pow_two] using hh
  have hfix:(x*b)⁻¹*t*(x*b)=t:=by
    calc
      _=b⁻¹*(x⁻¹*t*x)*b:=by group
      _=(b⁻¹*t*b)*(b⁻¹*z*b):=by rw [hx];group
      _= (t*z)*z:=by rw [hb',hzT.2 b⁻¹ (T.inv_mem hb.1)];group
      _=t:=by rw [mul_assoc,hzz,mul_one]
  have hh:=congrArg (fun a=>(x*b)*a) hfix
  simpa only [mul_assoc,mul_inv_cancel_left] using hh.symm
omit [Finite G] in
theorem fixed_mark_of_central_four_crossing
    (S T:Subgroup G) (hST:S≤T) [IsKleinFour (centerIn S)]
    (t z:G) (ht:orderOf t=2) (hz:orderOf z=2)
    (htS:t∈centerIn S) (hzT:z∈centerIn T) (htz:t≠z)
    (hCt:T⊓centralizer ({t}:Set G)=S)
    (x:G) (hxT:x∈T) (hxN:x∈normalizer (S:Set G)) (hxS:x∉S)
    (k:G) (hk:orderOf k=2) (hkS:k∈centerIn S) (hfix:x⁻¹*k*x=k) : k=z := by
  have hzS:z∈centerIn S:=⟨(hCt ▸ ⟨hzT.1,mem_centralizer_singleton_iff.mpr
    ((hzT.2 t (hST htS.1)).symm)⟩),fun a ha=>hzT.2 a (hST ha)⟩
  have hc:=normalizer_crossing_on_central_four S T hST t z ht hz htS hzT htz hCt x hxT hxN hxS
  have ht1:t≠1:=by intro h;rw [h,orderOf_one] at ht;omega
  have hz1:z≠1:=by intro h;rw [h,orderOf_one] at hz;omega
  have hk1:k≠1:=by intro h;rw [h,orderOf_one] at hk;omega
  have hkt:k≠t:=by
    intro h
    rw [h,hc] at hfix
    exact hz1 (mul_left_cancel (hfix.trans (mul_one t).symm))
  by_contra hkz
  have hthird:=IsKleinFour.eq_mul_of_ne_all
    (x:=(⟨t,htS⟩:centerIn S)) (y:=(⟨z,hzS⟩:centerIn S)) (z:=(⟨k,hkS⟩:centerIn S))
    (fun h=>ht1 (congrArg Subtype.val h)) (fun h=>hz1 (congrArg Subtype.val h))
    (fun h=>htz (congrArg Subtype.val h)) (fun h=>hk1 (congrArg Subtype.val h))
    (fun h=>hkt (congrArg Subtype.val h)) (fun h=>hkz (congrArg Subtype.val h))
  have hke:k=t*z:=congrArg Subtype.val hthird
  have hzz:z*z=1:=by
    have hh:z^2=1:=by rw [←hz];exact pow_orderOf_eq_one z
    simpa only [pow_two] using hh
  apply hkt
  calc
    k=x⁻¹*k*x:=hfix.symm
    _=(x⁻¹*t*x)*(x⁻¹*z*x):=by rw [hke];group
    _=(t*z)*z:=by rw [hc,hzT.2 x⁻¹ (T.inv_mem hxT)];group
    _=t:=by rw [mul_assoc,hzz,mul_one]
end Subgroup
