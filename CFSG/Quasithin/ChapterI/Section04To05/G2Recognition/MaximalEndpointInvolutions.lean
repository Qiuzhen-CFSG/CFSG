module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalAmbientSylow

/-!
# Torus alignment and original cubic-normalizer involutions

Sylow conjugacy inside the common Borel corrects the original Sylow
aligner so that it also preserves the original Klein four. The Borel
normalizes no additional torus elements: its odd complement-normalizer
centralizes the torus, whose centralizer has order prime to three.

The outer quaternion involution calculation supplies q in the opposite
factor with q²=z and nqn⁻¹=q⁻¹. Thus qn is an actual endpoint involution;
it fixes z and interchanges n and zn. Its nontrivial torus action places
it outside the whole Borel. Apply this on both sides and conjugate the
second involution with the torus-preserving Sylow aligner. Every Sylow
aligner moves z: otherwise the opposite derived cubic would lie in the
original fixed cubic, contradicting their proved nonconjugacy.

All endpoints, four-groups and involutions here belong to the original
I.4(G1)–(G2) configuration. The exact order-six product, compatible Atlas
endpoint maps, generation and recognition remain to be proved. The literal
source consumer is Chapter14EndpointInvolutions. Source: Aschbacher–Smith,
I.4.5, printed p.417, continuing Fong–Wong §3A–B, Nagoya Math. J.36 (1969),
pp.155–156; the quaternion calculation is the cited lower-layer theorem.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace CubicTorus
omit [Finite G] in
private theorem map_conj_mul (U : Subgroup G) (a b : G) :
    U.map (MulAut.conj (a*b)).toMonoidHom =
      (U.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  change (a*b)*x*(a*b)⁻¹=a*(b*x*b⁻¹)*a⁻¹
  group

omit [Finite G] in
private theorem map_conj_subtype (U B : Subgroup G) (hU : U≤B) (b : B) :
    ((U.subgroupOf B).map (MulAut.conj b).toMonoidHom).map B.subtype =
      U.map (MulAut.conj (b:G)).toMonoidHom := by
  rw [map_map]
  have he : B.subtype.comp (MulAut.conj b).toMonoidHom =
      (MulAut.conj (b:G)).toMonoidHom.comp B.subtype := by ext x; rfl
  rw [he,←map_map,map_subgroupOf_eq_of_le hU]

/-- Sylow alignment may be chosen to preserve the original torus. -/
theorem maximal_extensions_conjugate_in_torus_normalizer (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    ∃ g : G, g∈normalizer (t.torus.map c.H.subtype:Set G) ∧
      t.swap.leftCoreExtension.map (MulAut.conj g).toMonoidHom=t.leftCoreExtension := by
  obtain ⟨g,hg⟩ := t.maximal_extensions_conjugate hc
  let A := t.torus.map c.H.subtype
  let B := t.leftCubicBorel
  let Ag := A.map (MulAut.conj g).toMonoidHom
  have hAB : A≤B := le_sup_right
  have hAgB : Ag≤B := by
    change Ag≤t.leftCubicBorel
    rw [←t.maximal_aligned_borels hc g hg]
    exact map_mono (show A≤t.swap.leftCubicBorel from le_sup_right)
  have hAc : Nat.card A=4 := by
    let : IsKleinFour A := t.ambient_torus_kleinFour
    exact IsKleinFour.card_four
  have hAgc : Nat.card Ag=4 := by rw [card_map_of_injective (MulAut.conj g).injective,hAc]
  have sylow (U : Subgroup G) (hU : U≤B) (hcard : Nat.card U=4) :
      ∃ P : Sylow 2 B, (P:Subgroup B)=U.subgroupOf B := by
    have hh : Nat.card (U.subgroupOf B)=4 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hU).toEquiv,hcard]
    have hi : (U.subgroupOf B).index=729 := by
      have he := (U.subgroupOf B).card_mul_index
      rw [hh,t.maximal_leftCubicBorel_split hc |>.2.2.2] at he
      omega
    exact ⟨(IsPGroup.of_card (p:=2) (n:=2) hh).toSylow (by rw [hi]; decide),rfl⟩
  obtain ⟨P,hP⟩ := sylow Ag hAgB hAgc
  obtain ⟨Q,hQ⟩ := sylow A hAB hAc
  obtain ⟨b,hb⟩ := MulAction.exists_smul_eq B P Q
  have hb' := congrArg Sylow.toSubgroup hb
  change (P:Subgroup B).map (MulAut.conj b).toMonoidHom=(Q:Subgroup B) at hb'
  rw [hP,hQ] at hb'
  have hbA := congrArg (fun U : Subgroup B => U.map B.subtype) hb'
  rw [map_conj_subtype Ag B hAgB b,map_subgroupOf_eq_of_le hAB] at hbA
  refine ⟨(b:G)*g,mem_normalizer_iff_map_conj_eq.mpr ?_,?_⟩
  · change A.map (MulAut.conj ((b:G)*g)).toMonoidHom=A
    rw [map_conj_mul]
    exact hbA
  · rw [map_conj_mul,hg]
    apply mem_normalizer_iff_map_conj_eq.mp
    rw [t.maximal_sylow_normalizer_eq hc]
    exact b.property

private theorem right_quaternion_inverted_square (t : CubicTorus c) :
    ∃ q : c.H, q∈c.H₂ ∧ q^2=t.z ∧ t.n*q*t.n⁻¹=q⁻¹ := by
  let Q := quaternionCore c
  let d := quaternionCoreData c
  have hzC : t.z∈c.H₁.pCoreIn 2 ⊓ c.H₂.pCoreIn 2 := by
    rw [factor_core_intersection c]
    exact t.central_line ▸ mem_zpowers t.z
  let zQ : Q := ⟨t.z,mem_sup_left hzC.1⟩
  let zD : (d.right⊓d.left:Subgroup Q) := ⟨zQ,hzC.2,hzC.1⟩
  let a : MulAut Q := MulAut.conjNormal t.n
  have ha : a^2=1 := by
    change (MulAut.conjNormal t.n : MulAut Q)^2=1
    rw [←map_pow,show t.n^2=1 from t.n_order ▸ pow_orderOf_eq_one t.n,map_one]
  have ho := outside_bothOuter c t.n t.outside
  obtain ⟨hf,_⟩ := quaternion_outer_involution_factor_data d.right d.left d.right_model
    (by rw [inf_comm]; exact d.intersection_card) a ha ho.right_map ho.right_outer
  obtain ⟨hc,hs⟩ := hf zD
  obtain ⟨q,hq⟩ := (Nat.card_pos_iff.mp (show 0<Nat.card {b : d.right //
    (b:Q)⁻¹*a (b:Q)=(zD:Q)} by rw [hc]; decide)).1
  have hsq : (q.val:c.H)^2=t.z := congrArg Subtype.val (hs q hq)
  have he : (q.val:c.H)⁻¹*(t.n*(q.val:c.H)*t.n⁻¹)=t.z := congrArg Subtype.val hq
  refine ⟨q.val,c.H₂.pCoreIn_le 2 q.property,hsq,?_⟩
  have hn2 : t.z^2=1 := t.z_order ▸ pow_orderOf_eq_one t.z
  have hq4 : (q.val:c.H)^4=1 := by rw [show 4=2*2 from rfl,pow_mul,hsq,hn2]
  have hh : t.n*(q.val:c.H)*t.n⁻¹=(q.val:c.H)*t.z :=
    (inv_mul_eq_iff_eq_mul).mp he
  rw [hh,←hsq,←pow_succ']
  exact eq_inv_of_mul_eq_one_left (by rw [←pow_succ,hq4])

/-- An actual endpoint involution acts as the marked torus reflection. -/
theorem exists_left_endpoint_reflection (t : CubicTorus c) :
    ∃ s : G, s∈cubicNormalizer c t.x ∧ orderOf s=2 ∧
      s∈normalizer (t.torus.map c.H.subtype:Set G) ∧
      MulAut.conj s (t.z:G)=(t.z:G) ∧
      MulAut.conj s (t.n:G)=(t.z:G)*(t.n:G) := by
  obtain ⟨q,hq,hq2,hnq⟩ := t.right_quaternion_inverted_square
  let s : c.H := q*t.n
  have hsq : s^2=1 := by
    have hn2 : t.n*t.n=1 := by simpa only [pow_two,t.n_order] using pow_orderOf_eq_one t.n
    have he : t.n*q=q⁻¹*t.n := mul_inv_eq_iff_eq_mul.mp hnq
    change (q*t.n)^2=1
    rw [pow_two,mul_assoc,←mul_assoc t.n q t.n,he,mul_assoc,hn2,mul_one,mul_inv_cancel]
  have hs1 : s≠1 := by
    intro he
    have hn : t.n=q⁻¹ := eq_inv_of_mul_eq_one_right he
    exact t.outside (mem_sup_right (hn ▸ c.H₂.inv_mem hq))
  have hs2 : orderOf s=2 := orderOf_eq_prime hsq hs1
  have hsz : MulAut.conj (s:G) (t.z:G)=(t.z:G) := by
    apply mul_inv_eq_iff_eq_mul.mpr
    exact mem_centralizer_singleton_iff.mp (t.centralizer ▸ s.property)
  have hsn : MulAut.conj s t.n=t.z*t.n := by
    change (q*t.n)*t.n*(q*t.n)⁻¹=t.z*t.n
    calc
      _ = q*t.n*q⁻¹ := by group
      _ = q*q*t.n := by
        have hh := congrArg Inv.inv hnq
        simp only [mul_inv_rev,inv_inv,←mul_assoc] at hh
        have hh' : t.n*q⁻¹=q*t.n := mul_inv_eq_iff_eq_mul.mp hh
        rw [mul_assoc,hh',←mul_assoc]
      _ = t.z*t.n := by rw [←pow_two,hq2]
  have hsN : s∈normalizer (t.torus:Set c.H) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rw [torus,Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
      apply sup_le
      · apply zpowers_le.mpr
        have hz : MulAut.conj s t.z=t.z := Subtype.ext hsz
        change MulAut.conj s t.z∈zpowers t.z⊔zpowers t.n
        rw [hz]
        exact mem_sup_left (mem_zpowers _)
      · apply zpowers_le.mpr
        change MulAut.conj s t.n∈zpowers t.z⊔zpowers t.n
        rw [hsn]
        exact mul_mem_sup (mem_zpowers _) (mem_zpowers _)
    · rw [card_map_of_injective (MulAut.conj s).injective]
  refine ⟨s,?_,(orderOf_coe s).trans hs2,?_,hsz,congrArg Subtype.val hsn⟩
  · rw [t.left_ambient_normalizer]
    exact mul_mem (mem_sup_left (mem_sup_right (mem_map_of_mem c.H.subtype hq)))
      (mem_sup_right (mem_map_of_mem c.H.subtype (mem_sup_right (mem_zpowers _))))
  · exact (t.torus.le_normalizer_map c.H.subtype) (mem_map_of_mem c.H.subtype hsN)

/-- The Borel contains no additional normalizers of its marked four-group. -/
theorem maximal_borel_torus_normalizer (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    t.leftCubicBorel⊓normalizer (t.torus.map c.H.subtype:Set G)=t.torus.map c.H.subtype := by
  let S := t.leftCoreExtension
  let A := t.torus.map c.H.subtype
  let C := Subgroup.centralizer (A:Set G)
  obtain ⟨_,hAN,hd,_⟩ := t.maximal_leftCubicBorel_split hc
  have hSC : S⊓C=⊥ := by
    apply card_eq_one.mp
    have h1 : Nat.card (S⊓C:Subgroup G)∣3^6 := by
      have hh := card_dvd_of_le (show S⊓C≤S from inf_le_left)
      rwa [t.maximal_leftCoreExtension_card hc] at hh
    have h2 := card_dvd_of_le (show S⊓C≤C from inf_le_right)
    exact Nat.eq_one_of_dvd_coprimes
      ((Nat.prime_three.coprime_iff_not_dvd.mpr t.three_not_dvd_torus_centralizer).pow_left 6)
      h1 h2
  have hSN : S⊓normalizer (A:Set G)=⊥ := by
    apply bot_unique
    intro u hu
    apply hSC.le
    refine ⟨hu.1,?_⟩
    intro a ha
    have hcommA : u*a*u⁻¹*a⁻¹∈A :=
      A.mul_mem ((mem_normalizer_iff.mp hu.2 a).mp ha) (A.inv_mem ha)
    have hcommS : u*a*u⁻¹*a⁻¹∈S := by
      have hh := S.mul_mem hu.1 ((mem_normalizer_iff.mp (hAN ha) u⁻¹).mp (S.inv_mem hu.1))
      simpa only [←mul_assoc] using hh
    have he : u*a*u⁻¹*a⁻¹=1 := hd.le_bot ⟨hcommS,hcommA⟩
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp he)).symm
  apply le_antisymm
  · rintro v ⟨hvB,hvN⟩
    have hv : v∈(S:Set G)*(A:Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left S A hAN]
      exact hvB
    obtain ⟨s,hs,a,ha,rfl⟩ := hv
    have hsN : s∈normalizer (A:Set G) :=
      ((normalizer (A:Set G)).mul_mem_cancel_right (A.le_normalizer ha)).mp hvN
    have hs1 : s=1 := hSN.le ⟨hs,hsN⟩
    change s*a∈A
    rw [hs1,one_mul]
    exact ha
  · exact le_inf le_sup_right A.le_normalizer

/-- Both original endpoints have involutions outside their entire Borel. -/
theorem maximal_left_endpoint_involution (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    ∃ s : G, s∈cubicNormalizer c t.x ∧ s∉t.leftCubicBorel ∧ orderOf s=2 ∧
      s∈normalizer (t.torus.map c.H.subtype:Set G) ∧
      MulAut.conj s (t.z:G)=(t.z:G) ∧
      MulAut.conj s (t.n:G)=(t.z:G)*(t.n:G) := by
  obtain ⟨s,hs,ho,hn,hz,he⟩ := t.exists_left_endpoint_reflection
  refine ⟨s,hs,?_,ho,hn,hz,he⟩
  intro hb
  have hsA := (t.maximal_borel_torus_normalizer hc).le ⟨hb,hn⟩
  let A := t.torus.map c.H.subtype
  let : IsKleinFour A := t.ambient_torus_kleinFour
  let : IsMulCommutative A := IsKleinFour.isMulCommutative
  have hnA : (t.n:G)∈A := mem_map_of_mem c.H.subtype (mem_sup_right (mem_zpowers _))
  have hh : s*(t.n:G)=(t.n:G)*s :=
    congrArg Subtype.val (mul_comm' (⟨s,hsA⟩:A) ⟨t.n,hnA⟩)
  have hfix : MulAut.conj s (t.n:G)=(t.n:G) := by
    change s*(t.n:G)*s⁻¹=(t.n:G)
    rw [hh,mul_inv_cancel_right]
  have hz1 : (t.z:G)=1 := mul_right_cancel (he.symm.trans (hfix.trans (one_mul _).symm))
  have hz2 : t.z=1 := Subtype.ext hz1
  have hzorder := t.z_order
  simp [hz2] at hzorder

/-- A torus-preserving Sylow aligner moves the original central involution. -/
theorem maximal_aligner_moves_central_involution (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) (g : G)
    (hg : t.swap.leftCoreExtension.map (MulAut.conj g).toMonoidHom=t.leftCoreExtension) :
    MulAut.conj g (t.z:G)≠(t.z:G) := by
  intro hfix
  let Y := (zpowers ((t.y:c.H):G)).map (MulAut.conj g).toMonoidHom
  have hYcenter : Y≤centerIn t.leftCoreExtension := by
    rw [←t.maximal_aligned_center_lines hc g hg]
    exact le_sup_right
  have hYcore : Y≤cubicOddCore c t.x :=
    hYcenter.trans ((t.maximal_extension_center hc).le.trans (inf_le_left.trans inf_le_left))
  have hYH : Y≤c.H := by
    rintro _ ⟨y,hy,rfl⟩
    rw [t.centralizer]
    apply mem_centralizer_singleton_iff.mpr
    have hyH := (zpowers_le.mpr t.y.val.property) hy
    have hh := congrArg (MulAut.conj g)
      (mem_centralizer_singleton_iff.mp (t.centralizer ▸ hyH))
    change MulAut.conj g y*(t.z:G)=(t.z:G)*MulAut.conj g y
    simpa only [map_mul,hfix] using hh
  have hle : Y≤zpowers ((t.x:c.H):G) :=
    (le_inf hYcore hYH).trans (cubic_oddCore_fixed c t.x t.x_order).le
  have he : Y=zpowers ((t.x:c.H):G) := eq_of_le_of_card_ge hle (by
    rw [card_map_of_injective (MulAut.conj g).injective,
      Nat.card_zpowers,Nat.card_zpowers,orderOf_coe,orderOf_coe,
      orderOf_coe,orderOf_coe,t.y_order,t.x_order])
  exact cubic_lines_not_conjugate (swapFactors c) t.y t.x t.y_order g he

/-- Torus-preserving alignment supplies actual involutions in both endpoints,
retaining the whole Borel and the two distinct fixed torus involutions. -/
theorem maximal_aligned_endpoint_involutions (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    ∃ g s r : G,
      g∈normalizer (t.torus.map c.H.subtype:Set G) ∧
      t.swap.leftCoreExtension.map (MulAut.conj g).toMonoidHom=t.leftCoreExtension ∧
      cubicNormalizer c t.x ⊓
        (cubicNormalizer (swapFactors c) t.y).map (MulAut.conj g).toMonoidHom=t.leftCubicBorel ∧
      s∈cubicNormalizer c t.x ∧
      r∈(cubicNormalizer (swapFactors c) t.y).map (MulAut.conj g).toMonoidHom ∧
      s∉t.leftCubicBorel ∧ r∉t.leftCubicBorel ∧
      orderOf s=2 ∧ orderOf r=2 ∧
      s∈normalizer (t.torus.map c.H.subtype:Set G) ∧
      r∈normalizer (t.torus.map c.H.subtype:Set G) ∧
      MulAut.conj s (t.z:G)=(t.z:G) ∧
      MulAut.conj s (t.n:G)=(t.z:G)*(t.n:G) ∧
      MulAut.conj r (MulAut.conj g (t.z:G))=MulAut.conj g (t.z:G) ∧
      MulAut.conj r (MulAut.conj g (t.n:G))=
        MulAut.conj g ((t.z:G)*(t.n:G)) ∧
      MulAut.conj g (t.z:G)≠(t.z:G) := by
  obtain ⟨g,hgA,hg⟩ := t.maximal_extensions_conjugate_in_torus_normalizer hc
  obtain ⟨s,hs,hsB,hs2,hsA,hsz,hsn⟩ := t.maximal_left_endpoint_involution hc
  obtain ⟨r,hr,hrB,hr2,hrA,hrz,hrn⟩ :=
    t.swap.maximal_left_endpoint_involution (t.oddCore_card_eq.symm.trans hc)
  let f := MulAut.conj g
  have hfN : (normalizer (t.torus.map c.H.subtype:Set G)).map f.toMonoidHom=
      normalizer (t.torus.map c.H.subtype:Set G) := by
    rw [map_normalizer_eq_of_bijective _ f.bijective]
    rw [show (t.torus.map c.H.subtype).map f.toMonoidHom=t.torus.map c.H.subtype
      from mem_normalizer_iff_map_conj_eq.mp hgA]
  refine ⟨g,s,f r,hgA,hg,t.maximal_aligned_endpoint_overlap hc g hg,
    hs,mem_map_of_mem f.toMonoidHom hr,hsB,?_,hs2,(f.orderOf_eq r).trans hr2,
    hsA,hfN.le (mem_map_of_mem f.toMonoidHom hrA),hsz,hsn,?_,?_,
    t.maximal_aligner_moves_central_involution hc g hg⟩
  · intro hb
    rw [←t.maximal_aligned_borels hc g hg] at hb
    exact hrB ((mem_map_iff_mem f.injective).mp hb)
  · change f r*f (t.z:G)*(f r)⁻¹=f (t.z:G)
    change r*(t.z:G)*r⁻¹=(t.z:G) at hrz
    simpa only [map_mul,map_inv] using congrArg f hrz
  · change f r*f (t.n:G)*(f r)⁻¹=f ((t.z:G)*(t.n:G))
    change r*(t.n:G)*r⁻¹=(t.z:G)*(t.n:G) at hrn
    simpa only [map_mul,map_inv] using congrArg f hrn

end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
