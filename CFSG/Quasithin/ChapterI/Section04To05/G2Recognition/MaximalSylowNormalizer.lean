module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalCoreStructure
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Theory.SpecificGroups.GL2.ThreeFourCentralizer

/-!
# The full ambient Borel of an original large cubic extension

The order729 extension has precisely the constructed order2916 Borel
as its full ambient normalizer. Each involution in the original torus
fixes nine elements of the extension. Its normalizer centralizer has order
at most36, by conjugating the fixed plane into H. The faithful center-plane
action embeds in GL₂(3); the torus image contains the scalar involution.
Coprime centralizer lifting at this involution bounds the whole quotient
by four, proving the normalizer equality.

MaximalAmbientSylow promotes the two original extensions to ambient
Sylow subgroups and aligns their endpoints using this equality. Compatible
Atlas endpoint isomorphisms remain necessary. Source: Aschbacher–Smith
I.4.5, printed p.417.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace CubicTorus

private theorem fixed_nine_conjugate (t : CubicTorus c)
    (P : Subgroup G) (hP : Nat.card P=9) (u : G) (hu : orderOf u=2)
    (hPu : P≤Subgroup.centralizer ({u}:Set G)) :
    ∃ g : G, MulAut.conj g u=(t.z:G) ∧
      P.map (MulAut.conj g).toMonoidHom=
        zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) := by
  obtain ⟨a,ha⟩ := isConj_iff.mp
    (involutions_conjugate c u t.z hu ((orderOf_coe t.z).trans t.z_order))
  let f := MulAut.conj a
  let R := P.map f.toMonoidHom
  let E := zpowers (t.x:c.H) ⊔ zpowers (t.y:c.H)
  have hRH : R≤c.H := by
    rintro _ ⟨v,hv,rfl⟩
    rw [t.centralizer]
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg f (mem_centralizer_singleton_iff.mp (hPu hv))
    simp only [map_mul,show f u=(t.z:G) from ha] at hh
    exact hh
  have hR : Nat.card (R.subgroupOf c.H)=9 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hRH).toEquiv,
      card_map_of_injective f.injective,hP]
  have hEmap : E.map c.H.subtype=
      zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) := by
    rw [Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
    rfl
  have hE : Nat.card E=9 := by
    rw [←card_map_of_injective c.H.subtype_injective,hEmap]
    exact (cubic_plane_data c t.x t.y t.x_order t.y_order).2
  have hi (A : Subgroup c.H) (hA : Nat.card A=9) : ¬3∣A.index := by
    have hh := A.card_mul_index
    rw [hA,H_card c] at hh
    have hh' : A.index=64 := by omega
    rw [hh']; decide
  let S : Sylow 3 c.H := (IsPGroup.of_card (p:=3) (n:=2) hR).toSylow (hi _ hR)
  let T : Sylow 3 c.H := (IsPGroup.of_card (p:=3) (n:=2) hE).toSylow (hi _ hE)
  obtain ⟨b,hb⟩ := MulAction.exists_smul_eq c.H S T
  have hb' : (R.subgroupOf c.H).map (MulAut.conj b).toMonoidHom=E :=
    congrArg Sylow.toSubgroup hb
  refine ⟨(b:G)*a,?_,?_⟩
  · change (b:G)*a*u*((b:G)*a)⁻¹=(t.z:G)
    calc
      _ = (b:G)*(a*u*a⁻¹)*(b:G)⁻¹ := by group
      _ = (b:G)*(t.z:G)*(b:G)⁻¹ := by rw [ha]
      _ = (t.z:G) := by
        have hcomm : (b:G)*(t.z:G)=(t.z:G)*(b:G) :=
          mem_centralizer_singleton_iff.mp (t.centralizer ▸ b.property)
        rw [hcomm,mul_inv_cancel_right]
  · have hm := congrArg (fun A : Subgroup c.H => A.map c.H.subtype) hb'
    rw [hEmap] at hm
    rw [←hm]
    ext v
    constructor
    · rintro ⟨w,hw,rfl⟩
      refine ⟨b*⟨f w,hRH (mem_map_of_mem f.toMonoidHom hw)⟩*b⁻¹,
        mem_map_of_mem (MulAut.conj b).toMonoidHom
          (show (⟨f w,hRH (mem_map_of_mem f.toMonoidHom hw)⟩:c.H)∈R.subgroupOf c.H
            from mem_map_of_mem f.toMonoidHom hw),?_⟩
      change (b:G)*(a*w*a⁻¹)*(b:G)⁻¹=((b:G)*a)*w*((b:G)*a)⁻¹
      group
    · rintro ⟨w,⟨v,hv,rfl⟩,rfl⟩
      obtain ⟨q,hq,hqv⟩ := (show (v:G)∈R from hv)
      refine ⟨q,hq,?_⟩
      change ((b:G)*a)*q*((b:G)*a)⁻¹=(b:G)*(v:G)*(b:G)⁻¹
      rw [←hqv]
      change ((b:G)*a)*q*((b:G)*a)⁻¹=(b:G)*(a*q*a⁻¹)*(b:G)⁻¹
      group

private theorem odd_fixed_le_nine (_t : CubicTorus c) (S : Subgroup G)
    (hodd : Odd (Nat.card S)) (v : G) (hv : orderOf v=2) :
    Nat.card (S⊓Subgroup.centralizer ({v}:Set G):Subgroup G)≤9 := by
  let F := S⊓Subgroup.centralizer ({v}:Set G)
  have ho : Odd (Nat.card F) := hodd.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hd : Nat.card F∣64*9 := by
    have hh := card_dvd_of_le (show F≤Subgroup.centralizer ({v}:Set G) from inf_le_right)
    rwa [involution_centralizer_card c v hv] at hh
  exact Nat.le_of_dvd (by decide) ((ho.coprime_two_right.pow_right 6).dvd_of_dvd_mul_left hd)

/-- Every nonidentity torus involution fixes a plane of order nine in the Sylow. -/
theorem maximal_sylow_torus_fixed_card (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) (v : G)
    (hvA : v∈t.torus.map c.H.subtype) (hv : orderOf v=2) :
    Nat.card (t.leftCoreExtension⊓Subgroup.centralizer ({v}:Set G):Subgroup G)=9 := by
  let S := t.leftCoreExtension
  let A := t.torus.map c.H.subtype
  let : IsKleinFour A := t.ambient_torus_kleinFour
  let : IsMulCommutative A := IsKleinFour.isMulCommutative
  let a : A := ⟨v,hvA⟩
  have ha : orderOf a=2 := (orderOf_coe a).symm.trans hv
  have hproper : zpowers a≠⊤ := by
    intro he
    have hh := Nat.card_zpowers a
    rw [he,card_top,IsKleinFour.card_four,ha] at hh
    omega
  obtain ⟨b,hb⟩ : ∃ b : A, b∉zpowers a :=
    not_forall.mp (fun hh => hproper ((Subgroup.eq_top_iff' _).mpr hh))
  have hb1 : b≠1 := fun he => hb (he ▸ one_mem _)
  have hab1 : a*b≠1 := by
    intro he
    have he' : b=a⁻¹ := eq_inv_of_mul_eq_one_right he
    exact hb (he' ▸ inv_mem (mem_zpowers _))
  have hp (u : A) : u^2=1 := by
    have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (show Monoid.exponent A∣2 by rw [IsKleinFour.exponent_two]) u
    exact hh
  have hbo : orderOf (b:G)=2 := (orderOf_coe b).trans (orderOf_eq_prime (hp b) hb1)
  have habo : orderOf ((a*b:A):G)=2 :=
    (orderOf_coe (a*b)).trans (orderOf_eq_prime (hp (a*b)) hab1)
  have hAN : A≤normalizer (S:Set G) := (t.maximal_leftCubicBorel_split hc).2.1
  let aa : normalizer (S:Set G) := ⟨a,hAN a.property⟩
  let bb : normalizer (S:Set G) := ⟨b,hAN b.property⟩
  have haa : aa^2=1 := Subtype.ext (congrArg (fun u : A => (u:G)) (hp a))
  have hbb : bb^2=1 := Subtype.ext (congrArg (fun u : A => (u:G)) (hp b))
  have hab : Commute aa bb := Subtype.ext (congrArg (fun u : A => (u:G)) (mul_comm' a b))
  have hodd : Odd (Nat.card S) := by rw [t.maximal_leftCoreExtension_card hc]; decide
  have hf := S.card_three_odd_centralizers hodd aa bb haa hbb hab
  change Nat.card S * Nat.card
      ((S⊓Subgroup.centralizer ({v}:Set G))⊓Subgroup.centralizer ({(b:G)}:Set G):Subgroup G)^2 =
      Nat.card (S⊓Subgroup.centralizer ({v}:Set G):Subgroup G)*
      Nat.card (S⊓Subgroup.centralizer ({(b:G)}:Set G):Subgroup G)*
      Nat.card (S⊓Subgroup.centralizer ({((a*b:A):G)}:Set G):Subgroup G) at hf
  have hpos := Nat.card_pos (α:=
    ((S⊓Subgroup.centralizer ({v}:Set G))⊓Subgroup.centralizer ({(b:G)}:Set G):Subgroup G))
  have hx := t.odd_fixed_le_nine S hodd v hv
  have hy := t.odd_fixed_le_nine S hodd b hbo
  have hz := t.odd_fixed_le_nine S hodd (a*b) habo
  have hmul := Nat.mul_le_mul hy hz
  rw [t.maximal_leftCoreExtension_card hc] at hf
  have hlo : 729≤Nat.card (S⊓Subgroup.centralizer ({v}:Set G):Subgroup G)*81 := by
    calc
      729 ≤ 729 * Nat.card
        ((S⊓Subgroup.centralizer ({v}:Set G))⊓Subgroup.centralizer ({(b:G)}:Set G):Subgroup G)^2 := by nlinarith
      _ = _ := hf
      _ ≤ _ := by rw [mul_assoc]; exact Nat.mul_le_mul_left _ hmul
  change Nat.card (S⊓Subgroup.centralizer ({v}:Set G):Subgroup G)=9
  omega

private theorem plane_normalizer_inf_H (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    Nat.card (normalizer
      ((zpowers ((t.x:c.H):G)⊔zpowers ((t.y:c.H):G):Subgroup G):Set G)⊓c.H:Subgroup G)≤36 := by
  let E := zpowers ((t.x:c.H):G)⊔zpowers ((t.y:c.H):G)
  let U := E⊔(cubicOddCore c t.x⊓cubicOddCore (swapFactors c) t.y)
  have hle : normalizer (E:Set G)⊓c.H ≤ normalizer (U:Set G)⊓c.H :=
    inf_le_inf_right c.H (t.maximal_plane_extension_normalized hc)
  have hh := card_le_of_le hle
  have he := t.maximal_extension_normalizer_involution_centralizer_card hc
  rw [←t.centralizer] at he
  exact he ▸ hh

/-- The full Sylow normalizer has involution centralizer at most36 on the original torus. -/
theorem maximal_sylow_torus_centralizer_bound (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) (v : G)
    (hvA : v∈t.torus.map c.H.subtype) (hv : orderOf v=2) :
    Nat.card (normalizer (t.leftCoreExtension:Set G)⊓
      Subgroup.centralizer ({v}:Set G):Subgroup G)≤36 := by
  let S := t.leftCoreExtension
  let F := S⊓Subgroup.centralizer ({v}:Set G)
  let C := normalizer (S:Set G)⊓Subgroup.centralizer ({v}:Set G)
  let E := zpowers ((t.x:c.H):G)⊔zpowers ((t.y:c.H):G)
  obtain ⟨g,hgv,hgF⟩ := t.fixed_nine_conjugate F
    (t.maximal_sylow_torus_fixed_card hc v hvA hv) v hv inf_le_right
  have hCN : C≤normalizer (F:Set G) :=
    (le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer ({v}:Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hmap : C.map (MulAut.conj g).toMonoidHom≤normalizer (E:Set G)⊓c.H := by
    rintro _ ⟨w,hw,rfl⟩
    refine ⟨?_,?_⟩
    · change MulAut.conj g w∈normalizer (E:Set G)
      change F.map (MulAut.conj g).toMonoidHom=E at hgF
      rw [←hgF]
      exact (F.le_normalizer_map (MulAut.conj g).toMonoidHom)
        (mem_map_of_mem (MulAut.conj g).toMonoidHom (hCN hw))
    · rw [t.centralizer]
      apply mem_centralizer_singleton_iff.mpr
      change MulAut.conj g w*(t.z:G)=(t.z:G)*MulAut.conj g w
      have hh := congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp hw.2)
      simpa only [map_mul,hgv] using hh
  have hh := card_le_of_le hmap
  rw [card_map_of_injective (MulAut.conj g).injective] at hh
  exact hh.trans (t.plane_normalizer_inf_H hc)

/-- The ambient Sylow normalizer is exactly the original Borel. -/
theorem maximal_sylow_normalizer_eq (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    normalizer (t.leftCoreExtension:Set G)=t.leftCubicBorel := by
  let S := t.leftCoreExtension
  let K := centerIn S
  let N := normalizer (S:Set G)
  let A := t.torus.map c.H.subtype
  let : IsKleinFour A := t.ambient_torus_kleinFour
  let : IsMulCommutative A := IsKleinFour.isMulCommutative
  have hAN : A≤N := (t.maximal_leftCubicBorel_split hc).2.1
  have hKN : N≤normalizer (K:Set G) := normalizes_centerIn le_rfl
  let ρ := K.normalizerMonoidHom.comp (inclusion hKN)
  have hker : ρ.ker=S.subgroupOf N := by
    ext n
    change (inclusion hKN n)∈K.normalizerMonoidHom.ker ↔ (n:G)∈S
    rw [normalizerMonoidHom_ker]
    change (n:G)∈Subgroup.centralizer (K:Set G) ↔ (n:G)∈S
    rw [t.maximal_extension_center_centralizer hc]
  let : IsElementaryAbelian 3 K := t.maximal_extension_center_elementary hc
  obtain ⟨j,hj⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p:=3) (n:=2) K (by rw [t.maximal_extension_center_card hc]; decide)
  let f := j.comp ρ
  have hfker : f.ker=S.subgroupOf N := by
    rw [←hker]
    ext a
    change j (ρ a)=1 ↔ ρ a=1
    rw [←j.map_one,hj.eq_iff]
  let d := f.comp (inclusion hAN)
  have hdi : Function.Injective d := (MonoidHom.ker_eq_bot_iff d).mp (by
    apply bot_unique
    intro a ha
    have hsa : (a:G)∈S := by
      have hh : inclusion hAN a∈f.ker := ha
      rwa [hfker] at hh
    exact Subtype.ext ((t.maximal_leftCubicBorel_split hc).2.2.1.le_bot ⟨hsa,a.property⟩))
  let R := d.range
  let : IsElementaryAbelian 2 A := {exponent_dvd_p := by rw [IsKleinFour.exponent_two]}
  let : IsElementaryAbelian 2 R := IsElementaryAbelian.of_surjective d.rangeRestrict
    d.rangeRestrict_surjective
  have hR : Nat.card R=4 :=
    (Nat.card_congr (MonoidHom.ofInjective hdi).toEquiv).symm.trans IsKleinFour.card_four
  have hscalar : (-1:Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))∈R := by
    rw [←Matrix.GeneralLinearGroup.three_four_centralizer R hR]
    intro b _
    simp
  obtain ⟨a,ha⟩ := hscalar
  have ha1 : a≠1 := by
    intro he
    have hh : (1:Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))=-1 := by simpa [he] using ha
    have hv := congrArg (fun m : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) => m 0 0) hh
    change (1:ZMod 3)=-1 at hv
    exact (by decide : (1:ZMod 3)≠-1) hv
  have ha2 : orderOf a=2 := orderOf_eq_prime
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (show Monoid.exponent A∣2 by rw [IsKleinFour.exponent_two]) a) ha1
  let v : N := inclusion hAN a
  have hv : orderOf v=2 := by
    exact (orderOf_coe v).symm.trans ((orderOf_coe a).trans ha2)
  let Q := N ⧸ f.ker
  let q : N →* Q := QuotientGroup.mk' f.ker
  have hqv : Subgroup.centralizer ({q v}:Set Q)=⊤ := by
    apply top_unique
    intro b _
    obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective f.ker b
    apply mem_centralizer_singleton_iff.mpr
    apply (QuotientGroup.kerLift_injective f)
    rw [map_mul,map_mul]
    change f w*f v=f v*f w
    change f w*d a=d a*f w
    rw [ha]
    simp
  have hkernelcard : Nat.card f.ker=729 := by
    rw [hfker,Nat.card_congr (subgroupOfEquivOfLe S.le_normalizer).toEquiv]
    exact t.maximal_leftCoreExtension_card hc
  let C := Subgroup.centralizer ({v}:Set N)
  have hmap : C.map q=⊤ := by
    let : Fact (IsPGroup 2 (zpowers v)) := ⟨IsPGroup.of_card (p:=2) (n:=1)
      (by rw [Nat.card_zpowers,hv,pow_one])⟩
    have hh := centralizer_map_quotient_eq_map_centralizer 2 (zpowers v)
      f.ker inferInstance (by rw [hkernelcard]; decide)
    change Subgroup.centralizer ((zpowers v).map q:Set Q)=
      (Subgroup.centralizer (zpowers v:Set N)).map q at hh
    rw [MonoidHom.map_zpowers,zpowers_eq_closure,centralizer_closure,
      zpowers_eq_closure,centralizer_closure,hqv] at hh
    exact hh.symm
  have hfix : Nat.card (f.ker.subgroupOf C)=9 := by
    have he : (f.ker.subgroupOf C).map (N.subtype.comp C.subtype)=
        S⊓Subgroup.centralizer ({(a:G)}:Set G) := by
      ext g
      constructor
      · rintro ⟨w,hw,rfl⟩
        have hs : (w.val:G)∈S := by
          change w.val∈S.subgroupOf N
          rwa [←hfker]
        exact ⟨hs,
          mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
            (mem_centralizer_singleton_iff.mp w.property))⟩
      · rintro ⟨hgS,hga⟩
        refine ⟨⟨⟨g,S.le_normalizer hgS⟩,?_⟩,?_,rfl⟩
        · exact mem_centralizer_singleton_iff.mpr
            (Subtype.ext (mem_centralizer_singleton_iff.mp hga))
        · change (⟨g,S.le_normalizer hgS⟩:N)∈f.ker
          rw [hfker]
          exact hgS
    rw [←card_map_of_injective (f:=N.subtype.comp C.subtype)
      (N.subtype_injective.comp C.subtype_injective),he]
    exact t.maximal_sylow_torus_fixed_card hc a a.property ((orderOf_coe a).trans ha2)
  have hC : Nat.card C≤36 := by
    rw [←card_map_of_injective N.subtype_injective,map_subtype_centralizer_singleton]
    exact t.maximal_sylow_torus_centralizer_bound hc a a.property ((orderOf_coe a).trans ha2)
  have hQ : Nat.card Q≤4 := by
    have hh := (f.ker.subgroupOf C).card_mul_index
    rw [hfix] at hh
    change 9 * f.ker.relIndex C=Nat.card C at hh
    rw [←show q.ker=f.ker from QuotientGroup.ker_mk' f.ker,relIndex_ker,hmap,card_top] at hh
    omega
  have hN : Nat.card N≤2916 := by
    have hh := f.ker.card_mul_index
    rw [hkernelcard,index_eq_card] at hh
    change 729*Nat.card Q=Nat.card N at hh
    omega
  exact (eq_of_le_of_card_ge (show t.leftCubicBorel≤N from sup_le S.le_normalizer hAN)
    (by rw [(t.maximal_leftCubicBorel_split hc).2.2.2]; exact hN)).symm


end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
