module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalWeylProduct
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.LocalGeneration

/-!
# Generation by the original aligned cubic normalizers

A subgroup containing H and a conjugator from the marked central involution
z to the outer involution n is the whole ambient group. Indeed C_G(z,n) is
an elementary eight, so it has an involution outside the marked four-group.
Conjugation inside the transported H fuses that involution with its product
by n. Exactly one lies in H₁H₂; the known two local involution orbits therefore
fuse inside the overgroup. Sylow conjugacy and the full centralizer C_G(z)=H
then make a proper overgroup strongly two-embedded, which is already excluded.

For the original aligned cubic normalizers, their two marked reflections
rotate the torus. Correcting the Sylow aligner by that rotation gives an
element of H. Normality of its first SL₂(3) factor therefore puts that entire
factor in the endpoint join. The other factor and the outer involution are
already in the first endpoint, so the join contains H and the required
central-to-outer conjugator. Thus these actual endpoints generate G.

This discharges generation in the large-core completion construction for
Aschbacher–Smith I.4.5, printed p.417 (refs/quasithin.pdf, PDF p.428).
The centralizer and involution calculations continue Fong–Wong §2F and §3A,
Nagoya Math. J.36 (1969), pp.153–155. Compatible Atlas endpoint maps and the
independent strongly-three-embedded exclusion remain required for recognition.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace CubicTorus

private theorem overgroup_eq_top_of_fusion (t : CubicTorus c) (K : Subgroup G)
    (hHK : c.H≤K)
    (hf : ∀ x : c.H, orderOf x=2 →
      IsConj (⟨t.z,hHK t.z.property⟩:K) ⟨x,hHK x.property⟩) : K=⊤ := by
  let z : K := ⟨t.z,hHK t.z.property⟩
  have hz : orderOf z=2 := (orderOf_coe z).symm.trans ((orderOf_coe t.z).trans t.z_order)
  have hall (x : K) (hx : orderOf x=2) : IsConj z x := by
    let T : Sylow 2 c.H := Classical.choice inferInstance
    obtain ⟨S,hS⟩ := H_sylow_is_ambient c T
    have hSK : (S:Subgroup G)≤K := (hS ▸ map_subtype_le _).trans hHK
    let U : Sylow 2 K := S.comapOfInjective K.subtype K.subtype_injective
      (by simpa only [range_subtype] using hSK)
    have px : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n:=1)
      (by rw [Nat.card_zpowers,hx]; rfl)
    obtain ⟨V,hV⟩ := px.exists_le_sylow
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq K V U
    have hyU : MulAut.conj g x∈(U:Subgroup K) := hg ▸
      mem_map_of_mem (MulAut.conj g).toMonoidHom (hV (mem_zpowers x))
    have hyS : (MulAut.conj g x:G)∈(S:Subgroup G) := hyU
    have hyH : (MulAut.conj g x:G)∈c.H := (hS ▸ map_subtype_le _) hyS
    let y : c.H := ⟨MulAut.conj g x,hyH⟩
    have hy2 : orderOf y=2 := (orderOf_coe y).symm.trans
      ((orderOf_coe (MulAut.conj g x)).trans (((MulAut.conj g).orderOf_eq x).trans hx))
    exact (hf y hy2).trans (isConj_iff.mpr ⟨g,rfl⟩).symm
  have hcentral (x : K) (hx : orderOf x=2) : Subgroup.centralizer ({(x:G)}:Set G)≤K := by
    obtain ⟨g,hg⟩ := isConj_iff.mp (hall x hx)
    have hgG : MulAut.conj (g:G) (t.z:G)=(x:G) := congrArg Subtype.val hg
    intro y hy
    have hyH : MulAut.conj (g:G)⁻¹ y∈c.H := by
      rw [t.centralizer,mem_centralizer_singleton_iff]
      apply (MulAut.conj (g:G)).injective
      simpa [map_mul,hgG,MulAut.conj_apply,mul_assoc] using
        mem_centralizer_singleton_iff.mp hy
    have hmem := K.mul_mem (K.mul_mem g.property (hHK hyH)) (K.inv_mem g.property)
    simpa [MulAut.conj_apply,mul_assoc] using hmem
  by_contra hK
  apply no_strongly_embedded c K
  refine ⟨hK,⟨z,z.property,?_,?_⟩,?_⟩
  · intro he
    have hh := (orderOf_coe z).trans hz
    simp [he] at hh
  · exact congrArg Subtype.val (hz ▸ pow_orderOf_eq_one z)
  · intro g hg x hx hxc hxi
    change x∈K.map (MulAut.conj g⁻¹).toMonoidHom at hxc
    obtain ⟨y,hy,he⟩ := hxc
    have hx2 : orderOf x=2 := orderOf_eq_prime hxi.2 hxi.1
    have hy2 : orderOf y=2 := by
      have hh : MulAut.conj g⁻¹ y=x := he
      rw [←(MulAut.conj g⁻¹).orderOf_eq y,hh]
      exact hx2
    obtain ⟨k,hk⟩ := isConj_iff.mp ((hall ⟨y,hy⟩ (by simpa using hy2)).symm.trans
      (hall ⟨x,hx⟩ (by simpa using hx2)))
    have hkG : (k:G)*y*(k:G)⁻¹=x := congrArg Subtype.val hk
    have hfix : (g*(k:G))*y*(g*(k:G))⁻¹=y := by
      calc
        _ = g*((k:G)*y*(k:G)⁻¹)*g⁻¹ := by group
        _ = g*x*g⁻¹ := by rw [hkG]
        _ = y := by rw [←he]; simp [mul_assoc]
    have hmem : g*(k:G)∈K := by
      apply hcentral ⟨y,hy⟩ (by simpa using hy2)
      rw [mem_centralizer_singleton_iff]
      simpa [mul_assoc] using congrArg (fun a:G=>a*(g*(k:G))) hfix
    exact hg ((K.mul_mem_cancel_right k.property).mp hmem)

/-- An overgroup of H that realizes the marked central-to-outer fusion is all of G. -/
theorem overgroup_eq_top_of_torus_rotation (t : CubicTorus c) (K : Subgroup G)
    (hHK : c.H≤K) (g : K) (hg : MulAut.conj (g:G) (t.z:G)=(t.n:G)) : K=⊤ := by
  classical
  let j : c.H →* K := inclusion hHK
  have hgz : MulAut.conj g (j t.z)=j t.n := Subtype.ext hg
  let A := t.torus.map c.H.subtype
  let C := Subgroup.centralizer (A:Set G)
  have hzA : (t.z:G)∈A := mem_map_of_mem _ (mem_sup_left (mem_zpowers _))
  have hnA : (t.n:G)∈A := mem_map_of_mem _ (mem_sup_right (mem_zpowers _))
  have hCH : C≤c.H := by
    intro u hu
    rw [t.centralizer,mem_centralizer_singleton_iff]
    exact (hu _ hzA).symm
  have hnot : ¬C≤A := by
    intro hh
    have hc := card_le_of_le hh
    have hAc : Nat.card A=4 := by
      let := t.ambient_torus_kleinFour
      exact IsKleinFour.card_four
    rw [t.torus_centralizer_structure.2,hAc] at hc
    omega
  obtain ⟨v,hvC,hvA⟩ := SetLike.not_le_iff_exists.mp hnot
  let u : c.H := ⟨v,hCH hvC⟩
  have huA : u∉t.torus := fun h=>hvA (mem_map_of_mem _ h)
  have hu1 : u≠1 := fun h=>huA (h ▸ one_mem _)
  have huz : u≠t.z := fun h=>huA (h ▸ mem_sup_left (mem_zpowers _))
  have hun : u≠t.n := fun h=>huA (h ▸ mem_sup_right (mem_zpowers _))
  have hncomm : Commute t.n u := Subtype.ext (hvC _ hnA)
  have hu2 : orderOf u=2 := orderOf_eq_prime (by
    let : IsElementaryAbelian 2 C := t.torus_centralizer_structure.1
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A:=C) v hvC)) hu1
  have hnuA : t.n*u∉t.torus := fun h=>huA
    ((t.torus.mul_mem_cancel_left (mem_sup_right (mem_zpowers _))).mp h)
  have hnu2 : orderOf (t.n*u)=2 := orderOf_eq_prime (by
    rw [hncomm.mul_pow,show t.n^2=1 from t.n_order ▸ pow_orderOf_eq_one t.n,
      show u^2=1 from hu2 ▸ pow_orderOf_eq_one u,one_mul])
    (fun h=>hnuA (h ▸ one_mem _))
  have hfuse : IsConj (j u) (j (t.n*u)) := by
    let w := MulAut.conj g⁻¹ (j u)
    have hwH : (w:G)∈c.H := by
      rw [t.centralizer,mem_centralizer_singleton_iff]
      apply (MulAut.conj (g:G)).injective
      have he : Commute (u:G) (t.n:G) := congrArg Subtype.val hncomm.symm.eq
      have hwu : MulAut.conj (g:G) (w:G)=(u:G) := by
        simp [w,j,MulAut.conj_apply,mul_assoc]
      simpa only [map_mul,hwu,hg] using he.eq
    let wH : c.H := ⟨w,hwH⟩
    have hgw : MulAut.conj g (j wH)=j u := by
      change MulAut.conj g (MulAut.conj g⁻¹ (j u))=j u
      simp [MulAut.conj_apply,mul_assoc]
    have hw2 : orderOf wH=2 := (orderOf_coe wH).symm.trans
      ((orderOf_coe w).trans (((MulAut.conj g⁻¹).orderOf_eq (j u)).trans
        ((orderOf_injective j (inclusion_injective hHK) u).trans hu2)))
    have hwz : wH≠t.z := by
      intro he
      rw [he,hgz] at hgw
      exact hun (inclusion_injective hHK hgw.symm)
    have hh := marked_involution_product_conjugate c t.z wH t.z_order
      t.central_line t.centralizer hw2 hwz
    have hh' := (MulAut.conj g).toMonoidHom.map_isConj (j.map_isConj hh)
    simpa only [MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,map_mul,hgw,hgz] using hh'
  have hzline : ∀ x : c.H, orderOf x=2 → x∈c.H₁⊓c.H₂ → x=t.z := by
    intro x hx hxi
    have hi : x∈zpowers t.z := t.central_line ▸ hxi
    rw [mem_zpowers_iff_mem_range_orderOf,t.z_order] at hi
    obtain ⟨i,hiBound,he⟩ := Finset.mem_image.mp hi
    have hi2 := Finset.mem_range.mp hiBound
    interval_cases i
    · have hx1 : x=1 := by simpa using he.symm
      simp [hx1] at hx
    · simpa using he.symm
  have core_fuse (q : c.H) (hq : q∈c.H₁⊔c.H₂) (hq2 : orderOf q=2)
      (hqz : q≠t.z) (hfq : IsConj (j t.z) (j q)) :
      ∀ x : c.H, orderOf x=2 → IsConj (j t.z) (j x) := by
    have hqQ := residual_involution_mem_core c q hq2 hq
    have hqZ : (⟨q,hqQ⟩:quaternionCore c)∉center (quaternionCore c) := by
      intro he
      apply hqz
      apply hzline q hq2
      rw [←quaternionCore_center c]
      exact mem_map_of_mem _ he
    intro x hx
    by_cases hxres : x∈c.H₁⊔c.H₂
    · by_cases hxz : x=t.z
      · rw [hxz]
      have hxQ := residual_involution_mem_core c x hx hxres
      have hxZ : (⟨x,hxQ⟩:quaternionCore c)∉center (quaternionCore c) := by
        intro he
        apply hxz
        apply hzline x hx
        rw [←quaternionCore_center c]
        exact mem_map_of_mem _ he
      exact hfq.trans (j.map_isConj (core_noncentral_involutions_conjugate c
        ⟨q,hqQ⟩ ⟨x,hxQ⟩ (by simpa using hq2) hqZ (by simpa using hx) hxZ))
    · exact (isConj_iff.mpr ⟨g,hgz⟩).trans (j.map_isConj
        (outside_involutions_conjugate c t.n x t.n_order t.outside hx hxres))
  apply t.overgroup_eq_top_of_fusion K hHK
  change ∀ x : c.H, orderOf x=2 → IsConj (j t.z) (j x)
  by_cases hures : u∈c.H₁⊔c.H₂
  · have hnuout : t.n*u∉c.H₁⊔c.H₂ := fun h=>t.outside
      (((c.H₁⊔c.H₂).mul_mem_cancel_right hures).mp h)
    have hzn : IsConj (j t.z) (j (t.n*u)) :=
      (isConj_iff.mpr ⟨g,hgz⟩).trans (j.map_isConj
        (outside_involutions_conjugate c t.n (t.n*u) t.n_order t.outside hnu2 hnuout))
    exact core_fuse u hures hu2 huz (hzn.trans hfuse.symm)
  · have hnures : t.n*u∈c.H₁⊔c.H₂ :=
      ((c.H₁⊔c.H₂).mul_mem_iff_of_index_two c.index).mpr (by simp [t.outside,hures])
    have hzu : IsConj (j t.z) (j u) := (isConj_iff.mpr ⟨g,hgz⟩).trans
      (j.map_isConj (outside_involutions_conjugate c t.n u t.n_order t.outside hu2 hures))
    exact core_fuse (t.n*u) hnures hnu2
      (fun h=>hnuA (h ▸ mem_sup_left (mem_zpowers _))) (hzu.trans hfuse)

omit [Finite G] in
private theorem four_cases (D : Subgroup G) [IsKleinFour D]
    (a b x : D) (ha : a≠1) (hb : b≠1) (hab : a≠b) :
    x=1 ∨ x=a ∨ x=b ∨ x=a*b := by
  by_cases h1 : x=1
  · exact Or.inl h1
  by_cases h2 : x=a
  · exact Or.inr (Or.inl h2)
  by_cases h3 : x=b
  · exact Or.inr (Or.inr (Or.inl h3))
  exact Or.inr (Or.inr (Or.inr (IsKleinFour.eq_mul_of_ne_all ha hb hab h1 h2 h3)))

omit [Finite G] in
private theorem reflection_other (D : Subgroup G) [IsKleinFour D]
    (a b : D) (ha : a≠1) (hb : b≠1) (hab : a≠b)
    (f : MulAut D) (hf : f≠1) (hfa : f a=a) : f b=a*b := by
  apply IsKleinFour.eq_mul_of_ne_all ha hb hab
  · exact fun h=>hb (f.injective (h.trans (map_one f).symm))
  · exact fun h=>hab (f.injective (h.trans hfa.symm)).symm
  · intro hfb
    apply hf
    apply MulEquiv.ext
    intro x
    rcases four_cases D a b x ha hb hab with rfl|rfl|rfl|rfl
    · exact map_one f
    · exact hfa
    · exact hfb
    · rw [map_mul,hfa,hfb]; rfl

omit [Finite G] in
private theorem reflection_product (D : Subgroup G) [IsKleinFour D]
    (a b : D) (ha : a≠1) (hb : b≠1) (hab : a≠b)
    (f k : MulAut D) (hf : f≠1) (hk : k≠1) (hfa : f a=a) (hkb : k b=b) :
    (f*k)^3=1 ∧ (f*k) a=b := by
  let : IsMulCommutative D := IsKleinFour.isMulCommutative
  have hfb := reflection_other D a b ha hb hab f hf hfa
  have hka : k a=a*b := by
    rw [reflection_other D b a hb ha hab.symm k hk hkb,mul_comm' b a]
  have hpa : (f*k) a=b := by
    change f (k a)=b
    rw [hka,map_mul,hfa,hfb,←mul_assoc,IsKleinFour.mul_self,one_mul]
  have hpb : (f*k) b=a*b := by change f (k b)=a*b; rw [hkb,hfb]
  have hpab : (f*k) (a*b)=a := by
    rw [map_mul,hpa,hpb,mul_comm' a b,←mul_assoc,IsKleinFour.mul_self,one_mul]
  refine ⟨?_,hpa⟩
  apply MulEquiv.ext
  intro x
  change (f*k) ((f*k) ((f*k) x))=x
  rcases four_cases D a b x ha hb hab with rfl|rfl|rfl|rfl
  · simp only [map_one]
  · rw [hpa,hpb,hpab]
  · rw [hpb,hpab,hpa]
  · rw [hpab,hpa,hpb]

/-- The actual aligned endpoint join is the ambient group. This uses the marked
reflection actions; no Atlas endpoint equivalences or completion are assumed. -/
theorem aligned_endpoints_generate (t : CubicTorus c) (a s r : G)
    (ha : a∈normalizer (t.torus.map c.H.subtype:Set G))
    (hs : s∈cubicNormalizer c t.x)
    (hr : r∈(cubicNormalizer (swapFactors c) t.y).map (MulAut.conj a).toMonoidHom)
    (hsA : s∈normalizer (t.torus.map c.H.subtype:Set G))
    (hrA : r∈normalizer (t.torus.map c.H.subtype:Set G))
    (hsz : MulAut.conj s (t.z:G)=(t.z:G))
    (hsn : MulAut.conj s (t.n:G)=(t.z:G)*(t.n:G))
    (hrz : MulAut.conj r (MulAut.conj a (t.z:G))=MulAut.conj a (t.z:G))
    (hrn : MulAut.conj r (MulAut.conj a (t.n:G))=MulAut.conj a ((t.z:G)*(t.n:G)))
    (haz : MulAut.conj a (t.z:G)≠(t.z:G)) :
    cubicNormalizer c t.x ⊔
      (cubicNormalizer (swapFactors c) t.y).map (MulAut.conj a).toMonoidHom=⊤ := by
  let K := cubicNormalizer c t.x ⊔
    (cubicNormalizer (swapFactors c) t.y).map (MulAut.conj a).toMonoidHom
  let A := t.torus.map c.H.subtype
  let : IsKleinFour A := t.ambient_torus_kleinFour
  have hzA : (t.z:G)∈A := mem_map_of_mem _ (mem_sup_left (mem_zpowers _))
  have hnA : (t.n:G)∈A := mem_map_of_mem _ (mem_sup_right (mem_zpowers _))
  have haA : A.map (MulAut.conj a).toMonoidHom=A := mem_normalizer_iff_map_conj_eq.mp ha
  have hazA : MulAut.conj a (t.z:G)∈A := haA ▸ mem_map_of_mem _ hzA
  have hanA : MulAut.conj a (t.n:G)∈A := haA ▸ mem_map_of_mem _ hnA
  let z : A := ⟨t.z,hzA⟩
  let n : A := ⟨t.n,hnA⟩
  let b : A := ⟨MulAut.conj a (t.z:G),hazA⟩
  let f := A.normalizerMonoidHom ⟨s,hsA⟩
  let h := A.normalizerMonoidHom ⟨r,hrA⟩
  have hz1 : z≠1 := by
    intro he
    have hh := t.z_order
    have he' : t.z=1 := Subtype.ext (congrArg (fun q:A=>(q:G)) he)
    simp [he'] at hh
  have hn1 : n≠1 := by
    intro he
    have hh := t.n_order
    have he' : t.n=1 := Subtype.ext (congrArg (fun q:A=>(q:G)) he)
    simp [he'] at hh
  have hzn : z≠n := by
    intro he
    have he' : t.z=t.n := Subtype.ext (congrArg (fun q:A=>(q:G)) he)
    exact t.outside (he' ▸ mem_sup_left ((t.central_line ▸ mem_zpowers t.z).1))
  have hb1 : b≠1 := by
    intro he
    apply hz1
    exact Subtype.ext ((MulAut.conj a).injective
      ((congrArg Subtype.val he).trans (map_one _).symm))
  have hzb : z≠b := fun he=>haz (congrArg Subtype.val he).symm
  have hfz : f z=z := Subtype.ext hsz
  have hhb : h b=b := Subtype.ext hrz
  have hf : f≠1 := by
    intro he
    have hh := congrArg (fun e:MulAut A=>(e n:G)) he
    change MulAut.conj s (t.n:G)=(t.n:G) at hh
    rw [hsn] at hh
    exact hz1 (Subtype.ext (mul_right_cancel (hh.trans (one_mul _).symm)))
  have hh : h≠1 := by
    intro he
    have hh := congrArg (fun e:MulAut A=>(e ⟨MulAut.conj a (t.n:G),hanA⟩:G)) he
    change MulAut.conj r (MulAut.conj a (t.n:G))=MulAut.conj a (t.n:G) at hh
    rw [hrn,map_mul] at hh
    exact hb1 (Subtype.ext (mul_right_cancel (hh.trans (one_mul _).symm)))
  have hkz : MulAut.conj (s*r) (t.z:G)=MulAut.conj a (t.z:G) := by
    have hh := congrArg Subtype.val (reflection_product A z b hz1 hb1 hzb f h hf hh hfz hhb).2
    change s*(r*(t.z:G)*r⁻¹)*s⁻¹=MulAut.conj a (t.z:G) at hh
    simpa [MulAut.conj_apply,mul_assoc] using hh
  have hsK : s∈K := mem_sup_left hs
  have hrK : r∈K := mem_sup_right hr
  have hkK : s*r∈K := K.mul_mem hsK hrK
  let u : G := (s*r)⁻¹*a
  have huH : u∈c.H := by
    rw [t.centralizer,mem_centralizer_singleton_iff]
    apply mul_inv_eq_iff_eq_mul.mp
    change ((s*r)⁻¹*a)*(t.z:G)*((s*r)⁻¹*a)⁻¹=(t.z:G)
    calc
      _ = (s*r)⁻¹*(MulAut.conj a (t.z:G))*(s*r) := by simp [MulAut.conj_apply]; group
      _ = _ := by rw [←hkz]; simp [MulAut.conj_apply,mul_assoc]
  let uH : c.H := ⟨u,huH⟩
  have hH1K : c.H₁.map c.H.subtype≤K := by
    rintro _ ⟨x,hx,rfl⟩
    have hv : uH⁻¹*x*uH∈c.H₁ := by
      simpa only [inv_inv] using c.H₁_normal.conj_mem x hx uH⁻¹
    have hvP : ((uH⁻¹*x*uH:c.H):G)∈cubicNormalizer (swapFactors c) t.y := by
      rw [t.right_ambient_normalizer]
      exact mem_sup_left (mem_sup_right (mem_map_of_mem _ hv))
    have hvK : MulAut.conj a ((uH⁻¹*x*uH:c.H):G)∈K :=
      mem_sup_right (mem_map_of_mem _ hvP)
    have hh := K.mul_mem (K.mul_mem (K.inv_mem hkK) hvK) hkK
    convert hh using 1
    dsimp [uH,u,MulAut.conj_apply]
    group
  have hH2K : c.H₂.map c.H.subtype≤K := by
    apply le_trans ?_ le_sup_left
    rw [t.left_ambient_normalizer]
    exact le_trans le_sup_right le_sup_left
  have hnK : (t.n:G)∈K := by
    apply mem_sup_left
    rw [t.left_ambient_normalizer]
    exact mem_sup_right hnA
  have hHK : c.H≤K := by
    have hres : ∀ x : c.H, x∈c.H₁⊔c.H₂ → (x:G)∈K := by
      intro x hx
      exact (sup_le hH1K hH2K) (by rw [←Subgroup.map_sup]; exact mem_map_of_mem _ hx)
    intro x hx
    let v : c.H := ⟨x,hx⟩
    by_cases hv : v∈c.H₁⊔c.H₂
    · exact hres v hv
    · have hnv : t.n*v∈c.H₁⊔c.H₂ :=
        ((c.H₁⊔c.H₂).mul_mem_iff_of_index_two c.index).mpr (by simp [t.outside,hv])
      exact (K.mul_mem_cancel_left hnK).mp (hres (t.n*v) hnv)
  have hb : b=n ∨ b=z*n := by
    rcases four_cases A z n b hz1 hn1 hzn with he|he|he|he
    · exact (hb1 he).elim
    · exact (hzb he.symm).elim
    · exact Or.inl he
    · exact Or.inr he
  rcases hb with hb|hb
  · apply t.overgroup_eq_top_of_torus_rotation K hHK ⟨s*r,hkK⟩
    exact hkz.trans (congrArg Subtype.val hb)
  · apply t.overgroup_eq_top_of_torus_rotation K hHK ⟨s*(s*r),K.mul_mem hsK hkK⟩
    calc
      MulAut.conj (s*(s*r)) (t.z:G) = MulAut.conj s (MulAut.conj (s*r) (t.z:G)) := by
        simp [MulAut.conj_apply,mul_assoc]
      _ = (t.n:G) := by
        rw [hkz,show MulAut.conj a (t.z:G)=(t.z:G)*(t.n:G) from congrArg Subtype.val hb,
          map_mul,hsz,hsn,←mul_assoc]
        have hzz : (t.z:G)*(t.z:G)=1 := congrArg Subtype.val
          (show t.z*t.z=1 from by
            have hz2 : t.z^2=1 := t.z_order ▸ pow_orderOf_eq_one t.z
            simpa only [pow_two] using hz2)
        rw [hzz,one_mul]

end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
