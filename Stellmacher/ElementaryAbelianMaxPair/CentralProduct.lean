module
public import Stellmacher.ElementaryAbelianMaxPair
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.MaxElementaryImageComparison
/-! # Maximum elementary pairs across a shared central kernel
In J(S)=K C with elementary C centralizing K, each maximum elementary
subgroup absorbs C and splits as its intersection with K times C. An actual
quotient of K whose elementary subgroups lie in two equally sized planes,
and whose full plane preimages are elementary, therefore supplies the exact
two-member maximum family. The common intersection K cap C lies in the
literal kernel; no direct-product hypothesis is imposed.
Source: Aschbacher--Smith 2.5.7, printed p.555, exceptional PSL3(4) cover.
-/
public section
open Subgroup
open scoped Pointwise
namespace Stellmacher
variable {G:Type*} [Group G] [Finite G]
theorem maxFamily_pair_central_product (S K C V W:Subgroup G)
    (hJ:elementaryAbelianMaxJ S=K⊔C)
    (hc:K≤centralizer (C:Set G)) [IsElementaryAbelian 2 C]
    (hV:V≤K) (hW:W≤K) [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W]
    (hcover:∀ A:Subgroup G, IsElementaryAbelian 2 A → A≤K → A≤V ∨ A≤W)
    (hcard:Nat.card V=Nat.card W) (hZV:K⊓C≤V) (hZW:K⊓C≤W) :
    elementaryAbelianMaxSubgroups S={V⊔C,W⊔C} := by
  have hJS:elementaryAbelianMaxJ S≤S:=sSup_le fun _ hA=>hA.1
  have hKC:K⊔C≤S:=hJ ▸ hJS
  have hVC:V≤centralizer (C:Set G):=hV.trans hc
  have hWC:W≤centralizer (C:Set G):=hW.trans hc
  let : IsElementaryAbelian 2 (V⊔C:Subgroup G):=
    IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hVC)
  let : IsElementaryAbelian 2 (W⊔C:Subgroup G):=
    IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hWC)
  have hintV:V⊓C=K⊓C:=le_antisymm (inf_le_inf_right C hV) (le_inf hZV inf_le_right)
  have hintW:W⊓C=K⊓C:=le_antisymm (inf_le_inf_right C hW) (le_inf hZW inf_le_right)
  have hprodV:=card_mul_eq_card_inf_mul_card_sup_of_normalizes V C
    ((le_centralizer_iff.mp hVC).trans (Subgroup.centralizer_le_normalizer _))
  have hprodW:=card_mul_eq_card_inf_mul_card_sup_of_normalizes W C
    ((le_centralizer_iff.mp hWC).trans (Subgroup.centralizer_le_normalizer _))
  have hcards:Nat.card (V⊔C:Subgroup G)=Nat.card (W⊔C:Subgroup G) := by
    rw [hcard,hintV] at hprodV
    rw [hintW] at hprodW
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hprodV.symm.trans hprodW)
  apply maxFamily_eq_pair_of_cover S _ _ ((sup_le_sup_right hV C).trans hKC)
    ((sup_le_sup_right hW C).trans hKC) hcards
  intro A hA
  let : IsElementaryAbelian 2 A:=hA.2.1
  have hAKC:A≤K⊔C:=hJ ▸ (le_sSup hA)
  have hCC:C≤centralizer (C:Set G):=by
    intro c hc' d hd
    let : CommGroup C:=IsMulCommutative.instCommGroup
    exact congrArg (fun x:C=>(x:G)) (mul_comm (⟨d,hd⟩:C) ⟨c,hc'⟩)
  have hAC:A≤centralizer (C:Set G):=hAKC.trans (sup_le hc hCC)
  have he:IsElementaryAbelian 2 (A⊔C:Subgroup G):=
    IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hAC)
  have hCA:C≤A:=by
    have heq:A=A⊔C:=eq_of_le_of_card_ge le_sup_left
      (hA.2.2 _ (sup_le hA.1 (le_sup_right.trans hKC)) he)
    rw [heq]
    exact le_sup_right
  have haeq:A=(A⊓K)⊔C:=by
    apply le_antisymm ?_ (sup_le inf_le_left hCA)
    intro a ha
    have hp:a∈(K:Set G)*(C:Set G):=by
      rw [←coe_mul_of_right_le_normalizer_left K C
        ((le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _))]
      exact hAKC ha
    obtain ⟨k,hk,c,hc',hkc⟩:=hp
    have hkA:k∈A:=by
      have ht:=A.mul_mem ha (A.inv_mem (hCA hc'))
      change a*c⁻¹∈A at ht
      have hk':a*c⁻¹=k:=by rw [←hkc]; simp only [mul_inv_cancel_right]
      rwa [hk'] at ht
    rw [←hkc]
    exact mul_mem_sup ⟨hkA,hk⟩ hc'
  have hAE:IsElementaryAbelian 2 (A⊓K:Subgroup G):=IsElementaryAbelian.of_le inf_le_left
  rcases hcover (A⊓K) hAE inf_le_right with hv | hw
  · left
    rw [haeq]
    exact sup_le_sup_right hv C
  · right
    rw [haeq]
    exact sup_le_sup_right hw C

omit [Finite G] in
theorem sup_ne_of_central_intersection (K C V W:Subgroup G)
    (hc:K≤centralizer (C:Set G)) (hV:V≤K) (hW:W≤K)
    (hZV:K⊓C≤V) (hZW:K⊓C≤W) (hne:V≠W) : V⊔C≠W⊔C := by
  have hle (A B:Subgroup G) (hA:A≤K) (hB:B≤K) (hZB:K⊓C≤B)
      (he:A⊔C=B⊔C) : A≤B := by
    intro a ha
    have ha':a∈(B:Set G)*(C:Set G):=by
      rw [←coe_mul_of_right_le_normalizer_left B C
        ((le_centralizer_iff.mp (hB.trans hc)).trans (Subgroup.centralizer_le_normalizer _))]
      rw [←he]
      exact mem_sup_left ha
    obtain ⟨b,hb,c,hc',hbc⟩:=ha'
    have hcK:c∈K := by
      have ht:=K.mul_mem (K.inv_mem (hB hb)) (hA ha)
      rw [←hbc,inv_mul_cancel_left] at ht
      exact ht
    exact hbc ▸ B.mul_mem hb (hZB ⟨hcK,hc'⟩)
  intro he
  exact hne (le_antisymm (hle V W hV hW hZW he) (hle W V hW hV hZV he.symm))

theorem maxFamily_pair_central_preimages {Y:Type*} [Group Y] [Finite Y]
    (S K C:Subgroup G) (q:K→*Y) (hq:Function.Surjective q)
    (hJ:elementaryAbelianMaxJ S=K⊔C)
    (hc:K≤centralizer (C:Set G)) [IsElementaryAbelian 2 C]
    (hker:K⊓C≤q.ker.map K.subtype)
    (V W:Subgroup Y) (hne:V≠W) (hcard:Nat.card V=Nat.card W)
    (hV:IsElementaryAbelian 2 (V.comap q)) (hW:IsElementaryAbelian 2 (W.comap q))
    (hcover:∀ A:Subgroup Y, IsElementaryAbelian 2 A → A≤V ∨ A≤W) :
    let V':=(V.comap q).map K.subtype
    let W':=(W.comap q).map K.subtype
    elementaryAbelianMaxSubgroups S={V'⊔C,W'⊔C} ∧ V'⊔C≠W'⊔C := by
  let V':=(V.comap q).map K.subtype
  let W':=(W.comap q).map K.subtype
  let :=hV
  let :=hW
  let : IsElementaryAbelian 2 V':=IsElementaryAbelian.map K.subtype
  let : IsElementaryAbelian 2 W':=IsElementaryAbelian.map K.subtype
  have hv:V'≤K:=map_subtype_le _
  have hw:W'≤K:=map_subtype_le _
  have hZA (A:Subgroup Y) : K⊓C≤(A.comap q).map K.subtype := by
    apply hker.trans (map_mono ?_)
    intro k hk
    change q k∈A
    rw [show q k=1 from hk]
    exact A.one_mem
  have hcov (A:Subgroup G) (he:IsElementaryAbelian 2 A) (ha:A≤K) : A≤V' ∨ A≤W' := by
    let :=he
    let : IsElementaryAbelian 2 (A.subgroupOf K):=IsElementaryAbelian.subgroupOf ha
    let : IsElementaryAbelian 2 ((A.subgroupOf K).map q):=IsElementaryAbelian.map q
    have hstep (B:Subgroup Y) (hb:(A.subgroupOf K).map q≤B) : A≤(B.comap q).map K.subtype := by
      intro a ha'
      exact ⟨⟨a,ha ha'⟩,hb (mem_map_of_mem q ha'),rfl⟩
    exact (hcover _ inferInstance).imp (hstep V) (hstep W)
  have hsize : Nat.card V'=Nat.card W' := by
    rw [show V'=(V.comap q).map K.subtype from rfl,
      show W'=(W.comap q).map K.subtype from rfl,
      card_map_of_injective K.subtype_injective,card_map_of_injective K.subtype_injective]
    have hVker:q.ker≤V.comap q:=by
      intro k hk
      change q k∈V
      rw [show q k=1 from hk]
      exact V.one_mem
    have hWker:q.ker≤W.comap q:=by
      intro k hk
      change q k∈W
      rw [show q k=1 from hk]
      exact W.one_mem
    rw [←IsElementaryAbelian.card_inf_ker_mul_card_map (V.comap q) q,
      ←IsElementaryAbelian.card_inf_ker_mul_card_map (W.comap q) q,
      inf_eq_right.mpr hVker,inf_eq_right.mpr hWker,
      map_comap_eq_self_of_surjective hq,map_comap_eq_self_of_surjective hq,hcard]
  have hneq:V'≠W':=by
    intro he
    have hh:V.comap q=W.comap q:=Subgroup.map_injective K.subtype_injective he
    apply hne
    have hm:=congrArg (Subgroup.map q) hh
    simpa only [map_comap_eq_self_of_surjective hq] using hm
  exact ⟨maxFamily_pair_central_product S K C V' W' hJ hc hv hw hcov hsize (hZA V) (hZA W),
    sup_ne_of_central_intersection K C V' W' hc hv hw (hZA V) (hZA W) hneq⟩

end Stellmacher
