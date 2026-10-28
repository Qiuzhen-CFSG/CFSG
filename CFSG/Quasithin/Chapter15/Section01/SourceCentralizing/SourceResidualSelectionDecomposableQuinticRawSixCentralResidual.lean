module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawConstrainedSource
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawClassicalCore
public import Theory.SpecificGroups.AlternatingSix.LocalResidual
public import Theory.GroupTheory.PResidual.TwoThreeComparison

/-!
# The original central A6 intersection, including the cubic cover

The residual comparison for full Sylow overgroups of A6 lifts through a
kernel with prime divisors two and three. After factoring out the actual
prime-to-three residual, the kernel image is a two-group, so two-perfectness
kills the remaining two-residual image. The original local center bound
supplies precisely this kernel condition, including center of order three.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem twoResidual_eq_primeToResidual_of_twoThree_kernel
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (f : A →* B) (hf : Function.Surjective f)
    (hk : IsPiGroup twoThreePrimes f.ker)
    (hB : pResidual 2 B = primeToResidual 3 B) :
    pResidual 2 A = primeToResidual 3 A := by
  apply le_antisymm _ primeToResidual_three_le_twoResidual
  let N := primeToResidual 3 A
  let q := QuotientGroup.mk' N
  have hXN : pResidual 2 A ≤ N ⊔ f.ker := by
    rw [←comap_map_eq]
    apply (le_comap_map f (pResidual 2 A)).trans
    apply comap_mono
    rw [map_pResidual_of_surjective 2 f hf,
      map_primeToResidual_of_surjective 3 f hf,hB]
  have hpi : IsPiGroup twoThreePrimes (f.ker.map q) :=
    hk.of_surjective (q.subgroupMap f.ker) (q.subgroupMap_surjective f.ker)
  have hc : Nat.Coprime 3 (Nat.card (A ⧸ N)) := by
    simpa only [N,←index_eq_card] using (primeToResidual_index_coprime (G := A) 3)
  have hp : IsPGroup 2 (f.ker.map q) :=
    isPGroup_two_of_isPiGroup_twoThree hpi
      ((Nat.prime_three.coprime_iff_not_dvd.mp hc).imp fun hd =>
        hd.trans (card_subgroup_dvd_card _))
  have hi : (pResidual 2 A).map q ≤ f.ker.map q := by
    have hm := map_mono (f := q) hXN
    simpa only [Subgroup.map_sup,q,QuotientGroup.map_mk'_self,bot_sup_eq] using hm
  let a : pResidual 2 A →* f.ker.map q :=
    (q.comp (pResidual 2 A).subtype).codRestrict _
      (fun x => hi (mem_map_of_mem q x.property))
  have ha := (isPPerfect_pResidual (G := A) 2).hom_eq_one_of_isPGroup hp a
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  exact congrArg (fun b : pResidual 2 A →* f.ker.map q => (b ⟨x,hx⟩ : A ⧸ N)) ha

private theorem two_group_isPiGroup_twoThree
    {A : Type*} [Group A] [Finite A] (hp : IsPGroup 2 A) :
    IsPiGroup twoThreePrimes A := by
  apply (IsPiGroup_iff _ _).mpr
  intro p hd
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have htwo : p.val ∣ 2 := p.property.dvd_of_dvd_pow (hn ▸ hd)
  exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp htwo |>.resolve_left p.property.ne_one)

private theorem central_preimage_isPiGroup
    {A : Type*} [Group A] [Finite A]
    (hc : Nat.card (center (A ⧸ pCore 2 A)) = 1 ∨
      Nat.card (center (A ⧸ pCore 2 A)) = 3) :
    IsPiGroup twoThreePrimes (centralPreimage (pCore 2 A)) := by
  let K := centralPreimage (pCore 2 A)
  let a := (QuotientGroup.mk' (pCore 2 A)).comp K.subtype
  have hk : IsPGroup 2 a.ker := by
    let j : a.ker →* pCore 2 A := {
      toFun := fun x => ⟨x.val.val,(QuotientGroup.eq_one_iff _).mp x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    apply pCore_isPGroup.of_injective j
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : pCore 2 A => (z : A)) he
  have hcenter : IsPiGroup twoThreePrimes (center (A ⧸ pCore 2 A)) := by
    apply (IsPiGroup_iff _ _).mpr
    intro p hd
    rcases hc with hc | hc
    · exact (p.property.not_dvd_one (hc ▸ hd)).elim
    · have hthree : p.val = 3 :=
        (Nat.dvd_prime Nat.prime_three).mp (hc ▸ hd) |>.resolve_left p.property.ne_one
      exact Or.inr hthree
  have hr : IsPiGroup twoThreePrimes a.range := by
    let j : a.range →* center (A ⧸ pCore 2 A) := {
      toFun := fun x => ⟨x.val,by
        obtain ⟨y,hy⟩ := x.property
        rw [←hy]
        exact y.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    apply hcenter.of_injective j
    intro x y he
    apply Subtype.ext
    exact congrArg (fun z : center (A ⧸ pCore 2 A) => (z : A ⧸ pCore 2 A)) he
  exact IsPiGroup.of_normal_subgroup_and_quotient a.ker
    ((two_group_isPiGroup_twoThree hk).isPiSubgroup _)
    (hr.of_equiv (QuotientGroup.quotientKerEquivRange a))

/-- The literal intersection retains residual equality in both central A6 rows. -/
theorem PreparedChosenModule.raw_six_central_intersection_residuals
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V Z1 L : Subgroup G} (h : PreparedChosenModule T M V)
    (hTM : (T : Subgroup G) ≤ M)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hLG : L ≤ centralizer (Z1 : Set G)) (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hs : Chapter1.IsSylowIn 2 (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) L)
    (e : ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃*
      alternatingGroup (Fin 6)) :
    pResidual 2 (M ⊓ L : Subgroup G) = primeToResidual 3 (M ⊓ L : Subgroup G) := by
  let A := alternatingGroup (Fin 6)
  let ec := (centralPreimageQuotientEquiv (pCore 2 L)).trans e
  let f := ec.toMonoidHom.comp (QuotientGroup.mk' (centralPreimage (pCore 2 L)))
  have hf : Function.Surjective f := ec.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = centralPreimage (pCore 2 L) := by
    rw [MonoidHom.ker_comp_of_injective _ _ ec.injective,QuotientGroup.ker_mk']
  have hpi : IsPiGroup twoThreePrimes f.ker := by
    rw [hk]
    exact central_preimage_isPiGroup (h.raw_local_core_center_card hG T hZ hZne hLG hq)
  let P := M ⊓ L
  let j : P →* L := inclusion inf_le_right
  let g := f.comp j
  have hgk : IsPiGroup twoThreePrimes g.ker := by
    let a : g.ker →* f.ker := {
      toFun := fun x => ⟨j x.val,x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    apply hpi.of_injective a
    intro x y he
    apply Subtype.ext
    exact (inclusion_injective inf_le_right) (congrArg Subtype.val he)
  obtain ⟨Q,hQ⟩ := hs
  let S := Q.mapSurjective hf
  have hS : (S : Subgroup A) ≤ g.range := by
    rintro _ ⟨x,hx,rfl⟩
    have hxSL : (x : G) ∈ ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L :=
      hQ ▸ mem_map_of_mem L.subtype hx
    exact ⟨⟨x,⟨hTM hxSL.1.1,x.property⟩⟩,rfl⟩
  have hmodel := AlternatingSix.LocalResidual.sylow_overgroup_residuals S g.range hS
  exact twoResidual_eq_primeToResidual_of_twoThree_kernel g.rangeRestrict
    g.rangeRestrict_surjective
    (hgk.of_equiv (MulEquiv.subgroupCongr (MonoidHom.ker_rangeRestrict g))) hmodel

/-- The original intersection lies in Mc even when the local core has cubic center. -/
theorem PreparedChosenModule.raw_six_central_intersection_le_partner
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G} (h : PreparedChosenModule T M V)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hLG : L ≤ centralizer (Z1 : Set G)) (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hs : Chapter1.IsSylowIn 2 (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) L)
    (hcubic : (primeToResidual 3 (M ⊓ L : Subgroup G)).map (M ⊓ L).subtype ≤
      centralizer (V : Set G))
    (e : ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃*
      alternatingGroup (Fin 6)) :
    M ⊓ L ≤ Mc := by
  let P := M ⊓ L
  let SL := ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L
  have hR : (pResidual 2 P).map P.subtype ≤ centralizer (V : Set G) := by
    rw [h.raw_six_central_intersection_residuals hG T hTM hZ hZne hLG hq hs e]
    exact hcubic
  have hCMc : centralizer (V : Set G) ≤ Mc := by
    rw [hfull]
    exact localModule_centralizer_le_partner T M hu
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hSLP : SL ≤ P := le_inf ((inf_le_left.trans inf_le_left).trans hTM) inf_le_right
  have hSyl : Chapter1.IsSylowIn 2 SL P := by
    obtain ⟨hp,hSL,hmax⟩ := Chapter1.isSylowIn_iff.mp hs
    exact Chapter1.isSylowIn_iff.mpr
      ⟨hp,hSLP,fun U hU hSU hUP => hmax U hU hSU (hUP.trans inf_le_right)⟩
  obtain ⟨Q,hQ⟩ := hSyl
  have he := congrArg (map P.subtype) (pResidual_sup_sylow_eq_top Q)
  rw [Subgroup.map_sup,hQ,←MonoidHom.range_eq_map,range_subtype] at he
  change P ≤ Mc
  rw [←he]
  exact sup_le (hR.trans hCMc) ((inf_le_left.trans inf_le_left).trans hTMc)

end CFSG.Quasithin.Chapter15.Section01
