module

public import Theory.GroupTheory.CentralExtensionAbelianSylowSection
public import Theory.GroupTheory.DisjointCommutingProduct
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Central cubic extensions of the five-letter symmetric group

The full preimage of A5 has an abelian Sylow-three preimage of order nine.
Transfer therefore splits its central cubic kernel over the perfect A5,
with the section range equal to the derived subgroup. Cubing a lift of a
transposition gives an actual involutory lift. These two subgroups supply a
section of the prescribed S5 quotient and an evaluated direct product.
-/

public noncomputable section
open Subgroup
namespace CentralExtension
variable {E : Type*} [Group E] [Finite E]
local notation "S5" => Equiv.Perm (Fin 5)
local notation "A5" => alternatingGroup (Fin 5)

omit [Finite E] in
private theorem comap_card {B : Type*} [Group B] (f : E →* B)
    (hf : Function.Surjective f) (K : Subgroup B) :
    Nat.card (K.comap f)=Nat.card f.ker*Nat.card K := by
  let L := K.comap f
  let q := f.subgroupComap K
  have hq : Function.Surjective q := f.subgroupComap_surjective_of_surjective K hf
  have hker : q.ker=f.ker.subgroupOf L := by
    ext x
    constructor
    · exact fun hx => congrArg Subtype.val hx
    · exact fun hx => Subtype.ext hx
  have hle : f.ker≤L := by intro x hx; change f x∈K; rw [show f x=1 from hx]; exact K.one_mem
  have hkcard : Nat.card q.ker=Nat.card f.ker := by
    rw [hker,Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
  have hh := q.ker.card_mul_index
  rw [hkcard,index_ker,q.range_eq_top_of_surjective hq,card_top] at hh
  exact hh.symm

private theorem even_preimage_sec (f : E →* S5) (hf : Function.Surjective f)
    (hc : f.ker≤center E) (hk : Nat.card f.ker=3) :
    let H := (A5).comap f
    ∃ s : A5 →* H, (f.subgroupComap A5).comp s=MonoidHom.id A5 ∧
      s.range=commutator H := by
  let H := (A5).comap f
  let q := f.subgroupComap A5
  have hq : Function.Surjective q := f.subgroupComap_surjective_of_surjective A5 hf
  have hker : q.ker=f.ker.subgroupOf H := by
    ext x
    constructor
    · exact fun hx => congrArg Subtype.val hx
    · exact fun hx => Subtype.ext hx
  have hle : f.ker≤H := by intro x hx; change f x∈A5; rw [show f x=1 from hx]; exact (A5).one_mem
  have hk3 : Nat.card q.ker=3 := by
    rw [hker,Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,hk]
  have hqc : q.ker≤center H := by
    intro x hx
    have hxk : (x : E)∈f.ker := congrArg Subtype.val hx
    exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp (hc hxk) y))
  let : Group.IsPerfect A5 := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let P : Sylow 3 A5 := Sylow.nonempty.some
  have hP3 : Nat.card P=3 := by
    rw [P.card_eq_multiplicity,Nat.card_eq_fintype_card,card_alternatingGroup]
    norm_num [Nat.factorial]
    decide +kernel
  have hP9 : Nat.card ((P : Subgroup A5).comap q)=9 := by
    rw [comap_card q hq,hk3,hP3]
  have hPa : IsMulCommutative ((P : Subgroup A5).comap q) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hP9
  exact exists_derived_section_of_abelian_sylow_preimage q hq hqc
    (IsPGroup.of_card (n := 1) (by simpa using hk3)) P hPa

private theorem sup_odd_eq_top (K : Subgroup S5) (hAK : A5≤K)
    (a : S5) (ha : a∈K) (haodd : a∉A5) : K=⊤ := by
  apply top_unique
  intro x _
  by_cases hx : x∈A5
  · exact hAK hx
  have hxa : x*a⁻¹∈A5 := by
    rw [(A5).mul_mem_iff_of_index_two alternatingGroup.index_eq_two,inv_mem_iff]
    exact iff_of_false hx haodd
  have hh := K.mul_mem (hAK hxa) ha
  simpa only [inv_mul_cancel_right] using hh

/-- Every central extension of S5 with kernel of order three splits over
the prescribed quotient map. Multiplication by the actual kernel gives
the displayed direct-product equivalence. -/
theorem exists_marked_section_of_cubic_kernel (f : E →* S5)
    (hf : Function.Surjective f) (hc : f.ker≤center E) (hk : Nat.card f.ker=3) :
    ∃ s : S5 →* E, f.comp s=MonoidHom.id S5 ∧
      ∃ e : f.ker × S5 ≃* E, ∀ k g, e (k,g)=(k : E)*s g := by
  classical
  let H := (A5).comap f
  obtain ⟨s,hs,hsrange⟩ := even_preimage_sec f hf hc hk
  let D := (commutator H).map H.subtype
  let : D.Normal := ConjAct.normal_of_characteristic_of_normal
  have hDH : D≤H := map_subtype_le _
  have hs' (a : A5) : f ((s a : H) : E)=(a : S5) :=
    congrArg Subtype.val (DFunLike.congr_fun hs a)
  have hDmap : D.map f=A5 := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact hDH hx
    · intro a ha
      exact ⟨s ⟨a,ha⟩,⟨s ⟨a,ha⟩,hsrange ▸ ⟨⟨a,ha⟩,rfl⟩,rfl⟩,hs' ⟨a,ha⟩⟩
  have hDker : Disjoint D f.ker := by
    apply disjoint_def.mpr
    intro x hx hxk
    obtain ⟨y,hy,rfl⟩ := hx
    rw [←hsrange] at hy
    obtain ⟨a,rfl⟩ := hy
    have ha : a=1 := Subtype.ext ((hs' a).symm.trans hxk)
    simp only [ha,map_one]
  let τ : S5 := Equiv.swap 0 1
  have hτ2 : τ^2=1 := by decide
  have hτodd : τ∉A5 := by
    intro hh
    have hs : Equiv.Perm.sign τ=1 := hh
    rw [Equiv.Perm.sign_swap (by decide : (0 : Fin 5)≠1)] at hs
    norm_num at hs
  obtain ⟨g,hg⟩ := hf τ
  have hg2 : g^2∈f.ker := by change f (g^2)=1; rw [map_pow,hg,hτ2]
  have hg6 : g^6=1 := by
    have hh := pow_card_eq_one' (x := (⟨g^2,hg2⟩ : f.ker))
    have hh' := congrArg Subtype.val hh
    simpa only [hk,coe_pow,coe_one,←pow_mul] using hh'
  let r := g^3
  have hr2 : r^2=1 := by dsimp [r]; rw [←pow_mul]; exact hg6
  have hfr : f r=τ := by
    change f (g^3)=τ
    rw [map_pow,hg,show 3=2+1 by decide,pow_add,hτ2,one_mul,pow_one]
  have hrH : r∉H := fun hh => hτodd (hfr ▸ hh)
  have hrne : r≠1 := fun hh => hrH (hh ▸ H.one_mem)
  have hrorder : orderOf r=2 := orderOf_eq_prime hr2 hrne
  have hv (x : E) (hx : x∈zpowers r) : x=1 ∨ x=r := by
    rw [mem_zpowers_iff_mem_range_orderOf,hrorder] at hx
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hx
    have hn2 := Finset.mem_range.mp hn
    interval_cases n <;> simp
  let K := D⊔zpowers r
  have hKmap : K.map f=⊤ := by
    apply sup_odd_eq_top (K.map f)
      (hDmap ▸ map_mono (show D≤K from le_sup_left)) τ
    · exact hfr ▸ mem_map_of_mem f (show r∈K from mem_sup_right (mem_zpowers r))
    · exact hτodd
  have hKker : Disjoint K f.ker := by
    apply disjoint_def.mpr
    intro x hx hxk
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_sup_of_normal_left.mp hx
    rcases hv b hb with rfl | rfl
    · exact hDker.le_bot ⟨by simpa using ha,hxk⟩
    · have hfa : f a∈A5 := hDH ha
      have he : f a=τ⁻¹ := eq_inv_of_mul_eq_one_left (by
        simpa only [map_mul,hfr] using (show f (a*r)=1 from hxk))
      have hi : τ⁻¹∈A5 := he ▸ hfa
      exact False.elim (hτodd (by simpa only [inv_inv] using (A5).inv_mem hi))
  let k : K →* S5 := f.comp K.subtype
  have hki : Function.Injective k := by
    apply (MonoidHom.ker_eq_bot_iff k).mp
    apply bot_unique
    intro x hx
    exact Subtype.ext (hKker.le_bot ⟨x.property,hx⟩)
  have hks : Function.Surjective k := by
    intro x
    obtain ⟨y,hy,hyx⟩ := (hKmap ▸ (mem_top x) : x∈K.map f)
    exact ⟨⟨y,hy⟩,hyx⟩
  let a := MulEquiv.ofBijective k ⟨hki,hks⟩
  let sec : S5 →* E := K.subtype.comp a.symm.toMonoidHom
  have hsec (x : S5) : f (sec x)=x := a.apply_symm_apply x
  have hcomm (u : f.ker) (x : S5) : Commute (u : E) (sec x) :=
    (mem_center_iff.mp (hc u.property) (sec x)).symm
  let m : f.ker × S5 →* E := f.ker.subtype.noncommCoprod sec hcomm
  have hmi : Function.Injective m := by
    intro x y hh
    have hxy : x.2=y.2 := by
      have hfxy := congrArg f hh
      change f ((x.1 : E)*sec x.2)=f ((y.1 : E)*sec y.2) at hfxy
      simpa only [map_mul,show f (x.1 : E)=1 from x.1.property,
        show f (y.1 : E)=1 from y.1.property,one_mul,hsec] using hfxy
    apply Prod.ext
    · apply Subtype.ext
      change (x.1 : E)*sec x.2=(y.1 : E)*sec y.2 at hh
      rw [hxy] at hh
      exact mul_right_cancel hh
    · exact hxy
  have hms : Function.Surjective m := by
    intro x
    have hkx : x*(sec (f x))⁻¹∈f.ker := by
      change f (x*(sec (f x))⁻¹)=1
      rw [map_mul,map_inv,hsec,mul_inv_cancel]
    refine ⟨(⟨x*(sec (f x))⁻¹,hkx⟩,f x),?_⟩
    change x*(sec (f x))⁻¹*sec (f x)=x
    simp only [inv_mul_cancel_right]
  exact ⟨sec,MonoidHom.ext hsec,MulEquiv.ofBijective m ⟨hmi,hms⟩,fun _ _ => rfl⟩

end CentralExtension
