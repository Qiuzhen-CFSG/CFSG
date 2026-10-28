module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.PairImage
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.SylowOuterSolvableKernel
public import Theory.GroupTheory.PerfectCentralCoverOuter
public import CFSG.Quasithin.ChapterI.Section03.SylowAutomorphisms
/-!
# The original pair survives solvable lifting and two quotient actions

Let F be the original perfect fixed residual and I = F N_T(B). The proved
pair-kernel theorem says that every nontrivial image of F under a map from
I has order divisible by twenty-five. This property survives a solvable
lift of the image of I: a quotient action of order avoiding twenty-five
has solvable image on the lifted F. Two such actions with solvable common
kernel therefore kill the original F.

Apply this to the actual Sylow stabilizer in Aut(K/Z(K)). Both the outer
projection kernel and the Sylow restriction kernel are solvable. Two normal
kernels in Aut(P) with solvable intersection and quotient orders avoiding
twenty-five force the unchanged residual to act innerly on K. The two
quotients may have separate nonsolvable images; the original factor exchange
is retained through I throughout this argument.

Source: Aschbacher--Smith 4.4.10--11, printed pp.621--622, and I.3.1.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G H J R : Type*} [Group G] [Finite G] [Group H]
  [Group J] [Group R] [Finite R]
  {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
/-- A quotient action whose order avoids twenty-five has solvable image on the lifted original residual. -/
theorem source_a5_oddActorResidual_lift_image_solvable
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G)) :
    let F := ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype)
    let I := F ⊔ ((T : Subgroup G) ⊓ normalizer (B : Set G))
    ∀ (f : I →* J) (q : H →* J), Function.Surjective q → Group.IsSolvable q.ker →
      ∀ r : H →* R, ¬ 25 ∣ Nat.card R →
      Group.IsSolvable ((((F.subgroupOf I).map f).comap q).map r) := by
  intro F I f q hq hqsol r hR
  let := hqsol
  let U := ((F.subgroupOf I).map f).comap q
  let r' := r.rangeRestrict
  let N := q.ker.map r'
  have hN : N.Normal := Normal.map inferInstance r' r.rangeRestrict_surjective
  have hsN : Group.IsSolvable N := Group.isSolvable_of_surjective (r'.subgroupMap_surjective q.ker)
  have hNrad : N ≤ solvableRadical r.range := le_solvableRadical N hN hsN
  let χ := (QuotientGroup.mk' (solvableRadical r.range)).comp r'
  have hk : q.ker ≤ χ.ker := by
    intro x hx
    exact (QuotientGroup.eq_one_iff _).mpr (hNrad (mem_map_of_mem r' hx))
  let a : J →* r.range ⧸ solvableRadical r.range := q.liftOfSurjective hq ⟨χ,hk⟩
  have ha (x : H) : a (q x) = χ x := by simp [a]
  have hz : (a.comp f).comp (inclusion (show F ≤ I from le_sup_left)) = 1 := by
    rcases source_a5_oddActorResidual_hom_trivial_or_twentyFive
      D e hn hp B hB hBC hperm (a.comp f) with he | hd
    · exact he
    · exact (hR (hd.trans ((Subgroup.card_subgroup_dvd_card _).trans
        ((card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card _))))).elim
  have hle : U.map r' ≤ solvableRadical r.range := by
    rintro y ⟨x,hx,rfl⟩
    have hx' : q x ∈ (F.subgroupOf I).map f := hx
    obtain ⟨z,hzF,hzq⟩ := hx'
    apply (QuotientGroup.eq_one_iff _).mp
    change χ x = 1
    rw [← ha, ← hzq]
    exact DFunLike.congr_fun hz (⟨z,hzF⟩ : F)
  let j : U.map r →* solvableRadical r.range := {
    toFun := fun y => ⟨⟨y, by obtain ⟨x,_,hx⟩ := y.property; exact ⟨x,hx⟩⟩, by
      apply hle
      obtain ⟨x,hx,he⟩ := y.property
      exact ⟨x,hx,Subtype.ext he⟩⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  exact Group.isSolvable_of_isSolvable_injective (f := j)
    (fun x y h => Subtype.ext (congrArg (fun z : solvableRadical r.range => (z : R)) h))

include D in
/-- Two such quotient actions with solvable common kernel kill the original residual after a solvable lift. -/
theorem source_a5_oddActorResidual_hom_eq_one_of_solvable_quotients
    {R₁ R₂ : Type*} [Group R₁] [Finite R₁] [Group R₂] [Finite R₂]
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G)) :
    let F := ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype)
    let I := F ⊔ ((T : Subgroup G) ⊓ normalizer (B : Set G))
    ∀ (f : I →* J) (q : H →* J), Function.Surjective q → Group.IsSolvable q.ker →
      ∀ (a : H →* R₁) (b : H →* R₂), ¬ 25 ∣ Nat.card R₁ → ¬ 25 ∣ Nat.card R₂ →
      Group.IsSolvable (a.prod b).ker →
      f.comp (inclusion (show F ≤ I from le_sup_left)) = 1 := by
  intro F I f q hq hqsol a b ha hb hk
  let U := ((F.subgroupOf I).map f).comap q
  let := source_a5_oddActorResidual_lift_image_solvable D e hn hp B hB hBC hperm f q hq hqsol a ha
  let := source_a5_oddActorResidual_lift_image_solvable D e hn hp B hB hBC hperm f q hq hqsol b hb
  let := hk
  let r : U →* U.map a × U.map b := {
    toFun := fun x => (⟨a x,mem_map_of_mem a x.property⟩,⟨b x,mem_map_of_mem b x.property⟩)
    map_one' := Prod.ext (Subtype.ext a.map_one) (Subtype.ext b.map_one)
    map_mul' := fun x y => Prod.ext (Subtype.ext (a.map_mul x y)) (Subtype.ext (b.map_mul x y)) }
  let k : r.ker →* (a.prod b).ker := {
    toFun := fun x => ⟨x.val.val,by
      apply Prod.ext
      · exact congrArg (fun z : U.map a × U.map b => (z.1 : R₁)) x.property
      · exact congrArg (fun z : U.map a × U.map b => (z.2 : R₂)) x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let : Group.IsSolvable r.ker := Group.isSolvable_of_isSolvable_injective (f := k)
    (fun x y h => Subtype.ext (Subtype.ext
      (congrArg (fun z : (a.prod b).ker => (z : H)) h)))
  let : Group.IsSolvable U := Group.isSolvable_of_ker_le_range r.ker.subtype r (by simp)
  let : Group.IsSolvable ((F.subgroupOf I).map f) :=
    Group.isSolvable_of_surjective (q.subgroupComap_surjective_of_surjective _ hq)
  let : Group.IsPerfect F := Group.IsPerfect.map _
  let : Group.IsPerfect (F.subgroupOf I) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe
      (show F ≤ I from le_sup_left)).symm.toMonoidHom)
      (subgroupOfEquivOfLe (show F ≤ I from le_sup_left)).symm.surjective
  let : Group.IsPerfect ((F.subgroupOf I).map f) := Group.IsPerfect.map f
  have hs : Subsingleton ((F.subgroupOf I).map f) := by
    by_contra! hh
    exact Group.IsPerfect.not_isSolvable ((F.subgroupOf I).map f) inferInstance
  ext x
  exact congrArg (fun y : (F.subgroupOf I).map f => (y : J))
    (hs.elim ⟨f (inclusion (show F ≤ I from le_sup_left) x),
      mem_map_of_mem f x.property⟩ 1)

include D in
/-- Two quotient actions on the actual Sylow automorphism group force every original outer action to kill the residual. -/
theorem source_a5_oddActorResidual_outer_hom_eq_one_of_sylow_quotients
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (P : Sylow 2 S) (A C : Subgroup (MulAut P)) [A.Normal] [C.Normal]
    (hAC : Group.IsSolvable (A ⊓ C : Subgroup (MulAut P)))
    (hA : ¬ 25 ∣ A.index) (hC : ¬ 25 ∣ C.index) :
    let F := ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype)
    let I := F ⊔ ((T : Subgroup G) ⊓ normalizer (B : Set G))
    ∀ f : I →* MulAut.Outer S, f.comp (inclusion (show F ≤ I from le_sup_left)) = 1 := by
  intro F I f
  let r := MulAut.sylowRestriction P
  let q := MulAut.sylowOuterMap P
  let a := (QuotientGroup.mk' A).comp r
  let b := (QuotientGroup.mk' C).comp r
  let : Group.IsSolvable (fixingSubgroup (MulAut S) (P : Set S)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  let : Group.IsSolvable r.ker := MulAut.sylowRestriction_ker_isSolvable P
  let := hAC
  have hk : (a.prod b).ker = (A ⊓ C).comap r := by
    ext x
    change (a x,b x) = (1,1) ↔ r x ∈ A ∧ r x ∈ C
    rw [Prod.mk.injEq]
    exact and_congr (QuotientGroup.eq_one_iff _) (QuotientGroup.eq_one_iff _)
  apply source_a5_oddActorResidual_hom_eq_one_of_solvable_quotients D e hn hp B hB hBC hperm f q
    (MulAut.sylowOuterMap_surjective P) (MulAut.sylowOuterMap_ker_isSolvable P) a b
  · simpa only [← index_eq_card] using hA
  · simpa only [← index_eq_card] using hC
  · rw [hk]
    exact isSolvable_comap_of_solvable_ker r (A ⊓ C)

include D in
/-- The original fixed residual acts innerly on the unchanged normal component when its Sylow automorphisms have two suitable quotient actions. -/
theorem source_a5_oddNormalizer_inner_of_sylow_quotients
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G))) [K.Normal] [IsQuasisimple K]
    (P : Sylow 2 (K ⧸ center K))
    (A C : Subgroup (MulAut P)) [A.Normal] [C.Normal]
    (hAC : Group.IsSolvable (A ⊓ C : Subgroup (MulAut P)))
    (hA : ¬ 25 ∣ A.index) (hC : ¬ 25 ∣ C.index) :
    ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf (normalizer (B : Set G)) ≤
      K ⊔ centralizer (K : Set (normalizer (B : Set G))) := by
  let N := normalizer (B : Set G)
  let F := (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
    (localOrbit T L ⊓ centralizer (B : Set G)).subtype
  let I := F ⊔ ((T : Subgroup G) ⊓ N)
  have hFN : F ≤ N := ((map_subtype_le _).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hIN : I ≤ N := sup_le hFN inf_le_right
  let α : N →* MulAut.Outer K :=
    (QuotientGroup.mk' (MulAut.innerSubgroup K)).comp MulAut.conjNormal
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  have hz := source_a5_oddActorResidual_outer_hom_eq_one_of_sylow_quotients D e hn hp B hB hBC hperm P A C hAC hA hC
    ((j.comp α).comp (inclusion hIN))
  have hker : α.ker = K ⊔ centralizer (K : Set N) := by
    rw [show α = (QuotientGroup.mk' (MulAut.innerSubgroup K)).comp
      (MulAut.conjNormal : N →* MulAut K) from rfl,
      ← MonoidHom.comap_ker,QuotientGroup.ker_mk',MulAut.conjNormal_comap_innerSubgroup]
  intro x hx
  rw [← hker]
  change α x = 1
  apply MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K))
  exact (DFunLike.congr_fun hz (⟨x,hx⟩ : F)).trans j.map_one.symm
end CFSG.Quasithin.Chapter10
