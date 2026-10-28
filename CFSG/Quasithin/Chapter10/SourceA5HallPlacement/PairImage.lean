module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.ResidualPair
public import CFSG.Quasithin.Chapter10.SourceNonnormalOddActorOrbit
public import Theory.GroupTheory.CComponent.SimplePairKernel
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.PrimeRankResidualCentralizer

/-!
# Every nontrivial image of the original fixed pair retains both factors

Let F be the perfect residual of the odd actor's fixed subgroup in the
original two-component orbit X, and let I = F N_T(B). For any homomorphism
from I, a nontrivial restriction to F has two-group kernel. Consequently
its three- and five-ranks are both two, and its order is divisible by25.

Adjoin O₂(X) to the restricted kernel. The cover X = F O₂(X) makes this
subgroup normal in X. The literal N_T(B) normalizes it and retains the
original component orbit. If it contains one component, it therefore
contains X; the image of F is then a perfect two-group and is trivial.
Otherwise the simple-pair kernel theorem makes it a two-group. This proof
does not assume that the original kernel contains O₂(F).

The normal-subgroup consumer applies the same result to the actual map
N_G(B) → Out(K): F acts innerly on K, or its outer image has order divisible
by25. It does not assert the model-specific exclusion of that second case.
Source: Aschbacher–Smith 4.4.6 and4.4.10, printed pp.620–621, specialized to
the original nonnormal A₅ setup of10.2.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G H : Type*} [Group G] [Finite G] [Group H]
  {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
/-- A nontrivial restriction to the fixed residual has a two-group kernel. -/
theorem source_a5_oddActorResidual_hom_kernel
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G)) :
    let F := ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype)
    let I := F ⊔ ((T : Subgroup G) ⊓ normalizer (B : Set G))
    ∀ f : I →* H, f.comp (inclusion (show F ≤ I from le_sup_left)) ≠ 1 →
      IsPGroup 2 (f.comp (inclusion (show F ≤ I from le_sup_left))).ker := by
  let X := localOrbit T L
  let F := ((solvableResidual (X ⊓ centralizer (B : Set G) : Subgroup G)).map
    (X ⊓ centralizer (B : Set G)).subtype)
  let S := (T : Subgroup G) ⊓ normalizer (B : Set G)
  let I := F ⊔ S
  change ∀ f : I →* H, f.comp (inclusion (show F ≤ I from le_sup_left)) ≠ 1 →
    IsPGroup 2 (f.comp (inclusion (show F ≤ I from le_sup_left))).ker
  intro f hf
  let g : F →* H := f.comp (inclusion (show F ≤ I from le_sup_left))
  change g ≠ 1 at hf
  change IsPGroup 2 g.ker
  have hFX : F ≤ X := (map_subtype_le _).trans inf_le_left
  have hSX : S ≤ normalizer (X : Set G) :=
    inf_le_left.trans (le_normalizer_componentOrbit L T)
  have hSF : S ≤ normalizer (F : Set G) :=
    ((le_inf hSX (inf_le_right.trans (normalizer_le_normalizer_centralizer B))).trans
      inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image
        (X ⊓ centralizer (B : Set G)) (solvableResidual (X ⊓ centralizer (B : Set G) : Subgroup G)))
  have hIF : I ≤ normalizer (F : Set G) := sup_le F.le_normalizer hSF
  let F' := F.subgroupOf I
  let : F'.Normal := normal_subgroupOf_of_le_normalizer hIF
  let U := (F' ⊓ f.ker).map I.subtype
  have hUF : U ≤ F := (map_mono (show F' ⊓ f.ker ≤ F' from inf_le_left)).trans_eq
    (map_subgroupOf_eq_of_le (show F ≤ I from le_sup_left))
  have hUX : U ≤ X := hUF.trans hFX
  have hIU : I ≤ normalizer (U : Set G) := by
    have hh := (F' ⊓ f.ker).le_normalizer_map I.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hUmem (x : F) : (x : G) ∈ U ↔ x ∈ g.ker := by
    constructor
    · rintro ⟨y,hy,he⟩
      have he' : inclusion (show F ≤ I from le_sup_left) x = y := Subtype.ext he.symm
      change f (inclusion (show F ≤ I from le_sup_left) x) = 1
      rw [he']
      exact hy.2
    · intro hx
      exact ⟨inclusion (show F ≤ I from le_sup_left) x,⟨x.property,hx⟩,rfl⟩
  let U' := U.subgroupOf X
  let Q := pCore 2 X
  let N := U' ⊔ Q
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n,he⟩ := hB.exists_card_eq
    rw [he]
    exact hp.pow
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect X := isPerfect_iSup_conjugates L T
  have hcover := perfect_centralizer_cover X B hBC hodd
  change (X : Set G) = (F : Set G) * (X.pCoreIn 2 : Set G) at hcover
  have hFgen : F.subgroupOf X ⊔ Q = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨a,ha,q,hq,he⟩ := hcover.subset x.property
    obtain ⟨q,hq,rfl⟩ := hq
    have hx : (⟨a,hFX ha⟩ : X) * q = x := Subtype.ext he
    rw [← hx]
    exact mul_mem (mem_sup_left ha) (mem_sup_right hq)
  have hFN : F.subgroupOf X ≤ normalizer (N : Set X) := by
    apply (le_inf ?_ le_normalizer_of_normal).trans
      (normalizer_inf_normalizer_le_normalizer_sup U' Q)
    rw [← subgroupOf_normalizer_eq hUX]
    exact subgroupOf_mono X ((show F ≤ I from le_sup_left).trans hIU)
  have hNnormal : N.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hFgen]
    exact sup_le hFN (le_sup_right.trans N.le_normalizer)
  let := hNnormal
  have hNmap : N.map X.subtype = U ⊔ X.pCoreIn 2 := by
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hUX]
    rfl
  have hSN : S ≤ normalizer (N.map X.subtype : Set G) := by
    rw [hNmap]
    exact (le_inf ((show S ≤ I from le_sup_right).trans hIU)
      (hSX.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))).trans
        (normalizer_inf_normalizer_le_normalizer_sup U (X.pCoreIn 2))
  have hNne : N ≠ ⊤ := by
    intro htop
    let Q' := Q.comap (inclusion hFX)
    have hQ : IsPGroup 2 Q' := pCore_isPGroup.comap_of_injective _ (inclusion_injective hFX)
    have hgr : g.range ≤ Q'.map g := by
      rintro _ ⟨x,rfl⟩
      have hxN : inclusion hFX x ∈ N := htop ▸ mem_top _
      obtain ⟨u,hu,q,hq,he⟩ := mem_sup_of_normal_right.mp hxN
      have huF : (u : G) ∈ F := hUF hu
      have hqF : (q : G) ∈ F := by
        have hv : (u : G) * (q : G) = (x : G) := congrArg (fun z : X => (z : G)) he
        exact (F.mul_mem_cancel_left huF).mp (hv.symm ▸ x.property)
      have hq' : (⟨q,hqF⟩ : F) ∈ Q' := hq
      refine mem_map.mpr ⟨⟨q,hqF⟩,hq',?_⟩
      have hu' : g (⟨u,huF⟩ : F) = 1 := (hUmem ⟨u,huF⟩).mp hu
      have he' : (⟨u,huF⟩ : F) * ⟨q,hqF⟩ = x := Subtype.ext (congrArg (fun z : X => (z : G)) he)
      rw [← he',map_mul,hu',one_mul]
    let : Finite g.range := Finite.of_surjective g.rangeRestrict g.rangeRestrict_surjective
    let : Group.IsNilpotent g.range := ((hQ.map g).to_le hgr).isNilpotent
    let : Group.IsPerfect F := Group.IsPerfect.map _
    let : Group.IsPerfect g.range := Group.IsPerfect.range g
    have hs : Subsingleton g.range := by
      by_contra! hh
      exact Group.IsPerfect.not_isSolvable g.range inferInstance
    apply hf
    ext x
    exact congrArg Subtype.val (hs.elim (g.rangeRestrict x) 1)
  have hLN : ¬ L.subgroupOf X ≤ N := by
    intro hh
    have hL : L ≤ N.map X.subtype := by
      have hm := map_mono (f := X.subtype) hh
      rwa [map_subgroupOf_eq_of_le (le_componentOrbit L T)] at hm
    have hXN : X ≤ N.map X.subtype := by
      change localOrbit T L ≤ N.map X.subtype
      rw [← source_oddPrimeActor_normalizer_orbit D hp B hB hBC hperm]
      exact iSup_conjugates_le_of_le_normalizer L S _ hL hSN
    apply hNne
    apply map_injective X.subtype_injective
    rw [← MonoidHom.range_eq_map,range_subtype]
    exact le_antisymm (map_subtype_le N) hXN
  have hSorbit : componentOrbit L S = X :=
    source_oddPrimeActor_normalizer_orbit D hp B hB hBC hperm
  have hnot : ¬ S ≤ normalizer (L : Set G) := by
    intro hs
    have he : X = L := hSorbit.symm.trans (le_antisymm
      (iSup_conjugates_le_of_le_normalizer L S L le_rfl hs) (le_componentOrbit L S))
    exact hn (he ▸ le_normalizer_componentOrbit L T)
  obtain ⟨t,htS,htn⟩ := Set.not_subset.mp hnot
  have ht : t ∈ (T : Subgroup G) := htS.1
  let A := L.subgroupOf X
  let L₂ := L.map (MulAut.conj t).toMonoidHom
  let C := L₂.subgroupOf X
  have hLX : L ≤ X := le_componentOrbit L T
  have hL₂X : L₂ ≤ X := by
    exact le_iSup (fun s : (T : Subgroup G) => L.map (MulAut.conj (s:G)).toMonoidHom) ⟨t,ht⟩
  have hpairs : L ⊔ L₂ = X :=
    (componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
      inf_le_right ht htn).symm
  have hgen : A ⊔ C = ⊤ := by
    rw [← subgroupOf_sup hLX hL₂X,hpairs,subgroupOf_self]
  have hA : A.IsCComponent := D.maximal.1.1.subgroupOf_of_le hLX (componentOrbit_le_sup L T)
  have hXt : X.map (MulAut.conj t).toMonoidHom = X :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_componentOrbit L T ht)
  let τ : MulAut X := ((MulAut.conj t).subgroupMap X).trans (MulEquiv.subgroupCongr hXt)
  have hAC : A.map τ.toMonoidHom = C := by
    apply map_injective X.subtype_injective
    rw [map_map,show X.subtype.comp τ.toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp X.subtype from rfl,←map_map,
      map_subgroupOf_eq_of_le hLX,map_subgroupOf_eq_of_le hL₂X]
  have hC : C.IsCComponent := hAC ▸ hA.map_equiv τ
  have hne : A ≠ C := by
    intro he
    apply htn
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hm := congrArg (map X.subtype) he
    change (L.subgroupOf X).map X.subtype = (L₂.subgroupOf X).map X.subtype at hm
    rw [map_subgroupOf_eq_of_le hLX,map_subgroupOf_eq_of_le hL₂X] at hm
    exact hm.symm
  let ae := (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hLX))).trans e
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (A ⧸ pCore 2 A) := ae.isSimpleGroup
  let ce : C ≃* A := (MulEquiv.subgroupCongr hAC.symm).trans (τ.subgroupMap A).symm
  let : IsSimpleGroup (C ⧸ pCore 2 C) :=
    (QuotientGroup.congr _ _ ce (pCore_map_iso 2 ce)).isSimpleGroup
  have hCN : ¬ C ≤ N := by
    intro hh
    have hCfull : L₂ ≤ N.map X.subtype := by
      have hm := map_mono (f := X.subtype) hh
      rwa [map_subgroupOf_eq_of_le hL₂X] at hm
    have hL : L ≤ N.map X.subtype := by
      intro l hl
      have hm := hCfull (mem_map_of_mem (MulAut.conj t).toMonoidHom hl)
      have hh := (mem_normalizer_iff.mp (hSN (S.inv_mem htS))
        (t * l * t⁻¹)).mp hm
      convert hh using 1
      group
    exact hLN (by
      intro l hl
      have hh := hL hl
      obtain ⟨x,hx,he⟩ := hh
      exact (Subtype.ext he : x = l) ▸ hx)
  let : (A ⊔ C).Normal := hgen ▸ inferInstance
  have hNtwo := isTwoGroup_of_normal_avoiding_simpleCore_pair A C ⊥ N hA hC hne
    IsPGroup.of_bot (by rw [hgen,sup_bot_eq]) hLN hCN
  let k : g.ker →* N := {
    toFun := fun x => ⟨inclusion hFX x.val,mem_sup_left ((hUmem x.val).mpr x.property)⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  exact hNtwo.of_injective k (fun x y he => Subtype.ext
    ((inclusion_injective hFX) (congrArg (fun z : N => (z : X)) he)))

include D in
/-- Every nontrivial image of the original fixed residual retains both odd ranks. -/
theorem source_a5_oddActorResidual_hom_primeRank [Finite H]
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G)) :
    let F := ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype)
    let I := F ⊔ ((T : Subgroup G) ⊓ normalizer (B : Set G))
    ∀ f : I →* H, f.comp (inclusion (show F ≤ I from le_sup_left)) ≠ 1 →
      ∀ q : ℕ, q = 3 ∨ q = 5 →
        primeRank q (f.comp (inclusion (show F ≤ I from le_sup_left))).range = 2 := by
  let F := ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype)
  let I := F ⊔ ((T : Subgroup G) ⊓ normalizer (B : Set G))
  change ∀ f : I →* H, f.comp (inclusion (show F ≤ I from le_sup_left)) ≠ 1 →
    ∀ q : ℕ, q = 3 ∨ q = 5 →
      primeRank q (f.comp (inclusion (show F ≤ I from le_sup_left))).range = 2
  intro f hf q hq
  have hqprime : q.Prime := by rcases hq with rfl | rfl <;> decide
  let : Fact q.Prime := ⟨hqprime⟩
  have hqo : Odd q := by rcases hq with rfl | rfl <;> decide
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n,he⟩ := hB.exists_card_eq
    rw [he]
    exact hp.pow
  let g := f.comp (inclusion (show F ≤ I from le_sup_left))
  have hk := source_a5_oddActorResidual_hom_kernel D e hn hp B hB hBC hperm f hf
  have hr := ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel hqo g hk ⊤
  rw [← MonoidHom.range_eq_map] at hr
  exact hr.trans ((primeRank_equiv q (topEquiv : (⊤ : Subgroup F) ≃* F)).trans
    (source_a5_oddActorResidual_primeRank D e hn B hBC hodd hq))

include D in
/-- The actual image is trivial or its order is divisible by twenty-five. -/
theorem source_a5_oddActorResidual_hom_trivial_or_twentyFive [Finite H]
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G)) :
    let F := ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype)
    let I := F ⊔ ((T : Subgroup G) ⊓ normalizer (B : Set G))
    ∀ f : I →* H, f.comp (inclusion (show F ≤ I from le_sup_left)) = 1 ∨
      25 ∣ Nat.card (f.comp (inclusion (show F ≤ I from le_sup_left))).range := by
  let F := ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype)
  let I := F ⊔ ((T : Subgroup G) ⊓ normalizer (B : Set G))
  change ∀ f : I →* H, f.comp (inclusion (show F ≤ I from le_sup_left)) = 1 ∨
    25 ∣ Nat.card (f.comp (inclusion (show F ≤ I from le_sup_left))).range
  intro f
  by_cases hf : f.comp (inclusion (show F ≤ I from le_sup_left)) = 1
  · exact Or.inl hf
  right
  have hr := source_a5_oddActorResidual_hom_primeRank D e hn hp B hB hBC hperm f hf 5 (Or.inr rfl)
  obtain ⟨E,_,he⟩ := exists_elementaryAbelian_card_primeRank
    (G := (f.comp (inclusion (show F ≤ I from le_sup_left))).range) (p := 5)
  have hd := E.card_subgroup_dvd_card
  rwa [he,hr] at hd


include D in
/-- Restricting any homomorphism from the literal odd-actor normalizer either
kills the original fixed residual or retains twenty-five in its image order. -/
theorem source_a5_oddNormalizer_hom_trivial_or_twentyFive [Finite H]
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (f : normalizer (B : Set G) →* H) :
    let F := ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf (normalizer (B : Set G))
    F ≤ f.ker ∨ 25 ∣ Nat.card (F.map f) := by
  let N := normalizer (B : Set G)
  let F := (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
    (localOrbit T L ⊓ centralizer (B : Set G)).subtype
  let I := F ⊔ ((T : Subgroup G) ⊓ N)
  have hFN : F ≤ N := ((map_subtype_le _).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hIN : I ≤ N := sup_le hFN inf_le_right
  let g : I →* H := f.comp (inclusion hIN)
  rcases source_a5_oddActorResidual_hom_trivial_or_twentyFive D e hn hp B hB hBC hperm g
    with hz | hd
  · left
    intro x hx
    exact DFunLike.congr_fun hz (⟨x,hx⟩ : F)
  · right
    have he : (g.comp (inclusion (show F ≤ I from le_sup_left))).range =
        (F.subgroupOf N).map f := by
      ext y
      constructor
      · rintro ⟨x,rfl⟩
        exact ⟨⟨x,hFN x.property⟩,x.property,rfl⟩
      · rintro ⟨x,hx,rfl⟩
        exact ⟨⟨x,hx⟩,rfl⟩
    rwa [he] at hd

include D in
/-- For an actual normal component of N_G(B), the original residual acts
innerly or its literal outer-action image has order divisible by twenty-five. -/
theorem source_a5_oddNormalizer_inner_or_twentyFive_outer
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G))) [K.Normal] :
    let F := ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf (normalizer (B : Set G))
    let α : normalizer (B : Set G) →* MulAut.Outer K :=
      (QuotientGroup.mk' (MulAut.innerSubgroup K)).comp MulAut.conjNormal
    F ≤ K ⊔ centralizer (K : Set (normalizer (B : Set G))) ∨ 25 ∣ Nat.card (F.map α) := by
  let α : normalizer (B : Set G) →* MulAut.Outer K :=
    (QuotientGroup.mk' (MulAut.innerSubgroup K)).comp MulAut.conjNormal
  have he : α.ker = K ⊔ centralizer (K : Set (normalizer (B : Set G))) := by
    rw [show α = (QuotientGroup.mk' (MulAut.innerSubgroup K)).comp
      (MulAut.conjNormal : normalizer (B : Set G) →* MulAut K) from rfl,
      ← MonoidHom.comap_ker,QuotientGroup.ker_mk',MulAut.conjNormal_comap_innerSubgroup]
  simpa only [he] using
    source_a5_oddNormalizer_hom_trivial_or_twentyFive D e hn hp B hB hBC hperm α

end CFSG.Quasithin.Chapter10
