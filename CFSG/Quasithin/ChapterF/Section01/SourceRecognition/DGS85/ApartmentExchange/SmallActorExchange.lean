module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.PathFactorization
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathBraidExchange
public import Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCubic

/-!
# Exchange from the smaller actor in DGS (14.9)(c)

The actor is exactly the join of the two genuine half-path radicals. Its
own two-core is the kernel of the natural SL₂ quotient. The marked diagonal
elements are taken from the intersection of the original Cartan with this
actor. Thus absorbing the Cartan factor keeps the reflection and correction
inside the smaller actor; no normality in the whole endpoint is needed.

The natural module constructs opposite cubic pairs and kills their common
centralizer in this same two-core. This gives actual apartment exchange from
the path factorization and the marked smaller-actor profiles. Constructing
those profiles from the earlier source remains a separate obligation.

The field has characteristic two, with no lower bound on its order. In
particular the field-four case is included. This argument makes no assertion
that there are only two invariant complements; the distinct complement
argument of (14.17) must retain its exceptional third-complement alternative.

Source: DGS, Groups and Graphs (1985), (14.3)(b,d), printed p.212;
(14.9)(c), pp.215--216; (14.12)--(14.13), pp.217--218; (14.17), p.221.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.WeakBNPair.RegularTree
open Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCubic
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
universe uF
variable {X V : Type*} [Group X] [MulAction X V]
variable {Γ : SimpleGraph V} {a b : V}

/-- The smaller source actor, with both literal half-path radicals. -/
abbrev halfPathActor (p : Γ.Walk a b) (n : ℕ) : Subgroup X :=
  pathRoot (X := X) (p.drop n) ⊔ pathRoot (X := X) (p.take n)

/-- The exact natural quotient of the smaller actor. Cartan markings are
inside this actor, rather than in an arbitrary full-endpoint quotient. -/
structure SmallActorPathCoordinates (p : Γ.Walk a b) (n : ℕ) (K : Subgroup X) where
  F : Type uF
  [field : Field F]
  [charTwo : CharP F 2]
  quotient : halfPathActor (X := X) p n →* SL(2,F)
  onto : Function.Surjective quotient
  kernel_eq : quotient.ker = ((halfPathActor (X := X) p n).pCoreIn 2).subgroupOf
    (halfPathActor (X := X) p n)
  natural : NaturalKernel quotient
  upper_image : ∀ x : halfPathActor (X := X) p n,
    (x:X)∈pathRoot (X := X) (p.drop n) → ∃ a : F, quotient x=upper a
  lower_elements : ∀ y : halfPathActor (X := X) p n,
    (y:X)∈pathRoot (X := X) (p.take n) → ∃ a : F, quotient y=lower a
  lower_image : ∀ a : F, ∃ y : halfPathActor (X := X) p n,
    (y:X)∈pathRoot (X := X) (p.take n) ∧ quotient y=lower a
  diagonal_image : ∀ a : F, ∀ ha : a≠0,
    diag2 a ha∈(K.subgroupOf (halfPathActor (X := X) p n)).map quotient
  reflection : halfPathActor (X := X) p n
  reverses : ∀ k≤2*n, (reflection:X) • p.getVert k=p.getVert (2*n-k)

attribute [instance] SmallActorPathCoordinates.field SmallActorPathCoordinates.charTwo

namespace SmallActorPathCoordinates
variable {p : Γ.Walk a b} {n : ℕ} {K : Subgroup X}
variable (d : SmallActorPathCoordinates.{uF} p n K)

private theorem actor_normalizes_core : halfPathActor (X := X) p n ≤
    normalizer ((halfPathActor (X := X) p n).pCoreIn 2 : Set X) := by
  let R := halfPathActor (X := X) p n
  have hh := (pCore 2 R).le_normalizer_map R.subtype
  simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype, Subgroup.pCoreIn] using hh

include d in
private theorem opposite_disjoint (hlen : p.length=2*n)
    (hSQ : pathRoot (X := X) (p.take n) ⊓ (halfPathActor (X := X) p n).pCoreIn 2=⊥) :
    pathRoot (X := X) (p.drop n) ⊓ (halfPathActor (X := X) p n).pCoreIn 2=⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hr := (pathRoot_halves_reflection p n hlen (d.reflection:X) d.reverses).2
  have hm : (d.reflection:X)*x*(d.reflection:X)⁻¹∈
      pathRoot (X := X) (p.take n) ⊓ (halfPathActor (X := X) p n).pCoreIn 2 := by
    constructor
    · rw [← hr]
      exact ⟨x,hx.1,rfl⟩
    · exact (Subgroup.mem_normalizer_iff.mp
        (actor_normalizes_core d.reflection.property) x).mp hx.2
  rw [hSQ] at hm
  have he := congrArg (fun z : X => (d.reflection:X)⁻¹*z*d.reflection)
    (show (d.reflection:X)*x*(d.reflection:X)⁻¹=1 from hm)
  change x=1
  simpa only [mul_one, ← mul_assoc, inv_mul_cancel, one_mul, inv_mul_cancel_right] using he

include d in
/-- The natural smaller actor supplies the cubic pair, a corrected reversing
actor, and the precise common-centralizer bound in its own two-core. -/
theorem exists_pair (hlen : p.length=2*n)
    (hK : K ≤ pathFixer (X := X) p)
    (hSQ : pathRoot (X := X) (p.take n) ⊓ (halfPathActor (X := X) p n).pCoreIn 2=⊥)
    (x : X) (hx : x∈pathRoot (X := X) (p.drop n)) (hne : x≠1) :
    ∃ y∈pathRoot (X := X) (p.take n), ∃ t∈halfPathActor (X := X) p n,
      x*x=1 ∧ y*y=1 ∧ orderOf (x*y)=3 ∧
      (∀ k≤2*n, t • p.getVert k=p.getVert (2*n-k)) ∧
      (x*y*x)*t⁻¹∈(halfPathActor (X := X) p n).pCoreIn 2 ∧
      ∀ z∈(halfPathActor (X := X) p n).pCoreIn 2,
        Commute x z → Commute y z → z=1 := by
  let A := halfPathActor (X := X) p n
  let Q := A.pCoreIn 2
  let R := (pathRoot (X := X) (p.drop n)).subgroupOf A
  let S := (pathRoot (X := X) (p.take n)).subgroupOf A
  have hRQ := d.opposite_disjoint hlen hSQ
  have hr : R ⊓ d.quotient.ker=⊥ := by
    rw [d.kernel_eq]
    apply le_bot_iff.mp
    intro z hz
    apply Subtype.ext
    have hm : (z:X)∈pathRoot (X := X) (p.drop n) ⊓ Q := ⟨hz.1,hz.2⟩
    rwa [hRQ] at hm
  have hs : S ⊓ d.quotient.ker=⊥ := by
    rw [d.kernel_eq]
    apply le_bot_iff.mp
    intro z hz
    apply Subtype.ext
    have hm : (z:X)∈pathRoot (X := X) (p.take n) ⊓ Q := ⟨hz.1,hz.2⟩
    rwa [hSQ] at hm
  have hxA : x∈A := Subgroup.mem_sup_left hx
  obtain ⟨a,ha,hπx,y,hy,hπy,hxx,hyy,horder,hcentral⟩ :=
    pair_of_opposite_images d.quotient d.natural R S hr hs d.upper_image
      d.lower_image ⟨x,hxA⟩ hx (fun he => hne (congrArg Subtype.val he))
  have hhalves := pathRoot_halves_reflection p n hlen (d.reflection:X) d.reverses
  let xx : A := ⟨x,hxA⟩
  have hxS : ((d.reflection*xx*d.reflection⁻¹ : A):X)∈pathRoot (X := X) (p.take n) := by
    rw [← hhalves.2]
    exact ⟨x,hx,rfl⟩
  have hyR : ((d.reflection*y*d.reflection⁻¹ : A):X)∈pathRoot (X := X) (p.drop n) := by
    rw [← hhalves.1]
    exact ⟨y,hy,rfl⟩
  obtain ⟨b,hb⟩ := d.lower_elements (d.reflection*xx*d.reflection⁻¹) hxS
  obtain ⟨e,he⟩ := d.upper_image (d.reflection*y*d.reflection⁻¹) hyR
  have hxπ : d.quotient xx=upper a := hπx
  have hux : d.quotient d.reflection*upper a=lower b*d.quotient d.reflection := by
    calc
      _ = d.quotient (d.reflection*xx*d.reflection⁻¹)*d.quotient d.reflection := by
        simp only [map_mul,map_inv,hxπ,mul_assoc,inv_mul_cancel,mul_one]
      _ = _ := by rw [hb]
  have hly : d.quotient d.reflection*lower a⁻¹=upper e*d.quotient d.reflection := by
    calc
      _ = d.quotient (d.reflection*y*d.reflection⁻¹)*d.quotient d.reflection := by
        simp only [map_mul,map_inv,hπy,mul_assoc,inv_mul_cancel,mul_one]
      _ = _ := by rw [he]
  obtain ⟨c,hc,hπt⟩ := braid_of_intertwines (d.quotient d.reflection) a b a⁻¹ e
    ha (inv_ne_zero ha) hux hly
  have hcor := correction_mem d.quotient (K.subgroupOf A) a c ha hc
    ⟨x,hxA⟩ y d.reflection hπx hπy hπt d.diagonal_image
  have hnorm : K ⊓ A ≤ normalizer (Q : Set X) :=
    inf_le_right.trans actor_normalizes_core
  have hcorX : (x*(y:X)*x)*(d.reflection:X)⁻¹∈Q ⊔ (K ⊓ A) := by
    have hm := Subgroup.mem_map_of_mem A.subtype hcor
    rw [Subgroup.map_sup,d.kernel_eq,
      Subgroup.map_subgroupOf_eq_of_le (Subgroup.pCoreIn_le 2 A),
      Subgroup.subgroupOf_map_subtype] at hm
    exact hm
  change (x*(y:X)*x)*(d.reflection:X)⁻¹∈((Q ⊔ (K ⊓ A) : Subgroup X) : Set X) at hcorX
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Q (K ⊓ A) hnorm] at hcorX
  obtain ⟨q,hq,k,hk,hcorEq⟩ := hcorX
  have hQt : (x*(y:X)*x)*(k*(d.reflection:X))⁻¹∈Q := by
    have heq : (x*(y:X)*x)*(k*(d.reflection:X))⁻¹=q := by
      calc
        _ = ((x*(y:X)*x)*(d.reflection:X)⁻¹)*k⁻¹ := by group
        _ = (q*k)*k⁻¹ := by rw [←hcorEq]
        _ = q := mul_inv_cancel_right q k
    rwa [heq]
  refine ⟨y,hy,k*d.reflection,A.mul_mem hk.2 d.reflection.property,
    congrArg Subtype.val hxx,congrArg Subtype.val hyy,?_,?_,hQt,?_⟩
  · exact (orderOf_injective A.subtype Subtype.coe_injective (⟨x,hxA⟩*y)).trans horder
  · intro j hj
    rw [mul_smul,d.reverses j hj]
    exact hK hk.1 (2*n-j) (by omega)
  · intro z hz hxz hyz
    have hzA : z∈A := Subgroup.pCoreIn_le 2 A hz
    have hzker : (⟨z,hzA⟩ : A)∈d.quotient.ker := by rw [d.kernel_eq]; exact hz
    have hxzA : Commute (⟨x,hxA⟩ : A) ⟨z,hzA⟩ := by
      apply Subtype.ext
      exact hxz.eq
    have hyzA : Commute y (⟨z,hzA⟩ : A) := by
      apply Subtype.ext
      exact hyz.eq
    exact congrArg Subtype.val (hcentral ⟨z,hzA⟩ hzker hxzA hyzA)

include d in
/-- The literal exchange actor on one centered path, using only the smaller
actor's normal two-core. -/
theorem exchange (hlen : p.length=2*n)
    (hK : K ≤ pathFixer (X := X) p)
    (hfactor : (pathFixer (X := X) (p.drop n) : Set X)=
      (pathRoot (X := X) (p.drop n) : Set X)*(K : Set X))
    (hSQ : pathRoot (X := X) (p.take n) ⊓ (halfPathActor (X := X) p n).pCoreIn 2=⊥)
    (g : X) (hg : ∀ k, n≤k → k≤2*n → g • p.getVert k=p.getVert k)
    (hmove : g • a≠a) :
    ∃ z : X, (∀ k≤n, z • p.getVert k=p.getVert k) ∧ z • (g • a)=b := by
  have hgF : g∈(pathFixer (X := X) (p.drop n) : Set X) := by
    intro k hk
    rw [SimpleGraph.Walk.drop_length,hlen] at hk
    rw [SimpleGraph.Walk.drop_getVert]
    exact hg (n+k) (by omega) (by omega)
  rw [hfactor] at hgF
  obtain ⟨x,hx,k,hk,rfl⟩ := hgF
  have hka : k • a=a := by
    simpa only [SimpleGraph.Walk.getVert_zero] using hK hk 0 (Nat.zero_le _)
  have he : (x*k) • a=x • a := by rw [mul_smul,hka]
  have hxne : x≠1 := by intro hh; rw [he,hh,one_smul] at hmove; exact hmove rfl
  obtain ⟨y,hy,t,_ht,hxx,hyy,horder,ht,hcor,hcentral⟩ := d.exists_pair hlen hK hSQ x hx hxne
  have hxn := actor_normalizes_core (show x∈halfPathActor (X := X) p n from Subgroup.mem_sup_left hx)
  have hyn := actor_normalizes_core (show y∈halfPathActor (X := X) p n from Subgroup.mem_sup_right hy)
  rcases path_braid_exchange_or_centralizer p n hlen _ (d.opposite_disjoint hlen hSQ)
      hSQ hx hy hxn hyn hxx hyy
      (by rw [←horder]; exact pow_orderOf_eq_one _) ht hcor with hex | ⟨z,hz,hzne,hxz,hyz⟩
  · simpa only [he] using hex
  · exact (hzne (hcentral z hz hxz hyz)).elim

end SmallActorPathCoordinates

/-- Source application of (14.9)(c) to the actual half-path actors. The
geometric inputs are precisely Cartan factorization and root-core separation;
the natural coordinates construct every cubic pair and its centralizer bound. -/
theorem chosenApartmentExchange_of_small_actor_natural
    (T : Set V) (n : ℕ) (K : Subgroup X)
    (hK : ∀ k∈K, ∀ z∈T, k • z=z)
    (hfactor : ∀ {a b} (p : Γ.Walk a b), p.IsPath → p.length=2*n →
      (∀ z∈p.support, z∈T) →
      (pathFixer (X := X) (p.drop n) : Set X)=
        (pathRoot (X := X) (p.drop n) : Set X)*(K : Set X))
    (hseparate : ∀ {a b} (p : Γ.Walk a b), p.IsPath → p.length=2*n →
      (∀ z∈p.support, z∈T) →
      pathRoot (X := X) (p.take n) ⊓ (halfPathActor (X := X) p n).pCoreIn 2=⊥)
    (hcoordinates : ∀ {a b} (p : Γ.Walk a b), p.IsPath → p.length=2*n →
      (∀ z∈p.support, z∈T) → Nonempty (SmallActorPathCoordinates.{uF} p n K)) :
    ChosenApartmentExchange (X := X) Γ T n := by
  intro a b p hp hl hT g hg hmove
  have hfix : K ≤ pathFixer (X := X) p := by
    intro k hk j _
    exact hK k hk _ (hT _ (p.getVert_mem_support j))
  exact (Classical.choice (hcoordinates p hp hl hT)).exchange hl hfix
    (hfactor p hp hl hT) (hseparate p hp hl hT) g hg hmove

namespace ReducedCartan
open RankTwoAmalgam Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The existing geometric inputs for a genuine six-path apartment. These
are independent of the smaller-actor natural-module branch. -/
structure SixPathSmallActorGeometry (c : CompatibleCartans L (reducedSylow L S)) where
  reflection : Bool → (reducedAmalgam L S).Universal
  fixes : ∀ i, reflection i • base (Universal.cosetFamily (reducedAmalgam L S)) i =
    base (Universal.cosetFamily (reducedAmalgam L S)) i
  moves : ∀ i, reflection i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
    base (Universal.cosetFamily (reducedAmalgam L S)) (!i)
  squares : ∀ i, reflection i*reflection i=1
  normalizes : ∀ i, reflection i∈normalizer (cartan c : Set (reducedAmalgam L S).Universal)
  transitive : BasedPathTransitive (X := (reducedAmalgam L S).Universal)
    (sourceGraph (reducedAmalgam L S)) 7
  thick : ∀ i, ∃ z, (sourceGraph (reducedAmalgam L S)).Adj
    (base (Universal.cosetFamily (reducedAmalgam L S)) i) z ∧
    z ≠ base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ∧
    z ≠ reflection i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i)
  odd : ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
    p.IsPath → p.length=7 →
    Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p))

/-- Literal (14.17) application of the smaller natural actor on the original
universal tree. A failing exchange instance selects the source (14.9)(c)
profile. Core placement supplies root disjointness, the proved Cartan
factorization supplies the half-fixer, and the natural actor contradicts the
failure. No natural-kernel profile is required at an already-exchanging path. -/
theorem source_six_small_actor_exchange
    (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S))
    (d : SixPathSmallActorGeometry c)
    (hlocal : ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
      p.IsPath → p.length=12 →
      (∀ z∈p.support, z∈cartanApartment (reducedAmalgam L S) (reflectionGroup c d.reflection)) →
      ∀ g : (reducedAmalgam L S).Universal,
      (∀ k, 6≤k → k≤12 → g • p.getVert k=p.getVert k) → g • a≠a →
      (¬∃ z : (reducedAmalgam L S).Universal,
        (∀ k≤6, z • p.getVert k=p.getVert k) ∧ z • (g • a)=b) →
      (halfPathActor (X := (reducedAmalgam L S).Universal) p 6).pCoreIn 2 ≤
        (MulAction.stabilizer (reducedAmalgam L S).Universal (p.getVert 6)).pCoreIn 2 ∧
      Nonempty (SmallActorPathCoordinates.{uF} p 6 (cartan c))) :
    ChosenApartmentExchange (X := (reducedAmalgam L S).Universal)
      (sourceGraph (reducedAmalgam L S))
      (cartanApartment (reducedAmalgam L S) (reflectionGroup c d.reflection)) 6 := by
  intro a b p hp hl hT g hg hmove
  classical
  by_contra hfail
  obtain ⟨hcore,⟨coords⟩⟩ := hlocal p hp hl hT g hg hmove hfail
  have hfix : cartan c ≤ pathFixer (X := (reducedAmalgam L S).Universal) p := by
    intro k hk j _
    exact reflectionApartment_fixed c d.reflection d.normalizes k hk _
      (hT _ (p.getVert_mem_support j))
  have hfactor := apartment_path_factorization h c 6 (by decide) d.reflection d.fixes d.moves
      d.squares d.normalizes d.transitive d.thick (p.drop 6)
      (by rw [SimpleGraph.Walk.drop_length,hl]; decide)
      (by
        intro z hz
        rw [SimpleGraph.Walk.drop_support_eq_support_drop_min] at hz
        exact hT z (List.mem_of_mem_drop hz))
  have hseparate : pathRoot (X := (reducedAmalgam L S).Universal) (p.take 6) ⊓
      (halfPathActor (X := (reducedAmalgam L S).Universal) p 6).pCoreIn 2=⊥ := by
    apply le_bot_iff.mp
    apply (inf_le_inf_left _ hcore).trans
    exact (pathRoot_take_inf_vertexCore p hp 6 (by omega) d.odd
      (universal_vertex_core_fixes_neighbors h _ _ (p.adj_getVert_succ (by omega)))).le
  exact hfail (coords.exchange hl hfix hfactor hseparate g hg hmove)

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
