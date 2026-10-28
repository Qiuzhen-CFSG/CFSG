module
public import Theory.GroupTheory.CentralCoverCenteredModules
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Lifting point cores and their normalizers through a central factor

Let B be normal in a finite group, and let an action have central kernel
on B. A prime subgroup W in the image of B, normalized by the image of
the original Sylow and point subgroup, lifts into their point-join core.
Take the core of B intersect the preimage of W: its image is W by central
covering, and Sylow maximality puts it inside the original Sylow.

When the full action kernel centralizes B, the lift also recovers the
normalizer of any subgroup with the same image. The preimage of a finite
subgroup in the B-action has order equal to its order times |Z(B)| when
the kernel is precisely C(B). These facts retain the original normalizer
in the cubic A₇-cover argument of Aschbacher–Smith 12.6.26, p.832.
-/

public section
open Subgroup
namespace Theory.GroupTheory
/-- A normal prime subgroup in the image of a normal central covering factor
lifts into the core of a point join containing an ambient Sylow subgroup. -/
theorem central_factor_point_core_lift
    {G J : Type*} [Group G] [Finite G] [Group J]
    {p : ℕ} [Fact p.Prime] (f : G →* J) (B A : Subgroup G) [B.Normal]
    (hc : B ⊓ f.ker ≤ centralizer (B : Set G)) (T : Sylow p G)
    (W : Subgroup J) (hW : IsPGroup p W) (hWB : W ≤ B.map f)
    (hAW : A.map f ≤ normalizer (W : Set J))
    (hTW : (T : Subgroup G).map f ≤ normalizer (W : Set J)) :
    ∃ X : Subgroup G, X ≤ B ∧ X ≤ (A ⊔ (T : Subgroup G)).pCoreIn p ∧
      X.map f = W ∧ (normalizer (W : Set J)).comap f ≤ normalizer (X : Set G) := by
  let P := B ⊓ W.comap f
  let r : P →* W := (f.comp P.subtype).codRestrict W (fun x => x.property.2)
  have hr : Function.Surjective r := by
    intro w
    obtain ⟨b,hb,hbw⟩ := hWB w.property
    exact ⟨⟨b,hb,by change f b ∈ W; rw [hbw]; exact w.property⟩,Subtype.ext hbw⟩
  have hrk : r.ker ≤ center P := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact hc ⟨x.property.1,congrArg Subtype.val hx⟩ y.val y.property.1
  have hm : (P.pCoreIn p).map f = W := by
    have he := r.map_pCore_of_central_kernel_centered hr hrk (p := p)
    have htop : pCore p W = ⊤ :=
      top_unique (le_sSup ⟨inferInstance,hW.to_subgroup ⊤⟩)
    rw [htop] at he
    have hh := congrArg (Subgroup.map W.subtype) he
    rw [map_map,←MonoidHom.range_eq_map,range_subtype] at hh
    change (pCore p P).map (f.comp P.subtype) = W at hh
    simpa only [pCoreIn,map_map] using hh
  have hnormalizes (U : Subgroup G) (hU : U.map f ≤ normalizer (W : Set J)) :
      U ≤ normalizer (P.pCoreIn p : Set G) := by
    apply le_trans ?_ (normalizer_le_normalizer_characteristic_image P (pCore p P))
    apply le_trans (le_inf (show U ≤ normalizer (B : Set G) from le_normalizer_of_normal) ?_)
      inf_normalizer_le_normalizer_inf
    exact (map_le_iff_le_comap.mp hU).trans (W.le_normalizer_comap f)
  have hT : P.pCoreIn p ≤ (T : Subgroup G) := by
    have he := T.is_maximal' (T.isPGroup'.to_sup_of_normal_right'
      (isPGroup_pCoreIn p P) (hnormalizes _ hTW)) le_sup_left
    exact le_sup_right.trans he.le
  refine ⟨P.pCoreIn p,(pCoreIn_le p P).trans inf_le_left,?_,hm,?_⟩
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn p P)
      (hT.trans le_sup_right) (sup_le (hnormalizes _ hAW) (hnormalizes _ hTW))
  · exact hnormalizes _ (map_comap_le _ _)
theorem central_factor_le_point_core_image
    {G J : Type*} [Group G] [Finite G] [Group J]
    {p : ℕ} [Fact p.Prime] (f : G →* J) (B A : Subgroup G) [B.Normal]
    (hc : B ⊓ f.ker ≤ centralizer (B : Set G)) (T : Sylow p G)
    (W : Subgroup J) (hW : IsPGroup p W) (hWB : W ≤ B.map f)
    (hAW : A.map f ≤ normalizer (W : Set J))
    (hTW : (T : Subgroup G).map f ≤ normalizer (W : Set J)) :
    W ≤ ((A ⊔ (T : Subgroup G)).pCoreIn p).map f := by
  obtain ⟨X,_,hX,hmap,_⟩ := central_factor_point_core_lift f B A hc T W hW hWB hAW hTW
  rw [←hmap]
  exact map_mono hX

end Theory.GroupTheory

namespace Theory.GroupTheory
/-- A lift inside a factor whose centralizer is the action kernel recovers
normalizers of any subgroup with that same image. -/
theorem normalizer_le_of_centralizer_kernel_lift
    {G J : Type*} [Group G] [Group J] (f : G →* J)
    (B R X : Subgroup G) (W : Subgroup J)
    (hc : f.ker ≤ centralizer (B : Set G))
    (hXR : X ≤ R) (hX : X.map f = W) (hR : R.map f = W)
    (hn : (normalizer (W : Set J)).comap f ≤ normalizer (X : Set G)) :
    B ⊓ (normalizer (W : Set J)).comap f ≤ normalizer (R : Set G) := by
  have he : R = X ⊔ (R ⊓ f.ker) := by
    apply le_antisymm
    · intro r hr
      have hm : f r ∈ X.map f := by rw [hX,←hR]; exact mem_map_of_mem f hr
      obtain ⟨x,hx,hxr⟩ := hm
      have hk : x⁻¹*r ∈ R ⊓ f.ker := by
        refine ⟨R.mul_mem (R.inv_mem (hXR hx)) hr,?_⟩
        change f (x⁻¹*r) = 1
        rw [map_mul,map_inv,hxr,inv_mul_cancel]
      have hh := (X ⊔ (R ⊓ f.ker)).mul_mem (mem_sup_left hx) (mem_sup_right hk)
      simpa only [mul_inv_cancel_left] using hh
    · exact sup_le hXR inf_le_left
  have hB : B ≤ centralizer (R ⊓ f.ker : Set G) :=
    (le_centralizer_iff.mp hc).trans (centralizer_le (show (R ⊓ f.ker : Set G) ⊆ f.ker from inf_le_right))
  rw [he]
  exact (le_inf (inf_le_right.trans hn)
    (inf_le_left.trans (hB.trans (Subgroup.centralizer_le_normalizer _)))).trans
      (normalizer_inf_normalizer_le_normalizer_sup X (R ⊓ f.ker))

/-- The preimage of a subgroup inside a component action retains exactly
the intrinsic component center as its kernel. -/
theorem centralizer_kernel_preimage_card
    {G J : Type*} [Group G] [Finite G] [Group J]
    (f : G →* J) (B : Subgroup G) (D : Subgroup J)
    (hk : f.ker = centralizer (B : Set G)) (hD : D ≤ B.map f) :
    Nat.card (B ⊓ D.comap f : Subgroup G) = Nat.card (center B) * Nat.card D := by
  let P := B ⊓ D.comap f
  let r : P →* D := (f.comp P.subtype).codRestrict D (fun x => x.property.2)
  have hr : Function.Surjective r := by
    intro d
    obtain ⟨b,hb,hbd⟩ := hD d.property
    refine ⟨⟨b,hb,?_⟩,Subtype.ext hbd⟩
    change f b ∈ D
    rw [hbd]
    exact d.property
  let k : r.ker →* center B := {
    toFun x := ⟨⟨x.val.val,x.val.property.1⟩,mem_center_iff.mpr (fun b => by
      apply Subtype.ext
      have hh : x.val.val ∈ f.ker := congrArg Subtype.val x.property
      exact (show x.val.val ∈ centralizer (B : Set G) from hk ▸ hh) b.val b.property)⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hki : Function.Injective k := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : center B => (z.val : G)) h))
  have hks : Function.Surjective k := by
    intro z
    have hzf : f z.val.val = 1 := by
      change z.val.val ∈ f.ker
      rw [hk]
      intro b hb
      exact congrArg Subtype.val (mem_center_iff.mp z.property ⟨b,hb⟩)
    let x : P := ⟨z.val.val,z.val.property,by change f z.val.val ∈ D; rw [hzf]; exact D.one_mem⟩
    refine ⟨⟨x,?_⟩,rfl⟩
    exact Subtype.ext hzf
  have hcard : Nat.card r.ker = Nat.card (center B) :=
    Nat.card_congr (Equiv.ofBijective k ⟨hki,hks⟩)
  have he := r.ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr hr,Nat.card_congr (topEquiv : (⊤ : Subgroup D) ≃* D).toEquiv,
    hcard] at he
  exact he.symm
end Theory.GroupTheory
