module
public import Theory.GroupAction.SymplecticRankThree.SpatialProjections

/-!
# Field coordinates on the entire affine three-space

The two transverse projections constructed in SpatialProjections share one
height parameter. Together with the original base projection, their planar line
equations force all three two-by-two minors to vanish, hence put every actual
spatial affine line in a vector line. Counting its q affine points proves the
reverse implication. This also handles collapsed projections and q=2.

The output is one compatible chart on all affine points, with every line
preserved in both directions. ProjectiveCompletion and ProjectiveCoordinates complete this chart at infinity
and supply the projective coordinates to the symplectic recognition consumer.

Source: Higman (1964), Lemma 10 and Theorem 2(i), pp.153–155,
expanded projective coordinatization.
-/

public noncomputable section
namespace Theory.GroupAction.SymplecticRankThree

/-- Three planar shadows detect an affine vector line in three dimensions.
The third shadow removes the degeneracy of the other two. -/
theorem affine_line_of_three_projections {K : Type*} [Field K]
    (a b x : (K × K) × K)
    (h₀ : ∃ r : K, x.1 = a.1 + r • (b.1-a.1))
    (h₁ : ∃ r : K, (x.1.1+x.2,x.1.2) =
      (a.1.1+a.2,a.1.2) + r • ((b.1.1+b.2,b.1.2)-(a.1.1+a.2,a.1.2)))
    (h₂ : ∃ r : K, (x.1.1,x.1.2+x.2) =
      (a.1.1,a.1.2+a.2) + r • ((b.1.1,b.1.2+b.2)-(a.1.1,a.1.2+a.2))) :
    ∃ r : K, x = a+r•(b-a) := by
  have minor (u v w : K × K) (h : ∃ r : K, w = u+r•(v-u)) :
      (w.1-u.1)*(v.2-u.2) = (v.1-u.1)*(w.2-u.2) := by
    obtain ⟨r,rfl⟩ := h
    change (u.1+r*(v.1-u.1)-u.1)*(v.2-u.2) =
      (v.1-u.1)*(u.2+r*(v.2-u.2)-u.2)
    ring
  have hxy := minor _ _ _ h₀
  have hx := minor _ _ _ h₁
  have hy := minor _ _ _ h₂
  have hxz : (x.1.1-a.1.1)*(b.2-a.2) = (b.1.1-a.1.1)*(x.2-a.2) := by
    linear_combination hy-hxy
  have hyz : (x.1.2-a.1.2)*(b.2-a.2) = (b.1.2-a.1.2)*(x.2-a.2) := by
    linear_combination hxy-hx
  by_cases hax : b.1.1 = a.1.1
  · by_cases hay : b.1.2 = a.1.2
    · obtain ⟨r,hr⟩ := h₁
      obtain ⟨s,hs⟩ := h₀
      have hb : b.1 = a.1 := Prod.ext hax hay
      rw [hb,sub_self,smul_zero,add_zero] at hs
      refine ⟨r,Prod.ext ?_ ?_⟩
      · change x.1 = a.1 + r • (b.1-a.1)
        rw [hb,sub_self,smul_zero,add_zero]
        exact hs
      · have hh := congrArg Prod.fst hr
        change x.1.1+x.2 = a.1.1+a.2+r*(b.1.1+b.2-(a.1.1+a.2)) at hh
        have hh' := congrArg Prod.fst hs
        change x.2 = a.2+r*(b.2-a.2)
        rw [hax,hh'] at hh
        linear_combination hh
    · have hby : b.1.2-a.1.2 ≠ 0 := sub_ne_zero.mpr hay
      let r := (x.1.2-a.1.2)/(b.1.2-a.1.2)
      have hry : r*(b.1.2-a.1.2) = x.1.2-a.1.2 := div_mul_cancel₀ _ hby
      have hrx : r*(b.1.1-a.1.1) = x.1.1-a.1.1 := by
        apply mul_right_cancel₀ hby
        linear_combination (b.1.1-a.1.1)*hry-hxy
      have hrz : r*(b.2-a.2) = x.2-a.2 := by
        apply mul_right_cancel₀ hby
        linear_combination (b.2-a.2)*hry+hyz
      refine ⟨r,Prod.ext (Prod.ext ?_ ?_) ?_⟩
      · change x.1.1 = a.1.1+r*(b.1.1-a.1.1)
        linear_combination -hrx
      · change x.1.2 = a.1.2+r*(b.1.2-a.1.2)
        linear_combination -hry
      · change x.2 = a.2+r*(b.2-a.2)
        linear_combination -hrz
  · have hbx : b.1.1-a.1.1 ≠ 0 := sub_ne_zero.mpr hax
    let r := (x.1.1-a.1.1)/(b.1.1-a.1.1)
    have hrx : r*(b.1.1-a.1.1) = x.1.1-a.1.1 := div_mul_cancel₀ _ hbx
    have hry : r*(b.1.2-a.1.2) = x.1.2-a.1.2 := by
      apply mul_right_cancel₀ hbx
      linear_combination (b.1.2-a.1.2)*hrx+hxy
    have hrz : r*(b.2-a.2) = x.2-a.2 := by
      apply mul_right_cancel₀ hbx
      linear_combination (b.2-a.2)*hrx+hxz
    refine ⟨r,Prod.ext (Prod.ext ?_ ?_) ?_⟩
    · change x.1.1 = a.1.1+r*(b.1.1-a.1.1)
      linear_combination -hrx
    · change x.1.2 = a.1.2+r*(b.1.2-a.1.2)
      linear_combination -hry
    · change x.2 = a.2+r*(b.2-a.2)
      linear_combination -hrz

end Theory.GroupAction.SymplecticRankThree
namespace Theory.GroupAction.SymplecticRankThree.AffineFrame
variable {Ω : Type*} [Finite Ω] {q : ℕ} {D : PolarityDesign Ω q}
variable (f : AffineFrame D)
variable (hl : ∀ a b, a ≠ b → (D.line a b).ncard = q+1) (hq : 2 ≤ q)
local instance : AddCommGroup (f.Base hl hq) := f.affineAddCommGroup hl hq
local instance : Field (f.scalarRing hl hq) := f.scalarField hl hq
local instance : Module (f.scalarRing hl hq) (f.Base hl hq) := f.scalarModule hl hq

include hl hq in
/-- Deleting the unique infinite point leaves exactly q points on each
nondegenerate spatial affine line. -/
theorem affineLine_card (a b : f.Affine) (hab : a ≠ b) :
    Nat.card {x : f.Affine // (x : Ω) ∈ D.line a b} = q := by
  have hab' : (a : Ω) ≠ b := fun he => hab (Subtype.ext he)
  obtain ⟨e,⟨hel,heI⟩,_⟩ := D.existsUnique_line_block hl hq a.property hab'
  let E : {x : f.Affine // (x : Ω) ∈ D.line a b} ≃ ↥(D.line a b \ {e}) :=
    { toFun := fun x => ⟨x,x.property,fun hx => x.val.property
        ((show (x : Ω) = e from hx).symm ▸ heI)⟩
      invFun := fun x => ⟨⟨x,fun hx => x.property.2
        (D.line_block_unique hab' a.property x.property.1 hel hx heI)⟩,x.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr E]
  change (D.line a b \ {e}).ncard = q
  rw [Set.ncard_sdiff_singleton_of_mem hel,hl a b hab']
  omega

include hl hq in
/-- A bijective affine chart which sends lines into vector lines reflects
all lines as well: both lines have exactly q affine points. -/
theorem affine_coordinates_reflect_lines
    {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    (hK : Nat.card K = q) (C : f.Affine ≃ V)
    (hC : ∀ a b x : f.Affine, (x : Ω) ∈ D.line a b →
      ∃ r : K, C x = C a+r•(C b-C a)) :
    ∀ a b x : f.Affine, (x : Ω) ∈ D.line a b ↔
      ∃ r : K, C x = C a+r•(C b-C a) := by
  intro a b x
  refine ⟨hC a b x,?_⟩
  rintro ⟨r,hr⟩
  by_cases hab : a = b
  · subst b
    rw [sub_self,smul_zero,add_zero] at hr
    have hx := C.injective hr
    subst x
    exact D.left_mem_line _ _
  let L := {y : f.Affine // (y : Ω) ∈ D.line a b}
  let t : L → K := fun y => (hC a b y.val y.property).choose
  have ht (y : L) : C y.val = C a+t y • (C b-C a) := (hC a b y.val y.property).choose_spec
  have hinj : Function.Injective t := by
    intro y z he
    apply Subtype.ext
    apply C.injective
    rw [ht y,ht z,he]
  let : Fintype L := Fintype.ofFinite _
  let : Fintype K := Fintype.ofFinite _
  have hbij : Function.Bijective t := (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hinj,by rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hK]
             exact f.affineLine_card hl hq a b hab⟩
  obtain ⟨y,hy⟩ := hbij.2 r
  have he : x = y.val := C.injective (hr.trans (by rw [ht y,hy]))
  exact he.symm ▸ y.property

/-- One compatible field chart on the entire affine three-space. Every
spatial line has its usual affine vector equation, also when q=2. -/
theorem exists_field_space_coordinates :
    ∃ C : f.Affine ≃ ((f.scalarRing hl hq × f.scalarRing hl hq) × f.scalarRing hl hq),
      ∀ a b x : f.Affine, (x : Ω) ∈ D.line a b ↔
        ∃ r : f.scalarRing hl hq, C x = C a+r•(C b-C a) := by
  obtain ⟨c,d,t,hc,hd⟩ := f.exists_compatible_axis_parameters hl hq
  let L := f.fieldPlaneCoordinates hl hq
  let C := (f.planeAxisEquiv hl hq).trans (L.toEquiv.prodCongr t)
  have h₀ (x : f.Affine) : L (f.parallelFoot hl hq (f.transverseK hl hq) x) = (C x).1 := rfl
  have h₁ (x : f.Affine) : L (f.parallelFoot hl hq c x) = ((C x).1.1+(C x).2,(C x).1.2) := by
    rw [f.parallelFoot_decomposition,hc,map_add,map_smul,f.fieldPlaneCoordinates_unitI]
    apply Prod.ext
    · change (L (f.foot hl hq x)).1 + t (f.height hl hq x)*1 = _
      rw [mul_one]
      rfl
    · change (L (f.foot hl hq x)).2 + t (f.height hl hq x)*0 = (L (f.foot hl hq x)).2
      rw [mul_zero,add_zero]
  have h₂ (x : f.Affine) : L (f.parallelFoot hl hq d x) = ((C x).1.1,(C x).1.2+(C x).2) := by
    rw [f.parallelFoot_decomposition,hd,map_add,map_smul,f.fieldPlaneCoordinates_unitJ]
    apply Prod.ext
    · change (L (f.foot hl hq x)).1 + t (f.height hl hq x)*0 = (L (f.foot hl hq x)).1
      rw [mul_zero,add_zero]
    · change (L (f.foot hl hq x)).2 + t (f.height hl hq x)*1 = _
      rw [mul_one]
      rfl
  refine ⟨C,f.affine_coordinates_reflect_lines hl hq (f.scalarField_card hl hq) C ?_⟩
  intro a b x hx
  have hh (e : f.Transverse hl hq) : ∃ r : f.scalarRing hl hq,
      L (f.parallelFoot hl hq e x) = L (f.parallelFoot hl hq e a) +
        r • (L (f.parallelFoot hl hq e b)-L (f.parallelFoot hl hq e a)) :=
    (f.fieldPlaneCoordinates_line hl hq _ _ _).mp (f.parallelFoot_collinear hl hq e a b x hx)
  apply affine_line_of_three_projections (C a) (C b) (C x)
  · simpa only [h₀] using hh (f.transverseK hl hq)
  · simpa only [h₁] using hh c
  · simpa only [h₂] using hh d

end Theory.GroupAction.SymplecticRankThree.AffineFrame
