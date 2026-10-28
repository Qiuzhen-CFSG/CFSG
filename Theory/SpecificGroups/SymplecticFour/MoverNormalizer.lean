module
public import Theory.SpecificGroups.SymplecticFour.PointSupplement
public import Theory.GroupTheory.SylowKernelCore
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.ParabolicWings
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.RootPairMarking

/-!
# The normalizing mover and the marked point-local Sylow

In the central-intersection branch, intersect the generated group with the
actual marked plane core. It has order at most q² and contains the whole
point-center root. The original mover normalizes this intersection. Its
nonzero first coordinate moves that full root to another full root, forcing
the intersection to equal their order-q² product. The quadratic equation
for roots in that product gives exactly two mover cosets over the intersection.

The relative normal two-subgroup argument identifies every marked Sylow T₀
with this entire intersection. All coordinates use the original finite
characteristic-two field; no scalar closure of arbitrary subgroups is assumed.

Source: MS93 (5.5), printed p.917, the normalizer/root-pair calculation.
The actual replacement application is CriticalReduction.ContainedNormalizer.
The subsequent full-kernel containment and generation alternatives require
further use of the original mover and source (5.1).
-/

public noncomputable section

open Subgroup Matrix
open scoped Pointwise
set_option linter.unusedSimpArgs false
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.MoverNormalizer
open CentralRootGeometry CentralRootGeometry.SmallMovers
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

omit [Finite F] in
private theorem conjugate_root_element (b u w v s a : F) :
    element b u w v * element 0 (s^2*a) (s*a) a * (element b u w v)⁻¹ =
      element 0 ((s+b)^2*a) ((s+b)*a) a := by
  rw [mul_inv_eq_iff_eq_mul,element_mul,element_mul,element_eq_iff]
  have hthree : (3:F)=1 := by
    calc (3:F) = 2+1 := by norm_num
         _ = 1 := by rw [CharTwo.two_eq_zero,zero_add]
  constructor
  · simp
  constructor
  · ring_nf
    simp [CharTwo.two_eq_zero,hthree]
  constructor
  · ring_nf
    simp [CharTwo.two_eq_zero]
  · ring

private theorem root_pair_product (s t : F) :
    ((finiteRoot s ⊔ finiteRoot t : Subgroup (unipotent (F := F))) : Set _) =
      (finiteRoot s : Set (unipotent (F := F))) * (finiteRoot t : Set (unipotent (F := F))) := by
  let := wing_elementary (F := F) true
  apply coe_mul_of_right_le_normalizer_left
  exact (rootFamily_le_wing (some t)).trans (((wing true).le_centralizer.trans
    (centralizer_le (rootFamily_le_wing (some s)))).trans (Subgroup.centralizer_le_normalizer _))

private theorem root_parameter_of_mem {s t x : F}
    (hx : element 0 (x^2) x 1 ∈ (finiteRoot s ⊔ finiteRoot t : Subgroup (unipotent (F := F)))) :
    x=s ∨ x=t := by
  change element 0 (x^2) x 1 ∈ ((finiteRoot s ⊔ finiteRoot t : Subgroup (unipotent (F := F))) : Set _) at hx
  rw [root_pair_product] at hx
  obtain ⟨a,ha,b,hb,he⟩ := hx
  obtain ⟨⟨ba,ua,wa,va⟩,rfl⟩ := element_surjective a
  obtain ⟨⟨bb,ub,wb,vb⟩,rfl⟩ := element_surjective b
  dsimp at ha hb he
  obtain ⟨rfl,rfl,rfl⟩ := (element_mem_finiteRoot _ _ _ _ _).mp ha
  obtain ⟨rfl,rfl,rfl⟩ := (element_mem_finiteRoot _ _ _ _ _).mp hb
  rw [element_mul,element_eq_iff] at he
  simp only [zero_mul,mul_zero,add_zero] at he
  have hp : (x-s)*(x-t)=0 := by
    linear_combination -he.2.1 + (s+t)*he.2.2.1 - s*t*he.2.2.2
  exact (mul_eq_zero.mp hp).imp sub_eq_zero.mp sub_eq_zero.mp

/-- A moved full root and normalization force the square-order group to be
exactly two full roots. Every normalizing first coordinate is one of two values. -/
theorem normalized_root_pair (E W : Subgroup (unipotent (F := F)))
    (hEW : E ≤ normalizer (W : Set (unipotent (F := F))))
    (hsize : Nat.card W ≤ Nat.card F^2) (s : F) (hs : finiteRoot s ≤ W)
    (hout : ¬ E ≤ wing true) :
    ∃ b : F, b≠0 ∧ W=finiteRoot s ⊔ finiteRoot (s+b) ∧
      ∀ c u w v : F, element c u w v ∈ E → c=0 ∨ c=b := by
  obtain ⟨x,hx,hxp⟩ := SetLike.not_le_iff_exists.mp hout
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
  have hb : b≠0 := by simpa only [element_mem_wing,↓reduceIte] using hxp
  have hroot (c u w v : F) (hc : element c u w v ∈ E) : finiteRoot (s+c) ≤ W := by
    rintro _ ⟨a,rfl⟩
    have hh := (mem_normalizer_iff.mp (hEW hc) (transvectionHom s a)).mp
      (hs ⟨a,rfl⟩)
    change element c u w v * element 0 (s^2*a.toAdd) (s*a.toAdd) a.toAdd *
      (element c u w v)⁻¹ ∈ W at hh
    rwa [conjugate_root_element] at hh
  have hle := sup_le hs (hroot b u w v hx)
  have he : (finiteRoot s ⊔ finiteRoot (s+b)) = W := by
    apply eq_of_le_of_card_ge hle
    rw [show Nat.card (finiteRoot s ⊔ finiteRoot (s+b) : Subgroup (unipotent (F := F))) = Nat.card F^2 from
      rootFamily_sup_card (s := some s) (t := some (s+b)) (by simpa using hb)]
    exact hsize
  refine ⟨b,hb,he.symm,?_⟩
  intro c u w v hc
  have hh := hroot c u w v hc ((element_mem_finiteRoot _ _ _ _ _).mpr
    ⟨rfl,by simp,by simp⟩ : element 0 ((s+c)^2) (s+c) 1 ∈ finiteRoot (s+c))
  rw [←he] at hh
  exact (root_parameter_of_mem hh).imp
    (fun h => add_left_cancel (h.trans (add_zero s).symm)) add_left_cancel


private def firstCoordinate : unipotent (F := F) →* Multiplicative F where
  toFun x := Multiplicative.ofAdd (x.val.val (.inl 0) (.inl 1))
  map_one' := rfl
  map_mul' x y := by
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
    obtain ⟨⟨c,z,t,a⟩,rfl⟩ := element_surjective y
    change Multiplicative.ofAdd ((element b u w v * element c z t a).val.val (.inl 0) (.inl 1)) = _
    rw [element_mul,element_matrix,element_matrix,element_matrix]
    rfl

private theorem firstCoordinate_element (b u w v : F) :
    firstCoordinate (element b u w v) = Multiplicative.ofAdd b := by
  change Multiplicative.ofAdd ((element b u w v).val.val (.inl 0) (.inl 1)) = _
  rw [element_matrix]
  rfl

private theorem firstCoordinate_ker : (firstCoordinate (F := F)).ker = wing true := by
  ext y
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective y
  rw [MonoidHom.mem_ker,firstCoordinate_element,element_mem_wing]
  rfl

private theorem plane_index_two (E : Subgroup (unipotent (F := F))) (b : F)
    (hcoords : ∀ c u w v : F, element c u w v ∈ E → c=0 ∨ c=b)
    (hout : ¬ E ≤ wing true) : (wing true).relIndex E = 2 := by
  classical
  have hbound : (wing true).relIndex E ≤ 2 := by
    rw [←firstCoordinate_ker,relIndex_ker]
    let code : E.map firstCoordinate → Bool := fun x => decide (x.val=1)
    have hi : Function.Injective code := by
      intro x y he
      obtain ⟨x₀,hx₀,hx⟩ := x.property
      obtain ⟨y₀,hy₀,hy⟩ := y.property
      obtain ⟨⟨c,u,w,v⟩,rfl⟩ := element_surjective x₀
      obtain ⟨⟨c',u',w',v'⟩,rfl⟩ := element_surjective y₀
      rw [firstCoordinate_element] at hx hy
      have hc := hcoords c u w v hx₀
      have hc' := hcoords c' u' w' v' hy₀
      apply Subtype.ext
      change decide (x.val=1)=decide (y.val=1) at he
      rw [←hx,←hy] at he ⊢
      change decide (c=0)=decide (c'=0) at he
      congr 1
      by_cases h0 : c=0 <;> by_cases h0' : c'=0 <;> simp_all
    simpa using Nat.card_le_card_of_injective code hi
  have h0 : (wing true).relIndex E ≠ 0 := index_ne_zero_of_finite (H := (wing true).subgroupOf E)
  have h1 : (wing true).relIndex E ≠ 1 := fun he => hout (relIndex_eq_one.mp he)
  omega

omit [Finite F] in
private theorem conjugate_point_root (g : planeLocal (F := F)) (a : F) :
    g.val * rootElement 0 a * g.val⁻¹ =
      (element 0 (g.val.val (.inl 0) (.inl 0)^2*a)
        (g.val.val (.inl 0) (.inl 0)*g.val.val (.inl 1) (.inl 0)*a)
        (g.val.val (.inl 1) (.inl 0)^2*a)).val := by
  let B : Plane.symmetricMatrices F := ⟨!![a,0;0,0],by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩
  have he : (Plane.shear B).val = rootElement 0 a := by
    apply Subtype.ext
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [B,Plane.shear,Plane.shearSp,rootElement,rootMatrix,Matrix.fromBlocks,Matrix.single]
  have hh := congrArg Subtype.val (Plane.conjugate_shear g B)
  change g.val * (Plane.shear B).val * g.val⁻¹ = _ at hh
  rw [he] at hh
  rw [hh]
  apply Subtype.ext
  rw [element_matrix]
  change fromBlocks 1 ((Plane.quotientMap g).val * !![a,0;0,0] *
      (Plane.quotientMap g).valᵀ) 0 1 = _
  have hb : (Plane.quotientMap g).val * !![a,0;0,0] * (Plane.quotientMap g).valᵀ =
      !![g.val.val (.inl 0) (.inl 0)^2*a,
         g.val.val (.inl 0) (.inl 0)*g.val.val (.inl 1) (.inl 0)*a;
         g.val.val (.inl 0) (.inl 0)*g.val.val (.inl 1) (.inl 0)*a,
         g.val.val (.inl 1) (.inl 0)^2*a] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_two,Plane.quotientMap_val,Matrix.toBlocks₁₁,pow_two,
        mul_assoc,mul_comm,mul_left_comm]
  rw [hb]
  simp only [mul_zero,zero_mul,add_zero,Matrix.one_fin_two]

/-- A different point of the same plane gives a finite full root in the
original Sylow coordinates, without changing the field. -/
theorem plane_conjugate_root_finite (g : Sp F) (hg : g∈planeLocal)
    (hgp : g∉pointParabolic) :
    ∃ s : F, (RootSubgroup.group 0).map (MulAut.conj g).toMonoidHom = rootImage (some s) := by
  let a := g.val (.inl 0) (.inl 0)
  let c := g.val (.inl 1) (.inl 0)
  have hc : c≠0 := by
    intro hc
    exact hgp ((mem_pointParabolic_iff g).mpr ⟨hc,fun i =>
      (mem_planeParabolic_iff g).mp (planeLocal_le hg) i 0⟩)
  refine ⟨a/c,?_⟩
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff _ _).mp hx
    change g * rootElement 0 t * g⁻¹ ∈ _
    rw [conjugate_point_root ⟨g,hg⟩]
    change unipotent.subtype (element 0 (a^2*t) (a*c*t) (c^2*t)) ∈
      (finiteRoot (a/c)).map unipotent.subtype
    apply mem_map_of_mem unipotent.subtype
    apply (element_mem_finiteRoot _ _ _ _ _).mpr
    refine ⟨rfl,?_,?_⟩ <;> dsimp [a,c] at * <;> field_simp
  · simp only [rootImage,card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective,
      card_map_of_injective unipotent.subtype_injective,RootSubgroup.card,card_rootFamily,le_refl]


omit [CharP F 2] [Finite F] in
private theorem map_conj_mul (A : Subgroup (Sp F)) (g k : Sp F) :
    A.map (MulAut.conj (g*k)).toMonoidHom =
      (A.map (MulAut.conj k).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply,mul_assoc]

/-- The intersection with the actual marked plane core is a full root pair.
The moving root is obtained from the actual normalizing mover, not from a
cardinality assertion about an arbitrary Sylow subgroup. -/
theorem marked_plane_intersection_root_pair {n : ℕ} (hcard : Nat.card F=2^n) (hn : 1<n)
    (J E : Subgroup (Sp F)) (hEU : E ≤ unipotent)
    (hout : ¬ E ≤ (wing true).map unipotent.subtype)
    (s w : Sp F) (hs : s∈planeLocal) (hsp : s∉pointParabolic) (hws : w*s∈pointLocal)
    (hEJ : E.map (MulAut.conj w).toMonoidHom ≤ J)
    (hcore : (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2 ≤ pointLocal)
    (hcentral : J.subgroupOf pointLocal ⊓ pointRadical = center (pointLocal (F := F))) :
    ∃ r b : F, b≠0 ∧
      (J ⊓ (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2).map
        (MulAut.conj w⁻¹).toMonoidHom = rootImage (some r) ⊔ rootImage (some (r+b)) ∧
      Nat.card (J ⊓ (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2 : Subgroup (Sp F)) =
        Nat.card F^2 ∧
      (J ⊓ (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2).relIndex
        (E.map (MulAut.conj w).toMonoidHom) = 2 ∧
      ∀ c u z v : F, (element c u z v).val ∈ E → c=0 ∨ c=b := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let C := (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2
  let W₀ := J ⊓ C
  let W₁ := W₀.map (MulAut.conj w⁻¹).toMonoidHom
  let W := W₁.subgroupOf unipotent
  have hC : C = ((wing true).map unipotent.subtype).map (MulAut.conj w).toMonoidHom := by
    dsimp only [C]
    rw [←map_pCoreIn_of_injective 2 _ _ (MulAut.conj w).injective,pCoreIn,
      planeParabolic_core_map_eq_radical hcard hn]
    exact congrArg (Subgroup.map (MulAut.conj w).toMonoidHom)
      SymplecticConjugatePair.planeRadical_eq_wing
  have hW₁ : W₁ ≤ (wing true).map unipotent.subtype := by
    have hh := map_mono (show W₀ ≤ C from inf_le_right) (f := (MulAut.conj w⁻¹).toMonoidHom)
    rw [hC,←map_conj_mul,inv_mul_cancel,show (MulAut.conj (1 : Sp F)).toMonoidHom = MonoidHom.id _ by ext x; simp,Subgroup.map_id] at hh
    exact hh
  have hWU := hW₁.trans (map_subtype_le _)
  have hWmap : W.map unipotent.subtype = W₁ := map_subgroupOf_eq_of_le hWU
  have hW₀L : W₀ ≤ pointLocal := inf_le_right.trans hcore
  have hW₂ : IsPGroup 2 W₀ := (isPGroup_pCoreIn 2 _).to_le inf_le_right
  have hsize : Nat.card W ≤ Nat.card F^2 := by
    have hh := PointSupplement.central_kernel_pgroup_card_bound hcard hn
      (J.subgroupOf pointLocal) (W₀.subgroupOf pointLocal)
      hcentral.le (comap_mono inf_le_left) hW₂.comap_subtype
    rw [←card_map_of_injective pointLocal.subtype_injective,
      map_subgroupOf_eq_of_le hW₀L] at hh
    rw [←card_map_of_injective unipotent.subtype_injective,hWmap,
      card_map_of_injective (MulAut.conj w⁻¹).injective]
    exact hh
  have hrootJ : RootSubgroup.group (F := F) 0 ≤ J := by
    rw [←PointRadicalAction.center_eq_root hcard hn,←hcentral]
    apply (map_mono inf_le_left).trans
    rw [subgroupOf_map_subtype]
    exact inf_le_left
  have hrootconj : (RootSubgroup.group (F := F) 0).map (MulAut.conj w⁻¹).toMonoidHom =
      (RootSubgroup.group (F := F) 0).map (MulAut.conj s).toMonoidHom := by
    have hz : w*s∈normalizer (RootSubgroup.group (F := F) 0 : Set (Sp F)) := by
      rw [RootNormalizerResidual.normalizer_zero_eq]
      exact pointLocal_le hws
    have hh : (RootSubgroup.group (F := F) 0).map (MulAut.conj (w*s)⁻¹).toMonoidHom =
        RootSubgroup.group 0 := mem_normalizer_iff_map_conj_eq.mp ((normalizer _).inv_mem hz)
    have he : w⁻¹=s*(w*s)⁻¹ := by group
    rw [he,map_conj_mul,hh]
  obtain ⟨r,hr⟩ := plane_conjugate_root_finite s hs hsp
  have hrootW : rootImage (some r) ≤ W₁ := by
    rw [←hr,←hrootconj]
    apply map_mono
    refine le_inf hrootJ ?_
    apply (map_le_map_iff_of_injective (f := (MulAut.conj w⁻¹).toMonoidHom)
      (MulAut.conj w⁻¹).injective).mp
    rw [hrootconj,hr,hC,←map_conj_mul,inv_mul_cancel,
      show (MulAut.conj (1 : Sp F)).toMonoidHom = MonoidHom.id _ by ext x; simp,Subgroup.map_id]
    exact map_mono (rootFamily_le_wing _)
  have hEW₀ : E.map (MulAut.conj w).toMonoidHom ≤ normalizer (W₀ : Set (Sp F)) := by
    apply (le_inf (hEJ.trans J.le_normalizer) ?_).trans inf_normalizer_le_normalizer_inf
    have hEP : E ≤ planeParabolic := hEU.trans (unipotent_le_borel.trans inf_le_right)
    exact ((map_mono hEP).trans (planeParabolic.map (MulAut.conj w).toMonoidHom).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hEW₁ : E ≤ normalizer (W₁ : Set (Sp F)) := by
    have hh := (map_mono hEW₀ (f := (MulAut.conj w⁻¹).toMonoidHom)).trans
      (le_normalizer_map (MulAut.conj w⁻¹).toMonoidHom)
    rw [←map_conj_mul,inv_mul_cancel,
      show (MulAut.conj (1 : Sp F)).toMonoidHom = MonoidHom.id _ by ext x; simp,Subgroup.map_id] at hh
    exact hh
  have hEW : E.subgroupOf unipotent ≤ normalizer (W : Set (unipotent (F := F))) :=
    (comap_mono hEW₁).trans (W₁.le_normalizer_comap unipotent.subtype)
  have hroot : finiteRoot r ≤ W := by
    intro x hx
    exact hrootW (mem_map_of_mem unipotent.subtype hx)
  have hout' : ¬ E.subgroupOf unipotent ≤ wing true := by
    intro hle
    apply hout
    rw [←map_subgroupOf_eq_of_le hEU]
    exact map_mono hle
  obtain ⟨b,hb,he,hcoords⟩ := normalized_root_pair (E.subgroupOf unipotent) W hEW hsize r hroot hout'
  refine ⟨r,b,hb,?_,?_,?_,hcoords⟩
  · change W₁ = _
    rw [←hWmap,he,Subgroup.map_sup]
    rfl
  · have hc : Nat.card W = Nat.card F^2 := by
      rw [he]
      exact rootFamily_sup_card (s := some r) (t := some (r+b)) (by simpa using hb)
    rw [←card_map_of_injective unipotent.subtype_injective,hWmap,
      card_map_of_injective (MulAut.conj w⁻¹).injective] at hc
    exact hc
  · have hi := plane_index_two (E.subgroupOf unipotent) b hcoords hout'
    have hh := relIndex_map_map_of_injective (wing (F := F) true)
      (E.subgroupOf unipotent) unipotent.subtype_injective
    rw [map_subgroupOf_eq_of_le hEU] at hh
    have hi' : ((wing true).map unipotent.subtype).relIndex E = 2 := hh ▸ hi
    have hiw := relIndex_map_map_of_injective ((wing (F := F) true).map unipotent.subtype)
      E (f := (MulAut.conj w).toMonoidHom) (MulAut.conj w).injective
    rw [←hiw,←hC] at hi'
    rw [inf_comm,←relIndex_inf_mul_relIndex,inf_eq_right.mpr hEJ,
      relIndex_eq_one.mpr hEJ,mul_one]
    exact hi'



omit [CharP F 2] in
/-- The source marked Sylow is the entire normalized plane-core intersection.
This identifies the actual T₀, so the root pair above belongs to that Sylow. -/
theorem marked_sylow_eq_plane_intersection (J : Subgroup (Sp F)) (w : Sp F)
    (hcore : (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2 ≤ pointLocal)
    (hsize : Nat.card (J ⊓ (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2 :
      Subgroup (Sp F)) = Nat.card F^2)
    (T : Sylow 2 (J ⊓ planeParabolic.map (MulAut.conj w).toMonoidHom ⊓ pointParabolic : Subgroup (Sp F)))
    (hT : Nat.card T = Nat.card F^2) :
    (T : Subgroup (J ⊓ planeParabolic.map (MulAut.conj w).toMonoidHom ⊓ pointParabolic : Subgroup (Sp F))).map
      (J ⊓ planeParabolic.map (MulAut.conj w).toMonoidHom ⊓ pointParabolic).subtype =
        J ⊓ (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2 := by
  let P := planeParabolic.map (MulAut.conj w).toMonoidHom
  let I := J ⊓ P ⊓ pointParabolic
  let N := J ⊓ P.pCoreIn 2
  have hNI : N ≤ I := le_inf (le_inf inf_le_left (inf_le_right.trans (pCoreIn_le 2 P)))
    (inf_le_right.trans (hcore.trans pointLocal_le))
  have hnormal : I ≤ normalizer (N : Set (Sp F)) :=
    (le_inf ((inf_le_left.trans inf_le_left).trans J.le_normalizer)
      (((inf_le_left.trans inf_le_right).trans P.le_normalizer).trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))).trans
      inf_normalizer_le_normalizer_inf
  let : (N.subgroupOf I).Normal := (normal_subgroupOf_iff_le_normalizer hNI).mpr hnormal
  have hp : IsPGroup 2 N := (isPGroup_pCoreIn 2 P).to_le inf_le_right
  let T' : Sylow 2 I := T
  have hpI : IsPGroup 2 (N.subgroupOf I) := hp.comap_subtype
  have hNT : N.subgroupOf I ≤ (T' : Subgroup I) := hpI.le_sylow_of_normal T'
  have hle := map_mono hNT (f := I.subtype)
  rw [map_subgroupOf_eq_of_le hNI] at hle
  symm
  apply eq_of_le_of_card_ge hle
  rw [card_map_of_injective I.subtype_injective,hT,hsize]

end Theory.SpecificGroups.SymplecticFour.MoverNormalizer
