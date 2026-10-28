module
public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedCellCount
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityOuterTorus

/-!
# Triality torus normalizers and local Weyl actions

For q>2, write a torus normalizer in its unique actual Bruhat normal form.
Comparing d*x with x*d' forces its two positive factors to centralize the
whole descended torus. The proved nonbinary root weights make both factors
trivial. Thus the normalizer is the torus times the twelve genuine relative
Weyl representatives. The two-cell decomposition of either parabolic leaves
just the identity and its simple reflection.

A torus-preserving automorphism of either parabolic must therefore preserve
the nonidentity Weyl coset. The companion source module applies this to
conjugation by the original Sylow actor through both compatible local maps;
these constraints are used to construct its root action in F.4.37--38.

Source: GLS3 2.3.4--8 and §2.4 (`refs/KGroup/GLS3/chapter2.tex`);
Aschbacher--Smith F.4.29, pp.289--290 (`refs/quasithin.pdf`). The internal
import reuses the checked torus-weight calculation in this source family.
-/

public noncomputable section
open Subgroup Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.ConcreteBruhat Triality.Standard.PositiveCoordinates
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityWeylAction
open SplitNormalForm

private theorem torus_ordered (P : Parameters) (D : Inputs P) (h : splitTorus P)
    (v : PositiveCoordinates.Coordinates P) :
    h.val * orderedProduct P v * h.val⁻¹ =
      orderedProduct P (fun i => (D.rootCharacter (rootIndex i) h).val * v i) := by
  have hc (x y : SplitGroup P) : h.val*(x*y)*h.val⁻¹ =
      (h.val*x*h.val⁻¹)*(h.val*y*h.val⁻¹) := by group
  simp only [orderedProduct, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  simp only [hc, ←rootCurve_positive, D.torus_conjugate_root]

private def leftTorus (P : Parameters) (D : Inputs P) (c : SplitNormalForm.Coordinates P)
    (h : splitTorus P) : SplitNormalForm.Coordinates P where
  left := ⟨h.val*c.left.val*h.val⁻¹,
    (mem_normalizer_iff.mp (D.torus_normalizes_positive h.property) _).mp c.left.property⟩
  torus := h*c.torus
  weyl := c.weyl
  right := c.right
  supported := c.supported

private def rightTorus (P : Parameters) (D : Inputs P) (c : SplitNormalForm.Coordinates P)
    (h : splitTorus P) : SplitNormalForm.Coordinates P where
  left := c.left
  torus := c.torus * ⟨D.lift c.weyl*h.val*(D.lift c.weyl)⁻¹,
    (mem_normalizer_iff.mp (D.weyl_normalizes_torus (D.weylEquiv.symm c.weyl).property) _).mp h.property⟩
  weyl := c.weyl
  right := fun i => (D.rootCharacter (rootIndex i) h⁻¹).val*c.right i
  supported := fun i hi => (congrArg ((D.rootCharacter (rootIndex i) h⁻¹).val * ·)
    (c.supported i hi)).trans (mul_zero _)

private theorem evaluate_left (P : Parameters) (D : Inputs P)
    (c : SplitNormalForm.Coordinates P) (h : splitTorus P) :
    evaluate D (leftTorus P D c h)=h.val*evaluate D c := by
  dsimp [evaluate,leftTorus]
  group

private theorem evaluate_right (P : Parameters) (D : Inputs P)
    (c : SplitNormalForm.Coordinates P) (h : splitTorus P) :
    evaluate D (rightTorus P D c h)=evaluate D c*h.val := by
  change c.left.val * (c.torus.val * (D.lift c.weyl * h.val * (D.lift c.weyl)⁻¹)) *
    D.lift c.weyl * orderedProduct P (fun i => (D.rootCharacter (rootIndex i) h⁻¹).val*c.right i) = _
  have he := torus_ordered P D h⁻¹ c.right
  calc
    _ = c.left.val * (c.torus.val * (D.lift c.weyl * h.val * (D.lift c.weyl)⁻¹)) *
        D.lift c.weyl * (h.val⁻¹ * orderedProduct P c.right * h.val) :=
      congrArg (c.left.val * (c.torus.val * (D.lift c.weyl * h.val * (D.lift c.weyl)⁻¹)) *
        D.lift c.weyl * ·) he.symm
    _ = evaluate D c * h.val := by dsimp [evaluate]; group

private theorem torus_intertwining (n : ℕ) (hn : 0<n)
    (D : Inputs (binaryParameters n hn))
    (c : SplitNormalForm.Coordinates (binaryParameters n hn))
    (h k : splitTorus (binaryParameters n hn))
    (he : h.val*evaluate D c=evaluate D c*k.val) :
    h.val*c.left.val*h.val⁻¹=c.left.val ∧
      k.val⁻¹*orderedProduct _ c.right*k.val=orderedProduct _ c.right := by
  have hh := evaluate_injective n hn D
    ((evaluate_left _ D c h).trans (he.trans (evaluate_right _ D c k).symm))
  refine ⟨congrArg (fun z => z.left.val) hh,?_⟩
  have hr := congrArg SplitNormalForm.Coordinates.right hh
  change c.right = (fun i => (D.rootCharacter (rootIndex i) k⁻¹).val*c.right i) at hr
  simpa only [Subgroup.coe_inv,inv_inv] using (torus_ordered _ D k⁻¹ c.right).trans
    (congrArg (orderedProduct _) hr.symm)

private theorem u_factor_centralizes (n : ℕ) (hn : 0<n)
    (x : Carrier (binaryParameters n hn))
    (hx : x∈normalizer (torus (binaryParameters n hn) : Set _))
    (c : SplitNormalForm.Coordinates (binaryParameters n hn))
    (hc : FixedDescent.carrierToSplit _ rfl x=evaluate (InputRealization.inputs _ rfl) c)
    (u : Carrier (binaryParameters n hn))
    (hu : FixedDescent.carrierToSplit _ rfl u=c.left.val) :
    u∈centralizer (torus (binaryParameters n hn) : Set _) := by
  let P := binaryParameters n hn
  let D := InputRealization.inputs P rfl
  let j := FixedDescent.carrierToSplit P rfl
  apply mem_centralizer_iff.mpr
  intro t ht
  have hkt : x⁻¹*t*x ∈ torus P := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp ((normalizer (torus P : Set (Carrier P))).inv_mem hx) t).mp ht
  let h : splitTorus P := ⟨j t,(FixedDescent.mem_descend_iff P rfl _ t).mp ht⟩
  let k : splitTorus P := ⟨j (x⁻¹*t*x),(FixedDescent.mem_descend_iff P rfl _ _).mp hkt⟩
  have hg : t*x=x*(x⁻¹*t*x) := by group
  have he : h.val*evaluate D c=evaluate D c*k.val :=
    (congrArg (j t * ·) hc.symm).trans
      (((map_mul j t x).symm.trans (congrArg j hg)).trans
        ((map_mul j x (x⁻¹*t*x)).trans (congrArg (· * j (x⁻¹*t*x)) hc)))
  have hh := (torus_intertwining n hn D c h k he).1
  have he' : t*u*t⁻¹=u := by
    apply FixedDescent.carrierToSplit_injective P rfl
    change j (t*u*t⁻¹)=j u
    change j u=c.left.val at hu
    change j t*c.left.val*(j t)⁻¹=c.left.val at hh
    simpa only [map_mul,map_inv,hu] using hh
  exact mul_inv_eq_iff_eq_mul.mp he'

private theorem v_factor_centralizes (n : ℕ) (hn : 0<n)
    (x : Carrier (binaryParameters n hn))
    (hx : x∈normalizer (torus (binaryParameters n hn) : Set _))
    (c : SplitNormalForm.Coordinates (binaryParameters n hn))
    (hc : FixedDescent.carrierToSplit _ rfl x=evaluate (InputRealization.inputs _ rfl) c)
    (v : Carrier (binaryParameters n hn))
    (hv : FixedDescent.carrierToSplit _ rfl v=orderedProduct (binaryParameters n hn) c.right) :
    v∈centralizer (torus (binaryParameters n hn) : Set _) := by
  let P := binaryParameters n hn
  let D := InputRealization.inputs P rfl
  let j := FixedDescent.carrierToSplit P rfl
  apply mem_centralizer_iff.mpr
  intro t ht
  have hht : x*t*x⁻¹ ∈ torus P := (mem_normalizer_iff.mp hx t).mp ht
  let h : splitTorus P := ⟨j (x*t*x⁻¹),(FixedDescent.mem_descend_iff P rfl _ _).mp hht⟩
  let k : splitTorus P := ⟨j t,(FixedDescent.mem_descend_iff P rfl _ t).mp ht⟩
  have hg : (x*t*x⁻¹)*x=x*t := by group
  have he : h.val*evaluate D c=evaluate D c*k.val :=
    (congrArg (j (x*t*x⁻¹) * ·) hc.symm).trans
      (((map_mul j (x*t*x⁻¹) x).symm.trans (congrArg j hg)).trans
        ((map_mul j x t).trans (congrArg (· * j t) hc)))
  have hh := (torus_intertwining n hn D c h k he).2
  have he' : t⁻¹*v*t=v := by
    apply FixedDescent.carrierToSplit_injective P rfl
    change j (t⁻¹*v*t)=j v
    change j v=orderedProduct P c.right at hv
    change (j t)⁻¹*orderedProduct P c.right*j t=orderedProduct P c.right at hh
    simpa only [map_mul,map_inv,hv] using hh
  calc
    t*v = t*(t⁻¹*v*t) := congrArg (t*·) he'.symm
    _ = v*t := by group

private theorem mul_trivial_ends {K : Type*} [Group K] (a b c d : K)
    (ha : a=1) (hd : d=1) : a*b*c*d=b*c := by rw [ha,hd,one_mul,mul_one]

/-- The genuine torus has precisely the expected torus--Weyl normalizer at q>2.
Uniqueness of the split Bruhat form kills both positive factors. -/
theorem normalizer_torus_factors (n : ℕ) (hn : 0<n) (hn2 : 1<n)
    (x : Carrier (binaryParameters n hn))
    (hx : x ∈ normalizer (torus (binaryParameters n hn) : Set _)) :
    ∃ t : torus (binaryParameters n hn), ∃ w : DihedralGroup 6,
      x=t.val*weylRepresentative (binaryParameters n hn) rfl w := by
  let P := binaryParameters n hn
  let D := InputRealization.inputs P rfl
  let j := FixedDescent.carrierToSplit P rfl
  change x ∈ normalizer (torus P : Set (Carrier P)) at hx
  obtain ⟨c,hc',_⟩ := existsUnique_coordinates n hn D (j x)
  have hc : j x=evaluate D c := hc'.symm
  have hfix := (evaluate_mem_fixed_iff n hn D c).mp
    (hc'.symm ▸ FixedDescent.carrierToSplit_mem_fixed P rfl x)
  obtain ⟨u,hu⟩ := FixedDescent.exists_carrier_of_fixed P rfl c.left.val hfix.1
  have huU : u∈unipotent P := (FixedDescent.mem_descend_iff P rfl _ u).mpr (hu ▸ c.left.property)
  obtain ⟨v,hv⟩ := FixedDescent.exists_carrier_of_fixed P rfl
    (orderedProduct P c.right)
    ((orderedProduct_mem_fixedSubgroup_iff_binary n hn _).mpr hfix.2.2.2)
  have hvU : v∈unipotent P := (FixedDescent.mem_descend_iff P rfl _ v).mpr
    (hv ▸ (range_orderedProduct_binary n hn).le ⟨c.right,rfl⟩)
  have huC := u_factor_centralizes n hn x hx c hc u hu
  have hvC := v_factor_centralizes n hn x hx c hc v hv
  have hu1 := TrialityOuterTorus.centralizer_trivial n hn hn2 u huU huC
  have hv1 := TrialityOuterTorus.centralizer_trivial n hn hn2 v hvU hvC
  obtain ⟨t,ht⟩ := FixedDescent.exists_carrier_of_fixed P rfl c.torus.val hfix.2.1
  have htD : t∈torus P := (FixedDescent.mem_descend_iff P rfl _ t).mpr (ht ▸ c.torus.property)
  obtain ⟨w,hw⟩ := FixedDescent.fixed_index P rfl c.weyl hfix.2.2.1
  refine ⟨⟨t,htD⟩,w,?_⟩
  have hleft : c.left.val=1 := hu.symm.trans ((congrArg j hu1).trans (map_one j))
  have hright : orderedProduct P c.right=1 := hv.symm.trans ((congrArg j hv1).trans (map_one j))
  have hw' : D.lift c.weyl=splitRepresentative P rfl w :=
    (congrArg D.lift hw.symm).trans (FixedDescent.lift_rootRepresentative P rfl w)
  apply FixedDescent.carrierToSplit_injective P rfl
  calc
    j x = evaluate D c := hc
    _ = c.torus.val * D.lift c.weyl :=
      mul_trivial_ends c.left.val c.torus.val (D.lift c.weyl)
        (orderedProduct P c.right) hleft hright
    _ = j t * splitRepresentative P rfl w := congrArg₂ (·*·) ht.symm hw'
    _ = j (t*weylRepresentative P rfl w) :=
      (congrArg (j t*·) (FixedDescent.carrierToSplit_representative P rfl w).symm).trans
        (map_mul j t (weylRepresentative P rfl w)).symm

/-- Inside either actual parabolic, the torus normalizer has just the two
rank-one Weyl cosets. The exponent restriction is inherited from the source. -/
theorem parabolic_normalizer_torus (n : ℕ) (hn : 0<n) (hn2 : 1<n) (a : Node)
    (x : Carrier (binaryParameters n hn))
    (hxP : x∈parabolic (binaryParameters n hn) a)
    (hxD : x∈normalizer (torus (binaryParameters n hn) : Set _)) :
    x∈torus (binaryParameters n hn) ∨
      ∃ t : torus (binaryParameters n hn),
        x=t.val*simpleRepresentative (binaryParameters n hn) rfl a := by
  let P := binaryParameters n hn
  obtain ⟨t,w,rfl⟩ := normalizer_torus_factors n hn hn2 x hxD
  have hwP : weylRepresentative P rfl w∈parabolic P a := by
    have hh := (parabolic P a).mul_mem
      ((parabolic P a).inv_mem ((torus_le_borel P).trans (borel_le_parabolic P a) t.property)) hxP
    simpa only [inv_mul_cancel_left] using hh
  have hwcell : weylRepresentative P rfl w∈ConcreteBruhat.cell P rfl w :=
    (mem_cell_iff P rfl w _).mpr ⟨1,(borel P).one_mem,1,(borel P).one_mem,by simp⟩
  rcases (FoldedCellGeometry.rootRepresentative_mem_parabolicWeyl_iff a w).mp
    ((FixedDescent.mem_parabolic_iff_of_mem_cell n hn a hwcell).mp hwP) with hw|hw
  · left
    rw [hw,weylRepresentative_one P rfl,mul_one]
    exact t.property
  · right
    exact ⟨t,by rw [hw,weylRepresentative_simple P rfl a]⟩

/-- A torus-preserving automorphism of either original parabolic fixes the
nonidentity Weyl coset. This uses the local automorphism alone. -/
theorem parabolic_aut_weyl (n : ℕ) (hn : 0<n) (hn2 : 1<n) (a : Node)
    (b : MulAut (parabolic (binaryParameters n hn) a))
    (hD : ((torus (binaryParameters n hn)).subgroupOf
      (parabolic (binaryParameters n hn) a)).map b.toMonoidHom =
        (torus (binaryParameters n hn)).subgroupOf (parabolic (binaryParameters n hn) a)) :
    ∃ t : torus (binaryParameters n hn),
      (b ⟨simpleRepresentative (binaryParameters n hn) rfl a,
        simpleRepresentative_mem_parabolic _ rfl a⟩).val =
        t.val * simpleRepresentative (binaryParameters n hn) rfl a := by
  let P := binaryParameters n hn
  let Q := parabolic P a
  let w : Q := ⟨simpleRepresentative P rfl a,simpleRepresentative_mem_parabolic P rfl a⟩
  have hwN : w.val∈normalizer (torus P : Set _) := by
    change simpleRepresentative P rfl a∈normalizer (torus P : Set _)
    rw [←weylRepresentative_simple P rfl a]
    exact RelativeNormalizer.weylRepresentative_normalizes_torus P rfl _
  have hwD : w.val∉torus P := by
    intro hh
    have hB := torus_le_borel P hh
    change simpleRepresentative P rfl a∈borel P at hB
    rw [←weylRepresentative_simple P rfl a] at hB
    exact (relativeReflection_involution a).1
      ((RelativeNormalizer.representative_mem_borel_iff n hn _).mp hB)
  have hw : w∈normalizer ((torus P).subgroupOf Q : Set Q) :=
    mem_normalizer_iff.mpr (fun x => mem_normalizer_iff.mp hwN x.val)
  have hbn := ((torus P).subgroupOf Q).le_normalizer_map b.toMonoidHom
    (mem_map_of_mem b.toMonoidHom hw)
  rw [hD] at hbn
  have hbN := ((torus P).subgroupOf Q).le_normalizer_map Q.subtype
    (mem_map_of_mem Q.subtype hbn)
  rw [map_subgroupOf_eq_of_le ((torus_le_borel P).trans (borel_le_parabolic P a))] at hbN
  rcases parabolic_normalizer_torus n hn hn2 a (b w).val (b w).property hbN with hb | hb
  · have hh : b w ∈ ((torus P).subgroupOf Q).map b.toMonoidHom := by rw [hD]; exact hb
    have hh' : w∈(torus P).subgroupOf Q := (mem_map_iff_mem b.injective).mp hh
    exact (hwD hh').elim
  · exact hb

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityWeylAction
