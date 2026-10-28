module
public import Theory.SpecificGroups.Triality.ArmsFusionPair
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.ArmsReduction.Weyl
public import Theory.SpecificGroups.Triality.TwoLocalCover
public import Theory.SpecificGroups.Triality.StandardTwoRank.Derived

/-!
# The full native triality short-root centralizer

The central subsystem commutes with the highest short-root group. For q > 2
this subsystem is nontrivial and perfect. The vertices fixed by a nonidentity
short-root element form a tree in the genuine parabolic hexagon. If the
normalizer-fixed vertex differed from the standard central vertex, the
central subsystem would fix the first edge of their unique path. Its
embedding in a conjugate Borel would make it solvable, a contradiction.
Thus the full centralizer lies in the central parabolic. The exact root
parameter, positive Borel and central/arms orientation are retained.

Source: Aschbacher–Smith F.4.27(4)(ii), printed p.288
(`refs/quasithin.pdf`); the finite-building normalizer argument is GLS3
Theorem 3.1.3. The restriction q > 2 is sufficient for the original
prepared rank-one triality row, including q = 4.
-/

public noncomputable section
open Subgroup
namespace Triality.Standard.ShortRootCentralizer
open Parabolics ConcreteBruhat RadicalCoordinates RadicalCoordinates.LeviCommutators
open PositiveCoordinates PositiveCoordinates.SumExchangeData
open EvenInvolutionGeometry.ArmsNormalization

private theorem split_positive_commutes (P : Parameters) (u t : ExtensionField P) :
    Commute (positiveRoot P 1 u) (shortSplit P 2 t) := by
  have hc (j : Fin 3) (v : ExtensionField P) :
      Commute (curve P 3 u) (curve P (shortPosition 2 j) v) := by
    apply nonsumCommute_parameters P _ _ (by fin_cases j <;> decide)
    rintro ⟨k,hk⟩
    have htable : ∀ j : Fin 3, ∀ k : Fin 12,
        (3,shortPosition 2 j,k) ∉ sumTriples := by decide +kernel
    exact htable j k ((mem_sumTriples_iff _ _ _).mpr ((root_sum_iff _ _ _).mp hk))
  have hpos : positiveRoot P 1 u = curve P 3 u := (curve_simple P 1 u).symm
  rw [hpos,shortSplit]
  exact ((hc 0 _).mul_right (hc 1 _)).mul_right (hc 2 _)

private theorem split_weyl_commutes (P : Parameters) (hp : P.prime = 2)
    (t : ExtensionField P) : Commute (weylWord P 1 1) (shortSplit P 2 t) := by
  have h := central_short_two P hp t
  have hw : weylElementary P hp (.sr 1) = simpleElementary P hp .central :=
    weylElementary_simple P hp .central
  have hh : toCarrier P (simpleElementary P hp .central * shortElementary P hp 2 t *
      (simpleElementary P hp .central)⁻¹) = toCarrier P (shortElementary P hp 2 t) := by
    simpa only [map_mul,map_inv,←hw,weylRepresentative,short] using h
  have he := ElementaryCentralKernel.toCarrier_injective P hp hh
  have hs := congrArg (elementaryInclusion P) he
  simp only [map_mul,map_inv,shortElementary_val] at hs
  rw [elementaryInclusion_simple_central] at hs
  exact (mul_inv_eq_iff_eq_mul.mp hs)

private theorem split_levi_centralizes (P : Parameters) (hp : P.prime = 2)
    (t : ExtensionField P) :
    splitLevi P .central ≤ centralizer ({shortSplit P 2 t} : Set (SplitGroup P)) := by
  apply (closure_le _).mpr
  rintro g ⟨i,hi,u,he⟩
  have hi' : i = 1 := hi
  subst i
  apply mem_centralizer_singleton_iff.mpr
  rcases he with rfl | rfl
  · exact (split_positive_commutes P u t).eq
  · rw [←SplitNormalForm.weylWord_positive P hp 1 u]
    exact (((split_weyl_commutes P hp t).mul_left
      (split_positive_commutes P u t)).mul_left (split_weyl_commutes P hp t)).eq

private theorem descend_centralizer {A B D : Type*} [Group A] [Group B] [Group D]
    (f : A →* B) (g : A →* D) (hf : Function.Injective f) (z : A) (K : Subgroup B)
    (hc : K ≤ centralizer ({f z} : Set B)) :
    (K.comap f).map g ≤ centralizer ({g z} : Set D) := by
  rintro x ⟨y,hy,rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  rw [←map_mul,←map_mul]
  apply congrArg g
  apply hf
  simpa only [map_mul] using mem_centralizer_singleton_iff.mp (hc hy)

/-- The genuine central subsystem fixes every element of the highest short root. -/
theorem levi_central_le_centralizer (P : Parameters) (hp : P.prime = 2)
    (t : ExtensionField P) :
    levi P .central ≤ centralizer ({short P hp 2 t} : Set (Carrier P)) := by
  apply descend_centralizer (elementaryInclusion P) (toCarrier P)
    (elementaryInclusion_injective P) (shortElementary P hp 2 t) (splitLevi P .central)
  rw [shortElementary_val]
  exact split_levi_centralizes P hp t

open GroupAction.EvenPolygon TwoLocalGeometry

private theorem fixed_neighbor (n : ℕ) (hn : 0 < n)
    (R J : Subgroup (BinaryCarrier n hn))
    (hT : ((incidenceGraph n hn).induce (fixedVertices R)).IsTree)
    (hJN : J ≤ normalizer (R : Set (BinaryCarrier n hn)))
    (x y : Vertex n hn) (hxR : x ∈ fixedVertices R) (hyR : y ∈ fixedVertices R)
    (hx : ∀ j ∈ J, j • x = x) (hy : ∀ j ∈ J, j • y = y) (hne : x ≠ y) :
    ∃ w : Vertex n hn, (incidenceGraph n hn).Adj x w ∧ ∀ j ∈ J, j • w = w := by
  let xR : fixedVertices R := ⟨x,hxR⟩
  let yR : fixedVertices R := ⟨y,hyR⟩
  obtain ⟨p,hp,huniq⟩ := hT.existsUnique_path xR yR
  have hnonnil : ¬ p.Nil := by
    intro hnil
    exact hne (congrArg Subtype.val hnil.eq)
  refine ⟨p.snd.val,p.adj_snd hnonnil,?_⟩
  intro j hj
  let f : ((incidenceGraph n hn).induce (fixedVertices R)) →g
      ((incidenceGraph n hn).induce (fixedVertices R)) :=
    ⟨fun v => ⟨j • v.val,normalizer_smul_mem_fixedVertices R (hJN hj) v.property⟩,
      fun h => smul_adj j h⟩
  have hxj : f xR = xR := Subtype.ext (hx j hj)
  have hyj : f yR = yR := Subtype.ext (hy j hj)
  let q := (p.map f).copy hxj hyj
  have hq : q.IsPath := by
    apply (SimpleGraph.Walk.isPath_copy ..).mpr
    apply hp.map
    intro a b hab
    exact Subtype.ext (MulAction.injective j (congrArg Subtype.val hab))
  have he := congrArg (fun w => (w.getVert 1).val) (huniq q hq)
  simp only [q,SimpleGraph.Walk.getVert_copy,SimpleGraph.Walk.getVert_map] at he
  exact he

private theorem solvable_of_fixed_neighbor (n : ℕ) (hn : 0 < n)
    (J : Subgroup (BinaryCarrier n hn))
    (hJ : J ≤ parabolic (binaryParameters n hn) .central)
    (w : Vertex n hn)
    (hw : (incidenceGraph n hn).Adj
      (CosetGeometry.base (parabolic (binaryParameters n hn)) .central) w)
    (hfix : ∀ j ∈ J, j • w = w) : Group.IsSolvable J := by
  let P := binaryParameters n hn
  have htype : w.type = Node.arms := by
    have hh : Node.central ≠ w.type := hw.1
    cases ht : w.type <;> simp_all
  obtain ⟨g,hg,hgw⟩ := (CosetGeometry.incident_base_iff _ _ _).mp hw.2
  have hew : g • CosetGeometry.base (parabolic P) .arms = w := by
    cases w with
    | mk a q =>
      change a = Node.arms at htype
      subst a
      change CosetGeometry.Vertex.mk Node.arms (g • ((1 : Carrier P) : Carrier P ⧸ parabolic P .arms)) = _
      simpa only [MulAction.Quotient.smul_mk,smul_eq_mul,mul_one] using
        congrArg (CosetGeometry.Vertex.mk Node.arms) hgw
  have hmap (j : J) : g⁻¹ * j.val * g ∈ borel P := by
    rw [←parabolic_inf_binary P rfl]
    refine ⟨?_,(parabolic P .central).mul_mem
      ((parabolic P .central).mul_mem ((parabolic P .central).inv_mem hg) (hJ j.property)) hg⟩
    rw [←CosetGeometry.stabilizer_base (parabolic P) .arms]
    change (g⁻¹ * j.val * g) • CosetGeometry.base (parabolic P) .arms = _
    rw [mul_smul,mul_smul,hew,hfix j j.property,←hew,inv_smul_smul]
  let f : J →* borel P := (((MulAut.conj g⁻¹).toMonoidHom).comp J.subtype).codRestrict _
    (fun j => by
      change g⁻¹ * j.val * (g⁻¹)⁻¹ ∈ borel P
      simpa only [inv_inv] using hmap j)
  let : Group.IsSolvable (borel P) := TwoRank.Derived.borel_isSolvable n hn
  apply Group.isSolvable_of_isSolvable_injective (f := f)
  intro a b hab
  exact Subtype.ext ((MulAut.conj g⁻¹).injective (congrArg Subtype.val hab))

/-- A nonzero marked short root is an involution in both root radicals. -/
theorem short_order (P : Parameters) (hp : P.prime = 2)
    (t : ExtensionField P) (ht : t ≠ 0) : orderOf (short P hp 2 t) = 2 := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  have hc (a : ExtensionField P) :
      (armsCoordinates P hp (![0,a],![0,0,0])).val = short P hp 2 a := by
    rw [armsCoordinates_factorization]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons,long_zero,short_zero,one_mul,mul_one]
  apply orderOf_eq_prime_iff.mpr
  refine ⟨?_,?_⟩
  · rw [pow_two,←short_add,CharTwo.add_self_eq_zero,short_zero]
  · intro he
    have hh : armsCoordinates P hp (![0,t],![0,0,0]) =
        armsCoordinates P hp (![0,0],![0,0,0]) := by
      apply Subtype.ext
      rw [hc,hc,he,short_zero]
    exact ht (congrFun (congrArg Prod.fst ((armsCoordinates P hp).injective hh)) 1)

/-- For q > 2 the full native short-root centralizer lies in the central
parabolic. The fixed-tree argument uses the genuine central rank-one subgroup. -/
theorem centralizer_le_central (n : ℕ) (hn : 0 < n) (hn2 : 1 < n)
    (t : ExtensionField (binaryParameters n hn)) (ht : t ≠ 0) :
    centralizer ({short (binaryParameters n hn) rfl 2 t} : Set (BinaryCarrier n hn)) ≤
      parabolic (binaryParameters n hn) .central := by
  let P := binaryParameters n hn
  let r := short P rfl 2 t
  let R := zpowers r
  let J := levi P .central
  let C := centralizer ({r} : Set (Carrier P))
  have hr : orderOf r = 2 := short_order P rfl t ht
  have hR : R ≠ ⊥ := by
    intro he
    have he1 : r = 1 := zpowers_eq_bot.mp he
    simp only [he1,orderOf_one] at hr
    omega
  have hpR : IsPGroup 2 R := by
    apply (IsPGroup.iff_card).mpr
    exact ⟨1, by rw [Nat.card_zpowers,hr,pow_one]⟩
  have hCN : C ≤ normalizer (R : Set (Carrier P)) := by
    change centralizer ({r} : Set (Carrier P)) ≤ _
    rw [←centralizer_closure ({r} : Set (Carrier P)),←zpowers_eq_closure]
    exact centralizer_le_normalizer _
  have hJC : J ≤ C := levi_central_le_centralizer P rfl t
  have hJP : J ≤ parabolic P .central := levi_le_parabolic P .central
  have hq : 2 < P.q := by
    change 2^1 < 2^n
    exact Nat.pow_lt_pow_right (by decide) hn2
  let : Group.IsPerfect J := levi_central_isPerfect P rfl hq
  let a : J := ⟨(CentralRootSquare.orderThreeActor P rfl).val,
    (CentralRootSquare.range_centralActor P rfl).le
      ⟨CentralRootSquare.orderThreeMatrix P,rfl⟩⟩
  let : Nontrivial J := ⟨⟨a,1,fun he => by
    have ha : CentralRootSquare.orderThreeActor P rfl = 1 :=
      Subtype.ext (show (CentralRootSquare.orderThreeActor P rfl).val = 1 from
        congrArg (fun x : J => x.val) he)
    have ho := CentralRootSquare.orderOf_orderThreeActor P rfl
    rw [ha,orderOf_one] at ho
    omega⟩⟩
  have hΓ := (hexagonGeometry n hn).toEvenPolygonAction
    (apartmentTranslates n hn) (standardApartment_fixer_odd n hn)
  have hedge := exists_fixed_edge n hn R hpR
  have hT := fixed_graph_isTree hΓ R hR hpR hedge
  obtain ⟨v,hv⟩ := normalizer_fixed_vertex_of_fixed_edge hΓ R hR hpR hedge
  let b := CosetGeometry.base (parabolic P) .central
  have hb : b ∈ fixedVertices R := by
    intro a ha
    have hRP : R ≤ parabolic P .central := zpowers_le.mpr
      (radical_le_parabolic P .central (descendedRootSubgroup_le_radical P rfl .central
        (short_mem P rfl .central 2 trivial t)))
    have hmem : a ∈ MulAction.stabilizer (Carrier P) b := by
      rw [CosetGeometry.stabilizer_base]
      exact hRP ha
    exact hmem
  have hvR : v ∈ fixedVertices R := fun a ha => hv a (R.le_normalizer ha)
  have hbJ : ∀ a ∈ J, a • b = b := by
    intro a ha
    have hmem : a ∈ MulAction.stabilizer (Carrier P) b := by
      rw [CosetGeometry.stabilizer_base]
      exact hJP ha
    exact hmem
  have he : b = v := by
    by_contra hne
    obtain ⟨w,hw,hfix⟩ := fixed_neighbor n hn R J hT (hJC.trans hCN)
      b v hb hvR hbJ (fun a ha => hv a (hCN (hJC ha))) hne
    exact Group.IsPerfect.not_isSolvable J (solvable_of_fixed_neighbor n hn J hJP w hw hfix)
  intro a ha
  rw [←CosetGeometry.stabilizer_base (parabolic P) .central]
  change a • b = b
  rw [he]
  exact hv a (hCN ha)

/-- The standard central vertex is the unique vertex fixed by the full
short-root centralizer. This strengthens containment to the exact geometric
fact needed to control automorphisms of a marked source extension. -/
theorem unique_centralizer_fixed_vertex (n : ℕ) (hn : 0 < n) (hn2 : 1 < n)
    (t : ExtensionField (binaryParameters n hn)) (ht : t ≠ 0)
    (v : Vertex n hn)
    (hv : ∀ g ∈ centralizer ({short (binaryParameters n hn) rfl 2 t} :
      Set (BinaryCarrier n hn)), g • v = v) :
    v = CosetGeometry.base (parabolic (binaryParameters n hn)) .central := by
  let P := binaryParameters n hn
  let r := short P rfl 2 t
  let R := zpowers r
  let J := levi P .central
  let C := centralizer ({r} : Set (Carrier P))
  have hr : orderOf r = 2 := short_order P rfl t ht
  have hR : R ≠ ⊥ := by
    intro he
    have he1 : r = 1 := zpowers_eq_bot.mp he
    simp only [he1,orderOf_one] at hr
    omega
  have hpR : IsPGroup 2 R := by
    apply (IsPGroup.iff_card).mpr
    exact ⟨1, by rw [Nat.card_zpowers,hr,pow_one]⟩
  have hRC : R ≤ C := zpowers_le.mpr
    (mem_centralizer_singleton_iff.mpr (Commute.refl r).eq)
  have hCN : C ≤ normalizer (R : Set (Carrier P)) := by
    change centralizer ({r} : Set (Carrier P)) ≤ _
    rw [←centralizer_closure ({r} : Set (Carrier P)),←zpowers_eq_closure]
    exact centralizer_le_normalizer _
  have hJC : J ≤ C := levi_central_le_centralizer P rfl t
  have hJP : J ≤ parabolic P .central := levi_le_parabolic P .central
  have hq : 2 < P.q := by
    change 2^1 < 2^n
    exact Nat.pow_lt_pow_right (by decide) hn2
  let : Group.IsPerfect J := levi_central_isPerfect P rfl hq
  let a : J := ⟨(CentralRootSquare.orderThreeActor P rfl).val,
    (CentralRootSquare.range_centralActor P rfl).le
      ⟨CentralRootSquare.orderThreeMatrix P,rfl⟩⟩
  let : Nontrivial J := ⟨⟨a,1,fun he => by
    have ha : CentralRootSquare.orderThreeActor P rfl = 1 :=
      Subtype.ext (show (CentralRootSquare.orderThreeActor P rfl).val = 1 from
        congrArg (fun x : J => x.val) he)
    have ho := CentralRootSquare.orderOf_orderThreeActor P rfl
    rw [ha,orderOf_one] at ho
    omega⟩⟩
  have hΓ := (hexagonGeometry n hn).toEvenPolygonAction
    (apartmentTranslates n hn) (standardApartment_fixer_odd n hn)
  have hT := fixed_graph_isTree hΓ R hR hpR (exists_fixed_edge n hn R hpR)
  let b := CosetGeometry.base (parabolic P) .central
  have hCb : ∀ g ∈ C, g • b = b := by
    intro g hg
    have hgP := centralizer_le_central n hn hn2 t ht hg
    rwa [←CosetGeometry.stabilizer_base (parabolic P) .central] at hgP
  have hbR : b ∈ fixedVertices R := fun g hg => hCb g (hRC hg)
  have hvR : v ∈ fixedVertices R := fun g hg => hv g (hRC hg)
  by_contra hne
  obtain ⟨w,hw,hfix⟩ := fixed_neighbor n hn R J hT (hJC.trans hCN)
    b v hbR hvR (fun g hg => hCb g (hJC hg)) (fun g hg => hv g (hJC hg))
      (Ne.symm hne)
  exact Group.IsPerfect.not_isSolvable J (solvable_of_fixed_neighbor n hn J hJP w hw hfix)

end Triality.Standard.ShortRootCentralizer
