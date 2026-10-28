module
public import Theory.SpecificGroups.GL2.AbelianNormalScalar
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.RootGeneration
import all CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.RootGeneration
/-!
# Normal elementary subgroups of odd PSL₃ involution centralizers

The full graph-extension centralizer of an inner involution has no normal
four-group. In its GL₂ Levi the inner part of a normal elementary subgroup
is scalar: conjugating by the two elementary matrices forces this directly,
also in characteristic three. Halving root parameters shows that both block
root groups centralize the entire elementary subgroup. An outer actor fixing
both groups has a skew-symmetric block and squares to the central involution,
so it cannot be elementary. Involution conjugacy transports the result to
any inner involution in the actual graph extension.

This is the adequate local input for E.2.15 with its original TI hypothesis;
we do not claim that the characteristic-three two-core is cyclic or that
the unrestricted local assertion in the printed E.2.7 argument holds.
Source: Aschbacher–Smith E.2.2(2d), E.2.7 and E.2.15, pp.215, 219, 228.
-/
public section
open Subgroup Matrix
open scoped MatrixGroups IsMulCommutative
open Matrix.PSL3 Matrix.PSL3.OuterSolvable Matrix.PSL3.OddInvolutionFixed
open Matrix.PSL3.OddPrimeGraphExtension Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
open CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerGenerationGeometry
namespace CFSG.Quasithin.ChapterE.Structure.OddDegreeThree.NormalElementary
variable (F:Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

omit [Finite F] in
private theorem projection_eq_of_innerSL_eq {x y:SL(3,F)}
    (h:innerSL F x=innerSL F y) : projection F x=projection F y := by
  have hZ:center PSL(3,F)=⊥ := by
    let _ : Group.IsPerfect PSL(3,F) := Atlas.psl_perfect 3 (by decide)
    exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun h=>Group.IsPerfect.not_isMulCommutative PSL(3,F) (center_eq_top_iff.mp h))
  apply MulAut.conj_injective_of_center_eq_bot hZ
  exact congrArg Subtype.val h

omit [Finite F] [IsSimpleGroup PSL(3,F)] in
private theorem block_mem_centralizer (h2:(2:F)≠0) (B:GL (Fin 2) F) :
    innerSL F (SL3.blockEmbedding F B)∈centralizer ({standardInner F}:Set (graphExtension F)) := by
  apply mem_centralizer_singleton_iff.mpr
  have hc:=mem_centralizer_singleton_iff.mp
    ((SL3.blockEmbedding_range F h2).le ⟨B,rfl⟩)
  exact (map_mul (innerSL F) _ _).symm.trans
    ((congrArg (innerSL F) hc).trans (map_mul (innerSL F) _ _))

/-- The inner part of a normal elementary subgroup is at most the marked
central involution, also in characteristic three. -/
theorem inner_mem_cases (h2:(2:F)≠0) (A:Subgroup (graphExtension F))
    [IsElementaryAbelian 2 A]
    (hAC:A≤centralizer ({standardInner F}:Set (graphExtension F)))
    (hCA:centralizer ({standardInner F}:Set (graphExtension F))≤normalizer (A:Set _))
    (a:graphExtension F) (ha:a∈A) (hai:a∈innerPart F) :
    a=1 ∨ a=standardInner F := by
  by_cases ha1:a=1
  · exact Or.inl ha1
  have hao:orderOf a=2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p:=2) a ha) ha1
  obtain ⟨s,hs⟩:=exists_standard_coordinates F h2 a hao hai
  let x:=s*SL3.standardInvolution F*s⁻¹
  have hx:innerSL F x=a := by simpa only [x,map_mul,map_inv,standardInner] using hs
  have hx2:x^2=1 := by
    change (MulAut.conj s (SL3.standardInvolution F))^2=1
    rw [←map_pow,SL3.standardInvolution_sq,map_one]
  have hxC:x∈centralizer ({SL3.standardInvolution F}:Set SL(3,F)) := by
    apply mem_centralizer_singleton_iff.mpr
    apply commutes_of_projective_commutes _ _ (SL3.standardInvolution_sq F)
    have hh:=mem_centralizer_singleton_iff.mp (hAC ha)
    rw [←hx] at hh
    have he := projection_eq_of_innerSL_eq F
      ((map_mul (innerSL F) x _).trans (hh.trans (map_mul (innerSL F) _ x).symm))
    simpa only [map_mul] using he
  obtain ⟨B,hBx⟩ := (SL3.blockEmbedding_range F h2 ▸ hxC)
  have hBscalar:B∈(GeneralLinearGroup.scalar (Fin 2):Fˣ→*GL (Fin 2) F).range := by
    apply GeneralLinearGroup.scalar_of_commutes_conjugates h2 B
    intro u
    have hu:=hCA (block_mem_centralizer F h2 u)
    have hconj:innerSL F (SL3.blockEmbedding F u)*a*(innerSL F (SL3.blockEmbedding F u))⁻¹∈A :=
      (mem_normalizer_iff.mp hu a).mp ha
    have hcomm:=congrArg Subtype.val (mul_comm (⟨a,ha⟩:A) ⟨_,hconj⟩)
    change a*(innerSL F (SL3.blockEmbedding F u)*a*(innerSL F (SL3.blockEmbedding F u))⁻¹)=
      (innerSL F (SL3.blockEmbedding F u)*a*(innerSL F (SL3.blockEmbedding F u))⁻¹)*a at hcomm
    have he : innerSL F (x*(SL3.blockEmbedding F u*x*(SL3.blockEmbedding F u)⁻¹))=
        innerSL F ((SL3.blockEmbedding F u*x*(SL3.blockEmbedding F u)⁻¹)*x) := by
      simpa only [map_mul,map_inv,hx] using hcomm
    have hproj:=projection_eq_of_innerSL_eq F he
    simp only [map_mul] at hproj
    have hSL := commutes_of_projective_commutes x
      (SL3.blockEmbedding F u*x*(SL3.blockEmbedding F u)⁻¹) hx2 hproj.symm
    apply (SL3.blockEmbedding_injective F)
    simpa only [map_mul,map_inv,hBx] using hSL.symm
  obtain ⟨c,hc⟩:=hBscalar
  have hB2:B^2=1 := (SL3.blockEmbedding_injective F) (by simpa only [map_pow,map_one,hBx] using hx2)
  have hc2:(c:F)^2=1 := by
    have h:=congrArg (fun B:GL (Fin 2) F=>B.val 0 0) hB2
    rw [←hc,←map_pow] at h
    exact h
  rcases sq_eq_one_iff.mp hc2 with hc1|hcn
  · have he:c=1 := Units.ext hc1
    have hx1:x=1 := by rw [←hBx,←hc,he,map_one,map_one]
    exact (ha1 (by rw [←hx,hx1,map_one])).elim
  · have he:c=-1 := Units.ext hcn
    right
    rw [←hx]
    apply congrArg (innerSL F)
    rw [←hBx,←hc,he]
    apply Subtype.ext
    change SL3.blockMatrix F (GeneralLinearGroup.scalar (Fin 2) (-1:Fˣ))=(SL3.standardInvolution F).val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SL3.blockMatrix,SL3.standardInvolution,GeneralLinearGroup.scalar,Matrix.scalar,Matrix.det_neg]

private theorem commute_square_of_displacement {G:Type*} [Group G] (r a d:G)
    (he:r*a=d*a*r) (hd:Commute r d) (hd2:d^2=1) : Commute (r^2) a := by
  change r^2*a=a*r^2
  calc
    r^2*a = r*(r*a) := by simp only [pow_two,mul_assoc]
    _ = r*(d*a*r) := by rw [he]
    _ = d*(r*a)*r := by simpa only [mul_assoc] using congrArg (fun x=>x*a*r) hd.eq
    _ = d*(d*a*r)*r := by rw [he]
    _ = d^2*a*r^2 := by simp only [pow_two,mul_assoc]
    _ = a*r^2 := by rw [hd2,one_mul]

/-- Every block root centralizes the normal elementary subgroup. Halving the
root parameter makes the argument valid in characteristic three. -/
theorem root_commutes (h2:(2:F)≠0) (A:Subgroup (graphExtension F))
    [IsElementaryAbelian 2 A]
    (hAC:A≤centralizer ({standardInner F}:Set (graphExtension F)))
    (hCA:centralizer ({standardInner F}:Set (graphExtension F))≤normalizer (A:Set _))
    (a:graphExtension F) (ha:a∈A)
    (i j:Fin 3) (hij:i≠j) (hi:i≠2) (hj:j≠2) (t:F) :
    Commute (innerSL F (SpecialLinearGroup.transvection hij t)) a := by
  let r:=innerSL F (SpecialLinearGroup.transvection hij (t/2))
  have hrC:r∈centralizer ({standardInner F}:Set (graphExtension F)) := by
    exact mem_centralizer_singleton_iff.mpr
      ((map_mul (innerSL F) _ _).symm.trans
        ((congrArg (innerSL F) (mem_centralizer_singleton_iff.mp
          (root_commute_standard F i j hij hi hj (t/2)))).trans (map_mul (innerSL F) _ _)))
  have hrI:r∈innerPart F := innerSL_range F ▸ ⟨_,rfl⟩
  let d:=r*a*r⁻¹*a⁻¹
  have hdA:d∈A := A.mul_mem ((mem_normalizer_iff.mp (hCA hrC) a).mp ha) (A.inv_mem ha)
  have hdI:d∈innerPart F := by
    change r*a*r⁻¹*a⁻¹∈innerPart F
    rw [mul_assoc r a, mul_assoc r (a*r⁻¹)]
    exact (innerPart F).mul_mem hrI ((inferInstance:Normal (innerPart F)).conj_mem _ ((innerPart F).inv_mem hrI) a)
  have hd2:d^2=1 := elemPow_eq_one_of_isElementaryAbelian (p:=2) d hdA
  have hrd:Commute r d := by
    rcases inner_mem_cases F h2 A hAC hCA d hdA hdI with hd|hd
    · rw [hd]; exact Commute.one_right _
    · rw [hd]; exact mem_centralizer_singleton_iff.mp hrC
  have he:r*a=d*a*r := by dsimp [d]; group
  have hsq:=commute_square_of_displacement r a d he hrd hd2
  have hr2:r^2=innerSL F (SpecialLinearGroup.transvection hij t) := by
    dsimp [r]
    rw [←map_pow,pow_two,←SpecialLinearGroup.transvection_add]
    congr 2
    field_simp
    ring
  rwa [hr2] at hsq
omit [Finite F] [IsSimpleGroup PSL(3,F)] in
private theorem eq_of_projection_eq_entry (x y:SL(3,F))
    (hp:projection F x=projection F y) (i j:Fin 3)
    (he:x.val i j=y.val i j) (hn:y.val i j≠0) : x=y := by
  have hc:x*y⁻¹∈center SL(3,F) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change projection F (x*y⁻¹)=1
    simp only [map_mul,map_inv,hp,mul_inv_cancel]
  obtain ⟨c,_,hc⟩:=Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have hm:(x*y⁻¹).val*y.val=x.val := by
    change ((x*y⁻¹)*y).val=x.val
    rw [inv_mul_cancel_right]
  rw [←hc] at hm
  have hij:=congrArg (fun m:Matrix (Fin 3) (Fin 3) F=>m i j) hm
  simp only [Matrix.scalar_apply,Matrix.diagonal_mul] at hij
  rw [he] at hij
  have hc1:c=1 := (mul_right_cancel₀ hn (hij.trans (one_mul _).symm))
  apply Subtype.ext
  simpa [hc1] using hm.symm

omit [IsSimpleGroup PSL(3,F)] in
private theorem outer_coordinates (a:graphExtension F) (ha:a∉innerPart F) :
    ∃g:SL(3,F),a=innerSL F g*graphElement F := by
  obtain ⟨i,hi,c,hc,hic⟩:=mem_sup_of_normal_left.mp a.property
  obtain ⟨y,rfl⟩:=hi
  obtain ⟨g,rfl⟩:=projection_surjective F y
  obtain ⟨n,rfl⟩ := (isOfFinOrder_of_finite _).mem_powers_iff_mem_zpowers.mpr hc
  change MulAut.conj (projection F g)*graph F^n=a.val at hic
  rw [pow_eq_pow_mod n (graph_sq F)] at hic
  have hn:n%2=0∨n%2=1 := by omega
  rcases hn with hn|hn
  · simp only [hn,pow_zero,mul_one] at hic
    exact (ha (by change a.val∈MulAut.innerSubgroup _; exact hic ▸ ⟨_,rfl⟩)).elim
  · refine ⟨g,Subtype.ext ?_⟩
    change a.val=MulAut.conj (projection F g)*graph F
    simpa only [hn,pow_one] using hic.symm

omit [Finite F] in
private theorem fixed_root_equation (g:SL(3,F))
    {i j:Fin 3} (hij:i≠j) (a:F)
    (hc:Commute (innerSL F (SpecialLinearGroup.transvection hij a))
      (innerSL F g*graphElement F)) :
    projection F (g*SpecialLinearGroup.transvection hij.symm (-a))=
      projection F (SpecialLinearGroup.transvection hij a*g) := by
  apply projection_eq_of_innerSL_eq F
  rw [←graphSL_transvection F hij a]
  calc
    innerSL F (g*graphSL F (SpecialLinearGroup.transvection hij a)) =
      (innerSL F g*graphElement F)*innerSL F (SpecialLinearGroup.transvection hij a)*(graphElement F)⁻¹ := by
        rw [map_mul,innerSL_graph]; group
    _ = innerSL F (SpecialLinearGroup.transvection hij a)*(innerSL F g*graphElement F)*(graphElement F)⁻¹ := by
      rw [hc.eq]
    _ = innerSL F (SpecialLinearGroup.transvection hij a*g) := by rw [map_mul]; group

omit [Finite F] in
private theorem block_root_equation (B:GL (Fin 2) F)
    {i j:Fin 3} (hij:i≠j) (hi:i≠2) (_hj:j≠2) (a:F)
    (hc:Commute (innerSL F (SpecialLinearGroup.transvection hij a))
      (innerSL F (SL3.blockEmbedding F B)*graphElement F)) :
    SL3.blockEmbedding F B*SpecialLinearGroup.transvection hij.symm (-a)=
      SpecialLinearGroup.transvection hij a*SL3.blockEmbedding F B := by
  apply eq_of_projection_eq_entry F _ _ (fixed_root_equation F _ hij a hc) 2 2
  · change (SL3.blockMatrix F B*(1+single j i (-a))) 2 2=
      ((1+single i j a)*SL3.blockMatrix F B) 2 2
    simp [Matrix.mul_apply,Fin.sum_univ_three,SL3.blockMatrix,hi]
  · change ((1+single i j a)*SL3.blockMatrix F B) 2 2≠0
    simp [Matrix.mul_apply,Fin.sum_univ_three,SL3.blockMatrix,hi,GeneralLinearGroup.det_ne_zero]

omit [Finite F] in
private theorem standardInner_ne_one (h2:(2:F)≠0) : standardInner F≠1 := by
  intro h
  have hp:projection F (SL3.standardInvolution F)=1 := by
    simpa using projection_eq_of_innerSL_eq F (y:=1) (by simpa only [map_one,standardInner] using h)
  have hc:SL3.standardInvolution F∈center SL(3,F) := (QuotientGroup.eq_one_iff _).mp hp
  obtain ⟨c,_,hc⟩:=Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have h00:=congrArg (fun m:Matrix (Fin 3) (Fin 3) F=>m 0 0) hc
  have h22:=congrArg (fun m:Matrix (Fin 3) (Fin 3) F=>m 2 2) hc
  have hc0:c=-1 := h00
  have hc2:c=1 := h22
  apply h2
  linear_combination hc0-hc2

/-- An outer actor centralizing both block root groups squares to the marked
central involution, so it cannot belong to an elementary subgroup. -/
theorem le_inner (h2:(2:F)≠0) (A:Subgroup (graphExtension F))
    [IsElementaryAbelian 2 A]
    (hAC:A≤centralizer ({standardInner F}:Set (graphExtension F)))
    (hCA:centralizer ({standardInner F}:Set (graphExtension F))≤normalizer (A:Set _)) :
    A ≤ innerPart F := by
  intro a ha
  by_contra hai
  obtain ⟨g,hg⟩:=outer_coordinates F a hai
  have hgC:innerSL F g∈centralizer ({standardInner F}:Set (graphExtension F)) := by
    have hh:=(centralizer ({standardInner F}:Set (graphExtension F))).mul_mem
      (hAC ha) ((centralizer ({standardInner F}:Set (graphExtension F))).inv_mem
        (graphElement_centralizes_standard F))
    simpa only [hg,mul_inv_cancel_right] using hh
  have hgSL:g∈centralizer ({SL3.standardInvolution F}:Set SL(3,F)) := by
    apply mem_centralizer_singleton_iff.mpr
    apply commutes_of_projective_commutes _ _ (SL3.standardInvolution_sq F)
    have hh:=mem_centralizer_singleton_iff.mp hgC
    have he := projection_eq_of_innerSL_eq F
      ((map_mul (innerSL F) g _).trans (hh.trans (map_mul (innerSL F) _ g).symm))
    simpa only [map_mul] using he
  obtain ⟨B,hB⟩:=(SL3.blockEmbedding_range F h2 ▸ hgSL)
  have h01:=root_commutes F h2 A hAC hCA a ha 0 1 (by decide) (by decide) (by decide) 1
  have h10:=root_commutes F h2 A hAC hCA a ha 1 0 (by decide) (by decide) (by decide) 1
  rw [hg,←hB] at h01 h10
  have he01:=block_root_equation F B (show (0:Fin 3)≠1 by decide) (by decide) (by decide) 1 h01
  have he10:=block_root_equation F B (show (1:Fin 3)≠0 by decide) (by decide) (by decide) 1 h10
  have h00:B.val 0 0=0 := by
    have hh:=congrArg (fun x:SL(3,F)=>x.val 1 0) he10
    change (SL3.blockMatrix F B*(1+single (0:Fin 3) (1:Fin 3) (-1:F))) 1 0=
      ((1+single (1:Fin 3) (0:Fin 3) (1:F))*SL3.blockMatrix F B) 1 0 at hh
    simp [SL3.blockMatrix,Matrix.mul_apply,Fin.sum_univ_three] at hh
    exact hh
  have h11:B.val 1 1=0 := by
    have hh:=congrArg (fun x:SL(3,F)=>x.val 0 1) he01
    change (SL3.blockMatrix F B*(1+single (1:Fin 3) (0:Fin 3) (-1:F))) 0 1=
      ((1+single (0:Fin 3) (1:Fin 3) (1:F))*SL3.blockMatrix F B) 0 1 at hh
    simp [SL3.blockMatrix,Matrix.mul_apply,Fin.sum_univ_three] at hh
    exact hh
  have h10:B.val 1 0= -B.val 0 1 := by
    have hh:=congrArg (fun x:SL(3,F)=>x.val 0 0) he01
    change (SL3.blockMatrix F B*(1+single (1:Fin 3) (0:Fin 3) (-1:F))) 0 0=
      ((1+single (0:Fin 3) (1:Fin 3) (1:F))*SL3.blockMatrix F B) 0 0 at hh
    simpa [SL3.blockMatrix,Matrix.mul_apply,Fin.sum_univ_three,h00] using hh.symm
  have ht:SpecialLinearGroup.transpose g=SL3.standardInvolution F*g := by
    apply Subtype.ext
    rw [←hB]
    change (SL3.blockMatrix F B).transpose=(SL3.standardInvolution F).val*SL3.blockMatrix F B
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SL3.blockMatrix,SL3.standardInvolution,Matrix.mul_apply,Fin.sum_univ_three,h00,h11,h10]
  have he:g*graphSL F g=SL3.standardInvolution F := by
    change g*(SpecialLinearGroup.transpose g)⁻¹=SL3.standardInvolution F
    rw [ht,_root_.mul_inv_rev,←mul_assoc,mul_inv_cancel,one_mul]
    exact (eq_inv_of_mul_eq_one_left ((pow_two _).symm.trans (SL3.standardInvolution_sq F))).symm
  have hgraph:(graphElement F)^2=1 := Subtype.ext (graph_sq F)
  have ha2:a^2=standardInner F := by
    rw [hg]
    calc
      (innerSL F g*graphElement F)^2=
        innerSL F g*(graphElement F*innerSL F g*(graphElement F)⁻¹)*(graphElement F)^2 := by
          simp only [pow_two]; group
      _=innerSL F (g*graphSL F g) := by rw [←innerSL_graph,hgraph,mul_one,map_mul]
      _=standardInner F := by rw [he]; rfl
  exact standardInner_ne_one F h2 (ha2.symm.trans (elemPow_eq_one_of_isElementaryAbelian (p:=2) a ha))

/-- A normal elementary subgroup of the full marked involution centralizer
has at most two elements, including the prime-field case of characteristic three. -/
theorem card_le_two (h2:(2:F)≠0) (A:Subgroup (graphExtension F))
    [IsElementaryAbelian 2 A]
    (hAC:A≤centralizer ({standardInner F}:Set (graphExtension F)))
    (hCA:centralizer ({standardInner F}:Set (graphExtension F))≤normalizer (A:Set _)) :
    Nat.card A≤2 := by
  have hA:A≤zpowers (standardInner F) := by
    intro a ha
    rcases inner_mem_cases F h2 A hAC hCA a ha (le_inner F h2 A hAC hCA ha) with h|h
    · rw [h]; exact one_mem _
    · rw [h]; exact mem_zpowers _
  have ho:orderOf (standardInner F)=2 := orderOf_eq_prime
    (by simpa only [standardInner,←map_pow,map_one] using congrArg (innerSL F) (SL3.standardInvolution_sq F))
    (standardInner_ne_one F h2)
  simpa only [Nat.card_zpowers,ho] using Subgroup.card_le_of_le hA
private theorem map_centralizer_singleton {G H:Type*} [Group G] [Group H]
    (e:G≃*H) (z:G) :
    (centralizer ({z}:Set G)).map e.toMonoidHom=centralizer ({e z}:Set H) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change e y*e z=e z*e y
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp hy)
  · intro hx
    refine ⟨e.symm x,mem_centralizer_singleton_iff.mpr ?_,e.apply_symm_apply _⟩
    apply e.injective
    simpa only [map_mul,e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hx

/-- The normal-elementary bound for every actual inner involution. -/
theorem card_le_two_of_inner_involution (h2:(2:F)≠0)
    (z:graphExtension F) (hz:orderOf z=2) (hzI:z∈innerPart F)
    (A:Subgroup (graphExtension F)) [IsElementaryAbelian 2 A]
    (hAC:A≤centralizer ({z}:Set (graphExtension F)))
    (hCA:centralizer ({z}:Set (graphExtension F))≤normalizer (A:Set _)) :
    Nat.card A≤2 := by
  obtain ⟨s,hs⟩:=exists_standard_coordinates F h2 z hz hzI
  let e:=MulAut.conj (innerSL F s)⁻¹
  have he:e z=standardInner F := by rw [←hs]; dsimp [e]; simp only [inv_inv]; group
  let A':=A.map e.toMonoidHom
  let : IsElementaryAbelian 2 A':=IsElementaryAbelian.map e.toMonoidHom
  have hC:(centralizer ({z}:Set (graphExtension F))).map e.toMonoidHom=
      centralizer ({standardInner F}:Set (graphExtension F)) := by
    rw [map_centralizer_singleton,he]
  have hAC':A'≤centralizer ({standardInner F}:Set (graphExtension F)) := hC ▸ map_mono hAC
  have hCA':centralizer ({standardInner F}:Set (graphExtension F))≤normalizer (A':Set _) := by
    rw [←hC]
    exact (map_mono hCA).trans (le_normalizer_map _)
  have hc:=card_le_two F h2 A' hAC' hCA'
  rwa [card_map_of_injective e.injective] at hc
end CFSG.Quasithin.ChapterE.Structure.OddDegreeThree.NormalElementary
