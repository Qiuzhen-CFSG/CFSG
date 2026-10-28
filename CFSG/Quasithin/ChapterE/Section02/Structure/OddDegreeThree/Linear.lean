module
public import CFSG.Quasithin.ChapterE.Section02.Structure.OddDegreeThree.GraphCentralizer
public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.CentralizerSource
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.PSL3.OddSylowCenter
public import Theory.SpecificGroups.PSL3.OddSolvableGeneration
public import Theory.SpecificGroups.ProjectiveLinearInvolutions
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.SplitMonomial
/-!
# The normal odd linear degree-three source row in E.2.2

Two proper solvable Sylow overgroups exclude the inner ambient group.
The source's normal simple component and trivial two-core then give the
literal full graph-extension realization. Its proved inner involution
centralizer maximality identifies the original unique maximal overgroup.
A split monomial overgroup excludes primes congruent to one modulo four.
The actual semidihedral Sylow center yields the exact centralizer of
Z(T∩K), and a prescribed Sylow actor has a genuine inverse-transpose part.

All stored fields, the original normal component, maximal overgroup and
conjugation maps are retained. The prime three is included; no cyclicity
of the quaternion two-core in its GL₂ centralizer is asserted.
Source: Aschbacher–Smith E.2.2(2d), printed pp.215–216.
-/
public section
noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups Pointwise
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
namespace CFSG.Quasithin.ChapterE.Structure.OddDegreeThree
variable {H:Type*} [Group H] [Finite H]

private theorem not_minimal_of_solvable_pair (T:Sylow 2 H)
    (hP:ChapterB.IsMinimalParabolicOver T ⊤) (hns:¬Group.IsSolvable H)
    (S:Sylow 2 H) (A B:Subgroup H) (hSA:(S:Subgroup H)≤A)
    (hSB:(S:Subgroup H)≤B) (hA:Group.IsSolvable A) (hB:Group.IsSolvable B)
    (hAB:A⊔B=⊤) : False := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H S T
  let e := MulAut.conj g
  have heT : (S:Subgroup H).map e.toMonoidHom=(T:Subgroup H) := congrArg Sylow.toSubgroup hg
  let M:=ChapterB.minimalParabolicMax T hP
  have proper (A:Subgroup H) (ha:Group.IsSolvable A) : A≠⊤ := by
    intro he
    let _ : Group.IsSolvable (⊤:Subgroup H) := he ▸ ha
    exact hns (Group.isSolvable_of_surjective (f:=(topEquiv (G:=H)).toMonoidHom) topEquiv.surjective)
  have leM (A:Subgroup H) (ha:Group.IsSolvable A) (hta:(S:Subgroup H)≤A) :
      A.map e.toMonoidHom≤M := by
    have ha' : Group.IsSolvable (A.map e.toMonoidHom) := by
      let _ := ha
      exact Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective A)
    apply hP.1.le_maximal ⟨(ChapterB.minimalParabolicMax_spec T hP).2,
      (ChapterB.minimalParabolicMax_spec T hP).1.covBy_top⟩
    · rw [← heT]
      exact map_mono hta
    · exact lt_top_iff_ne_top.mpr (proper _ ha')
  have hh := sup_le (leM A hA hSA) (leM B hB hSB)
  rw [← Subgroup.map_sup,hAB,map_top_of_surjective _ e.surjective] at hh
  exact (ChapterB.minimalParabolicMax_spec T hP).1.ne_top (top_unique hh)

/-- The original normal odd PSL₃ component must have a genuine outer actor. -/
theorem linear_ne_top (T:Sylow 2 H) (hP:ChapterB.IsMinimalParabolicOver T ⊤)
    (K:Subgroup H) [IsSimpleGroup K] {p:ℕ} (ho:Odd p)
    (hm:ClassicalGroup.IsPSL K 3 p) : K≠⊤ := by
  intro hK
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let f : H≃*PSL(3,F) := topEquiv.symm.trans ((MulEquiv.subgroupCongr hK.symm).trans e)
  let _ : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
  let _ : Group.IsPerfect PSL(3,F) := Atlas.psl_perfect 3 (by decide)
  have hns : ¬Group.IsSolvable H := by
    intro hs
    let _ := hs
    exact Group.IsPerfect.not_isSolvable PSL(3,F)
      (Group.isSolvable_of_surjective (f:=f.toMonoidHom) f.surjective)
  obtain ⟨S,A,B,hSA,hSB,hA,hB,hAB⟩ :=
    Matrix.PSL3.OddSolvableGeneration.exists_solvable_generating_pair F
      (Field.two_ne_zero_of_odd_card F (hF ▸ ho))
  apply not_minimal_of_solvable_pair T hP hns
    (S.mapSurjective (f:=f.symm.toMonoidHom) f.symm.surjective)
    (A.map f.symm.toMonoidHom) (B.map f.symm.toMonoidHom)
    (map_mono hSA) (map_mono hSB)
  · let _ := hA
    exact Group.isSolvable_of_surjective (f.symm.toMonoidHom.subgroupMap_surjective A)
  · let _ := hB
    exact Group.isSolvable_of_surjective (f.symm.toMonoidHom.subgroupMap_surjective B)
  · rw [← Subgroup.map_sup,hAB,map_top_of_surjective _ f.symm.surjective]

/-- The normal component and its Sylow supplement have the literal full graph-extension marking. -/
theorem linear_graph_extension (T:Sylow 2 H) (hP:ChapterB.IsMinimalParabolicOver T ⊤)
    (K:Subgroup H) [K.Normal] [IsSimpleGroup K]
    (hgen:K⊔(T:Subgroup H)=⊤) (hcore:pCore 2 H=⊥)
    {p:ℕ} (hp:p.Prime) (ho:Odd p)
    {F:Type} [Field F] [Finite F] (hF:Nat.card F=p) (e:K≃*PSL(3,F)) :
    ∃f:H≃*graphExtension F, K.map f.toMonoidHom=innerPart F := by
  let _ : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
  let _ : Group.IsPerfect PSL(3,F) := Atlas.psl_perfect 3 (by decide)
  let _ : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f:=e.symm.toMonoidHom) e.symm.surjective
  have hfit := (simple_two_quotient_structure K (Group.IsPerfect.not_isMulCommutative K)
    (isPGroup_quotient_of_sup_eq_top K (T:Subgroup H) T.isPGroup' hgen) hcore).1
  let ef := (MulEquiv.subgroupCongr hfit).trans e
  let _ : IsSimpleGroup (generalizedFitting H) := ef.isSimpleGroup
  obtain ⟨f⟩ := exists_mulEquiv_graphExtension T (hfit ▸ hgen)
    (hfit ▸ linear_ne_top T hP K ho ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩) hp ho hF ef
  refine ⟨f,?_⟩
  rw [← hfit,map_generalizedFitting_equiv,generalizedFitting_eq_innerPart]

/-- The original unique maximal Sylow overgroup is the full ambient
centralizer of an inner involution. -/
theorem linear_involution_centralizer
    (T:Sylow 2 H) (hP:ChapterB.IsMinimalParabolicOver T ⊤)
    (K:Subgroup H) [K.Normal] [IsSimpleGroup K]
    (hgen:K⊔(T:Subgroup H)=⊤) (hcore:pCore 2 H=⊥)
    {p:ℕ} (hp:p.Prime) (ho:Odd p) (hm:ClassicalGroup.IsPSL K 3 p) :
    ∃t:K,orderOf t=2 ∧ (t:H)∈(T:Subgroup H) ∧
      (T:Subgroup H)≤centralizer ({(t:H)}:Set H) ∧
      ChapterB.minimalParabolicMax T hP=centralizer ({(t:H)}:Set H) ∧
      (ChapterB.minimalParabolicMax T hP).subgroupOf K=centralizer ({t}:Set K) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let _ : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
  obtain ⟨f,hf⟩ := linear_graph_extension T hP K hgen hcore hp ho hF e
  have heven : 2∣Nat.card K := by
    rw [Nat.card_congr e.toEquiv]
    exact Matrix.ProjectiveSpecialLinearGroup.two_dvd_card_fin_three F
      (Field.two_ne_zero_of_odd_card F (hF ▸ ho))
  obtain ⟨t,ht,htT,hTt⟩ := normal_even_subgroup_central_sylow_involution T K heven
  have hto : orderOf t=2 := orderOf_eq_prime_iff.mpr ht.symm
  have htH : orderOf (t:H)=2 := (orderOf_injective K.subtype K.subtype_injective t).trans hto
  have hzI : f (t:H)∈innerPart F := hf ▸ mem_map_of_mem f.toMonoidHom t.property
  have hmax := (isCoatom_centralizer_equiv_iff f (t:H)).mp
    (GraphCentralizer.isCoatom F (Field.two_ne_zero_of_odd_card F (hF ▸ ho)) _
      ((orderOf_injective f.toMonoidHom f.injective (t:H)).trans htH) hzI)
  have hCM : centralizer ({(t:H)}:Set H)≤ChapterB.minimalParabolicMax T hP :=
    hP.1.le_maximal ⟨(ChapterB.minimalParabolicMax_spec T hP).2,
      (ChapterB.minimalParabolicMax_spec T hP).1.covBy_top⟩ hTt hmax.lt_top
  have hM : ChapterB.minimalParabolicMax T hP=centralizer ({(t:H)}:Set H) :=
    (hmax.le_iff_eq (ChapterB.minimalParabolicMax_spec T hP).1.ne_top).mp hCM
  refine ⟨t,hto,htT,hTt,hM,?_⟩
  rw [hM]
  ext x
  change (x:H)∈centralizer ({(t:H)}:Set H) ↔ x∈centralizer ({t}:Set K)
  simp only [mem_centralizer_singleton_iff,Subtype.ext_iff]
  rfl

/-- The split congruence would provide a proper solvable full-Sylow overgroup
that moves the central involution. Thus the source prime is three modulo four. -/
theorem linear_congruence
    (T:Sylow 2 H) (hP:ChapterB.IsMinimalParabolicOver T ⊤)
    (K:Subgroup H) [K.Normal] [IsSimpleGroup K]
    (hgen:K⊔(T:Subgroup H)=⊤) (hcore:pCore 2 H=⊥)
    {p:ℕ} (hp:p.Prime) (ho:Odd p) (hm:ClassicalGroup.IsPSL K 3 p) : p%4=3 := by
  obtain ⟨t,hto,_,hTt,hM,_⟩ := linear_involution_centralizer T hP K hgen hcore hp ho hm
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let _ : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
  obtain ⟨f,hf⟩ := linear_graph_extension T hP K hgen hcore hp ho hF e
  have hm : p%4=1 ∨ p%4=3 := by obtain ⟨k,hk⟩:=ho; omega
  rcases hm with hbad|hgood
  · let S := T.mapSurjective (f:=f.toMonoidHom) f.surjective
    let z := f (t:H)
    have hz : orderOf z=2 := (orderOf_injective f.toMonoidHom f.injective _).trans
      ((orderOf_injective K.subtype K.subtype_injective t).trans hto)
    have hzI : z∈innerPart F := hf ▸ mem_map_of_mem f.toMonoidHom t.property
    have hSz : (S:Subgroup (graphExtension F))≤centralizer ({z}:Set (graphExtension F)) := by
      rintro x ⟨y,hy,rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      exact (map_mul f y (t:H)).symm.trans
        ((congrArg f (mem_centralizer_singleton_iff.mp (hTt hy))).trans (map_mul f (t:H) y))
    obtain ⟨A,hSA,hsol,hmix⟩ :=
      ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerGenerationGeometry.solvableMixing_of_card_mod_four_eq_one
        F (hF ▸ hbad) S z hz hzI hSz
    have hne : A≠⊤ := by
      intro he
      let _ : Group.IsSolvable (⊤:Subgroup (graphExtension F)) := he ▸ hsol
      let _ : Group.IsSolvable (graphExtension F) := Group.isSolvable_of_surjective
        (f:=(topEquiv (G:=graphExtension F)).toMonoidHom) topEquiv.surjective
      exact Group.IsPerfect.not_isSolvable (innerPart F) inferInstance
    have hpre : A.comap f.toMonoidHom≠⊤ := by
      intro he
      apply hne
      rw [← map_comap_eq_self_of_surjective (f:=f.toMonoidHom) f.surjective A,he,
        map_top_of_surjective _ f.surjective]
    have hAM : A.comap f.toMonoidHom≤ChapterB.minimalParabolicMax T hP :=
      hP.1.le_maximal ⟨(ChapterB.minimalParabolicMax_spec T hP).2,
        (ChapterB.minimalParabolicMax_spec T hP).1.covBy_top⟩
        (fun x hx=>hSA (mem_map_of_mem f.toMonoidHom hx)) (lt_top_iff_ne_top.mpr hpre)
    have hAC : A≤centralizer ({z}:Set (graphExtension F)) := by
      intro x hx
      obtain ⟨y,rfl⟩:=f.surjective x
      have hy : y∈centralizer ({(t:H)}:Set H) := hM ▸ hAM hx
      apply mem_centralizer_singleton_iff.mpr
      exact (map_mul f y (t:H)).symm.trans
        ((congrArg f (mem_centralizer_singleton_iff.mp hy)).trans (map_mul f (t:H) y))
    have he := ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerGenerationGeometry.eq_top_of_mixing
      F z (centralizer ({z}:Set (graphExtension F))) le_rfl (hmix.mono F hAC)
    have hc := GraphCentralizer.isCoatom F (Field.two_ne_zero_of_odd_card F (hF ▸ ho)) z hz hzI
    exact (hc.ne_top he).elim
  · exact hgood

/-- E.2.2(2d), with the original Sylow-center centralizer in the linear case. -/
theorem linear
    (T:Sylow 2 H) (hP:ChapterB.IsMinimalParabolicOver T ⊤)
    (K:Subgroup H) [K.Normal] [IsSimpleGroup K]
    (hgen:K⊔(T:Subgroup H)=⊤) (hcore:pCore 2 H=⊥)
    {p:ℕ} (hp:p.Prime) (ho:Odd p) (hm:ClassicalGroup.IsPSL K 3 p) :
    p%4=3 ∧ (ChapterB.minimalParabolicMax T hP).subgroupOf K =
      centralizer ((center ((T:Subgroup H).subgroupOf K)).map
        ((T:Subgroup H).subgroupOf K).subtype : Set K) := by
  have hmod := linear_congruence T hP K hgen hcore hp ho hm
  obtain ⟨t,hto,htT,hTt,_,hMK⟩ := linear_involution_centralizer T hP K hgen hcore hp ho hm
  refine ⟨hmod,?_⟩
  let R := (T:Subgroup H).subgroupOf K
  have hR : Nat.card (center R)=2 := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    obtain ⟨P,hP⟩ := T.exists_subgroupOf_eq_of_normal K
    let P' := P.mapSurjective (f:=e.toMonoidHom) e.surjective
    let eP : P≃*P' := (P:Subgroup K).equivMapOfInjective e.toMonoidHom e.injective
    change Nat.card (center ((T:Subgroup H).subgroupOf K))=2
    rw [← hP,Nat.card_congr (Subgroup.centerCongr eP).toEquiv]
    exact Matrix.PSL3.OddSylowCenter.card_center F (hF ▸ hmod) P'
  let Z := (center R).map R.subtype
  have htZ : t∈Z := by
    refine ⟨⟨t,htT⟩,mem_center_iff.mpr ?_,rfl⟩
    intro r
    apply Subtype.ext
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hTt r.property)
  have hZ : Z=zpowers t := by
    apply (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr htZ) ?_).symm
    rw [card_map_of_injective R.subtype_injective,Nat.card_zpowers,hto]
    exact hR.le
  rw [hMK]
  change centralizer ({t}:Set K)=centralizer (Z:Set K)
  rw [hZ,zpowers_eq_closure,centralizer_closure]

/-- A Sylow actor has a genuine inverse-transpose part in the literal
faithful graph-extension realization; its inner component is retained. -/
theorem linear_graph_actor (T:Sylow 2 H) (hP:ChapterB.IsMinimalParabolicOver T ⊤)
    (K:Subgroup H) [K.Normal] [IsSimpleGroup K]
    (hgen:K⊔(T:Subgroup H)=⊤) (hcore:pCore 2 H=⊥)
    {p:ℕ} (hp:p.Prime) (ho:Odd p)
    {F:Type} [Field F] [Finite F] (hF:Nat.card F=p) (e:K≃*PSL(3,F)) :
    ∃f:H≃*graphExtension F, K.map f.toMonoidHom=innerPart F ∧
      ∃t:T, ∃g:PSL(3,F), (f (t:H)).val=MulAut.conj g*Matrix.PSL3.OuterSolvable.graph F ∧
        (f (t:H)).val∉MulAut.innerSubgroup PSL(3,F) := by
  obtain ⟨f,hf⟩ := linear_graph_extension T hP K hgen hcore hp ho hF e
  have hTK : ¬(T:Subgroup H)≤K := by
    intro hh
    have he : K=⊤ := by simpa only [sup_eq_left.mpr hh] using hgen
    exact linear_ne_top T hP K ho ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩ he
  obtain ⟨t,htT,htK⟩ := SetLike.not_le_iff_exists.mp hTK
  have hti : (f t).val∉MulAut.innerSubgroup PSL(3,F) := by
    intro h
    have hm : f t∈K.map f.toMonoidHom := hf ▸ h
    exact htK ((mem_map_iff_mem f.injective).mp hm)
  obtain ⟨i,hi,c,hc,hic⟩ := mem_sup_of_normal_left.mp (f t).property
  obtain ⟨g,rfl⟩ := hi
  obtain ⟨n,rfl⟩ := (isOfFinOrder_of_finite _).mem_powers_iff_mem_zpowers.mpr hc
  change MulAut.conj g * Matrix.PSL3.OuterSolvable.graph F ^ n = (f t).val at hic
  rw [pow_eq_pow_mod n (Matrix.PSL3.OuterSolvable.graph_sq F)] at hic
  have hn : n%2=0 ∨ n%2=1 := by omega
  rcases hn with hn|hn
  · simp only [hn,pow_zero,mul_one] at hic
    exact (hti (hic ▸ ⟨g,rfl⟩)).elim
  · refine ⟨f,hf,⟨t,htT⟩,g,?_,hti⟩
    simpa only [hn,pow_one] using hic.symm
end CFSG.Quasithin.ChapterE.Structure.OddDegreeThree
