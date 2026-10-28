module
public import Theory.SpecificGroups.PSL2.BinarySylowEmbedding
public import Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.Extension
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.SpecificGroups.SymplecticFour.FieldComponent
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.Complete
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual.MatrixIdentification
public import Theory.SpecificGroups.Suzuki.TwoRank
/-!
# Fixed components of involutions of binary symplectic four-space

For an inner involution, the actual centralizer embeds in a full point or
plane parabolic. A simple perfect subgroup projects injectively to its SL₂
Levi quotient and therefore has commutative Sylow two-subgroups. An odd graph
involution has a simple Suzuki fixed group of rank at least three. Finally,
the actual field fixed component is the derived smaller symplectic group;
rank at most two forces the binary A₆ endpoint inside Sp₄(4).

The complete involution normal forms supply all conjugators, and the final
conclusion preserves the field action itself. Source: Aschbacher–Smith 2.5.19,
p.561, and 16.1.4, pp.1170–1173.
-/
public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open InvolutionTypes InvolutionCentralizers
namespace Theory.SpecificGroups.SymplecticFour.FixedComponents
variable {K:Type*} [Group K] [Finite K] [IsSimpleGroup K] [Group.IsPerfect K]

omit [Finite K] in
private theorem injective_through_solvable_kernel {G H:Type*} [Group G] [Group H]
    (p:G→*H) [Group.IsSolvable p.ker] (f:K→*G) (hf:Function.Injective f) :
    Function.Injective (p.comp f) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases (inferInstance : (p.comp f).ker.Normal).eq_bot_or_eq_top with h|h
  · exact h
  · let j:=f.codRestrict p.ker (fun x=>by
      have hx:x∈(p.comp f).ker:=h ▸ mem_top x
      exact hx)
    have hj:Function.Injective j:=fun x y hxy=>hf (congrArg Subtype.val hxy)
    exact (Group.IsPerfect.not_isSolvable K (Group.isSolvable_of_isSolvable_injective hj)).elim

variable {F:Type*} [Field F] [Finite F] [CharP F 2]

omit [IsSimpleGroup K] [Group.IsPerfect K] in
private theorem sylow_commutative_of_sl2_embedding
    (f:K→*Matrix.SpecialLinearGroup (Fin 2) F) (hf:Function.Injective f)
    (S:Sylow 2 K) : IsMulCommutative S :=
  Theory.PSL2.binary_sylow_commutative_of_injective
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL.toMonoidHom.comp f)
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL.injective.comp hf) S

private theorem pointLocal_sylow_commutative (f:K→*pointLocal (F:=F))
    (hf:Function.Injective f) (S:Sylow 2 K) : IsMulCommutative S := by
  let : IsElementaryAbelian 2 (pointQuotient (F:=F)).ker:=pointRadical_elementaryAbelian
  exact sylow_commutative_of_sl2_embedding (pointQuotient.comp f)
    (injective_through_solvable_kernel pointQuotient f hf) S

private theorem planeLocal_sylow_commutative (f:K→*planeLocal (F:=F))
    (hf:Function.Injective f) (S:Sylow 2 K) : IsMulCommutative S := by
  let : IsElementaryAbelian 2 (Plane.quotientMap (F:=F)).ker:=Plane.radical_elementaryAbelian
  exact sylow_commutative_of_sl2_embedding (Plane.quotientMap.comp f)
    (injective_through_solvable_kernel Plane.quotientMap f hf) S

private noncomputable def lift_to_local (W:Submodule F (Vector F)) (f:K→*stabilizer W) :
    K→*determinantKernel W where
  toFun x:=⟨(f x).val,⟨f x,
    Abelianization.commutator_subset_ker ((determinantCharacter W).comp f)
      Group.IsPerfect.mem_commutator,rfl⟩⟩
  map_one':=Subtype.ext (congrArg (fun z:stabilizer W=>(z:Sp F)) f.map_one)
  map_mul' x y:=Subtype.ext (congrArg (fun z:stabilizer W=>(z:Sp F)) (f.map_mul x y))

omit [Finite K] [IsSimpleGroup K] [Finite F] [CharP F 2] in
private theorem lift_to_local_injective (W:Submodule F (Vector F))
    (f:K→*stabilizer W) (hf:Function.Injective f) :
    Function.Injective (lift_to_local W f) := by
  intro x y h
  exact hf (Subtype.ext (congrArg (fun z:determinantKernel W=>(z:Sp F)) h))

/-- A simple perfect subgroup of either full parabolic has commutative Sylow two-subgroups. -/
theorem sylow_commutative_of_simple_parabolic_embedding (P:Subgroup (Sp F))
    (hP:IsParabolic P) (f:K→*P) (hf:Function.Injective f) (S:Sylow 2 K) :
    IsMulCommutative S := by
  obtain ⟨g,hp|hp⟩:=hP
  · let e:P≃*pointParabolic (F:=F):=
      (MulEquiv.subgroupCongr hp).trans ((MulAut.conj g).subgroupMap pointParabolic).symm
    let j:=e.toMonoidHom.comp f
    exact pointLocal_sylow_commutative (lift_to_local (point F) j)
      (lift_to_local_injective _ j (e.injective.comp hf)) S
  · let e:P≃*planeParabolic (F:=F):=
      (MulEquiv.subgroupCongr hp).trans ((MulAut.conj g).subgroupMap planeParabolic).symm
    let j:=e.toMonoidHom.comp f
    exact planeLocal_sylow_commutative (lift_to_local (plane F) j)
      (lift_to_local_injective _ j (e.injective.comp hf)) S

/-- The inner fixed subgroup supplies its actual parabolic embedding. -/
theorem sylow_commutative_of_simple_inner_fixed_embedding (g:Sp F) (hg:orderOf g=2)
    (f:K→*(MulAut.conj g).fixedSubgroup) (hf:Function.Injective f) (S:Sylow 2 K) :
    IsMulCommutative S := by
  obtain ⟨P,hP,_,_,hc⟩:=involution_centralizer_parabolic g hg
  have hle:(MulAut.conj g).fixedSubgroup≤P:=by rwa [MulAut.fixedSubgroup_conj]
  exact sylow_commutative_of_simple_parabolic_embedding P hP ((inclusion hle).comp f)
    ((inclusion_injective hle).comp hf) S
end Theory.SpecificGroups.SymplecticFour.FixedComponents

namespace Theory.SpecificGroups.SymplecticFour.FixedComponents
open DiagramAutomorphisms DiagramAutomorphisms.FieldFixedResidual
variable {F:Type*} [Field F] [Finite F] [CharP F 2]

/-- The actual field component with two-rank at most two is the binary A₆ endpoint. -/
theorem field_component_of_rank_two {m:ℕ} (hm:1≤m)
    (hF:Nat.card F=2^(2*m)) (B:Subgroup (Sp F))
    (hB:IsComponentIn B (representative (F:=F) m).fixedSubgroup)
    (hr:primeRank 2 B≤2) : m=1 ∧ Nonempty (B≃*alternatingGroup (Fin 6)) := by
  have hs:=FieldComponent.component_eq_embedded hm hF B hB
  let K:=halfField (F:=F) m
  let j:=coefficientInclusion K
  let ed:commutator (Sp K)≃*B:=
    ((commutator (Sp K)).equivMapOfInjective j (coefficientInclusion_injective K)).trans
      (MulEquiv.subgroupCongr hs.symm)
  have hK:Nat.card K=2^m:=card_halfField hm hF
  have hsmall:m=1 := by
    by_contra hne
    have hge:2≤m:=by omega
    have hrD:primeRank 2 (commutator (Sp K))≤2:=by rw [primeRank_equiv 2 ed];exact hr
    rw [EvenTwoRank.derived_rank hK hge] at hrD
    omega
  subst m
  have hF4:Nat.card F=4:=by simpa using hF
  exact ⟨rfl,⟨(MulEquiv.subgroupCongr hs).trans
    (FieldComponent.binaryEmbeddedEquivAlternatingSix hF4)⟩⟩

/-- A component of an odd graph fixed group is the full Suzuki group and has rank greater than two. -/
theorem graph_component_rank_gt_two {m:ℕ} (hm:0<m)
    (hF:Nat.card F=2^(2*m+1)) (B:Subgroup (Sp F))
    (hB:IsComponentIn B (GraphFieldFixedResidual.graphFieldAut (F:=F) m).fixedSubgroup) :
    2<primeRank 2 B := by
  let e:=GraphFieldFixedResidual.fixedEquivOfBinaryModel m hF
    (GraphFieldFixedResidual.fixedSuzukiEquiv m)
  let : IsSimpleGroup (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m):=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  let : IsSimpleGroup (GraphFieldFixedResidual.graphFieldAut (F:=F) m).fixedSubgroup:=e.isSimpleGroup
  have htop:B.subgroupOf (GraphFieldFixedResidual.graphFieldAut (F:=F) m).fixedSubgroup=⊤ := by
    rcases hB.2.1.eq_bot_or_top_of_isSimpleGroup inferInstance with hb|ht
    · have hbot:B=⊥:=by
        simpa only [map_subgroupOf_eq_of_le hB.1,Subgroup.map_bot] using
          congrArg (map (GraphFieldFixedResidual.graphFieldAut (F:=F) m).fixedSubgroup.subtype) hb
      exact (hB.ne_bot hbot).elim
    · exact ht
  let eB:B≃*BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m:=
    (subgroupOfEquivOfLe hB.1).symm.trans
      ((MulEquiv.subgroupCongr htop).trans (Subgroup.topEquiv.trans e))
  rw [primeRank_equiv 2 eB,BenderSuzuki.MatrixGroups.suzuki_two_rank m hm]
  omega

omit [Finite F] [CharP F 2] in
private theorem component_map_fixed (e:MulAut (Sp F)) (a b:MulAut (Sp F))
    (he:MulAut.congr e a=b) (B:Subgroup (Sp F)) (hB:IsComponentIn B a.fixedSubgroup) :
    IsComponentIn (B.map e.toMonoidHom) b.fixedSubgroup := by
  have hfix:a.fixedSubgroup.map e.toMonoidHom=b.fixedSubgroup := by
    ext x
    rw [mem_map_equiv,MulAut.mem_fixedSubgroup,MulAut.mem_fixedSubgroup]
    rw [←e.injective.eq_iff]
    have hx:=congrArg (fun d:MulAut (Sp F)=>d x) he
    change e (a (e.symm x))=b x at hx
    rw [hx,e.apply_symm_apply]
  exact hfix ▸ hB.map e

omit [Finite F] [CharP F 2] in
private theorem exists_conjugator (a b:MulAut (Sp F)) (h:IsConj a b) :
    ∃e:MulAut (Sp F),MulAut.congr e a=b := by
  obtain ⟨e,he⟩:=isConj_iff.mp h
  refine ⟨e,?_⟩
  apply MulEquiv.ext
  intro x
  exact congrArg (fun d:MulAut (Sp F)=>d x) he

/-- The original simple source Sylow shape forces the field involution of Sp₄(4), retaining conjugacy. -/
theorem component_of_source_sylow_shape {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (a:MulAut (Sp F)) (ha:orderOf a=2)
    (B:Subgroup (Sp F)) (hB:IsComponentIn B a.fixedSubgroup) [IsSimpleGroup B]
    (hr:primeRank 2 B≤2) (P:Sylow 2 B)
    (hnc:¬∀x y:P,x^2=1→y^2=1→Commute x y) :
    n=2 ∧ Nonempty (B≃*alternatingGroup (Fin 6)) ∧
      IsConj a (representative (F:=F) 1) := by
  rcases InvolutionNormalForms.involution_normalForms hF hn a ha with
    ⟨g,hg,he⟩|⟨heven,hconj⟩|⟨hodd,hconj⟩
  · have hle:B≤(MulAut.conj g).fixedSubgroup:=he ▸ hB.1
    let : IsQuasisimple B:=hB.quasisimple
    let : IsMulCommutative P:=sylow_commutative_of_simple_inner_fixed_embedding g hg
      (inclusion hle) (inclusion_injective hle) P
    exact (hnc (fun x y _ _=>Commute.all x y)).elim
  · obtain ⟨e,he⟩:=exists_conjugator a _ hconj
    have hmul:2*(n/2)=n:=Nat.mul_div_cancel' (even_iff_two_dvd.mp heven)
    have hm:1≤n/2:=by omega
    have hcard:Nat.card F=2^(2*(n/2)):=by rw [hmul];exact hF
    let B':=B.map e.toMonoidHom
    let eB:B≃*B':=e.subgroupMap B
    have hB':IsComponentIn B' (representative (F:=F) (n/2)).fixedSubgroup:=
      component_map_fixed e a _ he B hB
    have hr':primeRank 2 B'≤2:=by rw [←primeRank_equiv 2 eB];exact hr
    obtain ⟨hn1,⟨d⟩⟩:=field_component_of_rank_two hm hcard B' hB' hr'
    have hn2:n=2:=by omega
    refine ⟨hn2,⟨eB.trans d⟩,?_⟩
    change IsConj a (representative (F:=F) (n/2)) at hconj
    rwa [hn1] at hconj
  · obtain ⟨m,hm⟩:=hodd
    have hnm:n=2*m+1:=hm
    have hmpos:0<m:=by omega
    obtain ⟨e,he⟩:=exists_conjugator a _ hconj
    let B':=B.map e.toMonoidHom
    let eB:B≃*B':=e.subgroupMap B
    have hB':IsComponentIn B' (GraphFieldFixedResidual.graphFieldAut (F:=F) m).fixedSubgroup := by
      have h:=component_map_fixed e a _ he B hB
      change IsComponentIn B' (ExceptionalGraph.graphAut^(2*m+1)).fixedSubgroup
      rw [hnm] at h
      exact h
    have hr':primeRank 2 B'≤2:=by rw [←primeRank_equiv 2 eB];exact hr
    exact (not_lt_of_ge hr' (graph_component_rank_gt_two hmpos (hnm ▸ hF) B' hB')).elim
end Theory.SpecificGroups.SymplecticFour.FixedComponents
