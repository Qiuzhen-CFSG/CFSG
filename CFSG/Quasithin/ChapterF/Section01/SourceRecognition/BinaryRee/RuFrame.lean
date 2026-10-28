module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuRootSeed
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSquaring
public import Theory.SpecificGroups.ReeTwo.SemilinearExtensionFrame
public import Theory.SpecificGroups.ReeTwo.CoreFaithfulness

/-!
# The actual first-core Ree frame and marking

The fixed cyclic four subgroup in Q₀Q₅ supplies t with t²=z and
C_{Q₅}(t)=U. The selected conjugate from J.4 supplies an involution b outside
U; its native B₅ orbit generates Q₅. The original B₅ normalizer realizes the
squaring automorphism, so `SemilinearExtensionData.exists_frameCoordinates`
constructs a literal frame in Q₀Q₅. The elementary derived layer then gives
all ten Ree core relations. Finally the verified finite core map is faithful
because its last root is nontrivial, and cardinality makes it an equivalence.

Source: Aschbacher–Smith J.2.4, J.3.6, J.4.1 and J.4.4–5,
printed pp.434,439–442; Parrott (1972), pp.672–674; Shinoda (1975), (2.3),
pp.81–82.
-/

public section
noncomputable section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

private theorem map_relative_centralizer {K L:Type*} [Group K] [Group L]
    (U V:Subgroup K) (f:K→*L) (hf:Function.Injective f) :
    (U⊓centralizer (V:Set K)).map f=U.map f⊓centralizer (V.map f:Set L) := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    refine ⟨mem_map_of_mem f hx.1,mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨v,hv,rfl⟩
    simpa only [map_mul] using congrArg f (mem_centralizer_iff.mp hx.2 v hv)
  · rintro _ ⟨⟨x,hx,rfl⟩,hc⟩
    refine mem_map_of_mem f ⟨hx,mem_centralizer_iff.mpr ?_⟩
    intro v hv
    apply hf
    simpa only [map_mul] using mem_centralizer_iff.mp hc (f v) (mem_map_of_mem f hv)

/-- A literal ten-root frame in the original first core, preserving the fixed
cyclic root and the original central line. -/
theorem SourceChoice.exists_firstCore_frame (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    ∃ (t z:fiveHyperplane d B5) (a:Fin 4→fiveHyperplane d B5),
      (t:G)∈centralizer (B5Image B5:Set G) ∧ orderOf t=4 ∧ t^2=z ∧
      zpowers (z:G)=d.toTypeRuSetup.Z ∧ ReeTwo.FrameCoordinates a t z ∧
      ReeTwo.CoreRelations (ReeTwo.frameRoots a t z) ∧ z≠1 := by
  obtain ⟨t,htK,htA,htP,ht4,htZ,hzgen,htgen,htQ0⟩:=exists_firstCore_fixed_root d B5
  obtain ⟨b,hbD,hb2,hbU⟩:=s.exists_Q₅_involution B5 hi
  let K:=fiveHyperplane d B5
  let R:Subgroup K:=(Q₅ d B5).subgroupOf K
  have hPK:Q₅ d B5≤K:=le_sup_right
  let e:R≃*Q₅ d B5:=subgroupOfEquivOfLe hPK
  let bR:R:=e.symm b
  let tK:K:=⟨t,htK⟩
  let z:K:=tK^2
  obtain ⟨ρ,σ,hρ,hσsq,hρt,hσt,hσR⟩:=exists_firstCore_squaring_action d B5 tK ht4 htgen
  let D:=(_root_.commutator R).map R.subtype
  let Z:Subgroup K:=(center R).map R.subtype
  have hRmap:R.map K.subtype=Q₅ d B5:=map_subgroupOf_eq_of_le hPK
  have hDmap:D.map K.subtype=d.toTypeRuSetup.U:=by
    dsimp only [D]
    rw [map_subtype_commutator,map_commutator,hRmap,Q₅_derived_eq_U]
  have hecomp:(Q₅ d B5).subtype.comp e.toMonoidHom=K.subtype.comp R.subtype:=rfl
  have hcenter_e:(center R).map e.toMonoidHom=center (Q₅ d B5):=by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (centerCongr e ⟨y,hy⟩).property
    · intro hx
      exact ⟨e.symm x,(centerCongr e.symm ⟨x,hx⟩).property,e.apply_symm_apply x⟩
  have hZmap:Z.map K.subtype=d.toTypeRuSetup.Z:=by
    dsimp only [Z]
    rw [map_map, ← hecomp, ← map_map, hcenter_e, Q₅_center_eq_Z]
  have hDsub:D=d.toTypeRuSetup.U.subgroupOf K:=by
    rw [←hDmap]
    exact (comap_map_eq_self_of_injective K.subtype_injective D).symm
  have hZsub:Z=d.toTypeRuSetup.Z.subgroupOf K:=by
    rw [←hZmap]
    exact (comap_map_eq_self_of_injective K.subtype_injective Z).symm
  have hRcard:Nat.card R=512:=(Nat.card_congr e.toEquiv).trans (card_Q₅ d B5)
  have hRtwo:IsPGroup 2 R:=IsPGroup.of_card (n:=9) hRcard
  let : Group.IsNilpotent R:=hRtwo.isNilpotent
  let : Group.IsNilpotent (Q₅ d B5):=(hRtwo.of_equiv e).isNilpotent
  have hclass:Group.nilpotencyClass R=3:=by
    have hlo:=Group.nilpotencyClass_le_of_surjective e.toMonoidHom e.surjective
    have hhi:=Group.nilpotencyClass_le_of_surjective e.symm.toMonoidHom e.symm.surjective
    rw [(Q₅_parrott_structure d B5).1] at hlo hhi
    omega
  have hZK:d.toTypeRuSetup.Z≤K:=(d.ru2.natural.kernel_le.trans (U_le_fiveHyperplane d B5))
  have hCZ:centralizer (R:Set K)=Z:=by
    apply map_injective K.subtype_injective
    rw [←top_inf_eq (centralizer (R:Set K)),map_relative_centralizer _ _ _ K.subtype_injective,
      ←MonoidHom.range_eq_map,range_subtype,hRmap,hZmap,centralizer_Q₅,
      inf_eq_right.mpr hZK]
  have hzZ:z∈Z:=by rw [hZsub]; exact htZ
  have htorder:orderOf tK=4:=by rw [←orderOf_coe]; exact ht4
  have hzorder:orderOf z=2:=by dsimp only [z]; rw [orderOf_pow,htorder]; decide
  have hdata:ReeTwo.SemilinearExtensionData ρ R tK z bR σ:=by
    refine {
      actor_card:=B5Image_card d.card_Z B5
      core_card:=fiveHyperplane_card d B5
      residual_card:=hRcard
      residual_normal:=normal_subgroupOf_of_le_normalizer
        ((fiveHyperplane_le_Q d B5).trans (Q₅_normalized d B5))
      residual_class:=hclass
      invariant:=?_
      center_card:=?_
      derived_card:=?_
      derived_elementary:=?_
      derived_eq:=?_
      derived_commutator:=?_
      center_eq:=?_
      residual_derived_centralizer:=?_
      residual_centralizer:=hCZ
      fixed_central:=?_
      root_outside:=htP
      central_mem:=hzZ
      central_order:=hzorder
      root_square:=rfl
      root_fixed:=hρt
      root_centralizes:=?_
      root_generates:=?_
      root_centralizer:=?_
      root_commutator:=?_
      seed_square:=?_
      seed_outside:=?_
      seed_generates:=?_
      symmetry_invariant:=hσR
      symmetry_squares:=hσsq
      symmetry_root:=hσt }
    · intro a x
      change (ρ a x:G)∈Q₅ d B5 ↔ (x:G)∈Q₅ d B5
      rw [hρ]
      exact ((mem_normalizer_iff.mp (normalizer_commutator_ge_right
        d.toTypeRuSetup.Q (B5Image B5) a.property)) (x:G)).symm
    · change Nat.card Z=2
      rw [←card_map_of_injective K.subtype_injective,hZmap,d.card_Z]
    · change Nat.card D=32
      rw [←card_map_of_injective K.subtype_injective,hDmap,d.ru2.card_U d.card_Z]
    · change IsElementaryAbelian 2 D
      rw [hDsub]
      let := d.elementary_U
      exact IsElementaryAbelian.subgroupOf (U_le_fiveHyperplane d B5)
    · apply map_injective K.subtype_injective
      rw [hDmap,map_subtype_commutator,firstCore_derived]
    · apply map_injective K.subtype_injective
      rw [map_commutator,hDmap,hZmap,←MonoidHom.range_eq_map,range_subtype,
        commutator_comm,firstCore_commutator_U]
    · apply map_injective K.subtype_injective
      rw [hZmap,firstCore_center]
    · apply map_injective K.subtype_injective
      rw [map_relative_centralizer _ _ _ K.subtype_injective,hRmap,hDmap,
        centralizer_U,Q₅_inf_HC]
    · intro x hx
      have hxc:((x:R):G)∈CQ B5:=by
        refine ⟨Q₅_le_Q d B5 x.property,?_⟩
        intro a ha
        have hh:=congrArg (fun q:K=>(q:G)) (hx ⟨a,ha⟩)
        rw [hρ] at hh
        exact mul_inv_eq_iff_eq_mul.mp hh
      have hxZ:= (Q₅_inf_CQ d B5).le ⟨x.property,hxc⟩
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      apply Subtype.ext
      exact ((pCoreIn_le 2 _ (Q₅_le_Q d B5 y.property)) ((x:R):G) hxZ).symm
    · apply mem_centralizer_iff.mpr
      intro u hu
      apply Subtype.ext
      exact (Q₀_le_HC d htQ0).2 u (hDmap ▸ mem_map_of_mem K.subtype hu)
    · apply map_injective K.subtype_injective
      rw [Subgroup.map_sup,hRmap,MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype]
      exact Q₅_sup_fixed_root d B5 t htK htP
    · apply map_injective K.subtype_injective
      rw [map_inf _ _ _ K.subtype_injective,hRmap,map_subtype_centralizer_singleton,
        hDmap,←inf_assoc,inf_eq_left.mpr hPK]
      exact Q₅_fixed_root_centralizer d B5 t htQ0 htP
    · apply map_injective K.subtype_injective
      rw [map_commutator,hRmap,MonoidHom.map_zpowers,hDmap]
      exact Q₅_fixed_root_commutator d B5 t htQ0 htP htA
    · apply e.injective
      rw [← map_pow, e.apply_symm_apply]
      exact hb2
    · intro h
      apply hbU
      have hm:=hDmap ▸ mem_map_of_mem K.subtype (mem_map_of_mem R.subtype h)
      have hbval:((bR:R):G)=(b:G):=congrArg (fun q:Q₅ d B5=>(q:G)) (e.apply_symm_apply b)
      exact hbval ▸ hm
    · apply map_injective K.subtype_injective
      rw [MonoidHom.map_closure,←Set.range_comp,hRmap]
      have he:K.subtype ∘ (fun a:B5Image B5=>ρ a (bR:K))=
          (fun a:B5Image B5=>(a:G)*(b:G)*(a:G)⁻¹):=by
        funext a
        rw [Function.comp_apply]
        have hh:=hρ a (bR:K)
        change ((ρ a (bR:K)):G)=_
        rw [hh]
        have hbval:((bR:R):G)=(b:G):=congrArg (fun q:Q₅ d B5=>(q:G)) (e.apply_symm_apply b)
        rw [hbval]
      rw [he]
      exact Q₅_five_orbit_generates d B5 b hbU
  obtain ⟨a,ha⟩:=hdata.exists_frameCoordinates
  have hzC:z∈center K:=hdata.center_eq ▸ hzZ
  let : IsElementaryAbelian 2 D:=hdata.derived_elementary
  have hrel:=ReeTwo.coreRelations_frameRoots_of_elementary D hdata.derived_eq.ge a tK z ha
    hdata.root_centralizes hzC hdata.root_square (hzorder ▸ pow_orderOf_eq_one z)
  refine ⟨tK,z,a,htA,htorder,rfl,hzgen,ha,hrel,?_⟩
  intro h
  rw [h,orderOf_one] at hzorder
  contradiction

/-- The source first core has the actual Ree ten-root model, including its
original central line and cyclic five-fixed root. -/
theorem SourceChoice.exists_firstCore_marking (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    ∃e:ReeTwo.Core≃*fiveHyperplane d B5,
      zpowers (e (ReeTwo.Core.root 9):G)=d.toTypeRuSetup.Z ∧
      (e (ReeTwo.Core.root 2):G)∈centralizer (B5Image B5:Set G) := by
  obtain ⟨t,z,a,ht,ht4,htz,hzgen,ha,hrel,hz⟩:=s.exists_firstCore_frame B5 hi
  let f:=ReeTwo.Core.lift hrel
  have hf9:f (ReeTwo.Core.root 9)=z:=by
    change ReeTwo.Core.lift hrel (ReeTwo.Core.root 9)=z
    rw [ReeTwo.Core.lift_root]
    rfl
  have hf2:f (ReeTwo.Core.root 2)=t:=by
    change ReeTwo.Core.lift hrel (ReeTwo.Core.root 2)=t
    rw [ReeTwo.Core.lift_root]
    rfl
  have hinj:=ReeTwo.Core.hom_injective_of_last_root f (by rw [hf9]; exact hz)
  have hbij:=hinj.bijective_of_nat_card_le (by rw [ReeTwo.Core.card,fiveHyperplane_card])
  exact ⟨MulEquiv.ofBijective f hbij,by change zpowers (f (ReeTwo.Core.root 9):G)=_; rw [hf9]; exact hzgen,
    by change (f (ReeTwo.Core.root 2):G)∈_; rw [hf2]; exact ht⟩

/-- Apply the constructed marking to the literal embedded O₂(F₁). -/
theorem SourceChoice.F₁_core_equiv_ree (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    Nonempty ((p.F₁ B5).pCoreIn 2≃*ReeTwo.Core) := by
  obtain ⟨e,_,_⟩:=s.exists_firstCore_marking B5 hi
  exact ⟨(MulEquiv.subgroupCongr (s.F₁_core_eq_fiveHyperplane p B5 hi)).trans e.symm⟩

/-- The original TypeRu hypotheses produce the actual first-core Ree marking. -/
theorem first_core_ree_marking_of_typeRu (h:IsTypeRu G) :
    ∃(d:LocalSetup G)(p:Plane d)(B5:Sylow 5 d.toTypeRuSetup.H),
      Nonempty ((p.F₁ B5).pCoreIn 2≃*ReeTwo.Core) := by
  obtain ⟨d,p,⟨s⟩⟩:=source_J4_choice h
  obtain ⟨B5,hi⟩:=s.inverts_sylow_five
  exact ⟨d,p,B5,s.F₁_core_equiv_ree B5 hi⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup
