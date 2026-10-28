module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ThompsonPairNormalizers
public import Theory.SpecificGroups.PSL3Even.ThompsonCentralCover.NormalizerGeneration
/-! # The original linear core has nontrivial Frattini subgroup
Assuming trivial Frattini makes the core factor in the proved Thompson product
elementary. The original maximum-family argument then puts every ambient
maximum elementary normalizer in M. The two actual root-plane normalizers
generate the component, contradicting its original exclusion from M.
Both centerless PSL₃ and the exceptional central PSL₃(4) cover are treated;
the latter uses the full elementary inverse-image theorem of I.2.2(3b).
No local, kernel, Borel, normalizer or generation input remains.
Source: Aschbacher--Smith 2.5.7, printed p.555, first contradiction.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
private theorem linear_core_frattini_ne_bot_of_cover
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] [CharP F 2] {n:ℕ} (hn:0<n) (hF:Nat.card F=2^n)
    (q:L.subgroupOf H→*PSL(3,F)) (hq:Function.Surjective q)
    (hk:IsPGroup 2 q.ker) (hZ:center (L.subgroupOf H)≤q.ker)
    (hlift:∀W:Subgroup PSL(3,F),IsElementaryAbelian 2 W→IsElementaryAbelian 2 (W.comap q))
    (hJ:elementaryAbelianMaxJ (S:Subgroup H)=((S:Subgroup H)⊓L.subgroupOf H)⊔
      (elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H))
    (hbound:frattini (elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H:Subgroup H)=⊥→
      ∀A∈elementaryAbelianMaxSubgroups ((S:Subgroup H).map H.subtype),normalizer (A:Set G)≤M) :
    frattini (elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H:Subgroup H)≠⊥ := by
  intro hphi
  let K:=L.subgroupOf H
  let C:=elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H
  have hCp:IsPGroup 2 C:=(pCore_isPGroup (p:=2) (G:=H)).to_le inf_le_right
  let : Fact (IsPGroup 2 C):=⟨hCp⟩
  let : IsElementaryAbelian 2 C:=(frattini_eq_bot_iff_isElementaryAbelian (p:=2)).mp hphi
  have hg:K⊔(S:Subgroup H)=⊤:=by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le c.component_le,←hgen]
    rw [←MonoidHom.range_eq_map,H.range_subtype]
  have ho:componentOrbit K (S:Subgroup H)=K:=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl
      (by rw [normalizer_eq_top];exact le_top)) (le_componentOrbit _ _)
  have hc:=c.component.sylow_centralizer_orbit_eq_pCore S hg
  rw [ho] at hc
  have hKC:pCore 2 H≤centralizer (K:Set H):=by rw [←hc];exact inf_le_right
  have hC:C≤centralizer (K:Set H):=inf_le_right.trans hKC
  have hker:((S:Subgroup H)⊓K)⊓C≤q.ker.map K.subtype:=by
    rintro x ⟨hx,hc⟩
    refine ⟨⟨x,hx.2⟩,hZ ?_,rfl⟩
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hC hc y y.property)
  have hnorm (A:Subgroup H) (hA:A∈elementaryAbelianMaxSubgroups (S:Subgroup H)) :
      normalizer (A:Set H)≤M.subgroupOf H:=by
    have ha:=(maxFamily_map_injective_iff H.subtype H.subtype_injective (S:Subgroup H) A).mpr hA
    intro a ha'
    exact hbound hphi _ ha ((A.le_normalizer_map H.subtype) (mem_map_of_mem H.subtype ha'))
  have hKM:=Matrix.PSL3Even.ThompsonCentralCover.component_le_of_maxFamily_normalizers_of_sylow
    S K C (M.subgroupOf H) q hq hk hn hF hJ hC hker hlift hnorm
  apply (c.localSetup hG structural115Input sourceC).outside
  intro l hl
  exact hKM (show (⟨l,c.component_le hl⟩:H)∈K from hl)

theorem MathieuSourceSetup.linear_simple_thompson_core_frattini_ne_bot
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*PSL(3,F)) :
    frattini (elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H:Subgroup H)≠⊥ := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let K:=L.subgroupOf H
  let eK:K≃*PSL(3,F):=(subgroupOfEquivOfLe c.component_le).trans e
  let : K.Normal:=MathieuSourceSetup.linear_nonbinary_component_normal c hG sourceC hempty F hn hF
    (quotientOfLinear F e)
  have hk:IsPGroup 2 eK.toMonoidHom.ker:=by
    rw [(MonoidHom.ker_eq_bot_iff eK.toMonoidHom).mpr eK.injective]
    exact IsPGroup.of_subsingleton 2 _
  have hZ:center K≤eK.toMonoidHom.ker:=by
    have hZ':center PSL(3,F)=⊥:=by
      let :=Atlas.sl_perfect (F:=F) 3 (by decide)
      exact Group.IsPerfect.center_quotient_center_eq_bot (SL(3,F))
    intro k hk
    have he:eK k∈center PSL(3,F):=(centerCongr eK ⟨k,hk⟩).property
    rwa [hZ',mem_bot] at he
  have hlift (W:Subgroup PSL(3,F)) (hW:IsElementaryAbelian 2 W):
      IsElementaryAbelian 2 (W.comap eK.toMonoidHom):=by
    rw [comap_equiv_eq_map_symm']
    let :=hW
    exact IsElementaryAbelian.map _
  exact linear_core_frattini_ne_bot_of_cover c hG sourceC hgen F (by omega) hF
    eK.toMonoidHom eK.surjective hk hZ hlift
    (MathieuSourceSetup.linear_simple_thompson_product c hG sourceC hempty hgen F hn hF e)
    (MathieuSourceSetup.linear_simple_maxFamily_normalizers_le_of_frattini_eq_bot c hG sourceC hempty hgen F hn hF e)

open Matrix.PSL3Four.ElementaryParabolic in
theorem MathieuSourceSetup.linear_four_thompson_core_frattini_ne_bot
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (e:L⧸center L≃*Matrix.PSL3Four.PSL) :
    frattini (elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H:Subgroup H)≠⊥ := by
  let K:=L.subgroupOf H
  let eK:K≃*L:=subgroupOfEquivOfLe c.component_le
  have hF:Nat.card Matrix.PSL3Four.F=2^2:=by simpa using Matrix.PSL3Four.card_F
  let : K.Normal:=MathieuSourceSetup.linear_nonbinary_component_normal c hG sourceC hempty
    Matrix.PSL3Four.F (by decide : 1<2) hF e
  let q:K→*Matrix.PSL3Four.PSL:=(centerProjection e).comp eK.toMonoidHom
  have hq:Function.Surjective q:=(centerProjection_surjective e).comp eK.surjective
  have hZL:IsPGroup 2 (center L):=by
    rw [MathieuSourceSetup.center_eq_twoCore c hG sourceC hempty]
    exact pCore_isPGroup
  have hk:IsPGroup 2 q.ker:=by
    dsimp only [q]
    change IsPGroup 2 ((centerProjection e).ker.comap eK.toMonoidHom)
    rw [centerProjection_ker]
    exact hZL.comap_of_injective eK.toMonoidHom eK.injective
  have hZ:center K≤q.ker:=by
    intro k hk
    change eK k∈(centerProjection e).ker
    rw [centerProjection_ker]
    exact (centerCongr eK ⟨k,hk⟩).property
  have hlift (W:Subgroup Matrix.PSL3Four.PSL) (hW:IsElementaryAbelian 2 W):
      IsElementaryAbelian 2 (W.comap q):=by
    let :=hW
    let : IsElementaryAbelian 2 (W.comap (centerProjection e)):=
      MathieuSourceSetup.linear_four_elementary_preimage c hG sourceC hempty e W
    change IsElementaryAbelian 2 ((W.comap (centerProjection e)).comap eK.toMonoidHom)
    rw [comap_equiv_eq_map_symm']
    exact IsElementaryAbelian.map _
  exact linear_core_frattini_ne_bot_of_cover c hG sourceC hgen Matrix.PSL3Four.F (by decide : 0<2) hF
    q hq hk hZ hlift
    (MathieuSourceSetup.linear_four_thompson_product c hG sourceC hempty hgen e)
    (MathieuSourceSetup.linear_four_maxFamily_normalizers_le_of_frattini_eq_bot c hG sourceC hempty hgen e)
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
