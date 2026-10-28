module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.SeedCentralizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Natural.FixedLifting
public import Theory.Representation.CentralCoverOriginalAction.Quadratic
public import Theory.Representation.SL2NaturalOffenders.Semilinear
public import Theory.Representation.SL2NaturalOffenders.LinearLifts
public import Theory.Representation.SemilinearFixedPointCentralizer
public import Theory.GroupTheory.PCoreNormalizerAction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.SemilinearRigidity

/-!
# Odd seed-centralizing actors on the original natural pair

For an odd element of the maximal local group centralizing Ω₁Z(T), the
index-two diagonal fixes every stabilizer-fixed natural coordinate. Fixed
lifting through the retained central cover and fixed-field descent kill
its coefficient automorphism. A linear intertwiner makes the component
action inner. Applying the same argument to the original exchanger conjugate
proves innerness on both literal factors of L₀/O₂(L₀).

No Hall placement or seed-centralizer identity is assumed. The consumer
`SeedFaithfulness` lifts the resulting inner Hall-subgroup action to L₀.
Source: Aschbacher–Smith 10.1.2(5), 10.2.3, printed pp.742,745–746.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

private theorem moved_normalized {b : G} (hbM : b ∈ D.maximalLocal)
    (hbL : b ∈ normalizer (L : Set G)) :
    b ∈ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hbM),
    mem_normalizer_iff_map_conj_eq.mp hbL]

private theorem partner_normalized
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    {b : G} (hbM : b ∈ D.maximalLocal) (hbL : b ∈ normalizer (L : Set G)) :
    b ∈ normalizer ((⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom : Set G) := by
  have htM := le_normalizer_componentOrbit L T ht
  have hpair := source_nonnormal_maximal_pair D hn ht htn (b*t)
    (D.maximalLocal.mul_mem hbM htM)
  have hL : (L.map (MulAut.conj t).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      L.map (MulAut.conj t).toMonoidHom := by
    change (L.conjBy t).conjBy b = L.conjBy t
    change L.conjBy (b*t) = L ∨ L.conjBy (b*t) = L.conjBy t at hpair
    rw [conjBy_mul] at hpair
    rcases hpair with he | he
    · have hfix : L.conjBy b = L := mem_normalizer_iff_map_conj_eq.mp hbL
      have heq : L.conjBy t = L := map_injective (MulAut.conj b).injective
        (he.trans hfix.symm)
      exact he.trans heq.symm
    · exact he
  simp only [MulEquiv.toMonoidHom_eq_coe] at hL
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,MulEquiv.toMonoidHom_eq_coe,
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule htM),
    map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hbM),hL]

omit [Finite F] in
private theorem seed_centralizer_fixed_coordinates
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (d : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    {b : G} (hbM : b ∈ D.maximalLocal) (hbL : b ∈ normalizer (L : Set G))
    (hbZ : b ∈ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (w : (⁅D.fullModule,L⁆ : Subgroup G))
    (hw : (w:G) ∈ centralizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G)) :
    d.coordinates ⟨b*w*b⁻¹,(mem_normalizer_iff.mp (moved_normalized D hbM hbL) w).mp w.property⟩ =
      d.coordinates w := by
  let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hi : S.relIndex (T : Subgroup G) = 2 := by
    rw [inf_relIndex_left]
    exact source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn
  have h127 := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hWV : ⁅D.fullModule,L⁆ ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  have hWS : ⁅D.fullModule,L⁆ ≤ S := le_inf
    (hWV.trans (D.fullModule_le_sylow h127)) (d.section_le.trans L.le_normalizer)
  have hwS : (w:G) ∈ omegaOneCenterAmbient S := (mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨hWS w.property,elemPow_eq_one_of_isElementaryAbelian (p := 2) (w:G) w.property,hw⟩
  have htw : t*(w:G)*t⁻¹ ∈ D.fullModule :=
    (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule
      (le_normalizer_componentOrbit L T ht)) w).mp (hWV w.property)
  let := D.fullModule_elementary h127
  have hc : Commute (w:G) (t*(w:G)*t⁻¹) := congrArg D.fullModule.subtype
    (mul_comm (⟨w,hWV w.property⟩ : D.fullModule) ⟨_,htw⟩)
  exact d.coordinates_conj_eq_of_centralizes_diagonal inf_le_left hi t ht
    (fun h => htn h.2) (le_inf inf_le_left (inf_le_right.trans hcross)) w hwS hc b
    (moved_normalized D hbM hbL) (partner_normalized D hn ht htn hbM hbL) hbZ

/-- An odd element of the original maximal local group fixing the Sylow
omega-center induces an inner automorphism of the marked natural component. -/
theorem odd_component_inner_of_seed_centralizer
    (degree : ℕ) (hdegree : 1 < degree) (hF : Nat.card F = 2 ^ degree)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (mark : NaturalMarking D e)
    (b : G) (hbM : b ∈ D.maximalLocal) (hbL : b ∈ normalizer (L : Set G))
    (hbZ : b ∈ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hodd : Odd (orderOf b)) :
    normalizerPCoreQuotientAction L ⟨b,hbL⟩ ∈ MulAut.innerSubgroup (L ⧸ pCore 2 L) := by
  obtain ⟨⟨d⟩,t,ht,htn,hcross⟩ := mark
  let W := ⁅D.fullModule,L⁆
  let P := normalizer (L : Set G) ⊓ normalizer (W : Set G)
  let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hSP : S ≤ P := fun s hs => ⟨hs.2,
    moved_normalized D (le_normalizer_componentOrbit L T hs.1) hs.2⟩
  let bP : P := ⟨b,hbL,moved_normalized D hbM hbL⟩
  obtain ⟨τ,hτ⟩ := d.exists_original_quotient_action
    (show P ≤ normalizer (W : Set G) from inf_le_right)
    ((le_inf (show P ≤ normalizer (W : Set G) from inf_le_right)
      ((show P ≤ normalizer (L : Set G) from inf_le_left).trans
        (normalizer_le_normalizer_centralizer L))).trans
          inf_normalizer_le_normalizer_inf)
  let β : P →* MulAut (L ⧸ pCore 2 L) :=
    (normalizerPCoreQuotientAction L).comp (inclusion inf_le_left)
  have htau (p : P) (l : L) (v : Fin 2 → F) :
      τ p (SL2.BinarySmall.natural (e (QuotientGroup.mk' (pCore 2 L) l)) v) =
        SL2.BinarySmall.natural (e (β p (QuotientGroup.mk' (pCore 2 L) l))) (τ p v) := by
    obtain ⟨w,hw⟩ := d.onto (Multiplicative.ofAdd v)
    have hv : (d.coordinates w).toAdd = v := congrArg Multiplicative.toAdd hw
    rw [←hv]
    let l' := L.normalizerMonoidHom
      (inclusion (show P ≤ normalizer (L : Set G) from inf_le_left) p) l
    have hl' : β p (QuotientGroup.mk' (pCore 2 L) l) =
        QuotientGroup.mk' (pCore 2 L) l' := quotientAut_apply_mk _ _ _
    rw [hl']
    change τ p (((SL2.BinarySmall.natural).comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) l (d.coordinates w).toAdd) = _
    rw [←d.equivariant,hτ,hτ]
    refine Eq.trans ?_ (d.equivariant l' (W.normalizerMonoidHom
      (inclusion (show P ≤ normalizer (W : Set G) from inf_le_right) p) w))
    congr 2
    apply Subtype.ext
    change (p:G)*((l:G)*(w:G)*(l:G)⁻¹)*(p:G)⁻¹ =
      ((p:G)*(l:G)*(p:G)⁻¹)*((p:G)*(w:G)*(p:G)⁻¹)*((p:G)*(l:G)*(p:G)⁻¹)⁻¹
    group
  have hsemi : ∀ p : P, ∃ σ : F ≃+* F, ∀ a v, τ p (a • v) = σ a • τ p v := by
    intro p
    apply OneCohomology.CentralCoverOriginalAction.normalizer_semilinear
      (specialLinearNatural 2 (k := F))
      (fun f hf => SL2NaturalOffenders.centralizer_scalar f hf)
      (MulAut.congr e (β p)) (LinearMap.GeneralLinearGroup.toLinearEquiv (τ.asGroupHom p))
    intro g v
    obtain ⟨l,rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) g
    change τ p (SL2.BinarySmall.natural (e (QuotientGroup.mk' (pCore 2 L) l)) v) =
      SL2.BinarySmall.natural (e (β p (e.symm (e (QuotientGroup.mk' (pCore 2 L) l))))) (τ p v)
    rw [e.symm_apply_apply]
    exact htau p l v
  have hlinear : ∀ (a : F) (v : Fin 2 → F), τ bP (a • v) = a • τ bP v := by
    apply SemilinearFixedPointCentralizer.linear_of_odd_of_fixes_invariants τ hsemi
      (S.subgroupOf P)
      ((T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left)).of_injective
        (subgroupOfEquivOfLe hSP).toMonoidHom (subgroupOfEquivOfLe hSP).injective) bP
      (by rwa [←orderOf_injective P.subtype P.subtype_injective bP])
    intro v hv
    obtain ⟨w,hw,hwS⟩ := CentralHall.Nonlinear.HallGeometry.natural_section_fixed_lift
      D degree hdegree hF e d S inf_le_right (hSP.trans inf_le_right)
      (τ.comp (inclusion hSP)) (fun s w => hτ (inclusion hSP s) w) v
      (fun s => hv ⟨⟨s,hSP s.property⟩,s.property⟩)
    rw [←hw,hτ]
    exact congrArg Multiplicative.toAdd
      (seed_centralizer_fixed_coordinates D hn ht htn hcross e d hbM hbL hbZ w hwS)
  let E : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) := LinearEquiv.ofBijective
    { toFun := τ bP, map_add' := map_add (τ bP), map_smul' := hlinear }
    (LinearMap.GeneralLinearGroup.toLinearEquiv (τ.asGroupHom bP)).bijective
  obtain ⟨g,hg⟩ := SL2NaturalOffenders.linear_intertwiner_inner (MulAut.congr e (β bP)) E (by
    intro a v
    obtain ⟨l,rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) a
    change τ bP (SL2.BinarySmall.natural (e (QuotientGroup.mk' (pCore 2 L) l)) v) =
      SL2.BinarySmall.natural (e (β bP (e.symm (e (QuotientGroup.mk' (pCore 2 L) l))))) (τ bP v)
    rw [e.symm_apply_apply]
    exact htau bP l v)
  refine ⟨e.symm g,?_⟩
  apply (MulAut.congr e).injective
  rw [MulAut.congr_conj,e.apply_symm_apply]
  exact hg.symm


/-- Both literal component factors are inner for an odd seed-centralizing
actor. The second factor uses its conjugate by the original Sylow exchanger. -/
theorem odd_pair_inner_of_seed_centralizer
    (degree : ℕ) (hdegree : 1 < degree) (hF : Nat.card F = 2 ^ degree)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) (mark : NaturalMarking D e)
    (b : G) (hbM : b ∈ D.maximalLocal) (hbL : b ∈ normalizer (L : Set G))
    (hbZ : b ∈ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hodd : Odd (orderOf b)) :
    normalizerQuotientAction (localOrbit T L) (pCore 2 (localOrbit T L)) ⟨b,hbM⟩ ∈
      MulAut.innerSubgroup (localOrbit T L ⧸ pCore 2 (localOrbit T L)) := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp hn
  let M := D.maximalLocal
  let N := (normalizer (L : Set G)).subgroupOf M
  have htM : t ∈ M := le_normalizer_componentOrbit L T ht
  have hi : N.index = 2 := normalizer_relIndex_eq_two_of_pair M L
    (L.map (MulAut.conj t).toMonoidHom) (source_nonnormal_maximal_pair D hn ht htn)
    t htM (fun he => htn (mem_normalizer_iff_map_conj_eq.mpr he))
  let : N.Normal := normal_of_index_eq_two hi
  let x : G := t⁻¹*b*t
  have hxM : x ∈ M := M.mul_mem (M.mul_mem (M.inv_mem htM) hbM) htM
  have hxL : x ∈ normalizer (L : Set G) := by
    have hh := (inferInstance : N.Normal).conj_mem (⟨b,hbM⟩ : M) hbL (⟨t,htM⟩ : M)⁻¹
    change t⁻¹*b*(t⁻¹)⁻¹ ∈ normalizer (L : Set G) at hh
    simpa only [inv_inv] using hh
  have htZ : t ∈ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
    intro z hz
    exact (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht).symm
  have hxZ : x ∈ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) :=
    mul_mem (mul_mem (inv_mem htZ) hbZ) htZ
  have hxo : Odd (orderOf x) := by
    have he := orderOf_injective (MulAut.conj t⁻¹).toMonoidHom (MulAut.conj t⁻¹).injective b
    have ho : Odd (orderOf ((MulAut.conj t⁻¹).toMonoidHom b)) := he.symm ▸ hodd
    simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv] using ho
  obtain ⟨a,ha⟩ := odd_component_inner_of_seed_centralizer D degree hdegree hF e hn mark
    b hbM hbL hbZ hodd
  obtain ⟨a',ha'⟩ := odd_component_inner_of_seed_centralizer D degree hdegree hF e hn mark
    x hxM hxL hxZ hxo
  let R := localOrbit T L
  obtain ⟨q,hfirst,hsecond⟩ := source_original_natural_pair_quotient D degree hdegree hF e hn ht htn
  let f := q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))
  let α := MulAut.congr q (normalizerQuotientAction R (pCore 2 R) ⟨b,hbM⟩)
  have hα (r : R) : α (f r) = f (R.normalizerMonoidHom ⟨b,hbM⟩ r) := by
    change q (quotientAut (pCore 2 R) _ (q.symm (q (QuotientGroup.mk' (pCore 2 R) r)))) = _
    rw [q.symm_apply_apply,quotientAut_apply_mk]
    rfl
  have h1 (z : SL(2,F)) : α (z,1) = (e a*z*(e a)⁻¹,1) := by
    obtain ⟨l,rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) z
    change α (e (QuotientGroup.mk' (pCore 2 L) l),1) = _
    rw [←hfirst]
    change α (f _) = _
    rw [hα]
    let l' := L.normalizerMonoidHom ⟨b,hbL⟩ l
    have he : R.normalizerMonoidHom ⟨b,hbM⟩ ⟨l,le_componentOrbit L T l.property⟩ =
        ⟨l',le_componentOrbit L T l'.property⟩ := rfl
    rw [he]
    change q (QuotientGroup.mk' _ _) = _
    rw [hfirst]
    congr 1
    have hh := MulEquiv.congr_fun ha (QuotientGroup.mk' (pCore 2 L) l)
    change _ = quotientAut (pCore 2 L) _ _ at hh
    rw [quotientAut_apply_mk] at hh
    exact (congrArg e hh).symm.trans
      ((e.map_mul _ _).trans (congrArg₂ (· * ·) (e.map_mul _ _) (e.map_inv _)))
  have h2 (z : SL(2,F)) : α (1,z) = (1,e a'*z*(e a')⁻¹) := by
    obtain ⟨l,rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) z
    change α (1,e (QuotientGroup.mk' (pCore 2 L) l)) = _
    rw [←hsecond]
    change α (f _) = _
    rw [hα]
    let l' := L.normalizerMonoidHom ⟨x,hxL⟩ l
    have he : R.normalizerMonoidHom ⟨b,hbM⟩ (originalConjugateOrbitInclusion ht l) =
        originalConjugateOrbitInclusion ht l' := by
      apply Subtype.ext
      change b*(t*(l:G)*t⁻¹)*b⁻¹ = t*(x*(l:G)*x⁻¹)*t⁻¹
      dsimp [x]
      group
    rw [he]
    change q (QuotientGroup.mk' _ _) = _
    rw [hsecond]
    congr 1
    have hh := MulEquiv.congr_fun ha' (QuotientGroup.mk' (pCore 2 L) l)
    change _ = quotientAut (pCore 2 L) _ _ at hh
    rw [quotientAut_apply_mk] at hh
    exact (congrArg e hh).symm.trans
      ((e.map_mul _ _).trans (congrArg₂ (· * ·) (e.map_mul _ _) (e.map_inv _)))
  have he : α = MulAut.conj (e a,e a') := by
    apply MulEquiv.ext
    intro z
    have hz : z = (z.1,1)*(1,z.2) := by simp
    rw [hz,map_mul,h1,h2]
    simp only [Prod.mk_mul_mk,one_mul,mul_one,MulAut.conj_apply,Prod.inv_mk]
  refine ⟨q.symm (e a,e a'),?_⟩
  apply (MulAut.congr q).injective
  rw [MulAut.congr_conj,q.apply_symm_apply]
  exact he.symm


end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
